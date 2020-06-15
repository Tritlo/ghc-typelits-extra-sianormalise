-- Copyright (c) 2020 Matthías Páll Gissurarson
{-# LANGUAGE TypeFamilies, KindSignatures, PolyKinds, CPP #-}
module GHC.TypeLits.Extra.SIA.Solver where

import Data.Maybe (catMaybes)
import Control.Monad (when, guard)
import Data.IORef
import Data.Function (on)
import Data.Set (Set)
import qualified Data.Set as Set

import Data.List (isPrefixOf)

#if __GLASGOW_HASKELL__ > 810

import GHC.Plugins hiding (TcPlugin)
import GHC.Tc.Plugin
import GHC.Tc.Types.Evidence
import GHC.Tc.Types.Constraint
import GHC.Core.TyCo.Rep

#else

import GhcPlugins hiding (TcPlugin)
import TcPluginM
import TcEvidence
import TyCoRep (UnivCoProvenance(..))
import TcRnTypes

#if __GLASGOW_HASKELL__ < 810

isEqPrimPred = isCoVarType
instance Outputable SDoc where
  ppr x = x

#else

import Predicate (isEqPrimPred)
import Constraint

#endif
#endif

symmetricIdempotentAssociativeTyCons :: [String]
symmetricIdempotentAssociativeTyCons = ["Max", "Min"]

-- Wrapper for Type that we can Ord
data TySetTy = TST Type

instance Outputable TySetTy where
    ppr (TST t) = ppr t

instance Eq TySetTy where
  TST ty1 == TST ty2 = eqType ty1 ty2

instance Ord TySetTy where
  compare (TST ty1) (TST ty2) = nonDetCmpType ty1 ty2

plugin :: Plugin
plugin = defaultPlugin { tcPlugin = Just . extraExtraPlugin
                       , pluginRecompile = purePlugin }
extraExtraPlugin :: [CommandLineOption] -> TcPlugin
extraExtraPlugin opts = TcPlugin initialize solve stop
  where 
    debug = "debug" `elem` opts
    -- You can add more TyCons with 
    -- -fplugin-opt=GHC.TypeLits.Extra.SIA.Solver:--tc=Min
    additionalCons = map (drop 5) $ filter (isPrefixOf "--tc=") $ opts
    initialize = tcPluginIO $ newIORef (Set.empty :: Set TySetTy)
    solve :: IORef (Set TySetTy) -> [Ct] -> [Ct] -> [Ct] -> TcPluginM TcPluginResult
    solve tried_ref given derived wanted = do { 
          ; dflags <- unsafeTcPluginTcM getDynFlags
          ; let pprDebug :: Outputable a => String -> a -> TcPluginM ()
                pprDebug str a =
                   when debug $
                      tcPluginIO $ putStrLn (str ++ " " ++ showSDoc dflags (ppr a))
          ; pprDebug "Solving" empty
          ; mapM_ (pprDebug "Given:") given
          ; mapM_ (pprDebug "Derived:") derived
          ; mapM_ (pprDebug "Wanted:") wanted
          ; tyCons <- mapM getTLETyCon (symmetricIdempotentAssociativeTyCons ++ additionalCons)
          ; tried <- tcPluginIO $ readIORef tried_ref
          ; (proofs, new) <- (concat <$>) . unzip . catMaybes <$> mapM (solveTLE tried tyCons) wanted
          ; tcPluginIO $ writeIORef tried_ref (tried `Set.union` (Set.fromList $ map (TST . ctPred) new))
          ; mapM_ (pprDebug "Proofs:") proofs
          ; mapM_ (pprDebug "New:") new
          ; return $ TcPluginOk proofs new }
    stop _ = return ()

solveTLE :: Set TySetTy -> [Name] -> Ct -> TcPluginM (Maybe ((EvTerm, Ct), [Ct]))
solveTLE tried tyCons ct@(CNonCanonical{}) =
  case splitTyConApp_maybe (ctPred ct) of
      Just (topCon, [lhs_kind,rhs_kind,lhs_ty,rhs_ty])  |
               (isEqPrimPred (ctPred ct) && lhs_kind `eqType` rhs_kind) ->
                     let check = check' tried tyCons topCon lhs_kind
                     in check rhs_ty lhs_ty `orMaybeM` check rhs_ty lhs_ty
      _ -> return Nothing
  where
    check' :: Set TySetTy -> [Name] -> TyCon -> Kind -> Type -> Type -> TcPluginM (Maybe ((EvTerm, Ct),[Ct]))
    check' tried tyCons top_con kind lhs_ty rhs_ty =
        case splitTyConApp_maybe rhs_ty of
           Just (tc, [n1,n2]) | getName tc `elem` tyCons ->
            let -- Symmetric: op a a = a
                checkIdempotent ty1 ty2 = 
                  case splitTyConApp_maybe ty1 of
                    -- Shortcut when we don't have to solve any type familes
                    _ | ty1 `eqType` ty2 ->
                      return $ Just ((mkProof "Idempotent" Nominal ty1 ty2, ct), [])
                    -- Avoid trying to construct the infinite type:
                    Just (tc2, _) | tc2 == tc  &&
                                    isTyVarTy ty2 && 
                                    (getTyVar "Impossible!" ty2) `elem`
                                    (tyCoVarsOfTypeWellScoped ty1) ->
                        return Nothing
                    Just (tc2, [a,b]) | tc2 == tc -> do
                      let np1 = mkTyConApp top_con [kind, kind, ty1, ty2]
                          np2 = mkTyConApp top_con [kind, kind, ty1, lhs_ty]
                          sol = (mkProof "Idempotent" Nominal np1 np2, ct)
                      cts <- mapM (newNonCanonicalCt (ctLoc ct)) [np1,np2]
                      (tcPluginIO $ putStrLn $ showSDocUnsafe $ ppr cts)
                      return $ if (TST np1) `Set.member` tried then Nothing else Just (sol, cts)
                    _ -> return Nothing
                -- Associative: op (op a b) c = op a (op b c)
                checkAssociative ty1 ty2 =
                  case splitTyConApp_maybe ty1 of
                    Just (tc2, [a,b]) | tc2 == tc -> do
                      let unnested = mkTyConApp tc [a, mkTyConApp tc [b, ty2]]
                          new_pred = mkTyConApp top_con [kind, kind, unnested, lhs_ty]
                          sol = (mkProof "Associative" Nominal rhs_ty unnested, ct)
                      newCt <- newNonCanonicalCt (ctLoc ct) new_pred
                      return $ if (TST new_pred) `Set.member` tried then Nothing else Just (sol, [newCt])
                    _ -> return Nothing
               -- Symmetric: op a b = op b a
                checkSymmetric ty1 ty2 = do
                   let sym_ty = mkTyConApp tc [ty2, ty1]
                       new_pred = mkTyConApp top_con [kind, kind, sym_ty, lhs_ty]
                       sol = (mkProof "Symmetric" Nominal rhs_ty sym_ty, ct)
                   newCt <- newNonCanonicalCt (ctLoc ct) new_pred
                   return $ if (TST new_pred) `Set.member` tried then Nothing else Just (sol, [newCt])
            in checkIdempotent n1 n2 `orMaybeM` checkAssociative n1 n2 `orMaybeM` checkSymmetric n1 n2
           _ -> return Nothing
solveTLE _ _ _ = return Nothing

newNonCanonicalCt :: CtLoc -> PredType -> TcPluginM Ct
newNonCanonicalCt loc ty = (flip setCtLoc loc . CNonCanonical) <$> newWanted loc ty

orMaybeM :: Monad m => m (Maybe a) -> m (Maybe a) -> m (Maybe a)
orMaybeM a1 a2 = do res <- a1
                    case res of
                      Just _ -> return res
                      _ -> a2

mkProof :: String -> Role -> Type -> Type -> EvTerm
mkProof str role ty1 ty2 = evCoercion $ mkUnivCo (PluginProv str) role ty1 ty2

getTLETyCon :: String -> TcPluginM Name 
getTLETyCon name =
      do fpmRes <- findImportedModule (mkModuleName "GHC.TypeLits.Extra") Nothing
         case fpmRes of
            Found _ mod  -> lookupOrig mod (mkTcOcc name)
            _ -> pprPanic "TyCon not found:" (text name)
