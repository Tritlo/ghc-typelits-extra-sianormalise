-- Copyright (c) 2020 Matthías Páll Gissurarson
module GHC.TypeLits.Extra.SIA.Solver where

import GhcPlugins hiding (TcPlugin)
import TcRnTypes (TcPlugin(..),TcPluginResult(TcPluginOk))
import TcPluginM 
import Constraint
import Data.Maybe (catMaybes)
import Control.Monad (when, guard)
import TcEvidence
import Predicate (isEqPrimPred)

import Data.List (isPrefixOf)

symmetricIdempotentAssociativeTyCons :: [String]
symmetricIdempotentAssociativeTyCons = ["Max"]

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
    initialize = return ()
    solve :: () -> [Ct] -> [Ct] -> [Ct] -> TcPluginM TcPluginResult
    solve opts _ _ wanted = do { 
          ; dflags <- unsafeTcPluginTcM getDynFlags
          ; let pprDebug :: Outputable a => String -> a -> TcPluginM ()
                pprDebug str a =
                   when debug $
                      tcPluginIO $ putStrLn (str ++ " " ++ showSDoc dflags (ppr a))
          ; mapM_ (pprDebug "Wanted:") wanted
          ; tyCons <- mapM getTLETyCon (symmetricIdempotentAssociativeTyCons ++ additionalCons)
          ; (proofs, new) <- (concat <$>) . unzip . catMaybes <$> mapM (solveTLE tyCons) wanted
          ; mapM_ (pprDebug "Sols:") (zip proofs new)
          ; return $ TcPluginOk proofs new }
    stop _ = return ()

solveTLE :: [Name] -> Ct -> TcPluginM (Maybe ((EvTerm, Ct), [Ct]))
solveTLE tyCons ct@(CNonCanonical{}) =
  case splitTyConApp_maybe (ctPred ct) of
      Just (topCon, [lhs_kind,rhs_kind,lhs_ty,rhs_ty])  |
               (isEqPrimPred (ctPred ct) && lhs_kind `eqType` rhs_kind) ->
                     let check = check' tyCons topCon lhs_kind
                     in (check lhs_ty rhs_ty) `orMaybeM` (check rhs_ty lhs_ty)
      _ -> return Nothing
  where
    check' :: [Name] -> TyCon -> Kind -> Type -> Type -> TcPluginM (Maybe ((EvTerm, Ct),[Ct]))
    check' tyCons top_con kind lhs_ty rhs_ty =
        case splitTyConApp_maybe rhs_ty of
           Just (tc, [n1,n2]) | getName tc `elem` tyCons ->
               if n1 `eqType` n2 
               then do -- idempotent: op a a = a 
                      let new_pred = (mkTyConApp top_con [kind, kind, n1, lhs_ty])
                          sol = (evCoercion $ mkReflCo Nominal (mkTyConApp tc [n1,n2]), ct)
                      newCt <- CNonCanonical <$> newWanted (ctLoc ct) new_pred
                      let located = newCt `setCtLoc` (ctLoc ct)
                      return $ Just (sol, [located])
               else  -- op (op a b) a = op a (op b b)
                     let checkNested ty1 ty2 =
                           case splitTyConApp_maybe ty1 of
                             Just (tc2, [a,b]) | tc2 == tc && (a `eqType` ty2 || b `eqType` ty2) -> do
                                   let unnested = mkTyConApp tc [ty2, if a `eqType` ty2 then b else a]
                                       new_pred = mkTyConApp top_con [kind, kind, lhs_ty, unnested]
                                       sol = (evCoercion $ mkReflCo Nominal $
                                                   mkTyConApp top_con [kind, kind, rhs_ty, unnested] 
                                               ,ct)
                                   newCt <- CNonCanonical <$> newWanted (ctLoc ct) new_pred
                                   let located = newCt `setCtLoc` (ctLoc ct)
                                   return $ Just (sol, [located])
                             _ -> return Nothing
                     in checkNested n1 n2 `orMaybeM` checkNested n2 n1 
           _ -> return Nothing
solveTLE _ _ = return Nothing

orMaybeM :: Monad m => m (Maybe a) -> m (Maybe a) -> m (Maybe a)
orMaybeM a1 a2 = do res <- a1
                    case res of
                      Just _ -> return res
                      _ -> a2

getTLETyCon :: String -> TcPluginM Name 
getTLETyCon name =
      do fpmRes <- findImportedModule (mkModuleName "GHC.TypeLits.Extra") Nothing
         case fpmRes of
            Found _ mod  -> lookupOrig mod (mkTcOcc name)
            _ -> pprPanic "TyCon not found:" (text name)
