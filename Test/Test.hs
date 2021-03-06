{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Extra.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Extra.SIA.Solver 
                -fplugin-opt=GHC.TypeLits.Extra.SIA.Solver:debug #-}
{-# OPTIONS_GHC -fconstraint-solver-iterations=10 -dcore-lint #-}
{-# LANGUAGE TypeFamilies #-}
module Main where

import GHC.TypeLits
import GHC.TypeLits.Extra

f :: Max (Max n1 n2) n1 ~ Max n1 n2 => IO ()
f = print "works!"

f6 :: Max (Max n1 n2) n1 ~ Max n1 n2 => IO ()
f6 = print "works!"

f2 :: Max n1 (Max n1 n2) ~ Max n1 n2 => IO ()
f2 = print "works!"

f3 :: Min n1 (Min n1 n2) ~ Min n1 n2 => IO ()
f3 = print "works!"

f4 :: Max (Max (Max n1 n2) n2) n2 ~ Max n1 n2 => IO ()
f4 = print "works!"

f5 :: Max (Max n1 n2) (Max n2 n1) ~ Max n1 n2 => IO ()
f5 = print "works!"


f7 :: Max n nv ~ Max (Max n nv) nv => IO ()
f7 = print "hey"

f8 :: Max n nv ~ Max nv nv => IO ()
f8 = print "hey"

g :: Max n n ~ n => IO ()
g = print "works!"

main :: IO ()
main =  f >> f2 >> f3 >> f4 >> f5 >> f6 >> f7 >> g >> f8
