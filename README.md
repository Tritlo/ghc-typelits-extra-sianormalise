GHC.TypeLits.Extra.SIA
=====================

A plugin that tries to solve wanted constraints inlolving symmetric, associative
and idempotent operations laws for certain operations. Note that you might have
to bump the allowed iterations for very nested operations:

```
{-# OPTIONS_GHC -fconstraint-solver-iterations=10 #-}

```

By default it works for `Max` and `Min` from `GHC.TypeLits.Extra`, but additional
operations from `GHC.TypeLits.Extra` can be added by adding e.g.:
```
{-# OPTIONS_GHC -fplugin-opt=GHC.TypeLits.Extra.SIA.Solver:--tc=Max #-}

```
