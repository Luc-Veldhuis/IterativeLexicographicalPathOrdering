{-# LANGUAGE FlexibleInstances #-}
module Types where
    import Data.Rewriting.Rule as Rule

    data FunctionSymbol f = FunctionSymbol {name:: f, arity :: Int, star :: Bool} deriving (Show, Eq, Ord, Read)
    (-->) = Rule
    class (Eq v, Ord v, Show v) => EOS v
    instance EOS Int
    instance EOS [Char]
