module Types where
    import Data.Rewriting.Rule as Rule

    data FunctionSymbol f = FunctionSymbol {name:: f, arity :: Int, star :: Bool} deriving (Show, Eq, Ord, Read)
    (-->) = Rule