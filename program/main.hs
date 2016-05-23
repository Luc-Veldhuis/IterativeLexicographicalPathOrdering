module Main where
    import Data.Rewriting.Term as Term
    import Data.Rewriting.Rule as Rule
    import Types
    import IterativeLexicographicalGenerators
    import Helpers
    import Lexicographical

    --Function symbols
    mul = Fun (FunctionSymbol "mul" 2 False)
    add = Fun (FunctionSymbol "add" 2 False)
    suc = Fun (FunctionSymbol "suc" 1 False)
    zero = Fun (FunctionSymbol "zero" 0 False) []

    --Variables

    x = Var 1
    y = Var 2
    z = Var 3

    --Dedekind rules
    termRewiteSystem = [mul[x, suc[y]] --> add[x, mul [x, y]]
        , add[x, zero] --> x
        , mul[x, zero] --> zero
        , add[x, suc[y]] --> suc[add[x,y]]]

    --Order
    order = [mul[] --> add[], add[] --> suc[]]

    --Check if we found a lexicographical ordering
    isIterativeLexicographicalOrdered :: (Eq f, Eq v, Ord f, Ord v) => [Rule (FunctionSymbol f) v] -> [Rule (FunctionSymbol f) v] -> (Maybe Bool)
    isIterativeLexicographicalOrdered iterativeRules trs = if (and (Prelude.map (\rule -> (maybe False (\x->x)(isDerivable (lhs rule) iterativeRules (rhs rule)))) trs)) then Just True else Nothing

    isLexicographicalOrdered :: (Eq f, Eq v, Ord f, Ord v) => [Rule (FunctionSymbol f) v] -> [Rule (FunctionSymbol f) v] -> (Maybe Bool)
    isLexicographicalOrdered order trs = if and (Prelude.map (\rule -> maybe False (\y->y) (isLexicographical order (lhs rule) (rhs rule))) trs) then Just True else Nothing


    --iterative
    main :: IO()
    main = let iterativeRules = generateIterLexico order (getFunctionSymbolsFromRules termRewiteSystem ) in
        let result = (isIterativeLexicographicalOrdered iterativeRules termRewiteSystem) in
            if maybe False (\x->x) result then print("The TRS is lexicographical ordered") else print("The TRS might or might not be lexicographical ordered")

    --recursive
    main2 :: IO()
    main2 = let result = (isLexicographicalOrdered order termRewiteSystem) in
        if maybe False (\x->x) result then print("The TRS is lexicographical ordered") else print("The TRS might or might not be lexicographical ordered")