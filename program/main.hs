module Main where
    import Data.Rewriting.Term as Term
    import Data.Rewriting.Rule as Rule
    import Types
    import IterativeLexicographicalGenerators
    import Helpers
    import Lexicographical
    import TRSDedekind
    --import Reader
    
    --For now, to see different TRS you can change the TRS to TRSDedekind, TRSAckermann or TRSPredecate.
    --Note, I just found out that for TRSPredicate the iterative approach hangs a very very long time, but I am looking into that.

    --Also, I ran this on a windows machine, and last thursday I had trouble getting it to work on my linux machine.

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
