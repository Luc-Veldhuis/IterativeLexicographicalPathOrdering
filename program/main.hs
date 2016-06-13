module Main where
    import Data.Rewriting.Term as Term
    import Data.Rewriting.Rule as Rule
    import Data.Rewriting.Rules as Rules
    import Types
    import IterativeLexicographicalGenerators
    import Helpers
    import Lexicographical
    import TRSDedekind
    import Reader
    
    --For now, to see different TRS you can change the TRS to TRSDedekind, TRSAckermann or TRSPredecate.
    --Note, I just found out that for TRSPredicate the iterative approach hangs a very very long time, but I am looking into that.


    --Check if we found a lexicographical ordering
    isIterativeLexicographicalOrdered :: (EOS f, EOS v) => [Rule (FunctionSymbol f) v] -> [Rule (FunctionSymbol f) v] -> (Maybe Bool)
    isIterativeLexicographicalOrdered iterativeRules trs = if (and (Prelude.map (\rule -> (maybe False (\x->x)(isDerivable (lhs rule) iterativeRules (rhs rule)))) trs)) then Just True else Nothing

    isLexicographicalOrdered :: (EOS f, EOS v) => [Rule (FunctionSymbol f) v] -> [Rule (FunctionSymbol f) v] -> (Maybe Bool)
    isLexicographicalOrdered order trs = if and (Prelude.map (\rule -> maybe False (\y->y) (isLexicographical order (lhs rule) (rhs rule))) trs) then Just True else Nothing

    iterativeAppoach :: [Rule (FunctionSymbol [Char]) Int] -> [Rule (FunctionSymbol [Char]) Int] -> IO()
    iterativeAppoach trs trsOrder = let iterativeRules = generateIterLexico (makeIrreflexive $ makeTransitive trsOrder) (getFunctionSymbolsFromRules trs ) in
        let result = (isIterativeLexicographicalOrdered iterativeRules trs) in
            if maybe False (\x->x) result then print("The TRS is lexicographical ordered") else print("The TRS might or might not be lexicographical ordered")

    recursiveApproch :: [Rule (FunctionSymbol [Char]) Int] -> [Rule (FunctionSymbol [Char]) Int] -> IO()
    recursiveApproch trs trsOrder = let result = (isLexicographicalOrdered (makeIrreflexive $ makeTransitive trsOrder) trs) in
        if maybe False (\x->x) result then print("The TRS is lexicographical ordered") else print("The TRS might or might not be lexicographical ordered")

    --iterative
    main :: IO()
    main = iterativeAppoach termRewiteSystem order

    --recursive
    main2 :: IO()
    main2 = recursiveApproch termRewiteSystem order

    iterativeFromInput :: String -> String -> IO()
    iterativeFromInput trsFile orderFile = 
        do
        trs <- processTRS trsFile
        order <- processOrder orderFile
        iterativeAppoach trs order

    recursiveFromInput :: String -> String -> IO()
    recursiveFromInput trsFile orderFile = 
        do
        trs <- processTRS trsFile
        order <- processOrder orderFile
        recursiveApproch trs order

    test = 
        do
        order <- processOrder "order.txt"
        return $greater (makeIrreflexive $ makeTransitive order) (FunctionSymbol "mul" 2 False) (FunctionSymbol "mul" 0 False)

    test2 = 
        do
        trs <- processTRS "trs.txt"
        return trs