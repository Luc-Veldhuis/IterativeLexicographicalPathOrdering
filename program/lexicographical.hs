module Lexicographical where
    import Types
    import Helpers
    import Data.Rewriting.Term as Term
    import Data.Rewriting.Rule as Rule

    isLexicographicalList :: (Eq f, Eq v, Ord f, Ord rhs) => [Rule (FunctionSymbol f) rhs] ->[Term (FunctionSymbol f) v] -> [Term (FunctionSymbol f) v] -> (Maybe Bool)
    isLexicographicalList order [] [] = Nothing
    isLexicographicalList order [] list2 = Just False
    isLexicographicalList order list1 [] = Just True
    isLexicographicalList order list1 list2 = if head(list1) == head(list2) then isLexicographicalList order (tail list1) (tail list2) else isGreater order (head list1) (head list2)

    isGreater :: (Eq f, Eq v, Ord f, Ord rhs) => [Rule (FunctionSymbol f) rhs] ->(Term (FunctionSymbol f) v) -> (Term (FunctionSymbol f) v) -> (Maybe Bool)
    isGreater irreflexiveOrder (Var v1) (Var v2) = if v1 /= v2 then Just True else Just False --LPO1
    isGreater irreflexiveOrder (Var v) (Fun f list) = Just False --trivial
    isGreater irreflexiveOrder (Fun f list) (Var v) = Just True ----LPO1
    isGreater irreflexiveOrder (Fun f1 list1) (Fun f2 list2) = if or (Prelude.map (\x -> or [(maybe False (\y->y) (isGreater irreflexiveOrder x (Fun f2 list2))), (x == (Fun f2 list2))] ) list1) then Just True --lpo2a
        else if (and [(maybe False (\x->x) (isDerivable (Fun f1 (emptyList list1)) irreflexiveOrder (Fun f2 (emptyList list2)))), and (Prelude.map (\x-> maybe False (\y->y) (isGreater irreflexiveOrder (Fun f1 list1) x) ) list2)]) then Just True--lpo2b
        else if (and [(f1 == f2), (and (Prelude.map (\x-> maybe False (\y->y) (isGreater irreflexiveOrder (Fun f1 list1) x)) list2))]) then (isLexicographicalList irreflexiveOrder list1 list2) --lpo2c
        else Nothing

    isLexicographical::(Eq f, Eq v, Ord f, Ord rhs) =>  [Rule (FunctionSymbol f) rhs] ->(Term (FunctionSymbol f) v) -> (Term (FunctionSymbol f) v) -> (Maybe Bool)
    isLexicographical order leftTerm rightTerm = let irreflexiveOrder = makeIrreflexive order in
        isGreater irreflexiveOrder leftTerm rightTerm

    test1 :: (Eq f, Eq v, Ord f, Ord rhs) => [Rule (FunctionSymbol f) rhs] ->(Term (FunctionSymbol f) v) -> (Term (FunctionSymbol f) v) -> (Maybe Bool)
    test1 order (Fun f1 list1) (Fun f2 list2) = (isDerivable (Fun f1 (emptyList list1)) order (Fun f2 (emptyList list2)))