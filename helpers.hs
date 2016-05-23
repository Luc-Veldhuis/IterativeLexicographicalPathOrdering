module Helpers where
    import Types
    import Data.Rewriting.Term as Term
    import Data.Rewriting.Rule as Rule
    import Data.Rewriting.Rules as Rules
    import Data.Set

    flatten :: [[a]] -> [a]
    flatten [] = []
    flatten (h:t) = h ++ (flatten t)

    makeList:: Int -> [Int]
    makeList 0 = []
    makeList n = makeList (n-1) ++ [n]

    containsTerm :: (Eq f, Eq v) => [Reduct f v v'] -> Term  f v -> Bool
    containsTerm reductions term = if length reductions == 0 then 
            False 
        else if result (head(reductions)) == term then
            True
        else (containsTerm (tail(reductions)) term)

    getFunctionName :: (Eq f, Eq v, Ord f) => (Term (FunctionSymbol f) v) -> f 
    getFunctionName (Fun f list) = name f

    getFunctionSymbol::(Eq f, Eq v, Ord f) => (Term (FunctionSymbol f) v) -> (FunctionSymbol f) 
    getFunctionSymbol (Fun f list) = f

    makeTransitiveRule :: (Eq f, Eq v, Ord f, Ord rhs) => [Rule (FunctionSymbol f) rhs] -> (Term (FunctionSymbol f) v) -> (Term (FunctionSymbol f) v) -> [Rule (FunctionSymbol f) rhs]
    makeTransitiveRule order termLeft termRight = if maybe False (\x->x) (isDerivable termLeft order termRight) then [Fun (FunctionSymbol (getFunctionName termLeft) (arity (getFunctionSymbol termLeft)) True) [] --> Fun (FunctionSymbol (getFunctionName termRight) (arity (getFunctionSymbol termRight)) True) []] else []

    makeTransitiveRules::(Eq f, Eq v, Ord f, Ord rhs) => [(Term (FunctionSymbol f) v)] -> [Rule (FunctionSymbol f) rhs] -> (Term (FunctionSymbol f) v) -> [Rule (FunctionSymbol f) rhs]
    makeTransitiveRules terms order termLeft = flatten (Prelude.map (makeTransitiveRule order termLeft) terms)

    makeTransitive ::(Eq f, Eq v, Ord f, Ord rhs) => [Rule (FunctionSymbol f) rhs] -> [Term (FunctionSymbol f) v] -> [Rule (FunctionSymbol f) rhs]
    makeTransitive order terms = flatten (Prelude.map (makeTransitiveRules terms order) terms)


    --Remove reflexivity from terms
    makeIrreflexive :: (Eq lhs, Eq rhs) => [Rule lhs rhs] -> [Rule lhs rhs]
    makeIrreflexive order = Prelude.filter (\x -> (lhs x) /= (rhs x)) order

    --get the arity of a term without arity if a list with terms with arity is supplied
    getArity :: (Eq f, Eq v, Ord f) => [(Term f v, Int)] -> Term f v -> Int
    getArity terms term = snd (head(Prelude.filter (\x -> if fst x == term then True else False) terms)) --not the nicest, but filter should return only 1 element

    --Copy a term x number of times (helper for the copy function)
    copyTerm::(Eq f, Eq v, Ord f) => (Term f v) -> Int -> [Term f v]
    copyTerm term 0 = []
    copyTerm term times = term : (copyTerm term (times -1))

    --Casts the list into a set and back to remove duplicates POSSIBLE BUG: IS THE ORDER CHANGED???
    removeDuplicates :: (Ord a) => [a] -> [a]
    removeDuplicates list = toList(fromList(list))

    containsRule:: (Eq lhs, Eq rhs) => [Rule lhs rhs] -> (Rule lhs rhs) -> Bool
    containsRule [] rule = False
    containsRule (h:t) rule = if(h == rule) then True else containsRule t rule

    printRuleApplications :: (Show f, Show v, Show v') => [Reduct f v v'] -> IO[()]
    printRuleApplications reductions = mapM (\r -> print(result r)) reductions

    getDerivation:: (Eq f, Eq v, Ord f, Ord rhs) => (Term f v) -> Int -> [Reduct f v v'] -> [Rule f rhs] -> (Maybe Bool)
    getDerivation term counter reductions trs= if (containsTerm reductions term) then 
            Just True
        else if length reductions /= 0 && counter /= 0 then
            getDerivation term (counter-1) (flatten (Prelude.map (\x -> (fullRewrite trs (result x))) reductions)) trs
        else 
            Nothing

    isDerivable ::(Eq f, Eq v, Ord f, Ord rhs) => (Term f v) -> [Rule f rhs] -> (Term f v) -> (Maybe Bool)
    isDerivable leftTerm reductionRules rightTerm = let result = getDerivation rightTerm (length reductionRules +1) (fullRewrite reductionRules leftTerm) reductionRules in 
        if leftTerm == rightTerm then Just True else result

    getFunctionSymbolsFromTerm :: (Eq f, Eq v, Ord f) => Term (FunctionSymbol f) v -> [Term (FunctionSymbol f) v]
    getFunctionSymbolsFromTerm (Fun f list) = if length list > 0 then (Fun f []) : flatten(Prelude.map getFunctionSymbolsFromTerm list) else []
    getFunctionSymbolsFromTerm (Var v) = []

    getFunctionSymbolsFromRule :: (Eq f, Eq v, Ord f) => Rule (FunctionSymbol f) v -> [Term (FunctionSymbol f) v]
    getFunctionSymbolsFromRule rule = (getFunctionSymbolsFromTerm (lhs rule)) ++ (getFunctionSymbolsFromTerm (rhs rule))

    getFunctionSymbolsFromRules :: (Eq f, Eq v, Ord f) => [Rule (FunctionSymbol f) v] -> [Term (FunctionSymbol f) v]
    getFunctionSymbolsFromRules trs = flatten(Prelude.map getFunctionSymbolsFromRule trs)