module Helpers where
    import Types
    import Data.Rewriting.Term as Term
    import Data.Rewriting.Rule as Rule
    import Data.Rewriting.Rules as Rules
    import Data.Set

    setStar :: (EOS f) => (FunctionSymbol f) -> (FunctionSymbol f)
    setStar f = f { star = True }

    unsetStar :: (EOS f) => (FunctionSymbol f) -> (FunctionSymbol f)
    unsetStar f = f { star = False }

    splits :: (EOS f) => [Term (FunctionSymbol f) Int] -> [([Term (FunctionSymbol f) Int],[Term (FunctionSymbol f) Int])]
    splits [] = []
    splits (x:list) = ([],x:list) : (Prelude.map (\(l,r) -> (x:l,r)) $ splits list)

    containsTerm :: (EOS f, EOS v) => [Reduct (FunctionSymbol f) v v'] -> Term (FunctionSymbol f) v -> Bool
    containsTerm [] term = False
    containsTerm reductions term = or $ Prelude.map (term ==) $ Prelude.map result reductions

    getFunctionName :: (EOS f, EOS v) => (Term (FunctionSymbol f) v) -> f 
    getFunctionName (Fun f list) = name f

    getFunctionNameInt :: (EOS f) => (Term (FunctionSymbol f) Int) -> f 
    getFunctionNameInt (Fun f list) = name f

    getFunctionSymbol::(EOS f, EOS v) => (Term (FunctionSymbol f) v) -> (FunctionSymbol f) 
    getFunctionSymbol (Fun f list) = f

    --makeTransitiveRule :: (FunctionSymbol [Char]) -> [Rule (FunctionSymbol [Char]) Int] -> (FunctionSymbol [Char]) -> [Rule (FunctionSymbol [Char]) Int]
    --makeTransitiveRule left order right = if maybe False (\x->x) (isDerivable (Fun left ([]::[Term (FunctionSymbol [Char]) Int])) order (Fun right ([]::[Term (FunctionSymbol [Char]) Int]))) then [Fun left [] --> Fun right []] else []

    --makeTransitive :: [Rule (FunctionSymbol [Char]) Int] -> [Rule (FunctionSymbol [Char]) Int]
    --makeTransitive order = let allFunctionSymbols = getFunctionSymbolsFromRules order in
    --    concat $ Prelude.map (\left -> concat $ Prelude.map (\right -> makeTransitiveRule left order right) allFunctionSymbols) allFunctionSymbols


    --Trick to generate empty list with a type which somehow does not give an error
    emptyList :: (EOS f, EOS v) => [(Term (FunctionSymbol f) v)] ->[(Term (FunctionSymbol f) v)]
    emptyList list = if length list > 0 then emptyList (tail list) else []

    --Remove reflexivity from terms
    makeIrreflexive :: (Eq lhs, Eq rhs) => [Rule lhs rhs] -> [Rule lhs rhs]
    makeIrreflexive order = Prelude.filter (\x -> (lhs x) /= (rhs x)) order

    --get the arity of a term without arity if a list with terms with arity is supplied
    getArity :: (EOS f, EOS v) => [(Term f v, Int)] -> Term f v -> Int
    getArity terms term = snd (head(Prelude.filter (\x -> if fst x == term then True else False) terms)) --not the nicest, but filter should return only 1 element

    --Casts the list into a set and back to remove duplicates POSSIBLE BUG: IS THE ORDER CHANGED???
    removeDuplicates :: (Ord a) => [a] -> [a]
    removeDuplicates list = toList(fromList(list))

    containsRule:: (EOS f, EOS v) => [Rule (FunctionSymbol f) v] -> (Rule (FunctionSymbol f) v) -> Bool
    containsRule [] rule = False
    containsRule (h:t) rule = if(h == rule) then True else containsRule t rule

    printRuleApplications :: (Show f, Show v, Show v') => [Reduct f v v'] -> IO[()]
    printRuleApplications reductions = mapM (\r -> print(result r)) reductions

    getDerivation:: (EOS f, EOS v, EOS rhs) => (Term (FunctionSymbol f) v) -> Int -> [Reduct (FunctionSymbol f) v v'] -> [Rule (FunctionSymbol f) rhs] -> (Maybe Bool)
    getDerivation term counter reductions trs= if (containsTerm reductions term) then 
            Just True
        else if length reductions /= 0 && counter /= 0 then
            getDerivation term (counter-1) (concat (Prelude.map (\x -> (fullRewrite trs (result x))) reductions)) trs
        else 
            Nothing

    isDerivable ::(EOS f, EOS v, EOS rhs) => (Term (FunctionSymbol f) v) -> [Rule (FunctionSymbol f) rhs] -> (Term (FunctionSymbol f) v) -> (Maybe Bool)
    isDerivable leftTerm reductionRules rightTerm = let result = getDerivation rightTerm (length reductionRules +1) (fullRewrite reductionRules leftTerm) reductionRules in 
        if leftTerm == rightTerm then Just True else result

    getFunctionSymbolsFromTerm :: Term (FunctionSymbol [Char]) Int -> [(FunctionSymbol [Char])]
    getFunctionSymbolsFromTerm (Fun f []) = [f]
    getFunctionSymbolsFromTerm (Fun f list) = concat(Prelude.map getFunctionSymbolsFromTerm list)
    getFunctionSymbolsFromTerm (Var v) = []

    getFunctionSymbolsFromRule :: Rule (FunctionSymbol [Char]) Int -> [(FunctionSymbol [Char])]
    getFunctionSymbolsFromRule rule = (getFunctionSymbolsFromTerm (lhs rule)) ++ (getFunctionSymbolsFromTerm (rhs rule))

    getFunctionSymbolsFromRules :: [Rule (FunctionSymbol [Char]) Int] -> [(FunctionSymbol [Char])]
    getFunctionSymbolsFromRules trs = concat(Prelude.map getFunctionSymbolsFromRule trs)