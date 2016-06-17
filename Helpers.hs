module Helpers where
    import Types
    import Data.List
    import Data.Rewriting.Term as Term
    import Data.Rewriting.Rule as Rule
    import Data.Rewriting.Pos as Pos
    import Data.Rewriting.Rules as Rules
    import Data.Set hiding (filter)
    import Debug.Trace

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

    getFunctionSymbol::(EOS f, EOS v) => (Term (FunctionSymbol f) v) -> (FunctionSymbol f) 
    getFunctionSymbol (Fun f list) = f

    makeTransitive :: (EOS f, EOS v) => [Rule (FunctionSymbol f) v] -> [Rule (FunctionSymbol f) v]
    makeTransitive rules = let terms = Prelude.map (\f -> (Fun f [])) $ getFunctionSymbolsFromRules rules in
        concat $ Prelude.map (\lTerm -> concat $ Prelude.map (\rTerm -> if (maybe False (\x->x) $ isDerivable lTerm rules rTerm) then [(lTerm --> rTerm)] else []) terms ) terms

    greater :: (EOS f, EOS v) => [Rule (FunctionSymbol f) v] -> FunctionSymbol f -> FunctionSymbol f -> Bool
    greater order leftFunctionSymbol rightFunctionSymbol = or $ Prelude.map (\rule -> (getFunctionName $ lhs rule) == name leftFunctionSymbol && (getFunctionName $ rhs rule) == name rightFunctionSymbol) order

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

    getDerivationIterative:: (EOS f, EOS v, EOS rhs, Num v) => (Term (FunctionSymbol f) v) -> Int -> [Reduct (FunctionSymbol f) v v'] -> ([Rule (FunctionSymbol f) rhs],[Rule (FunctionSymbol f) rhs]) -> (Maybe Bool)
    getDerivationIterative term counter reductions (trs, putTRS)= if (containsTerm (trace (show $ length $ Prelude.map result reductions) reductions) term) then 
            Just True
        else if length reductions /= 0 && counter /= 0 then
            getDerivationIterative term (counter-1) (filterReductions term $concat $ Prelude.map (\x -> (fullRewrite trs (result x))) reductions)  (trs, putTRS)
        else if length reductions == 0 && counter /= 0 then
            getDerivationIterative term (counter-1) (filterReductions term $concat $ Prelude.map (\x -> (fullRewrite putTRS (result x))) reductions )  (trs, putTRS)
        else 
            Nothing

    --sortDerivations :: (EOS f, EOS v) =>  [Reduct (FunctionSymbol f) v v'] -> [Reduct (FunctionSymbol f) v v']
    --sortDerivations derivations = sortOn (\derivation -> case result derivation of 
    --    Var v -> 0
    --    Fun f list -> 1 + (sum $ Prelude.map (depth) list)) derivations

    getPath :: (EOS f, EOS v, Num v) => (Term (FunctionSymbol f) v) -> Pos -> [FunctionSymbol f]
    getPath term [] = if isFun term then [getFunctionSymbol term] else []
    getPath term position = let termAtPosition = maybe (Var 0) (\x->x) $ subtermAt term position in
        let currentFunctionSymbol = if isFun termAtPosition then [getFunctionSymbol termAtPosition] else [] in
            (getPath term $init position) ++ currentFunctionSymbol

    functionSymbolCanBeDerived :: (EOS f) => (FunctionSymbol f) -> (FunctionSymbol f) -> Bool
    functionSymbolCanBeDerived from to = if from == to then True
        else if star from then True
            else False

    termCanBeDerived :: (EOS f, EOS v, Num v) => (Term (FunctionSymbol f) v) -> Pos -> (Term (FunctionSymbol f) v) -> Bool
    termCanBeDerived newTerm positionInTerm toTerm = let pathSoFar = getPath newTerm positionInTerm in
        let pathToFollow = getPath toTerm positionInTerm in
        and $ Prelude.map (\index -> if index >= length pathToFollow then False else functionSymbolCanBeDerived (pathSoFar !! index) (pathToFollow !! index) ) [0.. (length pathSoFar)-1]

    filterReductions :: (EOS f, EOS v, EOS rhs, Num v) => (Term (FunctionSymbol f) v) -> [Reduct (FunctionSymbol f) v rhs] -> [Reduct (FunctionSymbol f) v rhs]
    filterReductions toTerm reductions= filter (\reduction -> termCanBeDerived (result reduction) (pos reduction) toTerm) reductions

    isDerivable ::(EOS f, EOS v, EOS rhs) => (Term (FunctionSymbol f) v) -> [Rule (FunctionSymbol f) rhs] -> (Term (FunctionSymbol f) v) -> (Maybe Bool)
    isDerivable leftTerm reductionRules rightTerm = let result = getDerivation rightTerm (length reductionRules +1) (fullRewrite reductionRules leftTerm) reductionRules in 
        if leftTerm == rightTerm then Just True else result

    isDerivableIterative ::(EOS f, EOS v, EOS rhs, Num v) => (Term (FunctionSymbol f) v) -> ([Rule (FunctionSymbol f) rhs],[Rule (FunctionSymbol f) rhs]) -> (Term (FunctionSymbol f) v) -> (Maybe Bool)
    isDerivableIterative leftTerm (reductionRules,putRules) rightTerm = let result = getDerivationIterative rightTerm (length reductionRules +1) (fullRewrite putRules leftTerm) (reductionRules,putRules) in 
        if leftTerm == rightTerm then Just True else result

    getFunctionSymbolsFromTerm :: (EOS f, EOS v) =>  Term (FunctionSymbol f) v -> [(FunctionSymbol f)]
    getFunctionSymbolsFromTerm (Fun f []) = [f]
    getFunctionSymbolsFromTerm (Fun f list) = [f] ++ concat(Prelude.map getFunctionSymbolsFromTerm list)
    getFunctionSymbolsFromTerm (Var v) = []

    getFunctionSymbolsFromRule :: (EOS f, EOS v) => Rule (FunctionSymbol f) v -> [(FunctionSymbol f)]
    getFunctionSymbolsFromRule rule = (getFunctionSymbolsFromTerm (lhs rule)) ++ (getFunctionSymbolsFromTerm (rhs rule))

    getFunctionSymbolsFromRules :: (EOS f, EOS v) => [Rule (FunctionSymbol f) v] -> [(FunctionSymbol f)]
    getFunctionSymbolsFromRules trs = removeDuplicates $ concat(Prelude.map getFunctionSymbolsFromRule trs)
