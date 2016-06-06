module IterativeLexicographicalGenerators2 where
    import Types
    import Helpers
    import Data.Rewriting.Term as Term
    import Data.Rewriting.Rule as Rule
    import Data.Rewriting.Rules as Rules
    --Generates x number of variables, numbering them starting from 1
    generateVariables :: (Eq f, Eq v, Ord f, Num v) => v -> [Term f v]
    generateVariables 0 = []
    generateVariables arity = generateVariables (arity -1) ++ [Var arity]

    --Generates x number of variables, numbering them starting from the offset
    generateVariablesOffset::(Eq f, Ord f, Eq v, Num v) => v -> v -> [Term f v]
    generateVariablesOffset 0  offset = []
    generateVariablesOffset arity  offset = generateVariablesOffset (arity -1) offset ++ [Var (arity+offset)]

    --Functions to generate all the rules:
    --Put
    generatePutRule::(Eq f, Eq v, Ord f) => (Term (FunctionSymbol f) v) -> Rule (FunctionSymbol f) Int
    generatePutRule term = Fun (FunctionSymbol(getFunctionName term) (arity (getFunctionSymbol term)) False) (generateVariables (arity (getFunctionSymbol term))) --> Fun (FunctionSymbol(getFunctionName term) (arity (getFunctionSymbol term)) True) (generateVariables (arity (getFunctionSymbol term)))

    generatePut::(Eq f, Eq v, Ord f) => [Term (FunctionSymbol f) v] -> [Rule (FunctionSymbol f) Int]
    generatePut terms = Prelude.map generatePutRule terms

    --Select
    generateSelectRule::(Eq f, Eq v, Ord f) => (Term (FunctionSymbol f) v) -> Int -> [Rule (FunctionSymbol f) Int]
    generateSelectRule term varNumber = if varNumber > 0 then (generateSelectRule term (varNumber-1)) ++ [Fun (FunctionSymbol (getFunctionName term) (arity (getFunctionSymbol term)) True) (generateVariables (arity (getFunctionSymbol term))) --> Var varNumber] else []

    generateSelectRules ::(Eq f, Eq v, Ord f) => (Term (FunctionSymbol f) v) -> [Rule (FunctionSymbol f) Int]
    generateSelectRules term = generateSelectRule term (arity (getFunctionSymbol term))

    generateSelect::(Eq f, Eq v, Ord f) => [Term (FunctionSymbol f) v] -> [Rule (FunctionSymbol f) Int]
    generateSelect terms = flatten(Prelude.map generateSelectRules terms)

    --Copy
    generateCopyRule :: (Eq f, Eq v, Ord f, Ord rhs) => [Rule (FunctionSymbol f) rhs] -> (Term (FunctionSymbol f) v) -> (Term (FunctionSymbol f) v) -> [Rule (FunctionSymbol f) Int]
    generateCopyRule irreflexiveOrder term rootTerm = if maybe False (\x->x) (isDerivable term irreflexiveOrder rootTerm) then 
        [Fun (FunctionSymbol (getFunctionName term) (arity (getFunctionSymbol term)) True) (generateVariables (arity (getFunctionSymbol term)))  --> 
            Fun (FunctionSymbol (getFunctionName rootTerm) (arity (getFunctionSymbol rootTerm)) False) (copyTerm (Fun (FunctionSymbol (getFunctionName term) (arity (getFunctionSymbol term)) True) (generateVariables (arity (getFunctionSymbol term)))) (arity (getFunctionSymbol rootTerm)))] 
        else []

    generateCopyRules ::  (Eq f, Eq v, Ord f, Ord v) => [Rule (FunctionSymbol f) v] -> (Term (FunctionSymbol f) v) -> [Rule (FunctionSymbol f) Int]
    generateCopyRules order term =  let irreflexiveOrder = makeIrreflexive order in --get irreflexive order
        let otherTerms = Prelude.filter (\x -> x /= term) (Prelude.map (\x -> rhs x) irreflexiveOrder) in --get all other terms in the order
            removeDuplicates (flatten (Prelude.map (\x -> generateCopyRule irreflexiveOrder term x) otherTerms)) --generate copy rules


    generateCopy :: (Eq f, Eq v, Ord f, Ord v) => [Term (FunctionSymbol f) v] -> [Rule (FunctionSymbol f) v] -> [Rule (FunctionSymbol f) Int] 
    generateCopy terms order = flatten (Prelude.map (generateCopyRules order) terms)

    --Lex
    generateLexicoRHSTerm :: (Eq f, Ord f, Eq v) => (Term (FunctionSymbol f) v) -> Int -> Int -> (Term (FunctionSymbol f) Int) -> [Term (FunctionSymbol f) Int ]
    generateLexicoRHSTerm substitutionTerm rootArity position lhsTerm = generateVariables (position -1) ++ [Fun (FunctionSymbol(getFunctionName substitutionTerm) (arity (getFunctionSymbol substitutionTerm)) True) (generateVariablesOffset (arity (getFunctionSymbol substitutionTerm)) rootArity)] ++ copyTerm lhsTerm (rootArity-position)

    generateLexicoLHSTerm :: (Eq f, Eq v, Ord f) => (Term (FunctionSymbol f) v) -> Int -> Int -> [Term (FunctionSymbol f) Int ]
    generateLexicoLHSTerm substitutionTerm rootArity position = generateVariables (position -1) ++ [Fun (FunctionSymbol (getFunctionName substitutionTerm) (arity (getFunctionSymbol substitutionTerm)) False) (generateVariablesOffset (arity (getFunctionSymbol substitutionTerm)) rootArity)] ++ (generateVariablesOffset (rootArity - position) position)

    generateLexicoRule :: (Eq f, Eq v, Ord f) => (Term (FunctionSymbol f) v) -> Int -> (Term (FunctionSymbol f) v) -> Rule (FunctionSymbol f) Int
    generateLexicoRule term position substitutionTerm = let lhsTerm = Fun (FunctionSymbol (getFunctionName term) (arity (getFunctionSymbol term)) True) (generateLexicoLHSTerm substitutionTerm (arity (getFunctionSymbol term)) position) in
        lhsTerm --> Fun (FunctionSymbol(getFunctionName term) (arity(getFunctionSymbol term)) False) (generateLexicoRHSTerm substitutionTerm (arity (getFunctionSymbol term)) position lhsTerm)

    generateLexicoRulesOnPosition :: (Eq f, Eq v, Ord f) => [(Term (FunctionSymbol f) v)] -> (Term (FunctionSymbol f) v) -> Int -> [Rule (FunctionSymbol f) Int]
    generateLexicoRulesOnPosition terms term position = Prelude.map (generateLexicoRule term position) terms

    generateLexicoRules :: (Eq f, Eq v, Ord f) => [(Term (FunctionSymbol f) v)] -> (Term (FunctionSymbol f) v) -> [Rule (FunctionSymbol f) Int]
    generateLexicoRules terms term = let numberOfPositions = makeList (arity (getFunctionSymbol term)) in
        flatten (Prelude.map (generateLexicoRulesOnPosition terms term) numberOfPositions)

    generateLexico :: (Eq f, Eq v, Ord f) => [(Term (FunctionSymbol f) v)] -> [Rule (FunctionSymbol f) Int]
    generateLexico terms = flatten (Prelude.map (generateLexicoRules terms) terms)

    generateIterLexico :: (Eq f, Eq v, Ord f, Ord v) => [Rule (FunctionSymbol f) v] -> [(Term (FunctionSymbol f) v)] -> [Rule (FunctionSymbol f) Int]
    generateIterLexico order functionSymbols = removeDuplicates((generatePut functionSymbols) ++ (generateCopy functionSymbols order) ++ (generateSelect functionSymbols) ++ (generateLexico functionSymbols))
