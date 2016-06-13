module IterativeLexicographicalGenerators where
    import Types
    import Helpers
    import Data.Rewriting.Term as Term
    import Data.Rewriting.Rule as Rule
    import Data.Rewriting.Rules as Rules
    --Generates x number of variables, numbering them starting from 1
    generateVariables :: (EOS f) => Int -> [Term (FunctionSymbol f) Int]
    generateVariables 0 = []
    generateVariables arity = Prelude.map Var [1..arity]

    --Generates x number of variables, numbering them starting from the offset
    generateVariablesOffset::(EOS f) => Int -> Int -> [Term (FunctionSymbol f) Int]
    generateVariablesOffset 0  offset = []
    generateVariablesOffset arity offset = Prelude.map Var [(1+offset)..(arity+offset)]

    --Functions to generate all the rules:
    --Put
    generatePutRule::(EOS f) => (FunctionSymbol f) -> Rule (FunctionSymbol f) Int
    generatePutRule f = let vars = generateVariables $ arity f in 
        Fun f vars --> Fun (setStar f) vars

    generatePut::(EOS f) => [(FunctionSymbol f)] -> [Rule (FunctionSymbol f) Int]
    generatePut functionSymbols = Prelude.map generatePutRule functionSymbols

    --Selects
    generateSelectRules ::(EOS f) => (FunctionSymbol f) -> [Rule (FunctionSymbol f) Int]
    generateSelectRules f = let vars = (generateVariables $ arity f) in
        Prelude.map (\var -> Fun (setStar f) vars --> var) vars

    generateSelect::(EOS f) => [(FunctionSymbol f)] -> [Rule (FunctionSymbol f) Int]
    generateSelect functionSymbols = concat(Prelude.map generateSelectRules functionSymbols)

    --Copy
    generateCopyRules ::  (EOS f, EOS v) => ([Rule (FunctionSymbol f) v]) -> [(FunctionSymbol f)] -> (FunctionSymbol f) -> [Rule (FunctionSymbol f) Int]
    generateCopyRules order symbols f = 
        let vars = (generateVariables $ arity f)
            left = Fun (setStar f) vars
        in Prelude.map (\g -> left --> Fun g (replicate (arity g) left)) $ filter (greater order f) symbols


    generateCopy :: (EOS f, EOS v) => ([Rule (FunctionSymbol f) v]) -> [(FunctionSymbol f)] -> [Rule (FunctionSymbol f) Int] 
    generateCopy order functionSymbols = concat (Prelude.map (generateCopyRules (order) functionSymbols) functionSymbols)

    --Lex
    generateLexicoRule :: (EOS f) => (FunctionSymbol f) -> (FunctionSymbol f) -> [Rule (FunctionSymbol f) Int]
    generateLexicoRule f g = 
        let vars_f = splits (generateVariables $ arity f - 1)
            vars_g = generateVariablesOffset (arity g) $ arity f
            left = (\(l,r) -> Fun (setStar f) (l ++ [Fun g vars_g] ++ r))
        in Prelude.map (\(l,r) ->  left (l,r) --> Fun f (l ++ [Fun (setStar g) vars_g] ++ (replicate (length r) $ left (l,r) ))) $ vars_f

    generateLexico :: (EOS f) => [(FunctionSymbol f)] -> [Rule (FunctionSymbol f) Int]
    generateLexico functionSymbols = concat (Prelude.map (\f -> concat (Prelude.map (\g -> generateLexicoRule f g) functionSymbols)) functionSymbols)

    generateIterLexico :: (EOS f, EOS v) => ([Rule (FunctionSymbol f) v]) -> [(FunctionSymbol f)] -> [Rule (FunctionSymbol f) Int]
    generateIterLexico order functionSymbols = removeDuplicates((generatePut functionSymbols) ++ (generateCopy order functionSymbols) ++ (generateSelect functionSymbols) ++ (generateLexico functionSymbols))
