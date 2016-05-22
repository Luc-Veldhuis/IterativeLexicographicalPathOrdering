import Data.Rewriting.Pos
import Data.Rewriting.Term as Term
import Data.Rewriting.Rule as Rule
import Data.Rewriting.Rules as Rules
import Data.Char
import Data.Set
import System.IO

--Using https://hackage.haskell.org/package/term-rewriting-0.2
--From http://cl-informatik.uibk.ac.at/software/haskell-rewriting/

--Initialize function symbols and variables in a way I later have to change
--Dedekind rules

zero = Fun '0' []

suc = Fun 's'

suc_1 = Fun 'S'

add = Fun 'a'

add_1 = Fun 'A'

mul = Fun 'm'

mul_1 = Fun 'M'

x = Var 'x'

y = Var 'y'

z = Var 'z'

(-->) = Rule

--Rules of the Dedekind TRS
originalTRS = [mul[x, suc[y]] --> add[x, mul [x, y]], add[x, zero] --> x, mul[x, zero] --> zero, add[x, suc[y]] --> suc[add[x,y]]]

--Testing rules:
--works for : add[x, zero] --> x
--works for : mul[x, zero] --> zero
--works for : add[x, suc[y]] --> suc[add[x,y]]
--works for : 

--How I would like to defined functions with arity and ordering
functions = [((suc []), 1), ((add []), 2), ((mul []), 2)]

order = [mul [] --> add [], add [] --> suc []]

--Still not working for this :(
-- rule I was testing
ruleTest = mul[x, suc[y]] --> add[x, mul[x,y]]


--manually constructed, I want to construct functions which will do this automatically
--All the possible put, select, copy and lex rules in a TRS which have to be applied to the originalTRS left hand side terms to 
iterLexicoTRS = [ suc[x] --> suc_1[x]
    , suc_1[x] --> x
    , add[x, y] --> add_1[x, y]
    , add_1[x, y] --> x --select
    , add_1[x, y] --> y
    , add_1[x, y] --> suc[add_1[x, y]] --copy
    , add_1[x, suc[y]] --> add[x, suc_1[y]] --lexo
    , add_1[suc[y], z] --> add[suc_1[y], add_1[suc[y], z]]
    , add_1[x, mul[y, z]] --> add[x, mul_1[y, z]]
    , add_1[mul[x, y], z] --> add[mul_1[x, y], add_1[mul[x, y], z]]
    , add_1[x, add[y, z]] --> add[x, add_1[y, z]]
    , add_1[add[x, y], z] --> add[add_1[x, y], add_1[add[x, y], z]]
    , mul[x, y] --> mul_1[x, y] --put
    , mul_1[x, y] --> x --select
    , mul_1[x, y] --> y
    , mul_1[x, y] --> add[mul_1[x, y], mul_1[x, y]] --copy
    , mul_1[x, y] --> suc[mul_1[x, y]] --copy
    , mul_1[x, suc[y]] --> mul[x, suc_1[y]] --lexo
    , mul_1[suc[y], z] --> mul[suc_1[y], mul_1[mul[y], z]]
    , mul_1[x, mul[y, z]] --> mul[x, mul_1[y, z]]
    , mul_1[mul[x, y], z] --> mul[mul_1[x, y], mul_1[mul[x, y], z]]
    , mul_1[x, add[y, z]] --> mul[x, add_1[y, z]]
    , mul_1[add[x, y], z] --> mul[add_1[x, y], mul_1[add[x, y], z]] ]

-- Handy functions:
makeList:: Int -> [Int]
makeList 0 = []
makeList n = makeList (n-1) ++ [n]

containsRule:: (Eq lhs, Eq rhs) => [Rule lhs rhs] -> (Rule lhs rhs) -> Bool
containsRule [] rule = False
containsRule (h:t) rule = if(h == rule) then True else containsRule t rule

flatten :: [[a]] -> [a]
flatten [] = []
flatten (h:t) = h ++ (flatten t)

containsTerm :: (Eq f, Eq v) => [Reduct f v v'] -> Term  f v -> Bool
containsTerm reductions term = if length reductions == 0 then 
        False 
    else if result (head(reductions)) == term then
        True
    else (containsTerm (tail(reductions)) term)

--Get the function symbols for a term. The first 'show' will print '{symbol}' with the ' so I have to get the second item in the [Char]
getFunctionSymbol::(Eq f, Eq v, Ord f) => (Term f v) -> f 
getFunctionSymbol (Fun f list) = f

--Also makes it reflexive. Make rules like m -> a, a -> s 
--into m -> a, a -> s, m -> s, m -> m, a -> a, s -> s

makeTransitiveRule :: (Eq f, Eq v, Ord f, Ord rhs) => [Rule f rhs] -> (Term f v) -> (Term f v) -> [Rule f rhs]
makeTransitiveRule order termLeft termRight = if maybe False (\x->x) (isDerivable termLeft order termRight) then [Fun (getFunctionSymbol termLeft) [] --> Fun (getFunctionSymbol termRight) []] else []

makeTransitiveRules::(Eq f, Eq v, Ord f, Ord rhs) => [(Term f v)] -> [Rule f rhs] -> (Term f v) -> [Rule f rhs]
makeTransitiveRules terms order termLeft = flatten (Prelude.map (makeTransitiveRule order termLeft) terms)

makeTransitive ::(Eq f, Eq v, Ord f, Ord rhs) => [Rule f rhs] -> [Term f v] -> [Rule f rhs]
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

--Generates x number of variables, numbering them starting from 1
generateVariables :: (Eq f, Ord f) => Int -> [Term f Int]
generateVariables 0 = []::(Eq f, Ord f) =>[(Term f Int)]
generateVariables arity = generateVariables (arity -1) ++ [Var arity]

--Generates x number of variables, numbering them starting from the offset
generateVariablesOffset::(Eq f, Ord f) => Int -> Int -> [Term f Int]
generateVariablesOffset 0  offset = []
generateVariablesOffset arity  offset = generateVariablesOffset (arity -1) offset ++ [Var (arity+offset)]

--Function which applies the rules x number of times until it found something or not yet.

getDerivation:: (Eq f, Eq v, Ord f, Ord rhs) => (Term f v) -> Int -> [Reduct f v v'] -> [Rule f rhs] -> (Maybe Bool)
getDerivation term counter reductions trs= if (containsTerm reductions term) then 
        Just True
    else if length reductions /= 0 && counter /= 0 then
        getDerivation term (counter-1) (flatten (Prelude.map (\x -> (fullRewrite trs (result x))) reductions)) trs
    else 
        Nothing

--Should make this return a Maybe, because you cannot say that it is not derivable
isDerivable ::(Eq f, Eq v, Ord f, Ord rhs) => (Term f v) -> [Rule f rhs] -> (Term f v) -> (Maybe Bool)
isDerivable leftTerm reductionRules rightTerm = let result = getDerivation rightTerm (length reductionRules +1) (fullRewrite reductionRules leftTerm) reductionRules in 
    if leftTerm == rightTerm then Just True else result

--print statement, gave an error otherwise
printRuleApplications :: (Show f, Show v, Show v') => [Reduct f v v'] -> IO[()]
printRuleApplications reductions = mapM (\r -> print(result r)) reductions

--Checks if the ruleTest is derivable
main :: IO()
main = print (isDerivable (lhs ruleTest) iterLexicoTRS (rhs ruleTest))

--Functions to generate all the rules:
--Put
--generatePutRule::(Eq f, Eq v, Ord f, Ord rhs) => ((Term f v), Int) -> Rule f rhs
generatePutRule (term, arity) = Fun (getFunctionSymbol term) (generateVariables arity) --> Fun (toUpper(getFunctionSymbol term)) (generateVariables arity)
--generatePut::(Eq f, Eq v, Ord f) => [Term f v] -> [Term f v]
generatePut terms = Prelude.map generatePutRule terms

--Select
--generateSelectRule:: ((Term f v), Int) -> Int -> [Term f v]
generateSelectRule (term, arity) varNumber = if varNumber > 0 then (generateSelectRule (term, arity) (varNumber-1)) ++ [Fun (toUpper(getFunctionSymbol term)) (generateVariables arity) --> Var varNumber] else []
--generateSelectRules :: ((Term f v), Int) -> [Term f v]
generateSelectRules (term, arity) = generateSelectRule (term, arity) arity

--generateSelect:: [Term f v] -> [Term f v]
generateSelect terms = flatten(Prelude.map generateSelectRules terms)

--Copy
--generateCopyRule :: [Term f v] -> 
generateCopyRule terms irreflexiveOrder (term, arity) rootTerm = if maybe False (\x->x) (isDerivable term irreflexiveOrder rootTerm) then 
    [Fun (toUpper(getFunctionSymbol term)) (generateVariables arity) --> 
        Fun (toLower(getFunctionSymbol rootTerm)) (copyTerm (Fun (toUpper(getFunctionSymbol term)) (generateVariables arity)) (getArity terms rootTerm))] 
    else []

generateCopyRules terms order (term, arity) = let irreflexiveOrder = makeIrreflexive order in --get irreflexive order
    let otherTerms = Prelude.filter (\x -> x /= term) (Prelude.map (\x -> rhs x) irreflexiveOrder) in --get all other terms in the order
        removeDuplicates (flatten (Prelude.map (\x -> generateCopyRule terms irreflexiveOrder (term, arity) x) otherTerms)) --generate copy rules
generateCopy terms order = flatten (Prelude.map (generateCopyRules terms order) terms)

--Lex
generateLexicoRHSTerm (substitutionTerm, substitutionArity) arity position lhsTerm = generateVariables (position -1) ++ [Fun (toUpper(getFunctionSymbol substitutionTerm)) (generateVariablesOffset substitutionArity arity)] ++ copyTerm lhsTerm (arity-position)

generateLexicoLHSTerm (substitutionTerm, substitutionArity) arity position = generateVariables (position -1) ++ [Fun (toLower(getFunctionSymbol substitutionTerm)) (generateVariablesOffset substitutionArity arity)] ++ (generateVariablesOffset (arity - position) position)

generateLexicoRule (term, arity) position (substitutionTerm, substitutionArity) = let lhsTerm = Fun (toUpper(getFunctionSymbol term)) (generateLexicoLHSTerm (substitutionTerm, substitutionArity) arity position) in
 lhsTerm --> Fun (toLower(getFunctionSymbol term)) (generateLexicoRHSTerm (substitutionTerm, substitutionArity) arity position lhsTerm)

generateLexicoRulesOnPosition terms (term, arity) position = Prelude.map (generateLexicoRule (term, arity) position) terms

generateLexicoRules terms (term, arity) = let numberOfPositions = makeList arity in
    flatten (Prelude.map (generateLexicoRulesOnPosition terms (term, arity)) numberOfPositions)

generateLexico terms = flatten (Prelude.map (generateLexicoRules terms) terms)

--Generate all rules and merge them together without duplicates
--generateIterLexico = removeDuplicates((generatePut functions) ++ (generateCopy functions order) ++ (generateSelect functions) ++ (generateLexico functions))


--Some test cases
test0 = print(mul_1[x, y] == mul_1[x, y])

--test1 = printRuleApplications(getDerivation (rhs ruleTest) 10 (fullRewrite iterLexicoTRS (lhs ruleTest)) iterLexicoTRS)

test2 = length (fullRewrite iterLexicoTRS (lhs ruleTest))

test3 = print(result (last(fullRewrite iterLexicoTRS (lhs ruleTest))) )

test4 = printRuleApplications (fullRewrite iterLexicoTRS (lhs ruleTest))

test5 = containsTerm (fullRewrite [Fun 'g' [ Var 1, Var 2, Fun 'f' [Var 3, Var 2]] --> Fun 'g' [ Var 1, Var 2, Fun 'f' [ Var 3, Var 1]]] (Fun 'g' [ Var 1, Var 2, Fun 'f' [Var 3, Var 2]])) (Fun 'g' [ Var 1, Var 2, Fun 'f' [ Var 3, Var 1]])

--test6 = generatePut [((suc []), 1)]

test7:: (Eq f, Ord f)=> [Term f Int]
test7 = generateVariables 3

--test8 = generateIterLexico

--test9 = makeTransitive order (Prelude.map (\x -> fst x) functions)
type Terms f v = [Term f v]
test10 = isDerivable (lhs ruleTest) iterLexicoTRS (rhs ruleTest)
--test12 = ([]::(Terms f v)) == ([]::(Terms f v))
test13 = ([]::String) == ([]::String)
--test14 = generateLexico functions
--test15 = generatePut functions
--test16 = generateSelect functions
--test17 = generateCopy functions order
test18 =  (Fun 'm' []) == (Fun 'm' [] :: Term Char Char)