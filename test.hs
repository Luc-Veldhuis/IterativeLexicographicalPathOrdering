import Data.Rewriting.Pos
import Data.Rewriting.Term as Term
import Data.Rewriting.Rule as Rule
import Data.Rewriting.Rules as Rules
import Data.Char
import Data.Set
import System.IO

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

originalTRS = [mul[x, suc[y]] --> add[x, mul [x, y]]]
--works for : add[x, zero] --> x
--works for : mul[x, zero] --> zero
--works for : add[x, suc[y]] --> suc[add[x,y]]
--works for : 

ruleTest = mul[x, suc[y]] --> add[x, mul[x,y]]

functions = [((suc []), 1), ((add []), 2), ((mul []), 2)]

order = [mul [] --> add [], add [] --> suc []]

--manually constructed, have to write something which constructs this...

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

printRuleApplications reductions = mapM (\r -> print(result r)) reductions

containsRule [] rule = False
containsRule (h:t) rule = if(h == rule) then True else containsRule t rule

containsTerm :: (Eq f, Eq v) => [Reduct f v v'] -> Term  f v -> Bool
containsTerm reductions term = if length reductions == 0 then 
        False 
    else if result (head(reductions)) == term then
        True
    else (containsTerm (tail(reductions)) term)

--getDerivation :: (Eq v) => Term Char v-> Int -> [Reduct  Char v Char] -> [Reduct  Char v Char]
getDerivation term counter reductions trs= if (containsTerm reductions term) then 
        reductions 
    else if length reductions /= 0 && counter /= 0 then
        flatten (Prelude.map (\x -> (getDerivation term (counter-1) (fullRewrite trs (result x))) trs) reductions)
    else 
        []

isDerivable leftTerm reductionRules rightTerm = let result = getDerivation rightTerm (length reductionRules +1) (fullRewrite reductionRules leftTerm) reductionRules in if leftTerm == rightTerm then True else if (length result) == 0 then False else True --Make this maybe, you cannot say false

main = printRuleApplications(getDerivation (rhs ruleTest) 10 (fullRewrite iterLexicoTRS (lhs ruleTest)) iterLexicoTRS)

flatten [] = []
flatten (h:t) = h ++ (flatten t)

makeTransitiveRules termLeft order termRight = if isDerivable termLeft order termRight then [termLeft --> termRight] else []

makeTransitive order functions = flatten (Prelude.map (\x -> flatten (Prelude.map (makeTransitiveRules x order) functions)) functions)

makeIrreflexive order = Prelude.filter (\x -> (lhs x) /= (rhs x)) order

getArity terms term = snd (head(Prelude.filter (\x -> if fst x == term then True else False) terms)) --not the nicest, but filter should return only 1 element

copyTerm term 0 = []
copyTerm term times = term : (copyTerm term (times -1))

getFunctionSymbol term = head(tail(show (head(Term.funs term))))

removeDuplicates list = toList(fromList(list))

generateVariables 0 = []
generateVariables arity = generateVariables (arity -1) ++ [Var arity]

generatePutRule (term, arity) = Fun (getFunctionSymbol term) (generateVariables arity) --> Fun (toUpper(getFunctionSymbol term)) (generateVariables arity)

generatePut terms = Prelude.map generatePutRule terms

generateSelectRule (term, arity) varNumber = if varNumber > 0 then (generateSelectRule (term, arity) (varNumber-1)) ++ [Fun (toUpper(getFunctionSymbol term)) (generateVariables arity) --> Var varNumber] else []

generateSelectRules (term, arity) = generateSelectRule (term, arity) arity

generateSelect terms = flatten(Prelude.map generateSelectRules terms)

generateCopyRule terms irreflexiveOrder (term, arity) rootTerm = if isDerivable term irreflexiveOrder rootTerm then [Fun (toUpper(getFunctionSymbol term)) (generateVariables arity) --> Fun (toUpper(getFunctionSymbol rootTerm)) (copyTerm (Fun (toUpper(getFunctionSymbol term)) (generateVariables arity)) (getArity terms term))] else []

generateCopyRules terms order (term, arity) = let irreflexiveOrder = makeIrreflexive order in --get irreflexive order
    let otherTerms = Prelude.filter (\x -> x /= term) (Prelude.map (\x -> lhs x) irreflexiveOrder) in --get all other terms in the order
        flatten (Prelude.map (\x -> generateCopyRule terms irreflexiveOrder (term, arity) x) otherTerms) --generate copy rules
		
generateCopy terms order = flatten (Prelude.map (generateCopyRules terms order) terms)

generateLexicoRule order (term, arity) = Fun (getFunctionSymbol term) (generateVariables arity) --> Fun (toUpper(getFunctionSymbol term)) (generateVariables arity)

generateLexico terms order = Prelude.map (generateLexicoRule order) terms

generateIterLexico = removeDuplicates((generatePut functions) ++ (generateCopy functions order) ++ (generateSelect functions) ++ (generateLexico functions order))

test = print(mul_1[x, y] == mul_1[x, y])

test2 = length (fullRewrite iterLexicoTRS (lhs ruleTest))

test3 = print(result (last(fullRewrite iterLexicoTRS (lhs ruleTest))) )

test4 = printRuleApplications (fullRewrite iterLexicoTRS (lhs ruleTest))

test5 = containsTerm (fullRewrite [Fun 'g' [ Var 1, Var 2, Fun 'f' [Var 3, Var 2]] --> Fun 'g' [ Var 1, Var 2, Fun 'f' [ Var 3, Var 1]]] (Fun 'g' [ Var 1, Var 2, Fun 'f' [Var 3, Var 2]])) (Fun 'g' [ Var 1, Var 2, Fun 'f' [ Var 3, Var 1]])

test6 = generatePut [((suc []), 1)]

test7 = generateVariables 3

test8 = generateIterLexico

--test9 = (makeTransitive order (Prelude.map (\x->fst x) functions)) --somehow does not work like this, but works when I type it in the console :/