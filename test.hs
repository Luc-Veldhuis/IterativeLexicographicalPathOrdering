import Data.Rewriting.Pos
import Data.Rewriting.Term as Term
import Data.Rewriting.Rule as Rule
import Data.Rewriting.Rules as Rules
import Data.Char
import Data.Set
import System.IO

zero = Fun '0' []

suc = Fun 's'

suc_1 = Fun 'S' --[Var 1]

add = Fun 'a' --[Var 1, Var 2]

add_1 = Fun 'A' --[Var 1, Var 2]

mul = Fun 'm' --[Var 1, Var 2]

mul_1 = Fun 'M' --[Var 1, Var 2]

x = Var 'x'

y = Var 'y'

z = Var 'z'

(-->) = Rule

originalTRS = [mul[x, suc[y]] --> add[x, mul [x, y]]]
--works for : add[x, zero] --> x
--works for : mul[x, zero] --> zero

ruleTest = add[x, suc[y]] --> suc[add[x,y]]

functions = [((suc []), 1), ((add []), 2), ((mul []), 2)]

--manually constructed, have to write something which constructs this...

iterLexicoTRS = [ suc[x] --> suc_1[x]
    , add[x, y] --> add_1[x, y]
    , add_1[x, y] --> x --select
    , add_1[x, y] --> y
    , add_1[x, y] --> suc[add_1[x, y]]
    , add_1[x, suc[y]] --> add[x, suc_1[y]] --lexo
    , add_1[suc[y], z] --> add[suc_1[y], add_1[suc[y], z]]
    , add_1[x, mul[y, z]] --> add[x, mul_1[y, z]]
    , add_1[mul[x, y], z] --> add[mul_1[x, y], add_1[mul[x, y], z]]
    , add_1[x, add[y, z]] --> add[x, add_1[y, z]]
    , add_1[add[x, y], z] --> add[add_1[x, y], add_1[add[x, y], z]]
    , mul[x, y] --> mul_1[x, y] --put
    , mul_1[x, y] --> x --select
    , mul_1[x, y] --> y
    , mul_1[x, y] --> add[mul_1[x, y], mul_1[x, y]]
    , mul_1[x, y] --> suc[mul_1[x, y]]
    , mul_1[x, suc[y]] --> mul[x, suc_1[y]] --lexo
    , mul_1[suc[y], z] --> mul[suc_1[y], mul_1[mul[y], z]]
    , mul_1[x, mul[y, z]] --> mul[x, mul_1[y, z]]
    , mul_1[mul[x, y], z] --> mul[mul_1[x, y], mul_1[mul[x, y], z]]
    , mul_1[x, add[y, z]] --> mul[x, add_1[y, z]]
    , mul_1[add[x, y], z] --> mul[add_1[x, y], mul_1[add[x, y], z]] ]

printRuleApplications reductions = mapM (\r -> print(result r)) reductions

containsTerm :: (Eq f, Eq v) => [Reduct f v v'] -> Term  f v -> Bool
containsTerm reductions term = if length reductions == 0 then 
        False 
    else if result (head(reductions)) == term then
        True
    else (containsTerm (tail(reductions)) term)

applyRules :: (Eq v) => Term Char v-> Int -> [Reduct  Char v Char] -> [Reduct  Char v Char]
applyRules term counter reductions = if length reductions /= 0 && counter /= 0 && not(containsTerm reductions term) then
    reductions--Prelude.map (\x -> (applyRules term (counter-1) (fullRewrite iterLexicoTRS (result x)))) reductions --Prelude.map (\x -> (applyRules term (counter-1) (fullRewrite iterLexicoTRS (result x)))) reductions --(applyRules term (counter-1) (fullRewrite iterLexicoTRS (result (head reductions)))) ++ (applyRules term counter (tail(reductions)))
    else reductions --reductions

main = printRuleApplications(applyRules (rhs ruleTest) 10 (fullRewrite iterLexicoTRS (lhs ruleTest)))

flatten [] = []
flatten (h:t) = h ++ (flatten t)

getFunctionSymbol term = head(tail(show (head(Term.funs term))))

removeDuplicates list = toList(fromList(list))

generateVariables 0 = []
generateVariables arity = generateVariables (arity -1) ++ [Var arity]

generatePutRule (term, arity) = Fun (getFunctionSymbol term) (generateVariables arity) --> Fun (toUpper(getFunctionSymbol term)) (generateVariables arity)

generatePut terms = Prelude.map generatePutRule terms

generateSelectRule (term, arity) varNumber = if varNumber > 0 then (generateSelectRule (term, arity) (varNumber-1)) ++ [Fun (toUpper(getFunctionSymbol term)) (generateVariables arity) --> Var varNumber] else []

generateSelectRules (term, arity) = generateSelectRule (term, arity) arity

generateSelect terms = flatten(Prelude.map generateSelectRules terms)

generateCopyRule (term, arity) = Fun (toUpper(getFunctionSymbol term)) (generateVariables arity) --> Fun (toUpper(getFunctionSymbol term)) [Fun (toUpper(getFunctionSymbol term)) (generateVariables arity)] --get different term

generateCopy terms = Prelude.map generateCopyRule terms

generateLexicoRule (term, arity) = Fun (getFunctionSymbol term) (generateVariables arity) --> Fun (toUpper(getFunctionSymbol term)) (generateVariables arity)

generateLexico terms = Prelude.map generateLexicoRule terms

generateIterLexico = removeDuplicates((generatePut functions) ++ (generateCopy functions) ++ (generateSelect functions) ++ (generateLexico functions))

test = print(mul_1[x, y] == mul_1[x, y])

test2 = length (fullRewrite iterLexicoTRS (lhs ruleTest))

test3 = print(result (last(fullRewrite iterLexicoTRS (lhs ruleTest))) )

test4 = printRuleApplications (fullRewrite iterLexicoTRS (lhs ruleTest))

test5 = containsTerm (fullRewrite [Fun 'g' [ Var 1, Var 2, Fun 'f' [Var 3, Var 2]] --> Fun 'g' [ Var 1, Var 2, Fun 'f' [ Var 3, Var 1]]] (Fun 'g' [ Var 1, Var 2, Fun 'f' [Var 3, Var 2]])) (Fun 'g' [ Var 1, Var 2, Fun 'f' [ Var 3, Var 1]])

test6 = generatePut [((suc []), 1)]

test7 = generateVariables 3

test8 = generateIterLexico