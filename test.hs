import Data.Rewriting.Pos
import Data.Rewriting.Term as Term
import Data.Rewriting.Rule as Rule
import Data.Rewriting.Rules as Rules

import System.IO

zero = Fun '0' []

suc = Fun 'S'

suc_1 = Fun 's' --[Var 1]

add = Fun 'A' --[Var 1, Var 2]

add_1 = Fun 'a' --[Var 1, Var 2]

mul = Fun 'M' --[Var 1, Var 2]

mul_1 = Fun 'm' --[Var 1, Var 2]

x = Var 'x'

y = Var 'y'

z = Var 'z'

(-->) = Rule

originalTRS = [mul[x, suc[y]] --> add[x, mul [x, y]]]
--works for : add[x, zero] --> x
--works for : mul[x, zero] --> zero

ruleTest = add[x, suc[y]] --> suc[add[x,y]]

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

--applyRules :: (Eq v) => Term f v-> Int -> [Reduct  f v v'] -> [Reduct  f v v']
applyRules term counter reductions = if length reductions /= 0 && counter /= 0 && not(containsTerm reductions term) then
    (applyRules term (counter-1) (fullRewrite iterLexicoTRS (result (head reductions)))) ++ (applyRules term counter (tail(reductions)))
    else reductions

main = printRuleApplications (applyRules (rhs ruleTest) 10 (fullRewrite iterLexicoTRS (lhs ruleTest)))

test = print(mul_1[x, y] == mul_1[x, y])

test2 = length (fullRewrite iterLexicoTRS (lhs ruleTest))

test3 = print(result (last(fullRewrite iterLexicoTRS (lhs ruleTest))) )

test4 = printRuleApplications (fullRewrite iterLexicoTRS (lhs ruleTest))
