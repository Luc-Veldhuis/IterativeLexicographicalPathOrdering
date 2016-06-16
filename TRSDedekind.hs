module TRSDedekind where
    import Types
    import Data.Rewriting.Term as Term
    import Data.Rewriting.Rule as Rule
    --Function symbols
    mul = Fun (FunctionSymbol "mul" 2 True)
    add = Fun (FunctionSymbol "add" 2 False)
    suc = Fun (FunctionSymbol "suc" 1 False)
    zero = Fun (FunctionSymbol "zero" 0 False) []

    --Variables

    x = Var 1
    y = Var 2
    z = Var 3

    --Dedekind rules
    termRewiteSystem :: [Rule (FunctionSymbol [Char]) Int]
    termRewiteSystem = [mul[x, suc[y]] --> add[x, mul [x, y]]
        , add[x, zero] --> x
        , mul[x, zero] --> zero
        , add[x, suc[y]] --> suc[add[x,y]]]

    --Order
    order :: [Rule (FunctionSymbol [Char]) Int]
    order = [mul[] --> add[], add[] --> suc[], suc[] --> zero, mul[] --> suc[], mul[] --> zero, add[] --> zero]