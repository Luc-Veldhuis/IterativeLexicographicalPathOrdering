module Main where
    import Data.Rewriting.Term as Term
    import Types
    import Generators
    import Helpers

    --Function symbols
    mul = Fun (FunctionSymbol "mul" 2 False)
    add = Fun (FunctionSymbol "add" 2 False)
    suc = Fun (FunctionSymbol "suc" 1 False)
    zero = Fun (FunctionSymbol "zero" 0 False) []

    --Variables

    x = Var 1
    y = Var 2
    z = Var 3

    --Dedekind rules
    termRewiteSystem = [mul[x, suc[y]] --> add[x, mul [x, y]]
        , add[x, zero] --> x
        , mul[x, zero] --> zero
        , add[x, suc[y]] --> suc[add[x,y]]]

    --Order
    order = [mul[] --> add[], add[] --> suc[]]

    main :: IO()
    main = print(generateIterLexico order (getFunctionSymbolsFromRules termRewiteSystem ))