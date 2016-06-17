module TRSAckermann where
    import Types
    import Data.Rewriting.Term as Term
    import Data.Rewriting.Rule as Rule
    --Function symbols
    ack = Fun (FunctionSymbol "ack" 2 False)
    suc = Fun (FunctionSymbol "suc" 1 False)
    zero = Fun (FunctionSymbol "zero" 0 False) []

    --Variables

    x = Var 1
    y = Var 2

    --Ackermann rules
    termRewiteSystem :: [Rule (FunctionSymbol [Char]) Int]
    termRewiteSystem = [ack[zero, y] --> suc[y]
        , ack[suc[x], zero] --> ack[x, suc[zero]]
        , ack[suc[x], suc[y]] --> ack[x, ack[suc[x], y]]]

    --Order
    order :: [Rule (FunctionSymbol [Char]) Int]
    order = [ack[] --> suc[], suc[] --> zero]
