module TRSPropositional where
    import Types
    import Data.Rewriting.Term as Term
    import Data.Rewriting.Rule as Rule
    --Function symbols
    neg = Fun (FunctionSymbol "neg" 1 False)
    land = Fun (FunctionSymbol "land" 2 False)
    lor = Fun (FunctionSymbol "lor" 2 False)

    --Variables

    alpha = Var 1
    beta = Var 2
    gamma = Var 3

    --Propositional rules
    termRewiteSystem :: [Rule (FunctionSymbol [Char]) Int]
    termRewiteSystem = [neg[neg[alpha]] --> alpha
        , neg[lor[alpha, beta]] --> land[neg[alpha], neg[beta]]
        , neg[land[alpha, beta]] --> lor[neg[alpha], neg[beta]]
        , land[alpha, lor[beta, gamma]] --> lor[land[alpha, beta], land[alpha, gamma]]
        , land[lor[beta, gamma], alpha] --> lor[land[beta, alpha], land[gamma, alpha]]
        , land[land[alpha, beta], gamma] --> land[alpha, land[beta, gamma]]
        , lor[alpha, alpha] --> alpha
        , land[alpha, alpha] --> alpha]

    --Order
    order = [neg[] --> land[], land[] --> lor[]]