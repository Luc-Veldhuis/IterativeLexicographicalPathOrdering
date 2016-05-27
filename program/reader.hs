module Reader where
    import Data.Rewriting.Term as Term
    import Data.Rewriting.Rule as Rule
    import Data.List.Split
    import Control.Monad
    import Control.Monad.Error ()
    import Text.Parsec hiding (parse)
    import Text.Parsec.Prim (runP)
    import Types

    --Still a work in progress...

    --getTRS :: [Rule (FunctionSymbol [Char]) Int]
    --getTRS = do
    --    fc <- readFile "trs.txt"
    --    parsed <- return ((read fc))
    --    parsed

    --getOrder ::  [Rule (FunctionSymbol [Char]) Int]
    --getOrder = do
    --    fc <- readFile "order.txt"
    --    parsed <- return ((read fc))
    --    parsed

    -- should look like : (["x", "y"],"f(x,y) --> g(y)|g(y) --> 0")
    parseInput = do
        file <- readFile "trs.txt"
        parsed <- parseFile file
        parsed

    parseFile file = do
        tuple <- return ((read file)::([String], String))
        parseRules tuple

    parseRules (variables, rules) = Prelude.map (parseRule variables) (splitOn "|" rules)

    parseRule variables rule = let splitRule = splitOn "-->" rule in
        convertStringTerm(fromString variables (head splitRule)) --> convertStringTerm(fromString variables (head(tail(splitRule))) )

    --Why does this work, but not what I did :(
    --parseIO :: [String] -> String -> IO (Term String String)
    --parseIO xs input = case fromString xs input of
    --Left err -> do { putStr "parse error at "; print err; mzero }
    --Right t  -> return t

    convertStringTerm :: Either ParseError (Term String String) -> (Term (FunctionSymbol String) Int)
    convertStringTerm term = case term of 
        Left err -> do { putStr "parse error at "; print err; mzero }
        Right t  -> return (convertStringTermHelper t)

    convertStringTermHelper :: Term String String -> (Term (FunctionSymbol String) Int)
    convertStringTermHelper (Fun f list) = Fun (FunctionSymbol f (length list) False) (Prelude.map (convertStringTermHelper) list)
    convertStringTermHelper (Var v) = Var (read v :: Int)