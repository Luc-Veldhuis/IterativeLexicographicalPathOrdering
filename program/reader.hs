module Reader where
    import Data.Rewriting.Term as Term
    import Data.Rewriting.Rule as Rule
    import Data.List.Split
    import Control.Monad
    import Control.Monad.Except ()
    import Text.Parsec hiding (parse)
    import Text.Parsec.Prim (runP)
    import Types

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

    -- should look like : (["x", "y"],"f(x,y) --> g(y)|g(y) --> 0") for TRS
    -- should look like : ([], "mul --> add|add --> suc") for order
    parseInput :: IO[(Rule (FunctionSymbol String) Int)]
    parseInput = do
        file <- readFile "trs.txt"
        parsed <- parseFile file
        return parsed --call main function here

    parseFile :: String -> IO[(Rule (FunctionSymbol String) Int)]
    parseFile file = do
        tuple <- return ((read file)::([String], String))
        return (parseRules tuple)

    --parseRules :: ([String], String) -> [(Rule (FunctionSymbol String) Int)]
    parseRules (variables, rules) = Prelude.map (parseRule variables) (splitOn "|" rules)

    --parseRule :: [String] -> String -> (Rule (FunctionSymbol String) Int)
    parseRule variables rule = let splitRule = splitOn "-->" rule in
        return (convertStringTerm (fromString variables (head splitRule)) (fromString variables (head(tail(splitRule))) ) )

    convertStringTerm :: Either ParseError (Term String String) -> Either ParseError (Term String String) -> IO(Rule (FunctionSymbol String) Int)
    convertStringTerm leftTerm rightTerm = case leftTerm of 
        Left err -> do { putStr "parse error at "; print err; mzero }
        Right left  -> case rightTerm of
            Left err -> do { putStr "parse error at "; print err; mzero }
            Right right -> 
                let leftTerm = convertStringTermHelper left
                    rightTerm = convertStringTermHelper right in
                    return (leftTerm --> rightTerm)

    convertStringTermHelper :: Term String String -> (Term (FunctionSymbol String) Int)
    convertStringTermHelper (Fun f list) = Fun (FunctionSymbol f (length list) False) (Prelude.map (convertStringTermHelper) list)
    convertStringTermHelper (Var v) = Var (read v :: Int)