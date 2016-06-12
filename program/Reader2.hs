module Reader where
    import Data.Rewriting.Term as Term hiding (parse)
    import Data.Rewriting.Rule as Rule
    import Control.Monad
    import Text.ParserCombinators.Parsec
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

    -- should look like : ["x", "y", "z"];"mul(x,suc(y)) --> add(x, mul(x, y))|add(x, zero) --> x" for TRS
    -- should look like : []; "mul --> add|add --> suc" for order
    --processRules :: [String] -> [(String, String)] -> [Rule (FunctionSymbol String) Int]
    --processRules varList ruleList = Prelude.map (\(l,r) -> (convertStringTerm (fromString varList l) (fromString varList r))) ruleList

    trsFile :: Parser [([String],[(String,String)])]
    trsFile = endBy line eol

    line :: Parser ([String],[(String,String)])
    line = do
        varList <- list
        (char ';')
        (char '"')
        rulesInput <- rules
        (char '"')
        return  $(varList, rulesInput)

    list :: Parser [String]
    list = do
        (char '[')
        items <- sepBy listItem (char ',')
        (char ']')
        return items

    listItem :: Parser String
    listItem = do
        (char '"')
        item <- many (noneOf ['"', ']', '[', ';', '\r', '\n'])
        (char '"')
        return item

    rules :: Parser [(String, String)]
    rules = sepBy rule (char '|')

    rule :: Parser (String, String)
    rule = do
        left <- many (noneOf "->|\"")
        (string "-->")
        right <- many (noneOf "->|\"")
        return (left, right)

    eol :: Parser String
    eol = try (string "\n") 
            <|> try (string "\r\n") 

    parseTRS :: IO (Either ParseError [([String],[(String,String)])])
    parseTRS = parseFromFile trsFile "test.txt"

    --convertStringTerm :: Either ParseError (Term String String) -> Either ParseError (Term String String) -> (Rule (FunctionSymbol String) Int)
    --convertStringTerm leftTerm rightTerm = case leftTerm of 
    --    Left err -> do { putStr "parse error at "; print err; mzero }
    --    Right left  -> case rightTerm of
    --        Left err -> do { putStr "parse error at "; print err; mzero }
    --        Right right -> 
    --            let leftTerm = convertStringTermHelper left
    --                rightTerm = convertStringTermHelper right in
    --                return (leftTerm --> rightTerm)

    --convertStringTermHelper :: Term String String -> (Term (FunctionSymbol String) Int)
    --convertStringTermHelper (Fun f list) = Fun (FunctionSymbol f (length list) False) (Prelude.map (convertStringTermHelper) list)
    --convertStringTermHelper (Var v) = Var (read v :: Int)