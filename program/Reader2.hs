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

    -- should look like : ["x", "y"];"f(x,y) > g(y)|g(y) > 0" for TRS
    -- should look like : []; "mul --> add|add --> suc" for order
    processRules :: [String] -> [(String, String)] -> [Rule (FunctionSymbol String) Int]
    processRules varList ruleList = Prelude.map (\(l,r) -> (convertStringTerm (fromString varList l) (fromString varList r))) ruleList

    trsFile :: GenParser Char st [(Rule (FunctionSymbol String) Int)]
    trsFile = endBy line eol

    line :: GenParser Char st [(Rule (FunctionSymbol String) Int)]
    line = do
        varList <- list
        (char '"')
        rulesInput <- rules
        (char '"')
        return  $processRules varList rulesInput

    list :: GenParser Char st [String]
    list = do
        (char '[')
        items <- listItems
        (char ']')
        return items

    listItems :: GenParser Char st [String]
    listItems = do
        first <- listItem
        next <- remainingItems
        return (first : next)

    listItem :: GenParser Char st String
    listItem = do
        (char '"')
        item <- many (noneOf ['"'])
        (char '"')
        return item

    remainingItems :: GenParser Char st [String]
    remainingItems = do
        (char ',' >> listItems)
        <|> return []


    rules :: GenParser Char st [(String, String)]
    rules = do
        first <- ruleContent
        next <- remainingRules
        return (first : next)

    remainingRules :: GenParser Char st [(String, String)]
    remainingRules = 
        (char '|' >> rules)
        <|> return []

    ruleContent :: GenParser Char st (String, String)
    ruleContent = do 
        left <- many (noneOf ">")
        right <- many (noneOf "|")
        return (left, right)

    eol :: GenParser Char st Char
    eol = char '\n'

    parseTRS :: String -> Either ParseError [(Rule (FunctionSymbol String) Int)]
    parseTRS input = parse trsFile "(unknown)" input

    convertStringTerm :: Either ParseError (Term String String) -> Either ParseError (Term String String) -> (Rule (FunctionSymbol String) Int)
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