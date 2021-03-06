module Reader where
    import Data.Rewriting.Term as Term hiding (parse)
    import Data.Rewriting.Rule as Rule
    import Control.Monad
    import Text.ParserCombinators.Parsec
    import Types

    -- should look like : []; "mul --> add|add --> suc" for order
    orderFile :: Parser [[(String, String)]]
    orderFile = endBy rules eol

    -- should look like : ["x", "y", "z"];"mul(x,suc(y)) --> add(x, mul(x, y))|add(x, zero) --> x" for TRS

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
        left <- many (noneOf "->|\"\n\r")
        (string "-->")
        right <- many (noneOf "->|\"\n\r")
        return (left, right)

    eol :: Parser String
    eol = try (string "\n") 
            <|> try (string "\r\n") 

    parseOrder :: String -> IO (Either ParseError [[(String,String)]])
    parseOrder filename = parseFromFile orderFile filename

    parseTRS :: String -> IO (Either ParseError [([String],[(String,String)])])
    parseTRS filename = parseFromFile trsFile filename

    --stripParseError :: IO ([String], [(String, String)])
    stripParseError parseOutput = do
        readInput <- parseOutput
        case readInput of
            Left err -> do {print $ "A parsing error was found: " ++ (show err); mzero}
            Right result -> return $head result

    mergeLists :: [a] -> [b] -> [(a,b)]
    mergeLists [] rList = []
    mergeLists lList [] = []
    mergeLists lList rList = (head(lList), head(rList)) : mergeLists (tail lList) (tail rList)
    
    convertToRules :: (EOS f, EOS v) => [(Term (FunctionSymbol f) v, Term (FunctionSymbol f) v)] -> [Rule (FunctionSymbol f) v]
    convertToRules [] = []
    convertToRules list = (fst(head list) --> snd (head list)) : (convertToRules $ tail list)

    getTupleFromList :: [(String, Int)] -> String -> (String, Int)
    getTupleFromList variables variable = let filteredList = filter (\v-> (fst v) == variable) variables in
        if length filteredList > 0 then
            head filteredList
        else
            (variable, 0)

    convertTerm :: [(String, Int)] -> (Term String String) -> (Term (FunctionSymbol String) Int)
    convertTerm variables (Fun f []) = Fun (FunctionSymbol f 0 False) []
    convertTerm variables (Fun f list) = Fun (FunctionSymbol f (length list) False) (Prelude.map (convertTerm variables) list)
    convertTerm variables (Var v) = Var (snd $ getTupleFromList variables v)

    generateTerm :: [String] -> String -> IO(Term (FunctionSymbol String) Int)
    generateTerm variables stringTerm = 
        do
        term <- (parseIO variables stringTerm)
        let variablesInt = mergeLists variables [1..(length variables)]
        let processedTerm = convertTerm variablesInt term
        return processedTerm

    processTRS :: String -> IO [Rule (FunctionSymbol String) Int]
    processTRS filename= 
        do
        input <- (stripParseError $ parseTRS filename)
        let variables = fst input
        let termList = snd input
        let leftTerms = sequence $ Prelude.map (\term -> generateTerm variables $fst term) $ termList
        let rightTerms = sequence $ Prelude.map (\term -> generateTerm variables $ snd term) $ termList
        lList <- leftTerms
        rList <- rightTerms
        let ruleList = convertToRules $ mergeLists lList rList
        return ruleList

    processOrder ::  String -> IO [Rule (FunctionSymbol String) Int]
    processOrder filename= 
        do
        input <- (stripParseError $ parseOrder filename)
        let rules = Prelude.map (\f -> (Fun (FunctionSymbol (fst f) 0 False) []) --> (Fun (FunctionSymbol (snd f) 0 False) [])) input
        return rules