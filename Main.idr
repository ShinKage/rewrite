module Main

import Data.Graph as G
import Data.Vect
import Data.Graph.VF2
import Data.Graph.Morphism
import Data.Graph.Pushout
import Lightyear
import Lightyear.Strings
import Graphviz
import Graphviz.Parser
import Graphviz.Pretty
import Graphviz.Extra
import Language.JSON
import Rewrite
import Rewrite.Utils
import Data.Vect.Extra
import Data.Fin.Extra

data RewriteMode = Simple | Interface | Negative | Typed

data Command
  = Find (ExGraph String String) (ExGraph String String)
  | ApplyRule (ExGraph String String) (Rewrite String String) Nat
  | ApplyNegRule (ExGraph String String) (RewriteNeg String String) Nat
  | ApplyIntRule (ExGraph String String) (Rewrite String String) (ExGraph String String) (List (String, String)) Nat
  | ApplyTypedRule (ExGraph String String) (RewriteTyped String String) (List (String, String)) Nat

data AppError = KeyNotPresent String
              | InvalidMode String
              | InvalidFormat String
              | FailedConversion String String
              | InvalidCommand String
              | GraphvizError GraphvizParsingError
              | JSONParseError
              | RewritingError RewriteError

appErrorMessage : AppError -> String
appErrorMessage (KeyNotPresent key)        = "Necessary key " ++ key ++ " is not found"
appErrorMessage (InvalidMode mode)         = "Invalid mode: " ++ mode
appErrorMessage (InvalidFormat fmt)        = "Invalid format: " ++ fmt
appErrorMessage (FailedConversion from to) = "Failed conversion " ++ from ++ " -> " ++ to
appErrorMessage (InvalidCommand cmd)       = "Invalid command: " ++ cmd
appErrorMessage (GraphvizError err)        = "Graphviz parsing error: " ++ graphvizParsingErrorMessage err 
appErrorMessage JSONParseError             = "Cannot parse JSON input"
appErrorMessage (RewritingError err)       = rewriteErrorMessage err

lookup' : (Show key, Eq key) => key -> List (key, val) -> Either AppError val
lookup' key vs = maybeToEither (KeyNotPresent (show key)) $ lookup key vs

leftMap : (a -> b) -> Either a c -> Either b c
leftMap f (Left l)  = Left (f l)
leftMap f (Right r) = Right r

convertMorph : String -> String -> (g1 : Graph n m {vertex = String} {edge = String} vs es)
            -> (g2 : Graph n' m' {vertex = String} {edge = String} vs' es')
            -> (morph : List (String, String)) -> Either AppError (Vect n (Fin n'))
convertMorph fs ft from to morph = leftMap RewritingError $ convertMorph fs ft from to morph

parseMode : JSON -> Either AppError RewriteMode
parseMode (JString str) = case str of
  "simple"    => Right Simple
  "negative"  => Right Negative
  "interface" => Right Interface
  "typed"     => Right Typed
  mode        => Left (InvalidMode mode)
parseMode _ = Left (InvalidFormat "mode")

parseGraphvizGraph : JSON -> Either AppError (ExGraph String String)
parseGraphvizGraph (JString str) = (leftMap (const JSONParseError) $ parse graphP str) >>= (leftMap GraphvizError . graphvizToGraph)
parseGraphvizGraph _ = Left (InvalidFormat "graphviz")

parseMorph : JSON -> Either AppError (List (String, String))
parseMorph (JObject xs) = traverse
  (\x => case x of (k, JString v) => Right (k, v); _ => Left (InvalidFormat "morph")) xs
parseMorph _ = Left (InvalidFormat "morph")

parseRewriteSimple : ExGraph String String -> ExGraph String String -> ExGraph String String
                  -> List (String, String) -> List (String, String)
                  -> Either AppError (Rewrite String String)
parseRewriteSimple (_ ** _ ** _ ** _ ** preGraph) (_ ** _ ** _ ** _ ** glueGraph)
                   (_ ** _ ** _ ** _ ** postGraph) gluePreMorph gluePostMorph = do
  gluePreMorph <-  convertMorph "glue" "pre" glueGraph preGraph gluePreMorph
  gluePostMorph <- convertMorph "glue" "post" glueGraph postGraph gluePostMorph
  let postPreAssoc = map (flip index gluePreMorph) <$> gluePostMorph .! range
  pure $ MkRule preGraph postGraph glueGraph gluePreMorph gluePostMorph postPreAssoc

parseRewriteNeg : ExGraph String String -> ExGraph String String -> ExGraph String String
               -> List (String, String) -> List (String, String)
               -> ExGraph String String -> List (String, String)
               -> Either AppError (RewriteNeg String String)
parseRewriteNeg (_ ** _ ** _ ** _ ** preGraph) (_ ** _ ** _ ** _ ** glueGraph)
                (_ ** _ ** _ ** _ ** postGraph) gluePreMorph gluePostMorph
                (_ ** _ ** _ ** _ ** negGraph) preNegMorph = do
  gluePreMorph <- convertMorph "glue" "pre" glueGraph preGraph gluePreMorph
  gluePostMorph <- convertMorph "glue" "post" glueGraph postGraph gluePostMorph
  preNegMorph <- convertMorph "pre" "neg" preGraph negGraph preNegMorph
  let postPreAssoc = map (flip index gluePreMorph) <$> gluePostMorph .! range
  pure $ MkRuleNeg preGraph postGraph glueGraph negGraph gluePreMorph gluePostMorph preNegMorph postPreAssoc

parseRewriteTyped : ExGraph String String -> ExGraph String String -> ExGraph String String -> ExGraph String String
                 -> List (String, String) -> List (String, String) -> List (String, String)
                 -> List (String, String) -> List (String, String)
                 -> Either AppError (RewriteTyped String String)
parseRewriteTyped (_ ** _ ** _ ** _ ** preGraph) (_ ** _ ** _ ** _ ** glueGraph) (_ ** _ ** _ ** _ ** postGraph) (_ ** _ ** _ ** _ ** typeGraph)
                  gluePreMorph gluePostMorph preTypeMorph glueTypeMorph postTypeMorph = do
  gluePreMorph <- convertMorph "glue" "pre" glueGraph preGraph gluePreMorph
  gluePostMorph <- convertMorph "glue" "post" glueGraph postGraph gluePostMorph
  preTypeMorph <- convertMorph "pre" "type" preGraph typeGraph preTypeMorph
  glueTypeMorph <- convertMorph "glue" "type" glueGraph typeGraph glueTypeMorph
  postTypeMorph <- convertMorph "post" "type" postGraph typeGraph postTypeMorph
  let postPreAssoc = map (flip index gluePreMorph) <$> gluePostMorph .! range
  pure $ MkRuleTyped typeGraph preGraph postGraph glueGraph gluePreMorph gluePostMorph preTypeMorph postTypeMorph glueTypeMorph postPreAssoc

parseFind : List (String, JSON) -> Either AppError Command
parseFind comObj = do
  graph <- lookup' "graph" comObj >>= parseGraphvizGraph
  sub <- lookup' "subgraph" comObj >>= parseGraphvizGraph
  pure $ Find graph sub

parseApply : List (String, JSON) -> Either AppError Command
parseApply comObj = do
  JObject ruleObj <- lookup' "rule" comObj | Left (InvalidFormat "rule")
  mode <- lookup' "mode" comObj >>= parseMode
  graph <- lookup' "graph" comObj >>= parseGraphvizGraph
  preGraph <- lookup' "pre" ruleObj >>= parseGraphvizGraph
  glueGraph <- lookup' "glue" ruleObj >>= parseGraphvizGraph
  postGraph <- lookup' "post" ruleObj >>= parseGraphvizGraph
  gluePreMorph <- lookup' "gluePreMorph" ruleObj >>= parseMorph
  gluePostMorph <- lookup' "gluePostMorph" ruleObj >>= parseMorph
  JNumber d <- lookup' "matchIndex" comObj | Left (InvalidFormat "matchIndex")
  let d = cast {to = Nat} $ cast {to = Integer} d
  case mode of
     Simple => do rule <- parseRewriteSimple preGraph glueGraph postGraph gluePreMorph gluePostMorph
                  pure $ ApplyRule graph rule d
     Negative => do negGraph <- lookup' "neg" ruleObj >>= parseGraphvizGraph
                    preNegMorph <- lookup' "preNegMorph" ruleObj >>= parseMorph
                    rule <- parseRewriteNeg preGraph glueGraph postGraph gluePreMorph gluePostMorph negGraph preNegMorph
                    pure $ ApplyNegRule graph rule d
     Interface => do rule <- parseRewriteSimple preGraph glueGraph postGraph gluePreMorph gluePostMorph
                     JObject intObj <- lookup' "interface" comObj | Left (InvalidFormat "interface")
                     intGraph <- lookup' "graph" intObj >>= parseGraphvizGraph
                     intMorph <- lookup' "morph" intObj >>= parseMorph
                     pure $ ApplyIntRule graph rule intGraph intMorph d
     Typed => do typeGraph <- lookup' "type" comObj >>= parseGraphvizGraph
                 preTypeMorph <- lookup' "preTypeMorph" ruleObj >>= parseMorph
                 glueTypeMorph <- lookup' "glueTypeMorph" ruleObj >>= parseMorph
                 postTypeMorph <- lookup' "postTypeMorph" ruleObj >>= parseMorph
                 graphTypeMorph <- lookup' "graphTypeMorph" comObj >>= parseMorph
                 rule <- parseRewriteTyped preGraph glueGraph postGraph typeGraph gluePreMorph gluePostMorph preTypeMorph glueTypeMorph postTypeMorph
                 pure $ ApplyTypedRule graph rule graphTypeMorph d

parseCommand : JSON -> Either AppError Command
parseCommand (JObject xs) = case !(lookup' "command" xs) of
  JString "FIND"  => parseFind xs
  JString "APPLY" => parseApply xs
  _               => Left (InvalidCommand "code")
parseCommand _ = Left (InvalidFormat "command")

findResponse : Graph n m {vertex = String} {edge = String} vs es
            -> Graph n' m' {vertex = String} {edge = String} vs' es' -> JSON
findResponse {vs} {vs'} g sub =
  let finds = List.catMaybes $ enumMaybe 0 $ map (convertVect . fst) $ match g sub
      matches = [ JObject [("id", JNumber $ cast $ fst f), ("matches", JObject $ toList $ pairGo vs vs' (snd f) <$> range)] | f <- finds ] in
      JArray matches
  where
    pairGo : Vect n String -> Vect n' String -> Vect n' (Fin n) -> Fin n' -> (String, JSON)
    pairGo vs vs' f i = (index i vs', JString (index (index i f) vs))

    enumMaybe : Nat -> List (Maybe a) -> List (Maybe (Nat, a))
    enumMaybe start []               = []
    enumMaybe start ((Just x) :: xs) = Just (start, x) :: enumMaybe (1 + start) xs
    enumMaybe start (Nothing  :: xs) = Nothing :: enumMaybe (1 + start) xs

-- DEBUG: Convert vertices and edge labels for debugging purpose
debugVertices : Graph n m vs es -> Graph n m (Show.show <$> Vect.range) es
debugVertices Empty        = Empty
debugVertices (Edge s t g) = Edge s t (debugVertices g)

singleResultJson : ExGraph String String -> JSON
singleResultJson (_ ** _ ** _ ** _ ** g)
  = JObject [("result", JString (prettyGraph $ graphToGraphviz $ debugVertices g))]

main : IO ()
main = do
  (_ :: f :: _) <- getArgs | putStrLn "Must provide a JSON file as argument"
  Right l <- readFile f | putStrLn "Must provide a valid JSON file as argument"
  case maybeToEither JSONParseError (parse l) >>= parseCommand of
    Right (Find (_ ** _ ** _ ** _ ** g) (_ ** _ ** _ ** _ ** sub)) => do
      putStrLn . format 2 $ findResponse g sub
    Right (ApplyRule (_ ** _ ** _ ** _ ** g) rule i) => do
      putStrLn $ either rewriteErrorMessage (format 2 . singleResultJson) $ singleRewrite g rule i
    Right (ApplyNegRule (_ ** _ ** _ ** _ ** g) rule i) => do
      putStrLn $ either rewriteErrorMessage (format 2 . singleResultJson) $ singleRewrite g rule i
    Right (ApplyIntRule (_ ** _ ** _ ** _ ** g) rule (_ ** _ ** _ ** _ ** j) jMorph i) => do
      putStrLn $ either rewriteErrorMessage (format 2 . singleResultJson) $ singleRewrite g rule j jMorph i
    Right (ApplyTypedRule (_ ** _ ** _ ** _ ** g) rule tMorph i) => do
      putStrLn $ either rewriteErrorMessage (format 2 . singleResultJson) $ singleRewrite g rule tMorph i
    Left err => do
      putStrLn $ appErrorMessage err
