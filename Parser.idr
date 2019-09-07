module Parser

import Data.Graph
import Lightyear
import Lightyear.Char
import Lightyear.Strings

%default covering
%access export

listToVect : (xs : List a) -> (p : Nat ** Vect p a)
listToVect []        = (_ ** [])
listToVect (x :: xs) = let (_ ** xs') = listToVect xs in (_ ** x :: xs')

vertex : Parser String
vertex = pack <$> some alphaNum

vertices : (g : ExGraph String String) -> Parser (ExGraph String String)
vertices (_ ** _ ** _ ** _ ** g) = do
  (_ ** vs) <- listToVect <$> sepBy vertex (char ' ')
  pure (_ ** _ ** _ ** _ ** addVertices vs g)

edge : (n : Nat) -> Parser (String, Fin n, Fin n)
edge n = do
  e <- pack <$> some alphaNum
  char ':'
  Just s <- (\i => integerToFin i n) <$> integer | fail "source must be a valid index"
  char ','
  Just t <- (\i => integerToFin i n) <$> integer | fail "target must be a valid index"
  pure (e, s, t)

edges : ExGraph String String -> Parser (ExGraph String String)
edges (n ** _ ** _ ** _ ** g) = do
  (_ ** es') <- listToVect <$> sepBy (edge n) (char ' ')
  let es = map fst es'
  let ss = map (Basics.fst . snd) es'
  let ts = map (Basics.snd . snd) es'
  pure (_ ** _ ** _ ** _ ** addEdges es ss ts g)

graph : Parser (ExGraph String String)
graph = do
  g <- vertices sigmaEmpty
  char ' '
  token "-"
  edges g
-- a b c d e f b - e1:0,1 e2:0,2 e3:1,2

private
encodeHelper : Graph n m {vertex = String} {edge = String} vs es -> String
encodeHelper {es = []} Empty = ""
encodeHelper {es = (e :: es)} (Edge s t g)
  = e ++ ":" ++ show (finToNat s) ++ "," ++ show (finToNat t) ++ " " ++ encodeHelper g

encode : Graph n m {vertex = String} {edge = String} vs es -> String
encode {vs} g = let vs' = unwords . toList $ vs
                    es' = encodeHelper g in
                    vs' ++ " - " ++ es'
