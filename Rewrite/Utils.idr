module Rewrite.Utils

import Data.Graph
import Data.Graph.Morphism
import Data.Graph.VF2
import Data.Vect.Extra
import Data.Vect.Subset

%default total
%access public export

data RewriteError = NotInjective String String
                  | NotHomomorphism String String
                  | IndexOutOfBounds Nat Nat
                  | FailedConversion String String
                  | CommutativeError String String
                  | NotAllowed String String
                  | NonEmptyNegative

rewriteErrorMessage : RewriteError -> String
rewriteErrorMessage (NotInjective from to)     = "The morphism " ++ from ++ " -> " ++ to ++ " is not injective"
rewriteErrorMessage (NotHomomorphism from to)  = "The morphism " ++ from ++ " -> " ++ to ++ " it not homomorphic"
rewriteErrorMessage (IndexOutOfBounds i m)     = "The index " ++ show i ++ " is out of bounds (max " ++ show m ++ ")"
rewriteErrorMessage (FailedConversion from to) = "Failure trying to build the morphism " ++ from ++ " -> " ++ to
rewriteErrorMessage (CommutativeError from to) = "Path " ++ from ++ " and " ++ to ++ " are not commutative"
rewriteErrorMessage (NotAllowed from to)       = "The morphism " ++ from ++ " -> " ++ to ++ " is not allowed"
rewriteErrorMessage NonEmptyNegative           = "There must not be any valid match"

maybeTuple : (Maybe a, Maybe b) -> Maybe (a, b)
maybeTuple (a, b) = [ (a', b') | a' <- a, b' <- b ]

convertVect : String -> String -> (xs : Vect n (Maybe elem)) -> Either RewriteError (Vect n elem)
convertVect from to = maybeToEither (FailedConversion from to) . convertVect

||| Given two graphs and a list of pair of vertices, tries to find a valid morphism between
||| the vertices of the two graphs.
||| @g1 The graph source of the morphism
||| @g2 The graph target of the morphism
||| @morph Pairs of source-target vertices
convertMorph : String -> String -> (g1 : Graph n m {vertex = String} {edge = String} vs es)
            -> (g2 : Graph n' m' {vertex = String} {edge = String} vs' es')
            -> (morph : List (String, String)) -> Either RewriteError (Vect n (Fin n'))
convertMorph {vs} {vs'} from to g g' morph = do
  morph <- maybeToEither (FailedConversion from to) $ traverse (\(x, y) => maybeTuple (elemIndex x vs, elemIndex y vs')) morph
  convertVect from to $ map (flip lookup morph) range

||| Given a morphism between the vertices of two graphs, finds, if possible, a morphism between the edges.
||| Given an edge "a -> b" searches the edge "f(a) -> f(b)".
||| @g1 The graph source of the morphism
||| @g2 The graph target of the morphism
||| @morph The morphism between the vertices
convertEdges : (g1 : Graph n m vs es) -> (g2 : Graph n' m' vs' es')
            -> (morph : Vect n' (Fin n)) -> Maybe (Vect m' (Fin m))
convertEdges g Empty mapping = Just []
convertEdges g (Edge s t l) mapping = do
  vec <- convertEdges g l mapping
  let s' = index s mapping
  let t' = index t mapping
  m <- edgeIndex' s' t' g
  pure $ m :: vec

convertList : String -> String -> List (Fin n, Fin n') -> Either RewriteError (Vect n (Fin n'))
convertList from to = maybeToEither (FailedConversion from to) . convertVect . listToVect
  where
    listToVect : List (Fin n, Fin n') -> Vect n (Maybe (Fin n'))
    listToVect {n} [] = replicate n Nothing
    listToVect ((a, b) :: xs) = replaceAt a (Just b) (listToVect xs)

vectToSubset : {xs : Vect n' a} -> Vect n (Maybe (Fin n')) -> VSub xs
vectToSubset = fromFins . catMaybes . toList

vectCompose : Vect bn (Fin cn) -> Vect an (Fin bn) -> Vect an (Fin cn)
vectCompose btoc atob = map (flip index btoc) atob

infixr 9 .
infixr 9 .!
infixr 9 .?
infixr 9 .*.

(.) : Vect bn (Fin cn) -> Vect an (Fin bn) -> Vect an (Fin cn)
(.) = vectCompose

vectMaybeCompose : Vect bn (Fin cn) -> Vect an (Maybe (Fin bn)) -> Vect an (Maybe (Fin cn))
vectMaybeCompose btoc atob = map (map (flip index btoc)) atob

(.?) : Vect bn (Fin cn) -> Vect an (Maybe (Fin bn)) -> Vect an (Maybe (Fin cn))
(.?) = vectMaybeCompose

vectBiCompose : Vect bn (Fin cn) -> Vect an (Fin bn, Fin bn) -> Vect an (Fin cn, Fin cn)
vectBiCompose btoc atob = map (\(f, s) => (index f btoc, index s btoc)) atob

(.*.) : Vect bn (Fin cn) -> Vect an (Fin bn, Fin bn) -> Vect an (Fin cn, Fin cn)
(.*.) = vectBiCompose

vectInverseCompose : Vect cn (Fin bn) -> Vect an (Fin bn) -> Vect an (Maybe (Fin cn))
vectInverseCompose ctob atob = map (flip elemIndex ctob) atob

(.!) : Vect cn (Fin bn) -> Vect an (Fin bn) -> Vect an (Maybe (Fin cn))
(.!) = vectInverseCompose

mergeMapping : {rn : Nat} -> Vect kn (Fin rn) -> Vect kn (Fin dn) -> Vect rn (Maybe (Fin dn))
mergeMapping {rn} ktor ktod = foldr (\(x, y) => replaceAt x (Just y)) (replicate rn Nothing) (zip ktor ktod)

||| Given a morphism between the vertices of two graphs, finds, if possible, a morphism between the graphs,
||| and checks if it is a structure preserving morphism.
||| @from The graph source of the morphism
||| @to The graph target of the morphism
||| @morph The morphism between the vertices
findMorphism : String -> String -> (from : Graph n m vs es) -> (to : Graph n' m' vs' es')
            -> (morph : Vect n (Fin n'))
            -> Either RewriteError (mor : Morphism from to ** Homomorphism from to mor)
findMorphism fs ts from to fromToMap = do
  fromToMapEdges <- maybeToEither (FailedConversion fs ts) $ convertEdges to from fromToMap
  let mor = Morph fromToMap fromToMapEdges
  let (Yes hom) = isHomomorphism from to mor | Left (NotHomomorphism fs ts)
  pure (mor ** hom)

eitherGuard : a -> Bool -> Either a ()
eitherGuard err False = Left err
eitherGuard err True = Right ()

checkInjective : String -> String -> Vect n (Fin m) -> Either RewriteError ()
checkInjective _ _ [] = Right ()
checkInjective from to (x :: xs) = eitherGuard (NotInjective from to) $
  all (\(x, y) => x /= y) $ sort $ zip (toList $ x :: xs) (toList xs)

checkPath : String -> String -> Vect n (Fin m) -> Vect n (Fin m) -> Either RewriteError ()
checkPath from to p1 p2 = eitherGuard (CommutativeError from to) $ p1 == p2

indexCheck : Nat -> List a -> Either RewriteError a
indexCheck i xs = maybeToEither (IndexOutOfBounds i (length xs)) $ index' i xs

eitherUnless : String -> String -> Either RewriteError a -> Either RewriteError ()
eitherUnless from to (Left _) = Right ()
eitherUnless from to (Right r) = Left (NotAllowed from to)

buildMatchState' : Graph n m vs es -> Graph n' m' vs' es' -> List (Fin n, Fin n') -> VF2State n n'
buildMatchState' g1 g2 morph = foldr (\(n, m) => updateState n m g1 g2) initState morph

catRightMaybes : List (a, Maybe b) -> List (a, b)
catRightMaybes [] = []
catRightMaybes ((x, Just y) :: xs) = (x, y) :: catRightMaybes xs
catRightMaybes ((x, Nothing) :: xs) = catRightMaybes xs

buildMatchState : Graph n m vs es -> Graph n' m' vs' es' -> Vect ln (Fin n') -> Vect n (Maybe (Fin ln)) -> VF2State n n'
buildMatchState g n lton gtol = buildMatchState' g n (map (\(x, y) => (x, index y lton)) $ catRightMaybes $ toList $ zip range gtol)
