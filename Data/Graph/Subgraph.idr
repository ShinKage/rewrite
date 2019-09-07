||| Provides function for finding subgraphs, glued graphs and graph merging.
module Data.Graph.Subgraph

import Data.Fin.Extra
import Data.Vect.Extra
import Data.Vect.Subset
import public Data.Graph
import Decidable.Extra

%default total
%access export

||| Given a set of vertices, returns the subgraph composed of the given vertices.
subgraph : VSub vs -> Graph n m {vertex} {edge} vs es -> ExGraph vertex edge
subgraph {n = Z}   sub g = (_ ** _ ** _ ** _ ** empty)
subgraph {n = S n} sub g = case toList $ toFins $ invert sub of
  [] => (_ ** _ ** _ ** _ ** g)
  (x :: xs) => let g' = removeVertex x g
                   sub' = delete x sub in
                   subgraph sub' g'

||| Given a subgraph check if the given edge holds a connection between a vertex in and out of
||| the subgraph.
isGlued : VSub vs -> Graph n m vs es -> Fin m -> Bool
isGlued sub g e = not (contains (source e g) sub) || not (contains (target e g) sub)

||| Given a subgraph returns the list of vertices that holds a connection to the vertices
||| external to the subgraph.
gluedVertices : VSub vs -> Graph n m vs es -> VSub vs
gluedVertices sub g = fromFins $ filter (\v => any (isGlued sub g) $ toFins $ adjacentEdges v g)
                               $ toList $ toFins sub

||| Given a subgraph returns the part of the graph glued to to it and how it maps to the
||| original graph.
||| @lsub The vertices in the subgraph
||| @ksub The vertices in the glue
||| @kedges The edges not in the glue
||| @g The graph
gluedGraph : (lsub : VSub vs) -> (ksub : VSub vs) -> (kedges : List (Fin n, Fin n))
          -> (g : Graph n m {vertex} {edge} vs es)
          -> (n' ** m' ** vs' ** es' ** (Graph n' m' {vertex} {edge} vs' es', Vect n' (Fin n)))
gluedGraph lsub ksub kedges g = let sub' = union (invert lsub) ksub
                                    (_ ** _ ** g') = removeMapped ksub kedges g
                                    (_ ** _ ** _ ** _ ** g'') = subgraph sub' g' in
                                    (_ ** _ ** _ ** _ ** (g'', believe_me $ toFins sub'))
  where
    removeMapped : VSub vs -> List (Fin n, Fin n) -> Graph n m {vertex} {edge} vs es
                -> (m' ** es' ** Graph n m' {vertex} {edge} vs es')
    removeMapped sub xs Empty = (_ ** _ ** Empty)
    removeMapped sub xs (Edge {e} s t g)
      = if contains s sub && contains t sub && s /= t && not (elem (s, t) xs)
           then removeMapped sub xs g
           else let (m' ** es' ** g') = removeMapped sub xs g in
                    (S m' ** e :: es' ** Edge s t g')

private
minusPlus : (left, right : Nat) -> (prf : LTE right left) -> (left - right) + right = left
minusPlus left Z prf = rewrite minusZeroRight left in
                       rewrite plusZeroRightNeutral left in Refl
minusPlus (S left) (S right) (LTESucc prf)
  = let hyp = cong {f = S} $ minusPlus left right prf in
        rewrite sym $ plusSuccRightSucc (minus left right) right in
        rewrite hyp in Refl

private
shiftTo : (x : Fin n) -> (prf : LTE n n') -> Fin n'
shiftTo {n} {n'} x prf = rewrite sym $ minusPlus n' n prf in shift (n' - n) x

private
buildMapHead : LTE fn n -> Vect fn (Fin n)
buildMapHead prf = map (\x => shiftTo x prf) range

||| Merges two graph given a map of glued vertices.
||| @mapping Map of glued vertices.
||| @from Original graph
||| @to Graph to merge on
covering
merge : {tvs : Vect tn vertex} -> {tes : Vect tm edge} -> (mapping : Vect tn (Maybe (Fin fn)))
     -> (from : Graph fn fm {vertex} {edge} fvs fes) -> (to : Graph tn tm {vertex} {edge} tvs tes)
     -> (n : Nat ** m : Nat ** vs : Vect n vertex ** es : Vect m edge
                 ** (Graph n m vs es, List (Fin tn, Fin n), Vect fn (Fin n)))
merge {fn} {tvs} {tes} mapping f t
  = let (n' ** _ ** _ ** _ ** (g', prf, mapping')) = goVertices f tvs (toList $ zip range mapping) 0
        (_ ** _ ** g'') = goEdges tes g' t mapping' mapping' in
        (_ ** _ ** _ ** _ ** (g'', mapping', buildMapHead prf))
  where
    covering
    goVertices : Graph n m {vertex} {edge} vs es -> Vect tn vertex -> List (Fin tn, Maybe (Fin n))
              -> Nat -> (n' : Nat ** m' : Nat ** vs' : Vect n' vertex ** es' : Vect m' edge
                                  ** (Graph n' m' vs' es', LTE n n', List (Fin tn, Fin n')))
    goVertices g _ [] count = (_ ** _ ** _ ** _ ** (g, lteRefl, []))
    goVertices g tvs ((i, Nothing) :: xs) count
      = let g' = addVertex (index i tvs) g
            xs' = map (\x => (fst x, map (shift 1) (snd x))) xs
            ((S k) ** _ ** _ ** _ ** (g'', prf, maps)) = goVertices g' tvs xs' (count + 1)
            maps' = (i, restrict k (cast count)) :: maps in
            (_ ** _ ** _ ** _ ** (g'', lteSuccLeft prf, maps'))
    goVertices g tvs ((i, Just x) :: xs) count
      = let (_ ** _ ** _ ** _ ** (g', prf, xs')) = goVertices g tvs xs count in
            (_ ** _ ** _ ** _ ** (g', prf, (i, shiftTo x prf) :: xs'))

    covering
    goEdges : {tvs : Vect tn vertex} -> (tes : Vect tm edge) -> Graph n m {vertex} {edge} vs es
           -> Graph tn tm {vertex} {edge} tvs tes -> List (Fin tn, Fin n) -> List (Fin tn, Fin n)
           -> (m' : Nat ** es' : Vect m' edge ** Graph n m' vs es')
    goEdges tes g tg mapping [] = (_ ** _ ** g)
    goEdges tes g tg mapping ((i, x) :: xs)
      = let conn = outEdges i tg
            (_ ** _ ** g') = goEdgesRec tes x g tg mapping conn in
            goEdges tes g' tg mapping xs
      where
        goEdgesFold : {vs : Vect n vertex} -> {es : Vect m edge} -> Fin n -> Fin n -> (e : edge)
                   -> Graph n m vs es
                   -> (m' : Nat ** es' : Vect m' edge ** (Graph n m' vs es', LTE m m'))
        goEdgesFold s t e g with (decIsFalse $ decAsBool (hasEdge s t g))
          goEdgesFold s t e g | Yes prf = (_ ** _ ** (addEdge s t e g, lteSuccRight lteRefl))
          goEdgesFold s t e g | No prf = (_ ** _ ** (g, lteRefl))

        goEdgesRec : {vs : Vect n vertex} -> {es : Vect m edge} -> {tvs : Vect tn vertex}
                  -> (tes : Vect tm edge) -> Fin n -> Graph n m vs es -> Graph tn tm tvs tes
                  -> List (Fin tn, Fin n) -> Vect p (Fin tm)
                  -> (m' : Nat ** es' : Vect m' edge ** Graph n m' vs es')
        goEdgesRec _ _ g _ _ [] = (_ ** _ ** g)
        goEdgesRec tes s g tg mapping (i :: xs)
          = let e = index i tes
                t = snd <$> find (\x => fst x == target i tg) mapping in
                case t of
                     Just t => let (_ ** _ ** (g', prf)) = goEdgesFold s t e g in
                                   goEdgesRec tes s g' tg mapping xs
                     Nothing => goEdgesRec tes s g tg mapping xs
