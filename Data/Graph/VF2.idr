module Data.Graph.VF2

import public Data.Graph
import Data.Graph.Subgraph
import Data.List
import Data.List.CList
import Data.List.Pos
import Data.Maybe
import Decidable.Equality

||| State of a VF2 computation.
public export
record VF2State {0 vertex, vertex', edge, edge' : Type} (g : Graph vertex edge) (g' : Graph vertex' edge') where
  constructor MkState
  depth  : Nat
  core_1 : CList g.vertices  (Maybe (Vertex g'))
  core_2 : CList g'.vertices (Maybe (Vertex g))
  in_1   : CList g.vertices  Nat
  out_1  : CList g.vertices  Nat
  in_2   : CList g'.vertices Nat
  out_2  : CList g'.vertices Nat

||| Initialize the state of a VF2 execution.
export
initState : (g : Graph vertex edge) -> (g' : Graph vertex' edge') -> VF2State g g'
initState g g' =
  MkState (length g.vertices) (initialize Nothing) (initialize Nothing)
          (initialize 0) (initialize 0) (initialize 0) (initialize 0)

||| Update the state of a VF2 execution given a match between two vertices.
||| @g1    Graph to search in
||| @g2    Graph to match
||| @v1    Index of the vertex in the graph to search in
||| @v2    Index of the vertex in the graph to match
||| @state Current VF2 state
export
updateState : (g1 : Graph vertex1 edge1) -> (g2 : Graph vertex2 edge2)
           -> (v1 : Vertex g1) -> (v2 : Vertex g2) -> (state : VF2State g1 g2)
           -> VF2State g1 g2
updateState g1 g2 v1 v2 (MkState depth core_1 core_2 in_1 out_1 in_2 out_2) =
    let core_1_set = filter (\x => isJust $ index core_1' x) $ range g1.vertices
        core_2_set = filter (\x => isJust $ index core_2' x) $ range g2.vertices
        new_nodes = findNewNodes core_1_set core_1' (predecessors g1)
        in_1' = updateVec depth' in_1' $ filter (\x => index new_nodes x && index in_1' x == 0) $ range g1.vertices
        new_nodes = findNewNodes core_2_set core_2' (predecessors g2)
        in_2' = updateVec depth' in_2' $ filter (\x => index new_nodes x && index in_2' x == 0) $ range g2.vertices
        new_nodes = findNewNodes core_1_set core_1' (successors g1)
        out_1' = updateVec depth' out_1' $ filter (\x => index new_nodes x && index out_1' x == 0) $ range g1.vertices
        new_nodes = findNewNodes core_2_set core_2' (successors g2)
        out_2' = updateVec depth' out_2' $ filter (\x => index new_nodes x && index out_2' x == 0) $ range g2.vertices
     in MkState depth' core_1' core_2' in_1' out_1' in_2' out_2'
  where
    depth' : Nat
    depth' = if isJust (index core_1 v1) then depth else depth + 1
    core_1' : CList g1.vertices (Maybe (Vertex g2))
    core_1' = replaceAt core_1 v1 (Just v2)
    core_2' : CList g2.vertices (Maybe (Vertex g1))
    core_2' = replaceAt core_2 v2 (Just v1)
    in_1' : CList g1.vertices Nat
    in_1' = if index in_1 v1 == 0 then in_1 else replaceAt in_1 v1 depth
    out_1' : CList g1.vertices Nat
    out_1' = if index out_1 v1 == 0 then out_1 else replaceAt out_1 v1 depth
    in_2' : CList g2.vertices Nat
    in_2' = if index in_2 v2 == 0 then in_2 else replaceAt in_2 v2 depth
    out_2' : CList g2.vertices Nat
    out_2' = if index out_2 v2 == 0 then out_2 else replaceAt out_2 v2 depth
    updateSubset : {g : Graph vertex edge} -> CList g.vertices Bool -> List (Vertex g) -> CList g.vertices Bool
    updateSubset acc xs = foldr (\y, acc => replaceAt acc y True) acc xs
    findNewNodes : {g : Graph vertex edge} -> {0 g' : Graph vertex' edge'} -> List (Vertex g) -> CList g.vertices (Maybe (Vertex g')) -> (Vertex g -> List (Vertex g)) -> CList g.vertices Bool
    findNewNodes xs core f = foldr (\x, acc => updateSubset acc $ filter (isNothing . index core) $ f x) (initialize False) xs
    updateVec : {0 g : Graph vertex edge} -> Nat -> CList g.vertices Nat -> List (Vertex g) -> CList g.vertices Nat
    updateVec v acc xs = foldr (\x, acc => replaceAt acc x v) acc xs


candidatePairsEmpty : (g1 : Graph vertex1 edge1) -> (g2 : Graph vertex2 edge2) -> VF2State g1 g2 -> List (Vertex g1, Vertex g2)
candidatePairsEmpty g1 g2 state =
  case filter (\x => isNothing $ index state.core_2 x) $ range g2.vertices of
       [] => []
       xs@(x :: _) => map (, x) $ filter (\x => isNothing $ index state.core_1 x) $ range g1.vertices

candidatePairsOutNonEmpty : (g1 : Graph vertex1 edge1) -> (g2 : Graph vertex2 edge2) -> VF2State g1 g2 -> List (Vertex g1) -> List (Vertex g2) -> List (Vertex g1, Vertex g2)
candidatePairsOutNonEmpty g1 g2 state t1_out [] = candidatePairsEmpty g1 g2 state
candidatePairsOutNonEmpty g1 g2 state t1_out (x :: xs) = map (, x) t1_out

candidatePairsInNonEmpty : (g1 : Graph vertex1 edge1) -> (g2 : Graph vertex2 edge2) -> VF2State g1 g2 -> List (Vertex g1) -> List (Vertex g2) -> List (Vertex g1, Vertex g2)
candidatePairsInNonEmpty g1 g2 state t1_in [] = candidatePairsEmpty g1 g2 state
candidatePairsInNonEmpty g1 g2 state t1_in (x :: xs) = map (, x) t1_in

-- ||| Finds all the possible candidate pairs given a VF2 state.
-- ||| @state The state of the VF2 algorithm
candidatePairs : (g1 : Graph vertex1 edge1) -> (g2 : Graph vertex2 edge2) -> VF2State g1 g2 -> List (Vertex g1, Vertex g2)
candidatePairs g1 g2 state =
  let t1_out = filter (\x => index state.out_1 x /= 0 && isNothing (index state.core_1 x)) $ range g1.vertices
      t2_out = filter (\x => index state.out_2 x /= 0 && isNothing (index state.core_2 x)) $ range g2.vertices
      t1_in = filter (\x => index state.in_1 x /= 0 && isNothing (index state.core_1 x)) $ range g1.vertices
      t2_in = filter (\x => index state.in_2 x /= 0 && isNothing (index state.core_2 x)) $ range g2.vertices
   in if isCons t1_out
         then candidatePairsOutNonEmpty g1 g2 state t1_out t2_out
         else if isCons t1_in
                 then candidatePairsInNonEmpty g1 g2 state t1_in t2_in
                 else candidatePairsEmpty g1 g2 state

predSuccFeasibility : (g1 : Graph vertex1 edge1) -> (g2 : Graph vertex2 edge2) -> Vertex g1 -> Vertex g2 -> VF2State g1 g2 -> Bool
predSuccFeasibility g1 g2 v1 v2 state =
  all (maybe True (flip elem (predecessors g1 v1)) . index state.core_2) (predecessors g2 v2)
    && all (maybe True (flip elem (successors g1 v1)) . index state.core_2) (successors g2 v2)

numPredInFeasibility : (g1 : Graph vertex1 edge1) -> (g2 : Graph vertex2 edge2) -> Vertex g1 -> Vertex g2 -> VF2State g1 g2 -> Bool
numPredInFeasibility g1 g2 v1 v2 state =
  count (\v => index state.in_1 v /= 0 && isNothing (index state.core_1 v)) (predecessors g1 v1)
    >= count (\v => index state.in_2 v /= 0 && isNothing (index state.core_2 v)) (predecessors g2 v2)

numSuccInFeasibility : (g1 : Graph vertex1 edge1) -> (g2 : Graph vertex2 edge2) -> Vertex g1 -> Vertex g2 -> VF2State g1 g2 -> Bool
numSuccInFeasibility g1 g2 v1 v2 state =
  count (\v => index state.in_1 v /= 0 && isNothing (index state.core_1 v)) (successors g1 v1)
    >= count (\v => index state.in_2 v /= 0 && isNothing (index state.core_2 v)) (successors g2 v2)

numPredOutFeasibility : (g1 : Graph vertex1 edge1) -> (g2 : Graph vertex2 edge2) -> Vertex g1 -> Vertex g2 -> VF2State g1 g2 -> Bool
numPredOutFeasibility g1 g2 v1 v2 state =
  count (\v => index state.out_1 v /= 0 && isNothing (index state.core_1 v)) (predecessors g1 v1)
    >= count (\v => index state.out_2 v /= 0 && isNothing (index state.core_2 v)) (predecessors g2 v2)

numSuccOutFeasibility : (g1 : Graph vertex1 edge1) -> (g2 : Graph vertex2 edge2) -> Vertex g1 -> Vertex g2 -> VF2State g1 g2 -> Bool
numSuccOutFeasibility g1 g2 v1 v2 state =
  count (\v => index state.out_1 v /= 0 && isNothing (index state.core_1 v)) (successors g1 v1)
    >= count (\v => index state.out_2 v /= 0 && isNothing (index state.core_2 v)) (successors g2 v2)

numPredNewFeasibility : (g1 : Graph vertex1 edge1) -> (g2 : Graph vertex2 edge2) -> Vertex g1 -> Vertex g2 -> VF2State g1 g2 -> Bool
numPredNewFeasibility g1 g2 v1 v2 state =
  count (\v => index state.in_1 v /= 0 && index state.out_1 v /= 0) (predecessors g1 v1)
    >= count (\v => index state.in_2 v /= 0 && index state.out_2 v /= 0) (predecessors g2 v2)

numSuccNewFeasibility : (g1 : Graph vertex1 edge1) -> (g2 : Graph vertex2 edge2) -> Vertex g1 -> Vertex g2 -> VF2State g1 g2 -> Bool
numSuccNewFeasibility g1 g2 v1 v2 state =
  count (\v => index state.in_1 v /= 0 && index state.out_1 v /= 0) (successors g1 v1)
    >= count (\v => index state.in_2 v /= 0 && index state.out_2 v /= 0) (successors g2 v2)

-- ||| Checks if the given pair can be safely added to the current partial mapping.
-- ||| @v1    Index of the vertex in the graph to search in
-- ||| @v2    Index of the vertex in the graph to match
-- ||| @state Current VF2 state
-- ||| @g1    Graph to search in
-- ||| @g2    Graph to match
feasibility : (g1 : Graph vertex1 edge1) -> (g2 : Graph vertex2 edge2) -> Vertex g1 -> Vertex g2 -> VF2State g1 g2 -> Bool
feasibility g1 g2 v1 v2 state =
  length (multiedges g1 v1 v1) >= length (multiedges g2 v2 v2)
    && predSuccFeasibility   g1 g2 v1 v2 state
    && numPredInFeasibility  g1 g2 v1 v2 state
    && numSuccInFeasibility  g1 g2 v1 v2 state
    && numPredOutFeasibility g1 g2 v1 v2 state
    && numSuccOutFeasibility g1 g2 v1 v2 state
    && numPredNewFeasibility g1 g2 v1 v2 state
    && numSuccNewFeasibility g1 g2 v1 v2 state

||| Search for subgraph isomorphism given an existing VF2 state.
||| Returns the list of found subgraph relations.
|||
||| @g1 Graph to search in
||| @g2 Graph to match
||| @state A VF2 state
export
match' : (g1 : Graph vertex1 edge1) -> (g2 : Graph vertex2 edge2) -> (state : VF2State g1 g2) -> List (Subgraph g2 g1)
match' g1 g2 state =
    if length (filter isJust $ forget state.core_1) == length g2.vertices
       then convert state.core_2
       else foldr candidateHelper [] (candidatePairs g1 g2 state)
  where
    step1 : CList xs (Maybe b) -> Maybe (CList xs b)
    step1 [] = Just []
    step1 (Nothing :: xs) = Nothing
    step1 (Just x :: xs) = [ x :: xs' | xs' <- step1 xs ]

    step2 : CList xs (Pos ys) -> ListMorphism xs ys
    step2 [] = []
    step2 (x :: xs) = x :: step2 xs

    go : (g : Graph vertex edge) -> (g' : Graph vertex' edge') -> ListMorphism g.vertices g'.vertices -> List (Edge g) -> List (CList g.edges (Maybe (Edge g')))
    go g g' mor [] = [initialize Nothing]
    go g g' mor [e] =
      let s = apply mor (apply g.source e)
          t = apply mor (apply g.target e)
          edges = multiedges g' s t
       in map (\x => replaceAt (initialize Nothing) e (Just x)) edges
    go g g' mor (e :: es) =
      let s = apply mor (apply g.source e)
          t = apply mor (apply g.target e)
          edges = multiedges g' s t
          prev = go g g' mor es
       in prev >>= (\x => map (\y => replaceAt x e (Just y)) edges)

    convert : CList g2.vertices (Maybe (Vertex g1)) -> List (Subgraph g2 g1)
    convert mor = case checkInjective =<< step2 <$> step1 mor of
      Just inj => do edgeMor <- catMaybes $ map (map step2) $ map step1 $ go g2 g1 inj.morphism (range g2.edges)
                     case (decEq (g1.source . edgeMor) (inj.morphism . g2.source), decEq (g1.target . edgeMor) (inj.morphism . g2.target)) of
                          (Yes srcPrf, Yes tgtPrf) => pure (MkSubgraph inj edgeMor srcPrf tgtPrf)
                          (_, _) => []
      Nothing => []

    candidateHelper : (Vertex g1, Vertex g2) -> List (Subgraph g2 g1) -> List (Subgraph g2 g1)
    candidateHelper (v1, v2) acc
      = if feasibility g1 g2 v1 v2 state
           then match' g1 g2 (updateState g1 g2 v1 v2 state) ++ acc
           else acc

||| Search for subgraph isomorphism. Returns the list of found subgraph relations.
|||
||| @g1 Graph to search in
||| @g2 Graph to match
export
match : (g1 : Graph vertex1 edge1) -> (g2 : Graph vertex2 edge2) -> List (Subgraph g2 g1)
match g1 g2 = match' g1 g2 (initState g1 g2)
