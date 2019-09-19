module Data.Graph.VF2

import public Data.Graph
import Data.SortedSet

%default covering
%access export

-- REFERENCE: https://networkx.github.io/documentation/latest/_modules/networkx/algorithms/isomorphism/isomorphvf2.html

private
foldSets : Ord k => List (SortedSet k) -> SortedSet k
foldSets = foldr union empty

||| State of a VF2 computation.
||| @n  Vertices number of the graph to search in
||| @n' Vertices number of the graph to match
public export
record VF2State (n : Nat) (n' : Nat) where
  constructor MkState
  depth  : Nat
  core_1 : Vect n  (Maybe (Fin n'))
  core_2 : Vect n' (Maybe (Fin n))
  in_1   : Vect n  Nat
  out_1  : Vect n  Nat
  in_2   : Vect n' Nat
  out_2  : Vect n' Nat

||| Initialize the state of a VF2 execution.
initState : VF2State n n'
initState {n} {n'} = MkState n (replicate n Nothing) (replicate n' Nothing)
                             (replicate n 0) (replicate n 0)
                             (replicate n' 0) (replicate n' 0)

||| Update the state of a VF2 execution given a match between two vertices.
||| @v1    Index of the vertex in the graph to search in
||| @v2    Index of the vertex in the graph to match
||| @g1    Graph to search in
||| @g2    Graph to match
||| @state Current VF2 state
updateState : (v1 : Fin n) -> (v2 : Fin n')
           -> (g1 : Graph n m vs es) -> (g2 : Graph n' m' vs' es') -> (state : VF2State n n')
           -> VF2State n n'
updateState v1 v2 g1 g2 (MkState depth core_1 core_2 in_1 out_1 in_2 out_2)
  = let depth'  = if isJust (index v1 core_1) then depth else depth + 1
        core_1' = replaceAt v1 (Just v2) core_1
        core_2' = replaceAt v2 (Just v1) core_2
        in_1'   = if index v1 in_1  == 0 then in_1  else replaceAt v1 depth in_1
        out_1'  = if index v1 out_1 == 0 then out_1 else replaceAt v1 depth out_1
        in_2'   = if index v2 in_2  == 0 then in_2  else replaceAt v2 depth in_2
        out_2'  = if index v2 out_2 == 0 then out_2 else replaceAt v2 depth out_2
        core_1_set = toList $ snd $ filter (isJust . flip index core_1') range
        core_2_set = toList $ snd $ filter (isJust . flip index core_2') range
        new_nodes = foldSets $ map (\x => fromList . filter (isNothing . flip index core_1') . toList $ predecessors x g1) core_1_set
        in_1' = foldr (replaceInAcc depth') in_1' . filter (\x => index x in_1' == 0) $ SortedSet.toList new_nodes
        new_nodes = foldSets $ map (\x => fromList . filter (isNothing . flip index core_2') . toList $ predecessors x g2) core_2_set
        in_2' = foldr (replaceInAcc depth') in_2' . filter (\x => index x in_2' == 0) $ SortedSet.toList new_nodes
        new_nodes = foldSets $ map (\x => fromList . filter (isNothing . flip index core_1') . toList $ successors x g1) core_1_set
        out_1' = foldr (replaceInAcc depth') out_1' . filter (\x => index x out_1' == 0) $ SortedSet.toList new_nodes
        new_nodes = foldSets $ map (\x => fromList . filter (isNothing . flip index core_2') . toList $ successors x g2) core_2_set
        out_2' = foldr (replaceInAcc depth') out_2' . filter (\x => index x out_2' == 0) $ SortedSet.toList new_nodes in
        MkState depth' core_1' core_2' in_1' out_1' in_2' out_2'
    where
      replaceInAcc : a -> Fin n -> Vect n a -> Vect n a
      replaceInAcc x i acc = replaceAt i x acc

private
candidatePairsEmpty : VF2State n n' -> List (Fin n, Fin n')
candidatePairsEmpty state
  = let node2 = vectToMaybe $ snd $ filter (isNothing . flip index (core_2 state)) range in
        maybe [] (\x => map (\v => (v, x)) $ toList $ snd $
                        filter (isNothing . flip index (core_1 state)) range) node2

private
candidatePairsOutNonEmpty : VF2State n n' -> List (Fin n) -> List (Fin n') -> List (Fin n, Fin n')
candidatePairsOutNonEmpty state t1_out t2_out with (nonEmpty t2_out)
  candidatePairsOutNonEmpty state t1_out (x :: xs) | Yes IsNonEmpty = map (\y => (y, x)) t1_out
  candidatePairsOutNonEmpty state t1_out t2_out | No _ = candidatePairsEmpty state

private
candidatePairsInNonEmpty : VF2State n n' -> List (Fin n) -> List (Fin n') -> List (Fin n, Fin n')
candidatePairsInNonEmpty state t1_in t2_in with (nonEmpty t2_in)
  candidatePairsInNonEmpty state t1_in (x :: xs) | Yes IsNonEmpty = map (\y => (y, x)) t1_in
  candidatePairsInNonEmpty state t1_in t2_in | No _ = candidatePairsEmpty state

||| Finds all the possible candidate pairs given a VF2 state.
||| @state The state of the VF2 algorithm
candidatePairs : (state : VF2State n n') -> List (Fin n, Fin n')
candidatePairs {n} {n'} state@(MkState depth core_1 core_2 in_1 out_1 in_2 out_2) =
  let t1_out = toList $ snd $ filter (\x => index x out_1 /= 0 && isNothing (index x core_1)) range
      t2_out = toList $ snd $ filter (\x => index x out_2 /= 0 && isNothing (index x core_2)) range
      t1_in  = toList $ snd $ filter (\x => index x in_1  /= 0 && isNothing (index x core_1)) range
      t2_in  = toList $ snd $ filter (\x => index x in_2  /= 0 && isNothing (index x core_2)) range in
      if isCons t1_out
         then candidatePairsOutNonEmpty state t1_out t2_out
         else if isCons t1_in
                 then candidatePairsInNonEmpty state t1_in t2_in
                 else candidatePairsEmpty state

private
predSuccFeasibility : Fin n -> Fin n' -> VF2State n n'
                   -> Graph n m vs es -> Graph n' m' vs' es' -> Bool
predSuccFeasibility v1 v2 (MkState depth core_1 core_2 in_1 out_1 in_2 out_2) g1 g2
  = all (\v => maybe True (\x => elem x (predecessors v1 g1)) (index v core_2)) (predecessors v2 g2)
      && all (\v => maybe True (\x => elem x (successors v1 g1)) (index v core_2)) (successors v2 g2)

private
numPredInFeasibility : Fin n -> Fin n' -> VF2State n n'
                    -> Graph n m vs es -> Graph n' m' vs' es' -> Bool
numPredInFeasibility v1 v2 (MkState depth core_1 core_2 in_1 out_1 in_2 out_2) g1 g2
  = foldr (\v, acc => if index v in_1 /= 0 && (isNothing $ index v core_1) then acc + 1 else acc) 0 (predecessors v1 g1)
      >= foldr (\v, acc => if index v in_2 /= 0 && (isNothing $ index v core_2) then acc + 1 else acc) 0 (predecessors v2 g2)

private
numSuccInFeasibility : Fin n -> Fin n' -> VF2State n n'
                    -> Graph n m vs es -> Graph n' m' vs' es' -> Bool
numSuccInFeasibility v1 v2 (MkState depth core_1 core_2 in_1 out_1 in_2 out_2) g1 g2
  = foldr (\v, acc => if index v in_1 /= 0 && (isNothing $ index v core_1) then acc + 1 else acc) 0 (successors v1 g1)
      >= foldr (\v, acc => if index v in_2 /= 0 && (isNothing $ index v core_2) then acc + 1 else acc) 0 (successors v2 g2)

private
numPredOutFeasibility : Fin n -> Fin n' -> VF2State n n'
                     -> Graph n m vs es -> Graph n' m' vs' es' -> Bool
numPredOutFeasibility v1 v2 (MkState depth core_1 core_2 in_1 out_1 in_2 out_2) g1 g2
  = foldr (\v, acc => if index v out_1 /= 0 && (isNothing $ index v core_1) then acc + 1 else acc) 0 (predecessors v1 g1)
      >= foldr (\v, acc => if index v out_2 /= 0 && (isNothing $ index v core_2) then acc + 1 else acc) 0 (predecessors v2 g2)

private
numSuccOutFeasibility : Fin n -> Fin n' -> VF2State n n'
                     -> Graph n m vs es -> Graph n' m' vs' es' -> Bool
numSuccOutFeasibility v1 v2 (MkState depth core_1 core_2 in_1 out_1 in_2 out_2) g1 g2
  = foldr (\v, acc => if index v out_1 /= 0 && (isNothing $ index v core_1) then acc + 1 else acc) 0 (successors v1 g1)
      >= foldr (\v, acc => if index v out_2 /= 0 && (isNothing $ index v core_2) then acc + 1 else acc) 0 (successors v2 g2)

private
numPredNewFeasibility : Fin n -> Fin n' -> VF2State n n'
                     -> Graph n m vs es -> Graph n' m' vs' es' -> Bool
numPredNewFeasibility v1 v2 (MkState depth core_1 core_2 in_1 out_1 in_2 out_2) g1 g2
  = foldr (\v, acc => if index v in_1 /= 0 && index v out_1 /= 0 then acc + 1 else acc) 0 (predecessors v1 g1)
      >= foldr (\v, acc => if index v in_2 /= 0 && index v out_2 /= 0 then acc + 1 else acc) 0 (predecessors v2 g2)

private
numSuccNewFeasibility : Fin n -> Fin n' -> VF2State n n'
                     -> Graph n m vs es -> Graph n' m' vs' es' -> Bool
numSuccNewFeasibility v1 v2 (MkState depth core_1 core_2 in_1 out_1 in_2 out_2) g1 g2
  = foldr (\v, acc => if index v in_1 /= 0 && index v out_1 /= 0 then acc + 1 else acc) 0 (successors v1 g1)
      >= foldr (\v, acc => if index v in_2 /= 0 && index v out_2 /= 0 then acc + 1 else acc) 0 (successors v2 g2)

||| Checks if the given pair can be safely added to the current partial mapping.
||| @v1    Index of the vertex in the graph to search in
||| @v2    Index of the vertex in the graph to match
||| @state Current VF2 state
||| @g1    Graph to search in
||| @g2    Graph to match
feasibility : (v1 : Fin n) -> (v2 : Fin n') -> (state : VF2State n n')
           -> (g1 : Graph n m vs es) -> (g2 : Graph n' m' vs' es') -> Bool
feasibility v1 v2 state g1 g2
  = multiedges v1 v1 g1 >= multiedges v2 v2 g2
      && predSuccFeasibility   v1 v2 state g1 g2
      && numPredInFeasibility  v1 v2 state g1 g2
      && numSuccInFeasibility  v1 v2 state g1 g2
      && numPredOutFeasibility v1 v2 state g1 g2
      && numSuccOutFeasibility v1 v2 state g1 g2
      && numPredNewFeasibility v1 v2 state g1 g2
      && numSuccNewFeasibility v1 v2 state g1 g2

||| Search for subgraph isomorphism given a VF2 state. Returns the list of mapping
||| from the subgraph to the graph and the partial inverse of each mapping.
||| @g1    Graph to search in
||| @g2    Graph to match
||| @state Current VF2 state
match' : (g1 : Graph n m vs es) -> (g2 : Graph n' m' vs' es') -> (state : VF2State n n')
      -> List (Vect n' (Maybe (Fin n)), Vect n (Maybe (Fin n')))
match' {n} {n'} g1 g2 state
  = if fst (filter isJust (core_1 state)) == n'
       then [(core_2 state, core_1 state)]
       else foldr candidateHelper [] (candidatePairs state)
  where
    candidateHelper : (Fin n, Fin n')
                   -> List (Vect n' (Maybe (Fin n)), Vect n (Maybe (Fin n')))
                   -> List (Vect n' (Maybe (Fin n)), Vect n (Maybe (Fin n')))
    candidateHelper (v1, v2) acc
      = if feasibility v1 v2 state g1 g2
           then match' g1 g2 (updateState v1 v2 g1 g2 state) ++ acc
           else acc

||| Search for subgraph isomorphism. Returns the list of mapping from the subgraph to
||| the graph and the partial inverse of each mapping.
||| @g1 Graph to search in
||| @g2 Graph to match
match : (g1 : Graph n m vs es) -> (g2 : Graph n' m' vs' es')
     -> List (Vect n' (Maybe (Fin n)), Vect n (Maybe (Fin n')))
match g1 g2 = match' g1 g2 initState
