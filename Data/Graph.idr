module Data.Graph

import public Data.Fin
import Data.Fin.Extra
import public Data.Vect
import Data.Vect.Extra
import Data.Vect.Subset

%default total
%access export

||| Inductive definition of simple directed graphs. The Graph type is indexed by both the number of
||| vertex and edges and the list of vertices and edges.
||| Each source or target is defined as the index of the vertex inside the vertices vector.
||| The definition is inductive on the number of edges.
||| @n      The number of vertices
||| @m      The number of edges
||| @vertex The type of the vertices
||| @edge   The type of the edges
||| @vs     The vector of vertices
||| @es     The vector of edges
public export
data Graph : (n, m : Nat) -> {vertex, edge : Type}
          -> (vs : Vect n vertex) -> (es : Vect m edge)
          -> Type where
  ||| A graph without edges
  Empty : Graph n Z vs []
  ||| A graph with an edge from s to t
  Edge  : (s : Fin n) -> (t : Fin n) -> Graph n m vs es -> Graph n (S m) vs (e :: es)

%name Graph g, h

||| Existential version of the `Graph` data type.
public export
ExGraph : Type -> Type -> Type
ExGraph vertex edge
  = (n : Nat ** m : Nat ** vs : Vect n vertex ** es : Vect m edge ** Graph n m vs es)

||| Returns the number of vertices in a given graph.
vertexCount : Graph n m vs es -> Nat
vertexCount {n} _ = n

||| Returns the information associated to each vertex in a given graph.
verticesLabels : Graph n m {vertex} {edge} vs es -> Vect n vertex
verticesLabels {vs} _ = vs

||| Returns the information associated to each edge in a given graph.
edgesLabels : Graph n m {vertex} {edge} vs es -> Vect m edge
edgesLabels {es} _ = es

||| Returns the number of edges in a given graph.
edgeCount : Graph n m vs es -> Nat
edgeCount {m} _ = m

||| The graph with no vertices and, consequently, no edges.
empty : Graph 0 0 [] []
empty = Empty

||| Existential of the `empty` graph.
sigmaEmpty : ExGraph vertex edge
sigmaEmpty = (_ ** _ ** _ ** _ ** empty)

||| Satisfiable if the graph `g` contains the edge from `s` to `t`.
||| @s The source of the edge
||| @t The target of the edge
||| @g The graph to be searched
data HasEdge : (s : Fin n) -> (t : Fin n) -> (g : Graph n m vs es) -> Type where
  ||| Source and target are the same so the edge is here.
  Here  : HasEdge s t (Edge s t g)
  ||| If the edge is in the graph `g` then is in the graph with another edge added.
  There : HasEdge s t g -> HasEdge s t (Edge s' t' g)

Uninhabited (HasEdge s t Empty) where
  uninhabited Here      impossible
  uninhabited (There _) impossible

||| An edge cannot be inside a graph if it has not the same source of the last edge
||| and it is not the same as the other edges of the graph.
notHereNorThereSource : Not (s = s') -> Not (HasEdge s t g) -> Not (HasEdge s t (Edge s' t' g))
notHereNorThereSource snots' notthere Here = snots' Refl
notHereNorThereSource snots' notthere (There prf) = notthere prf

||| An edge cannot be inside a graph if it has not the same target of the last edge
||| and it is not the same as the other edges of the graph.
notHereNorThereTarget : Not (t = t') -> Not (HasEdge s t g) -> Not (HasEdge s t (Edge s t' g))
notHereNorThereTarget tnott' notthere Here = tnott' Refl
notHereNorThereTarget tnott' notthere (There prf) = notthere prf

||| A decision procedure for the `HasEdge` predicate.
||| @s The source of the edge
||| @t The target of the edge
||| @g The graph
hasEdge : (s, t : Fin n) -> (g : Graph n m vs es) -> Dec (HasEdge s t g)
hasEdge s t Empty = No uninhabited
hasEdge s t (Edge s' t' g) with (decEq s s')
  hasEdge s t (Edge s t' g) | Yes Refl with (decEq t t')
    hasEdge s t (Edge s t  g) | Yes Refl | Yes Refl = Yes Here
    hasEdge s t (Edge s t' g) | Yes Refl | No tnott' with (hasEdge s t g)
      hasEdge s t (Edge s t' g) | Yes Refl | No tnott' | Yes prf = Yes (There prf)
      hasEdge s t (Edge s t' g) | Yes Refl | No tnott' | No notthere
        = No (notHereNorThereTarget tnott' notthere)
  hasEdge s t (Edge s' t' g) | No snots' with (hasEdge s t g)
    hasEdge s t (Edge s' t' g) | No snots' | Yes prf = Yes (There prf)
    hasEdge s t (Edge s' t' g) | No snots' | No notthere
      = No (notHereNorThereSource snots' notthere)

||| Given a proof of the graph `g` containing an edge from `s` to `t`,
||| returns the index of the first edge with respect of the edges vector.
||| @s   The source of the edge
||| @t   The target of the edge
||| @g   The graph
||| @prf The proof that the graph contains the edge
edgeIndex : (s, t : Fin n) -> (g : Graph n m vs es) -> {auto prf : HasEdge s t g} -> Fin m
edgeIndex s t (Edge s t g) {prf = Here}      = FZ
edgeIndex s t (Edge _ _ g) {prf = There prf} = FS (edgeIndex s t g)

||| If the graphs contains an edge from `s` to `t` returns the index of the
||| first edge with respect of the edges vector. Otherwise returns `Nothing`.
||| @s The source of the edge
||| @t The target of the edge
||| @g The graph
edgeIndex' : (s, t : Fin n) -> (g : Graph n m vs es) -> Maybe (Fin m)
edgeIndex' s t g with (hasEdge s t g)
  edgeIndex' s t g | Yes prf = Just (edgeIndex s t g)
  edgeIndex' _ _ _ | No _    = Nothing

||| Returns the edge at the given position.
edge : Fin m -> Graph n m {vertex} {edge} vs es -> edge
edge {es} i g = index i es

||| Returns the first edge with the given source and target.
||| @s   The source of the edge
||| @t   The target of the edge
||| @g   The graph
||| @prf A proof that that the edge is in the graph
findEdge : (s, t : Fin n) -> (g : Graph n m {vertex} {edge} vs es) -> {auto prf : HasEdge s t g}
        -> edge
findEdge s t g = edge (edgeIndex s t g) g

||| Returns the first edge with the given source and target if is in the graph.
||| @s   The source of the edge
||| @t   The target of the edge
||| @g   The graph
findEdge' : (s, t : Fin n) -> (g : Graph n m {vertex} {edge} vs es) -> Maybe edge
findEdge' s t g with (hasEdge s t g)
  findEdge' s t g | Yes prf = Just (findEdge s t g)
  findEdge' s t g | No _    = Nothing

||| Adds an edge to the graph, the graph can have multiedges.
||| @s The source of the new edge
||| @t The target of the new edge
||| @e The edge
||| @g The graph
addEdge : (s, t : Fin n) -> (e : edge) -> (g : Graph n m vs es) -> Graph n (S m) vs (e :: es)
addEdge s t e g = Edge s t g

||| Adds a specified size of edges to the given graph.
||| @edges The label of each edge
||| @sources The sources of the new edges
||| @targets The targets of the new edges
||| @g The graph
addEdges : (edges : Vect p edge) -> (sources : Vect p (Fin n)) -> (targets : Vect p (Fin n))
        -> (g : Graph n m vs es) -> Graph n (p + m) vs (edges ++ es)
addEdges []        []        []        g = g
addEdges (e :: es) (s :: ss) (t :: ts) g = addEdge s t e (addEdges es ss ts g)

||| Removes the edge at the given position from the graph.
removeEdge : (e : Fin (S m)) -> Graph n (S m) vs es -> Graph n m vs (deleteAt e es)
removeEdge           FZ     (Edge _ _ g) = g
removeEdge {m = S k} (FS e) (Edge s t g) = Edge s t (removeEdge e g)

||| Removes all the edges flagged as `Out` in the edges subset.
removeEdges : (edges : VSub es) -> Graph n m vs es -> Graph n (size edges) vs (extract es edges)
removeEdges Empty     Empty        = Empty
removeEdges (In sub)  (Edge s t g) = Edge s t (removeEdges sub g)
removeEdges (Out sub) (Edge s t g) = removeEdges sub g

||| Adds the vertex to the graph at the head of the vertices vector.
addVertex : (v : vertex) -> Graph n m vs es -> Graph (S n) m (v :: vs) es
addVertex _ Empty        = Empty
addVertex v (Edge s t g) = Edge (FS s) (FS t) (addVertex v g)

||| Adds the given list of vertices at the head of the vertices vector.
addVertices : (vertices : Vect p vertex) -> Graph n m vs es
           -> Graph (p + n) m (vertices ++ vs) es
addVertices []        g = g
addVertices (v :: vs) g = addVertex v (addVertices vs g)

||| Returns a vector with the pair source-target of each edge of the graph.
edges : Graph n m vs es -> Vect m (Fin n, Fin n)
edges Empty        = []
edges (Edge s t g) = (s, t) :: edges g

||| Returns the source of the edge at the given position.
public export
source : Fin m -> Graph n m vs es -> Fin n
source FZ     (Edge s _ g) = s
source (FS i) (Edge _ _ g) = source i g

||| Returns the target of the edge at the given position.
public export
target : Fin m -> Graph n m vs es -> Fin n
target FZ     (Edge _ t g) = t
target (FS i) (Edge _ _ g) = target i g

||| Returns the in-degree of the vertex at the given position.
indegree : Fin n -> Graph n m vs es -> Nat
indegree v Empty = 0
indegree v (Edge _ t g) with (decEq v t)
  indegree v (Edge _ v g) | Yes Refl = S (indegree v g)
  indegree v (Edge _ _ g) | No _     = indegree v g

||| Return the out-degree of the vertex at the given position.
outdegree : Fin n -> Graph n m vs es -> Nat
outdegree v Empty = 0
outdegree v (Edge s t g) with (decEq v s)
  outdegree v (Edge v _ g) | Yes Refl = S (outdegree v g)
  outdegree v (Edge _ _ g) | No _     = outdegree v g

||| Returns the predecessors of the vertex at the given position.
||| The number of predecessors is equal to the in-degree of the vertex.
predecessors : (v : Fin n) -> (g : Graph n m vs es) -> Vect (indegree v g) (Fin n)
predecessors v Empty = []
predecessors v (Edge s t g) with (decEq v t)
  predecessors v (Edge s v g) | Yes Refl = s :: predecessors v g
  predecessors v (Edge _ _ g) | No _     = predecessors v g

||| Returns the successors of the vertex at the given position.
||| The number of successors is equal to the out-degree of the vertex.
successors : (v : Fin n) -> (g : Graph n m vs es) -> Vect (outdegree v g) (Fin n)
successors v Empty = []
successors v (Edge s t g) with (decEq v s)
  successors v (Edge v t g) | Yes Refl = t :: successors v g
  successors v (Edge _ _ g) | No _     = successors v g

||| Returns the edges that have the vertex at the given position as target.
||| The number of edges is equal to the in-degree of the vertex.
inEdges : (v : Fin n) -> (g : Graph n m vs es) -> Vect (indegree v g) (Fin m)
inEdges v Empty = []
inEdges v (Edge s t g) with (decEq v t)
  inEdges v (Edge _ v g) | Yes Refl = FZ :: map FS (inEdges v g)
  inEdges v (Edge _ _ g) | No _     = map FS (inEdges v g)

||| Returns the edges that have the vertex at the given position as source.
||| The number of edges is equal to the out-degree of the vertex.
outEdges : (v : Fin n) -> (g : Graph n m vs es) -> Vect (outdegree v g) (Fin m)
outEdges v Empty = []
outEdges v (Edge s t g) with (decEq v s)
  outEdges v (Edge v _ g) | Yes Refl = FZ :: map FS (outEdges v g)
  outEdges v (Edge _ _ g) | No _     = map FS (outEdges v g)

||| A proof that the in-degree of a given vertex is less than or equal to the
||| number of edges in the graph.
indegreeLTE : (v : Fin n) -> (g : Graph n m vs es) -> LTE (indegree v g) m
indegreeLTE v Empty = LTEZero
indegreeLTE v (Edge s t g) with (decEq v t)
  indegreeLTE v (Edge s v g) | Yes Refl = LTESucc (indegreeLTE v g)
  indegreeLTE v (Edge s t g) | No _     = lteSuccRight (indegreeLTE v g)

||| A proof that the out-degree of a given vertex is less than or equal to the
||| number of edges in the graph.
outdegreeLTE : (v : Fin n) -> (g : Graph n m vs es) -> LTE (outdegree v g) m
outdegreeLTE v Empty = LTEZero
outdegreeLTE v (Edge s t g) with (decEq v s)
  outdegreeLTE v (Edge v t g) | Yes Refl = LTESucc (outdegreeLTE v g)
  outdegreeLTE v (Edge s t g) | No _     = lteSuccRight (outdegreeLTE v g)

||| Returns the number of adjacent edges to the vertex at the given position.
adjacent : Fin n -> Graph n m vs es -> Nat
adjacent v Empty = 0
adjacent v (Edge s t g) with (decEq v s)
  adjacent v (Edge v _ g) | Yes Refl = S (adjacent v g)
  adjacent v (Edge s t g) | No _ with (decEq v t)
    adjacent v (Edge _ v g) | No _ | Yes Refl = S (adjacent v g)
    adjacent v (Edge _ _ g) | No _ | No _     = adjacent v g

||| A proof that the number of adjacent edges to a given vertex is less than or equal to the
||| number of edges in the graph.
adjacentLTE : (v : Fin n) -> (g : Graph n m vs es) -> LTE (adjacent v g) m
adjacentLTE v Empty = LTEZero
adjacentLTE v (Edge s t g) with (decEq v s)
  adjacentLTE v (Edge v _ g) | Yes Refl = LTESucc (adjacentLTE v g)
  adjacentLTE v (Edge s t g) | No _ with (decEq v t)
    adjacentLTE v (Edge _ v g) | No _ | Yes Refl = LTESucc (adjacentLTE v g)
    adjacentLTE v (Edge _ _ g) | No _ | No _     = lteSuccRight (adjacentLTE v g)

||| A proof that given a graph with only one vertex, the number of adjacent edges is equal to the
||| number of edges.
adjacentLast : (g : Graph 1 m vs es) -> (adjacent 0 g = m)
adjacentLast Empty             = Refl
adjacentLast (Edge FZ     t g) = cong $ adjacentLast g
adjacentLast (Edge (FS x) t g) = absurd x

||| Returns the vertices adjacent to the vertex at the given position.
adjacentVertices : Fin n -> Graph n m vs es -> VSub vs
adjacentVertices v Empty = none
adjacentVertices v (Edge s t g) with (decEq v s)
  adjacentVertices v (Edge v t g) | Yes Refl = add t (adjacentVertices v g)
  adjacentVertices v (Edge s t g) | No _ with (decEq v t)
    adjacentVertices v (Edge s v g) | No _ | Yes Refl = add s (adjacentVertices v g)
    adjacentVertices v (Edge s t g) | No _ | No _     = adjacentVertices v g

||| Returns the edges that connects the vertex at the given position to the
||| adjacent vertices.
adjacentEdges : Fin n -> Graph n m vs es -> VSub es
adjacentEdges v Empty = Empty
adjacentEdges v (Edge s t g) with (decEq v s)
  adjacentEdges v (Edge v t g) | Yes Refl = In (adjacentEdges v g)
  adjacentEdges v (Edge s t g) | No _ with (decEq v t)
    adjacentEdges v (Edge s v g) | No _ | Yes Refl = In (adjacentEdges v g)
    adjacentEdges v (Edge s t g) | No _ | No _     = Out (adjacentEdges v g)

||| Returns the subset of all the edges connected to the given subset of vertices.
subAdjancecies : VSub vs -> Graph n m vs es -> VSub es
subAdjancecies sub g = foldr union none $ map (flip adjacentEdges g) $ toFins sub

||| Returns the number of edges between to vertex at the given positions.
||| @s The source of the edges
||| @t The target of the edges
||| @g The graph
multiedges : (s : Fin n) -> (t : Fin n) -> (g : Graph n m vs es) -> Nat
multiedges s t Empty = 0
multiedges s t (Edge s' t' g) with (decEq s s')
  multiedges s t (Edge s  t' g) | Yes Refl with (decEq t t')
    multiedges s t (Edge s t  g) | Yes Refl | Yes Refl = S (multiedges s t g)
    multiedges s t (Edge s t' g) | Yes Refl | No _     = multiedges s t g
  multiedges s t (Edge s' t' g) | No _ = multiedges s t g

||| Removes the vertex at the given position and all the connected edges from the graph.
||| @v The position of the vertex
||| @g The graph
removeVertex : (v : Fin (1 + n)) -> (g : Graph (1 + n) m {vertex} {edge} vs es)
            -> Graph n _ (deleteAt v vs) (extract es (invert $ adjacentEdges v g))
removeVertex v Empty = Empty
removeVertex v (Edge s t g) with (decEq v s)
  removeVertex v (Edge v t g) | Yes Refl = removeVertex v g
  removeVertex v (Edge s t g) | No contras with (decEq v t)
    removeVertex v (Edge s v g) | No contras | Yes Refl = removeVertex v g
    removeVertex v (Edge s t g) | No contras | No contrat
      = let s' = limitStrengthen v s {notEq = contras}
            t' = limitStrengthen v t {notEq = contrat}
            g' = removeVertex v g in Edge s' t' g'
