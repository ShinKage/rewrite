module Data.Graph

import Data.List
import Data.List.CList
import Data.List.Elem
import Data.List.Pos
import Data.List.Morphism
import Data.List.InjectiveListMorphism
import Decidable.Equality
import Decidable.Decidable

%default total

||| Type for simple directed (hyper-)graphs with labels for vertices and edges.
public export
record Graph (vertex : Type) (edge : Type) where
  constructor MkGraph
  vertices : List vertex
  edges : List edge
  source : ListMorphism edges vertices
  target : ListMorphism edges vertices

%name Graph g, h, k

||| Type for vertex indices.
public export
Vertex : Graph vertex edge -> Type
Vertex g = Pos g.vertices

||| Type for edge indices.
public export
Edge : Graph vertex edge -> Type
Edge g = Pos g.edges

||| Returns the vertex count of a graph.
public export
vertexCount : Graph vertex edge -> Nat
vertexCount = length . vertices

||| Returns the edge count of a graph.
public export
edgeCount : Graph vertex edge -> Nat
edgeCount = length . edges

||| Constructs a graph with no vertices and no edges.
public export
empty : Graph vertex edge
empty = MkGraph [] [] [] []

||| Proof that there exists an edge between two specific vertices.
public export
data HasEdge : (g : Graph vertex edge) -> (s, t : Vertex g) -> Type where
  Here : HasEdge (MkGraph vertices (e :: edges) (s :: source) (t :: target)) s t
  There : HasEdge (MkGraph vertices edges source target) s t
       -> HasEdge (MkGraph vertices (e :: edges) (s' :: source) (t' :: target)) s t

public export
Uninhabited (HasEdge (MkGraph vertices [] [] []) s t) where
  uninhabited Here impossible
  uninhabited (There _) impossible

||| Decision procedure for `HasEdge`.
public export
hasEdge : DecEq edge => (g : Graph vertex edge) -> (s, t : Vertex g) -> Dec (HasEdge g s t)
hasEdge (MkGraph vertices [] [] []) s t = No uninhabited
hasEdge g@(MkGraph vertices (e :: edges) (s :: source) (t :: target)) s' t' with (decEq s s')
  hasEdge g@(MkGraph vertices (e :: edges) (s :: source) (t :: target)) s t' | Yes Refl with (decEq t t')
    hasEdge g@(MkGraph vertices (e :: edges) (s :: source) (t :: target)) s t | Yes Refl | Yes Refl = Yes Here
    hasEdge g@(MkGraph vertices (e :: edges) (s :: source) (t :: target)) s t' | Yes Refl | No contra with (hasEdge (assert_smaller g (MkGraph vertices edges source target)) s t')
      hasEdge g@(MkGraph vertices (e :: edges) (s :: source) (t :: target)) s t' | Yes Refl | No contra | Yes prf = Yes (There prf)
      hasEdge g@(MkGraph vertices (e :: edges) (s :: source) (t :: target)) s t' | Yes Refl | No contra | No further =
        No (\case Here => contra Refl
                  There prf => further prf)
  hasEdge g@(MkGraph vertices (e :: edges) (s :: source) (t :: target)) s' t' | No contra with (hasEdge (assert_smaller g (MkGraph vertices edges source target)) s' t')
    hasEdge g@(MkGraph vertices (e :: edges) (s :: source) (t :: target)) s' t' | No contra | Yes prf = Yes (There prf)
    hasEdge g@(MkGraph vertices (e :: edges) (s :: source) (t :: target)) s' t' | No contra | No further =
      No (\case Here => contra Refl
                There prf => further prf)

||| Adds an edge between two vertices.
public export
addEdge : (g : Graph vertex edge) -> (e : edge) -> (s, t : Vertex g) -> Graph vertex edge
addEdge (MkGraph vertices edges source target) e s t =
  MkGraph vertices (e :: edges) (s :: source) (t :: target)

||| Removes a specific edge from a graph.
public export
removeEdge : (g : Graph vertex edge) -> Edge g -> Graph vertex edge
removeEdge (MkGraph vertices edges source target) i =
  MkGraph vertices (drop edges i) (drop source i) (drop target i)

||| Adds a new vertex to a graph.
public export
addVertex : (g : Graph vertex edge) -> (v : vertex) -> Graph vertex edge
addVertex (MkGraph vertices edges source target) v =
  MkGraph (v :: vertices) edges (rightShift source) (rightShift target)

||| Returns the number of incoming edges to a specific vertex.
public export
indegree : (g : Graph vertex edge) -> Vertex g -> Nat
indegree (MkGraph vertices edges source target) i = length $ preimages i target

||| Returns the number of outgoing edges to a specific vertex.
public export
outdegree : (g : Graph vertex edge) -> Vertex g -> Nat
outdegree (MkGraph vertices edges source target) i = length $ preimages i source

||| Returns the predecessors of a given vertex.
public export
predecessors : (g : Graph vertex edge) -> Vertex g -> List (Vertex g)
predecessors (MkGraph vertices edges source target) i = apply source <$> preimages i target

||| Returns the successors of a given vertex.
public export
successors : (g : Graph vertex edge) -> Vertex g -> List (Vertex g)
successors (MkGraph vertices edges source target) i = apply target <$> preimages i source

||| Returns the incoming edges to a specific vertex.
public export
inEdges : (g : Graph vertex edge) -> Vertex g -> List (Edge g)
inEdges (MkGraph vertices edges source target) i = preimages i target

||| Returns the outgoing edges to a specific vertex.
public export
outEdges : (g : Graph vertex edge) -> Vertex g -> List (Edge g)
outEdges (MkGraph vertices edges source target) i = preimages i source

||| Returns the edges connected to a specific vertex.
public export
connections : (g : Graph vertex edge) -> Vertex g -> List (Edge g)
connections (MkGraph vertices [] [] []) i = []
connections g@(MkGraph vertices (e :: edges) (s :: source) (t :: target)) i =
  case (decEq i s, decEq i t) of
       (Yes Refl, tprf) => Here :: map There (connections (assert_smaller g (MkGraph vertices edges source target)) i)
       (sprf, Yes Refl) => Here :: map There (connections (assert_smaller g (MkGraph vertices edges source target)) i)
       (No _, No _) => map There (connections (assert_smaller g (MkGraph vertices edges source target)) i)

||| Returns all the edges between two vertices.
public export
multiedges : (g : Graph vertex edge) -> Vertex g -> Vertex g -> List (Edge g)
multiedges (MkGraph vertices [] [] []) i j = []
multiedges g@(MkGraph vertices (e :: edges) (s :: source) (t :: target)) i j =
  case (decEq i s, decEq j t) of
       (Yes Refl, Yes Refl) => Here :: map There (multiedges (assert_smaller g (MkGraph vertices edges source target)) i j)
       (_, _) => map There (multiedges (assert_smaller g (MkGraph vertices edges source target)) i j)

public export
removeEdges : (edges : List edge) -> ListMorphism edges vertices -> ListMorphism edges vertices
           -> (i : Pos vertices)
           -> (edges : List edge ** (ListMorphism edges (drop vertices i), ListMorphism edges (drop vertices i)))
removeEdges [] [] [] i = ([] ** ([], []))
removeEdges (e :: edges) (s :: source) (t :: target) i with (decEq s i)
  removeEdges (e :: edges) (s :: source) (t :: target) s | Yes Refl =
    removeEdges edges source target s
  removeEdges (e :: edges) (s :: source) (t :: target) i | No contraSource with (decEq t i)
    removeEdges (e :: edges) (s :: source) (t :: target) t | No _ | Yes Refl =
      removeEdges edges source target t
    removeEdges (e :: edges) (s :: source) (t :: target) i | No contraSource | No contraTarget =
      let (edges' ** (source', target')) = removeEdges edges source target i in
          (e :: edges' ** (dropPos i s contraSource :: source', dropPos i t contraTarget :: target'))

||| Removes a vertex and all its connected edges from a graph.
public export
removeVertex : (g : Graph vertex edge) -> Vertex g -> Graph vertex edge
removeVertex (MkGraph vertices edges source target) i =
  let (edges' ** (source', target')) = removeEdges edges source target i in
      MkGraph (drop vertices i) edges' source' target'

||| Removes a set of vertices from a graph.
public export
removeVertices : (g : Graph vertex edge) -> InjectiveListMorphism vertices' g.vertices -> Graph vertex edge
removeVertices g [] = g
removeVertices g (v :: vs) =
  let (edges' ** (source', target')) = removeEdges g.edges g.source g.target v in
      removeVertices (MkGraph (drop g.vertices v) edges' source' target') vs

||| Substitutes the vertices labels in a graph.
public export
substVertices : (g : Graph vertex edge) -> CList g.vertices vertex' -> Graph vertex' edge
substVertices (MkGraph vertices edges source target) f = MkGraph (forget f) edges (update source f) (update target f)
  where update : ListMorphism xs ys -> (updated : CList ys b) -> ListMorphism xs (forget updated)
        update [] _ = []
        update (f :: fs) (c :: cs) = changePos f (c :: cs) :: update fs (c :: cs)

||| Substitutes the edges labels in a graph.
public export
substEdges : (g : Graph vertex edge) -> CList g.edges edge' -> Graph vertex edge'
substEdges (MkGraph vertices edges source target) f = MkGraph vertices (forget f) (update source f) (update target f)
  where update : ListMorphism xs ys -> (updated : CList xs b) -> ListMorphism (forget updated) ys
        update [] [] = []
        update (f :: fs) (c :: cs) = f :: update fs cs

||| Appends two graph together without connections between them.
public export
append : Graph vertex edge -> Graph vertex edge -> Graph vertex edge
append (MkGraph v1 e1 s1 t1) (MkGraph v2 e2 s2 t2) =
  MkGraph (v1 ++ v2) (e1 ++ e2) (append e1 e2 v1 v2 s1 s2) (append e1 e2 v1 v2 t1 t2)
