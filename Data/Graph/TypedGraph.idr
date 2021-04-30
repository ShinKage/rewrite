module Data.Graph.TypedGraph

import public Data.Graph
import public Data.Graph.Morphism

%default total

public export
record TypedGraph {0 typeVertex, typeEdge : Type} (0 vertex, edge : Type) (0 type : Graph typeVertex typeEdge) where
  constructor MkTypedGraph
  graph : Graph vertex edge
  typeness : Homomorphism graph type

public export
record Homomorphism {0 vertex, vertex', typeVertex, edge, edge', typeEdge : Type}
                    {0 type : Graph typeVertex typeEdge}
                    (0 g : TypedGraph vertex edge type) (0 g' : TypedGraph vertex' edge' type) where
  constructor MkHomomorphism
  morphism : Homomorphism g.graph g'.graph
  0 vertexTypeComposition : g'.typeness.vertexMorphism . morphism.vertexMorphism = g.typeness.vertexMorphism
  0 edgeTypeComposition : g'.typeness.edgeMorphism . morphism.edgeMorphism = g.typeness.edgeMorphism

public export
compose : {0 type : Graph tvertex tedge} -> {0 g1 : TypedGraph vertex1 edge1 type} -> {0 g2 : TypedGraph vertex2 edge2 type} -> {0 g3 : TypedGraph vertex3 edge3 type}
       -> Homomorphism g2 g3 -> Homomorphism g1 g2 -> Homomorphism g1 g3
compose f g =
  MkHomomorphism (f.morphism . g.morphism)
                 (rewrite composeAssociative g3.typeness.vertexMorphism f.morphism.vertexMorphism g.morphism.vertexMorphism in
                  rewrite f.vertexTypeComposition in
                  rewrite g.vertexTypeComposition in Refl)
                 (rewrite composeAssociative g3.typeness.edgeMorphism f.morphism.edgeMorphism g.morphism.edgeMorphism in
                  rewrite f.edgeTypeComposition in
                  rewrite g.edgeTypeComposition in Refl)

public export
(.) : {0 type : Graph tvertex tedge} -> {0 g1 : TypedGraph vertex1 edge1 type} -> {0 g2 : TypedGraph vertex2 edge2 type} -> {0 g3 : TypedGraph vertex3 edge3 type}
   -> Homomorphism g2 g3 -> Homomorphism g1 g2 -> Homomorphism g1 g3
(.) = compose

public export
identity : (g : TypedGraph vertex edge type) -> Homomorphism g g
identity g =
  MkHomomorphism (identity g.graph)
                 (rewrite composeRightUnit g.typeness.vertexMorphism in Refl)
                 (rewrite composeRightUnit g.typeness.edgeMorphism in Refl)

public export
composeAssociative : {0 type : Graph tvertex tedge} -> {0 g1 : TypedGraph vertex1 edge1 type} -> {0 g2 : TypedGraph vertex2 edge2 type}
                  -> {0 g3 : TypedGraph vertex3 edge3 type} -> {0 g4 : TypedGraph vertex4 edge4 type}
                  -> (f : Homomorphism g3 g4) -> (g : Homomorphism g2 g3) -> (h : Homomorphism g1 g2)
                  -> compose f (compose g h) = compose (compose f g) h
composeAssociative f g h =
  rewrite composeAssociative f.morphism.vertexMorphism g.morphism.vertexMorphism h.morphism.vertexMorphism in
  rewrite composeAssociative f.morphism.edgeMorphism g.morphism.edgeMorphism h.morphism.edgeMorphism in Refl

public export
composeLeftUnit : {0 type : Graph tvertex tedge} -> {0 g : TypedGraph vertex edge type} -> {0 g' : TypedGraph vertex' edge' type}
               -> (f : Homomorphism g g')
               -> compose (identity g') f = f
composeLeftUnit f =
  rewrite composeLeftUnit f.morphism.vertexMorphism in
  rewrite composeLeftUnit f.morphism.edgeMorphism in believe_me {a = f = f} Refl
    -- TODO: Find a way to match on the proofs inside f

public export
composeRightUnit : {0 type : Graph tvertex tedge} -> {0 g : TypedGraph vertex edge type} -> {0 g' : TypedGraph vertex' edge' type}
                -> (f : Homomorphism g g')
                -> compose f (identity g) = f
composeRightUnit f =
  rewrite composeRightUnit f.morphism.vertexMorphism in
  rewrite composeRightUnit f.morphism.edgeMorphism in believe_me {a = f = f} Refl
    -- TODO: Find a way to match on the proofs inside f
