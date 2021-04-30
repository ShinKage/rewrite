||| Definitions of morphism and structure-preserving morphism between graphs.
module Data.Graph.Morphism

import public Data.Graph
import Data.List
import Data.List.Pos
import public Data.List.Morphism
import Decidable.Equality
import public Syntax.PreorderReasoning

%default total

eqEq : (eq1 : a = b) -> (eq2 : a = b) -> eq1 = eq2
eqEq Refl Refl = Refl

||| Type of functions between vertices and edges of graphs.
public export
record Morphism {0 vertex, vertex', edge, edge' : Type} (0 g : Graph vertex edge) (0 g' : Graph vertex' edge') where
  constructor MkMorphism
  vertexMorphism : ListMorphism g.vertices g'.vertices
  edgeMorphism   : ListMorphism g.edges g'.edges

namespace Homomorphism
  public export
  record Homomorphism {0 vertex, vertex', edge, edge' : Type} (0 g : Graph vertex edge) (0 g' : Graph vertex' edge') where
    constructor MkHomomorphism
    vertexMorphism : ListMorphism g.vertices g'.vertices
    edgeMorphism : ListMorphism g.edges g'.edges
    0 isSourceHomomorphic : g'.source . edgeMorphism = vertexMorphism . g.source
    0 isTargetHomomorphic : g'.target . edgeMorphism = vertexMorphism . g.target

  ||| Decision procedure for `Homomorphism`.
  public export
  isHomomorphism : {g : Graph vertex edge} -> {g' : Graph vertex' edge'} -> ListMorphism g.vertices g'.vertices -> ListMorphism g.edges g'.edges -> Maybe (Homomorphism g g')
  isHomomorphism vMor eMor =
    case (decEq (g'.source . eMor) (vMor . g.source), decEq (g'.target . eMor) (vMor . g.target)) of
         (Yes srcPrf, Yes tgtPrf) => Just (MkHomomorphism vMor eMor srcPrf tgtPrf)
         (No contra, _) => Nothing
         (_, No contra) => Nothing

  public export
  DecEq (Homomorphism g g') where
    decEq (MkHomomorphism v e s t) (MkHomomorphism v' e' s' t') =
      case (decEq v v', decEq e e') of
           (Yes Refl, Yes Refl) => rewrite eqEq s s' in rewrite eqEq t t' in Yes Refl
           (No contra, _) => No (\case Refl => contra Refl)
           (_, No contra) => No (\case Refl => contra Refl)

  ||| Composes two morphisms between graphs.
  public export
  compose : {0 g1 : Graph vertex1 edge1} -> {0 g2 : Graph vertex2 edge2} -> {0 g3 : Graph vertex3 edge3}
         -> Homomorphism g2 g3 -> Homomorphism g1 g2 -> Homomorphism g1 g3
  compose f g =
    MkHomomorphism (f.vertexMorphism . g.vertexMorphism) (f.edgeMorphism . g.edgeMorphism)
                   (Calc $
                      |~ g3.source . (f.edgeMorphism . g.edgeMorphism)
                      ~~ (g3.source . f.edgeMorphism) . g.edgeMorphism ...(composeAssociative g3.source f.edgeMorphism g.edgeMorphism)
                      ~~ (f.vertexMorphism . g2.source) . g.edgeMorphism ...(cong (. g.edgeMorphism) f.isSourceHomomorphic)
                      ~~ f.vertexMorphism . (g2.source . g.edgeMorphism) ...(sym $ composeAssociative f.vertexMorphism g2.source g.edgeMorphism)
                      ~~ f.vertexMorphism . (g.vertexMorphism . g1.source) ...(cong (f.vertexMorphism .) g.isSourceHomomorphic)
                      ~~ (f.vertexMorphism . g.vertexMorphism) . g1.source ...(composeAssociative f.vertexMorphism g.vertexMorphism g1.source))
                   (Calc $
                      |~ g3.target . (f.edgeMorphism . g.edgeMorphism)
                      ~~ (g3.target . f.edgeMorphism) . g.edgeMorphism ...(composeAssociative g3.target f.edgeMorphism g.edgeMorphism)
                      ~~ (f.vertexMorphism . g2.target) . g.edgeMorphism ...(cong (. g.edgeMorphism) f.isTargetHomomorphic)
                      ~~ f.vertexMorphism . (g2.target . g.edgeMorphism) ...(sym $ composeAssociative f.vertexMorphism g2.target g.edgeMorphism)
                      ~~ f.vertexMorphism . (g.vertexMorphism . g1.target) ...(cong (f.vertexMorphism .) g.isTargetHomomorphic)
                      ~~ (f.vertexMorphism . g.vertexMorphism) . g1.target ...(composeAssociative f.vertexMorphism g.vertexMorphism g1.target))

  ||| Composes two morphisms between graphs.
  public export
  (.) : {0 g1 : Graph vertex1 edge1} -> {0 g2 : Graph vertex2 edge2} -> {0 g3 : Graph vertex3 edge3}
     -> Homomorphism g2 g3 -> Homomorphism g1 g2 -> Homomorphism g1 g3
  (.) = compose

  ||| Returns the identity morphism for a given graph.
  public export
  identity : (g : Graph vertex edge) -> Homomorphism g g
  identity g =
    MkHomomorphism (identity g.vertices) (identity g.edges)
                   (rewrite composeRightUnit g.source in
                    rewrite composeLeftUnit g.source in Refl)
                   (rewrite composeRightUnit g.target in
                    rewrite composeLeftUnit g.target in Refl)

  ||| Proof that that composition is associative for graph morphisms.
  public export
  composeAssociative : {0 g1 : Graph vertex1 edge1} -> {0 g2 : Graph vertex2 edge2} -> {0 g3 : Graph vertex3 edge3} -> {0 g4 : Graph vertex4 edge4}
                    -> (f : Homomorphism g3 g4) -> (g : Homomorphism g2 g3) -> (h : Homomorphism g1 g2)
                    -> compose f (compose g h) = compose (compose f g) h
  composeAssociative f g h =
    rewrite composeAssociative f.vertexMorphism g.vertexMorphism h.vertexMorphism in
    rewrite composeAssociative f.edgeMorphism g.edgeMorphism h.edgeMorphism in Refl

  ||| Proof that identity is the left unit of composition for graph morphisms.
  public export
  composeLeftUnit : {0 g : Graph vertex edge} -> {0 g' : Graph vertex' edge'}
                 -> (f : Homomorphism g g')
                 -> compose (identity g') f = f
  composeLeftUnit f =
    rewrite composeLeftUnit f.vertexMorphism in
    rewrite composeLeftUnit f.edgeMorphism in believe_me {a = f = f} Refl
      -- TODO: Find a way to match on the proofs inside f

  ||| Proof that identity is the right unit of composition for graph morphisms.
  public export
  composeRightUnit : {0 g : Graph vertex edge} -> {0 g' : Graph vertex' edge'}
                  -> (f : Homomorphism g g')
                  -> compose f (identity g) = f
  composeRightUnit f =
    rewrite composeRightUnit f.vertexMorphism in
    rewrite composeRightUnit f.edgeMorphism in believe_me {a = f = f} Refl
      -- TODO: Find a way to match on the proofs inside f

namespace Isomorphism
  ||| Type of isomorphisms between simple directed (hyper-)graphs.
  public export
  record Isomorphism {0 vertex, vertex', edge, edge' : Type} (0 g : Graph vertex edge) (0 g' : Graph vertex' edge') where
    constructor MkIsomorphism
    from : Homomorphism g g'
    to : Homomorphism g' g
    0 fromToIdentity : compose from to = identity g'
    0 toFromIdentity : compose to from = identity g

  ||| Decision procedure for `Isomorphism`.
  public export
  isIsomorphism : (g : Graph vertex edge) -> (g' : Graph vertex edge) -> Homomorphism g g' -> Homomorphism g' g -> Maybe (Isomorphism g g')
  isIsomorphism g g' from to =
    case (decEq (compose from to) (identity g'), decEq (compose to from) (identity g)) of
         (Yes fromToPrf, Yes toFromPrf) => Just (MkIsomorphism from to fromToPrf toFromPrf)
         (No contra, _) => Nothing
         (_, No contra) => Nothing

  public export
  DecEq (Isomorphism g g') where
    decEq (MkIsomorphism from to fromTo toFrom) (MkIsomorphism from' to' fromTo' toFrom') =
      case (decEq from from', decEq to to') of
           (Yes Refl, Yes Refl) => rewrite eqEq fromTo fromTo' in rewrite eqEq toFrom toFrom' in Yes Refl
           (No contra, _) => No (\case Refl => contra Refl)
           (_, No contra) => No (\case Refl => contra Refl)

  ||| Composes two isomorphisms between graphs.
  public export
  compose : Isomorphism g2 g3 -> Isomorphism g1 g2 -> Isomorphism g1 g3
  compose f g =
    MkIsomorphism (compose f.from g.from)
                  (compose g.to f.to)
                  (rewrite sym $ composeAssociative f.from g.from (compose g.to f.to) in
                   rewrite cong (\z => compose f.from z) $ composeAssociative g.from g.to f.to in
                   rewrite cong (\z => compose f.from (compose z f.to)) g.fromToIdentity in
                   rewrite cong (\z => compose f.from z) $ composeLeftUnit f.to in
                   rewrite f.fromToIdentity in Refl)
                  (rewrite sym $ composeAssociative g.to f.to (compose f.from g.from) in
                   rewrite cong (\z => compose g.to z) $ composeAssociative f.to f.from g.from in
                   rewrite cong (\z => compose g.to (compose z g.from)) f.toFromIdentity in
                   rewrite cong (\z => compose g.to z) $ composeLeftUnit g.from in
                   rewrite g.toFromIdentity in Refl)

  ||| Composes two isomorphisms between graphs.
  public export
  (.) : {0 g1 : Graph vertex1 edge1} -> {0 g2 : Graph vertex2 edge2} -> {0 g3 : Graph vertex3 edge3}
     -> Isomorphism g2 g3 -> Isomorphism g1 g2 -> Isomorphism g1 g3
  (.) = compose

  ||| Returns the identity isomorphism for a specific graph.
  public export
  identity : (g : Graph vertex edge) -> Isomorphism g g
  identity g =
    MkIsomorphism (identity g) (identity g)
                  (rewrite composeLeftUnit (identity g.vertices) in
                   rewrite composeLeftUnit (identity g.edges) in
                   rewrite composeRightUnit g.source in
                   rewrite composeRightUnit g.target in
                   Refl)
                  (rewrite composeLeftUnit (identity g.vertices) in
                   rewrite composeLeftUnit (identity g.edges) in
                   rewrite composeRightUnit g.source in
                   rewrite composeRightUnit g.target in
                   Refl)

  ||| Proof that composition is associative for isomorphisms between graphs.
  public export
  composeAssociative : {0 g1 : Graph vertex1 edge1} -> {0 g2 : Graph vertex2 edge2} -> {0 g3 : Graph vertex3 edge3} -> {0 g4 : Graph vertex4 edge4}
                    -> (f : Isomorphism g3 g4) -> (g : Isomorphism g2 g3) -> (h : Isomorphism g1 g2)
                    -> compose f (compose g h) = compose (compose f g) h
  composeAssociative f g h =
    rewrite composeAssociative f.from.vertexMorphism g.from.vertexMorphism h.from.vertexMorphism in
    rewrite composeAssociative f.from.edgeMorphism g.from.edgeMorphism h.from.edgeMorphism in
    rewrite composeAssociative h.to.vertexMorphism g.to.vertexMorphism f.to.vertexMorphism in
    rewrite composeAssociative h.to.edgeMorphism g.to.edgeMorphism f.to.edgeMorphism in Refl

  ||| Proof that identity is the left unit of composition for graph isomorphisms.
  public export
  composeLeftUnit : {0 g : Graph vertex edge} -> {0 g' : Graph vertex' edge'}
                 -> (f : Isomorphism g g')
                 -> compose (identity g') f = f
  composeLeftUnit f =
    rewrite composeLeftUnit f.from.vertexMorphism in
    rewrite composeLeftUnit f.from.edgeMorphism in
    rewrite composeRightUnit f.to.vertexMorphism in
    rewrite composeRightUnit f.to.edgeMorphism in believe_me {a = f = f} Refl
      -- TODO: Find a way to match on the proofs inside f

  ||| Proof that identity is the right unit of composition for graph isomorphisms.
  public export
  composeRightUnit : {0 g : Graph vertex edge} -> {0 g' : Graph vertex' edge'}
                  -> (f : Isomorphism g g')
                  -> compose f (identity g) = f
  composeRightUnit f =
    rewrite composeRightUnit f.from.vertexMorphism in
    rewrite composeRightUnit f.from.edgeMorphism in
    rewrite composeLeftUnit f.to.vertexMorphism in
    rewrite composeLeftUnit f.to.edgeMorphism in believe_me {a = f = f} Refl
      -- TODO: Find a way to match on the proofs inside f
