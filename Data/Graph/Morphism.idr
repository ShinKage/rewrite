||| Definitions of morphism and structure-preserving morphism between graphs.
module Data.Graph.Morphism

import public Data.Graph
import Data.Vect.Extra

%default total
%access export

||| Represents a morphism between graphs as a mapping of vertices and edges.
public export
data Morphism : (g : Graph n m vs es) -> (g' : Graph n' m' vs' es') -> Type where
  ||| Morphism constructor
  ||| @vmap Morphism between vertices
  ||| @emap Morphism between edges
  Morph : {g : Graph n m vs es} -> {g' : Graph n' m' vs' es'} -> (vmap : Vect n (Fin n'))
       -> (emap : Vect m (Fin m')) -> Morphism g g'

namespace Source
  ||| Satisfied if a given morphism between graphs preserves the sources of edges,
  ||| formally if e = (s, t) in g then f(e) = (f(s), t') in g'.
  ||| @g   The original graph
  ||| @g'  The mapped graph
  ||| @mor The morphism from `g` to `g'`
  data PreserveSource : (g : Graph n m vs es) -> (g' : Graph n' m' vs' es')
                     -> (mor : Morphism g g') -> Type where
    Empty : PreserveSource Empty g' mor
    Edge  : source e g' = index s vmap -> PreserveSource g g' (Morph vmap emap)
         -> PreserveSource (Edge s t g) g' (Morph vmap (e :: emap))

  ||| If the source is not preserved for one edge than the predicate is false.
  notEqualSourceNotPreserve : Not (source e g' = index s vmap)
                           -> Not (PreserveSource (Edge s t g) g' (Morph vmap (e :: emap)))
  notEqualSourceNotPreserve contra (Edge prf _) = contra prf

  ||| If the predicate is not valid for a given graph than is not valid for a
  ||| graph with additional edges.
  notLaterSourceNotPreserve : Not (PreserveSource g g' (Morph vmap emap))
                           -> Not (PreserveSource (Edge s t g) g' (Morph vmap (e :: emap)))
  notLaterSourceNotPreserve contra (Edge _ later) = contra later

  ||| A decision procedure for the `PreserveSource` predicate.
  ||| @g   The original graph
  ||| @g'  The mapped graph
  ||| @mor The morphism from `g` to `g'`
  preserveSource : (g : Graph n m vs es) -> (g' : Graph n' m' vs' es') -> (mor : Morphism g g')
                -> Dec (PreserveSource g g' mor)
  preserveSource Empty g' _ = Yes Empty
  preserveSource (Edge s _ g) g' (Morph vmap (e :: emap)) with (decEq (source e g') (index s vmap))
    preserveSource (Edge s _ g) g' (Morph vmap (e :: emap))
      | (Yes decprf) with (preserveSource g g' (Morph vmap emap))
        preserveSource (Edge s _ g) g' (Morph vmap (e :: emap))
          | (Yes decprf) | (Yes prf) = Yes (Edge decprf prf)
        preserveSource (Edge s _ g) g' (Morph vmap (e :: emap))
          | (Yes decprf) | (No contra) = No (notLaterSourceNotPreserve contra)
    preserveSource (Edge s _ g) g' (Morph vmap (e :: emap))
      | (No contra) = No (notEqualSourceNotPreserve contra)

namespace Target
  ||| Satisfied if a given morphism between graphs preserves the targets of edges,
  ||| formally if e = (s, t) in g then f(e) = (s', f(t)) in g'.
  ||| @g   The original graph
  ||| @g'  The mapped graph
  ||| @mor The morphism from `g` to `g'`
  data PreserveTarget : (g : Graph n m vs es) -> (g' : Graph n' m' vs' es')
                     -> (mor : Morphism g g') -> Type where
    Empty : PreserveTarget Empty g' mor
    Edge  : target e g' = index t vmap -> PreserveTarget g g' (Morph vmap emap)
         -> PreserveTarget (Edge s t g) g' (Morph vmap (e :: emap))

  ||| If the source is not preserved for one edge than the predicate is false.
  notEqualTargetNotPreserve : Not (target e g' = index t vmap)
                           -> Not (PreserveTarget (Edge s t g) g' (Morph vmap (e :: emap)))
  notEqualTargetNotPreserve contra (Edge prf _) = contra prf

  ||| If the predicate is not valid for a given graph than is not valid for a
  ||| graph with additional edges.
  notLaterTargetNotPreserve : Not (PreserveTarget g g' (Morph vmap emap))
                           -> Not (PreserveTarget (Edge s t g) g' (Morph vmap (e :: emap)))
  notLaterTargetNotPreserve contra (Edge _ later) = contra later

  ||| A decision procedure for the `PreserveTarget` predicate.
  ||| @g   The original graph
  ||| @g'  The mapped graph
  ||| @mor The morphism from `g` to `g'`
  preserveTarget : (g : Graph n m vs es) -> (g' : Graph n' m' vs' es') -> (mor : Morphism g g')
                -> Dec (PreserveTarget g g' mor)
  preserveTarget Empty g' _ = Yes Empty
  preserveTarget (Edge _ t g) g' (Morph vmap (e :: emap)) with (decEq (target e g') (index t vmap))
    preserveTarget (Edge _ t g) g' (Morph vmap (e :: emap))
      | (Yes decprf) with (preserveTarget g g' (Morph vmap emap))
        preserveTarget (Edge _ t g) g' (Morph vmap (e :: emap))
          | (Yes decprf) | (Yes prf) = Yes (Edge decprf prf)
        preserveTarget (Edge _ t g) g' (Morph vmap (e :: emap))
          | (Yes decprf) | (No contra) = No (notLaterTargetNotPreserve contra)
    preserveTarget (Edge _ t g) g' (Morph vmap (e :: emap))
      | (No contra) = No (notEqualTargetNotPreserve contra)

||| Satisfied if a given morphism between to graph is a Homomorphism, in other
||| words the morphism must preserve both source and targets of edges.
|||
||| @g   The original graph
||| @g'  The mapped graph
||| @mor The morphism from `g` to `g'`
data Homomorphism : (g : Graph n m vs es) -> (g' : Graph n' m' vs' es') -> (mor : Morphism g g')
                 -> Type where
  Homo : PreserveSource g g' mor -> PreserveTarget g g' mor -> Homomorphism g g' mor

||| If the morphism does not preserve sources than it is not an homomorphism.
notPreserveSourceNotHomomorphism : Not (PreserveSource g g' mor) -> Not (Homomorphism g g' mor)
notPreserveSourceNotHomomorphism contra (Homo s _) = contra s

||| If the morphism does not preserve targets than it is not an homomorphism.
notPreserveTargetNotHomomorphism : Not (PreserveTarget g g' mor) -> Not (Homomorphism g g' mor)
notPreserveTargetNotHomomorphism contra (Homo _ t) = contra t

||| A decision procedure for `Homomorphism` predicate.
|||
||| @g The original graph
||| @g' The mapped graph
||| @mor The morphism from `g` to `g'`
isHomomorphism : (g : Graph n m vs es) -> (g' : Graph n' m' vs' es') -> (mor : Morphism g g')
              -> Dec (Homomorphism g g' mor)
isHomomorphism g g' mor with (preserveSource g g' mor)
  isHomomorphism g g' mor | (Yes s) with (preserveTarget g g' mor)
    isHomomorphism g g' mor | (Yes s) | (Yes t) = Yes (Homo s t)
    isHomomorphism g g' mor | (Yes s) | (No contra) = No (notPreserveTargetNotHomomorphism contra)
  isHomomorphism g g' mor | (No contra) = No (notPreserveSourceNotHomomorphism contra)

||| Returns the identity morphism for a given graph.
||| @g The graph
idMorphism : (g : Graph n m vs es) -> Morphism g g
idMorphism g = Morph range range

||| Satisfied if a given pair of morphisms make up an isomorphism between the two graphs.
||| @g      The first graph
||| @g'     The second graph
||| @mor    The morphism from the first to the second graph
||| @invMor The morphism from the second to the first graph
data Isomorphism : (g : Graph n m vs es)
                -> (g' : Graph n m vs' es')
                -> (mor : Morphism g g')
                -> (invMor : Morphism g' g)
                -> Type where
  Iso : invertFun vmap = invvmap -> invertFun emap = invemap
     -> Isomorphism g g' (Morph vmap emap) (Morph invvmap invemap)

||| If the function between the source of the vertices is not invertible that it is not
||| an isomorphism.
noSourceInverse : Not (invertFun vmap = invvmap)
               -> Not (Isomorphism g g' (Morph vmap emap) (Morph invvmap invemap))
noSourceInverse contra (Iso s _) = contra s

||| If the function between the target of the vertices is not invertible that it is not
||| an isomorphism.
noTargetInverse : Not (invertFun emap = invemap)
               -> Not (Isomorphism g g' (Morph vmap emap) (Morph invvmap invemap))
noTargetInverse contra (Iso _ t) = contra t

||| Decision procedure for isomorphisms.
||| @g      The first graph
||| @g'     The second graph
||| @mor    The morphism from the first to the second graph
||| @invMor The morphism from the second to the first graph
isIsomorphism : (g : Graph n m vs es) -> (g' : Graph n m vs' es') -> (mor : Morphism g g')
             -> (invMor : Morphism g' g) -> Dec (Isomorphism g g' mor invMor)
isIsomorphism g g' (Morph vmap emap) (Morph invvmap invemap) with (decEq (invertFun vmap) invvmap)
  isIsomorphism g g' (Morph vmap emap) (Morph invvmap invemap) | Yes vprf with (decEq (invertFun emap) invemap)
    isIsomorphism g g' (Morph vmap emap) (Morph invvmap invemap) | Yes vprf | Yes eprf
      = Yes (Iso vprf eprf)
    isIsomorphism g g' (Morph vmap emap) (Morph invvmap invemap) | Yes vprf | No contra
      = No (noTargetInverse contra)
  isIsomorphism g g' (Morph vmap emap) (Morph invvmap invemap) | No contra
      = No (noSourceInverse contra)
