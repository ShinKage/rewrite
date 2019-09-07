||| Various types of double pushouts in the category of directed multi-graphs.
module Data.Graph.Pushout

import public Data.Graph
import public Data.Graph.Morphism

%default total
%access public export

||| Represents a double pushout in the category of directed multi-graphs.
||| @l Rule precondition
||| @g Graph to match
||| @k Glue between precondition and postcondition
||| @d Glue between original graph and rewritten graph
||| @r Rule postcondition
||| @h Rewritten graph
data DoublePushout : (l : Graph nl ml vsl esl) -> (g : Graph ng mg vsg esg)
                  -> (k : Graph nk mk vsk esk) -> (d : Graph nd md vsd esd)
                  -> (r : Graph nr mr vsr esr) -> (h : Graph nh mh vsh esh) -> Type where
  DP : Homomorphism l g morlg -> Homomorphism k d morkd -> Homomorphism r h morrh
    -> Homomorphism k l morkl -> Homomorphism k r morkr -> Homomorphism d g mordg
    -> Homomorphism d h mordh -> DoublePushout l g k d r h

||| Represents a double pushout in the category of directed multi-graphs, with a
||| restriction on the starting graph.
||| @l Rule precondition
||| @g Graph to match
||| @k Glue between precondition and postcondition
||| @d Glue between original graph and rewritten graph
||| @r Rule postcondition
||| @h Rewritten graph
||| @n The negative property
data DoublePushoutNeg : (l : Graph nl ml vsl esl) -> (g : Graph ng mg vsg esg)
                     -> (k : Graph nk mk vsk esk) -> (d : Graph nd md vsd esd)
                     -> (r : Graph nr mr vsr esr) -> (h : Graph nh mh vsh esh)
                     -> (n : Graph nn mn vsn esn) -> Type where
  DPN : Homomorphism l n morln -> DoublePushout l g k d r h -> DoublePushoutNeg l g k d r h n

||| Represents a double pushout in the category of directed multi-graphs,
||| with a preserved interface of the starting graph.
||| @l Rule precondition
||| @g Graph to match
||| @k Glue between precondition and postcondition
||| @d Glue between original graph and rewritten graph
||| @r Rule postcondition
||| @h Rewritten graph
||| @j Interface of the original graph
data DoublePushoutInterface : (l : Graph nl ml vsl esl) -> (g : Graph ng mg vsg esg)
                           -> (k : Graph nk mk vsk esk) -> (d : Graph nd md vsd esd)
                           -> (r : Graph nr mr vsr esr) -> (h : Graph nh mh vsh esh)
                           -> (j : Graph nj mj vsj esj) -> Type where
  DPI : Homomorphism j g morjg -> Homomorphism j d morjd -> Homomorphism j h morjh
     -> DoublePushout l g k d r h -> DoublePushoutInterface l g k d r h j

||| Represents a double pushout in the category of directed multi-graphs,
||| all graphs involved are typed.
||| @t The type
||| @l Rule precondition
||| @g Graph to match
||| @k Glue between precondition and postcondition
||| @d Glue between original graph and rewritten graph
||| @r Rule postcondition
||| @h Rewritten graph
data DoublePushoutTyped : (t : Graph nt mt vst est) -> (l : Graph nl ml vsl esl)
                       -> (g : Graph ng mg vsg esg) -> (k : Graph nk mk vsk esk)
                       -> (d : Graph nd md vsd esd) -> (r : Graph nr mr vsr esr)
                       -> (h : Graph nh mh vsh esh) -> Type where
  DPT : Homomorphism l t morlt -> Homomorphism k t morkt -> Homomorphism r t morrt
     -> Homomorphism g t morgt -> Homomorphism d t mordt -> Homomorphism h t morht
     -> DoublePushout l g k d r h -> DoublePushoutTyped t l g k d r h

||| Represents a rewrite rule between simple directed graphs.
||| A rule is described by a graph to match (l), a graph to substitute with (r)
||| and the glue (k) between l and r. Also a morphism from k to l and from
||| k to r must be provided, besides the mapping of vertices of with respect to
||| vertices of l.
data Rewrite : Type -> Type -> Type where
  ||| Rule constructor.
  ||| @l Rule precondition
  ||| @r Rule postcondition
  ||| @k Glue between precondition and postcondition
  ||| @ktol Mapping from glue to precondition
  ||| @ktor Mapping from glue to postcondition
  ||| @mapping Mapping from postcondition to precondition
  MkRule : (l : Graph ln lm {vertex} {edge} lvs les) -> (r : Graph rn rm {vertex} {edge} rvs res)
        -> (k : Graph kn km {vertex} {edge} kvs kes) -> (ktol : Vect kn (Fin ln))
        -> (ktor : Vect kn (Fin rn)) -> (mapping : Vect rn (Maybe (Fin ln))) -> Rewrite vertex edge

||| Represents a rewrite rule between simple directed graphs.
||| A rule is described by a graph to match (l), a graph to substitute with (r)
||| and the glue (k) between l and r. Also a morphism from k to l and from
||| k to r must be provided, besides the mapping of vertices of with respect to
||| vertices of l. A given property must not be present in the starting graph.
data RewriteNeg : Type -> Type -> Type where
  ||| Negative rule constructor.
  ||| @l Rule precondition
  ||| @r Rule postcondition
  ||| @k Glue between precondition and postcondition
  ||| @n Negative property
  ||| @ktol Mapping from glue to precondition
  ||| @ktor Mapping from glue to postcondition
  ||| @lton Mapping from precondition to negative property
  ||| @mapping Mapping from postcondition to precondition
  MkRuleNeg : (l : Graph ln lm {vertex} {edge} lvs les)
           -> (r : Graph rn rm {vertex} {edge} rvs res)
           -> (k : Graph kn km {vertex} {edge} kvs kes)
           -> (n : Graph nn nm {vertex} {edge} nvs nes)
           -> (ktol : Vect kn (Fin ln)) -> (ktor : Vect kn (Fin rn)) -> (lton : Vect ln (Fin nn))
           -> (mapping : Vect rn (Maybe (Fin ln))) -> RewriteNeg vertex edge

||| Represents a rewrite rule between simple directed graphs.
||| A rule is described by a graph to match (l), a graph to substitute with (r)
||| and the glue (k) between l and r. Also a morphism from k to l and from
||| k to r must be provided, besides the mapping of vertices of with respect to
||| vertices of l. All graphs must be typed.
data RewriteTyped : Type -> Type -> Type where
  ||| Typed rule constructor.
  ||| @t The type
  ||| @l Rule precondition
  ||| @r Rule postcondition
  ||| @k Glue between precondition and postcondition
  ||| @ktol Mapping from glue to precondition
  ||| @ktor Mapping from glue to postcondition
  ||| @ltot Mapping from precondition to type
  ||| @rtot Mapping from postcondition to type
  ||| @ktot Mapping from glue to type
  ||| @mapping Mapping from postcondition to precondition
  MkRuleTyped : (t : Graph tn tm {vertex} {edge} tvs tes)
             -> (l : Graph ln lm {vertex} {edge} lvs les)
             -> (r : Graph rn rm {vertex} {edge} rvs res)
             -> (k : Graph kn km {vertex} {edge} kvs kes)
             -> (ktol : Vect kn (Fin ln)) -> (ktor : Vect kn (Fin rn)) -> (ltot : Vect ln (Fin tn))
             -> (rtot : Vect rn (Fin tn)) -> (ktot : Vect kn (Fin tn))
             -> (mapping : Vect rn (Maybe (Fin ln))) -> RewriteTyped vertex edge
