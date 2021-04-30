||| Provides function for finding subgraphs, glued graphs and graph merging.
module Data.Graph.Subgraph

import Data.List.CList
import public Data.Graph
import public Data.Graph.Morphism
import public Data.List.Morphism
import public Data.List.InjectiveListMorphism
import Decidable.Equality
import Syntax.PreorderReasoning

%default total

public export
record Subgraph {0 svertex, sedge, vertex, edge : Type} (s : Graph svertex sedge) (g : Graph vertex edge) where
  constructor MkSubgraph
  vertexMorphism : InjectiveMorphism s.vertices g.vertices
  edgeMorphism : ListMorphism s.edges g.edges
  0 isSourceHomomorphic : g.source . edgeMorphism = vertexMorphism.morphism . s.source
  0 isTargetHomomorphic : g.target . edgeMorphism = vertexMorphism.morphism . s.target

public export
toHomomorphism : Subgraph s g -> Homomorphism s g
toHomomorphism (MkSubgraph vertexMorphism edgeMorphism isSourceHomomorphic isTargetHomomorphic) =
  MkHomomorphism vertexMorphism.morphism edgeMorphism isSourceHomomorphic isTargetHomomorphic

public export
identity : (g : Graph vertex edge) -> Subgraph g g
identity g = MkSubgraph (identity g.vertices) (identity g.edges)
                        (rewrite composeRightUnit g.source in
                         rewrite composeLeftUnit g.source in Refl)
                        (rewrite composeRightUnit g.target in
                         rewrite composeLeftUnit g.target in Refl)

public export
compose : {0 s1 : Graph svertex1 sedge1} -> {0 s2 : Graph svertex2 sedge2} -> {0 g : Graph vertex edge}
       -> Subgraph s2 g -> Subgraph s1 s2 -> Subgraph s1 g
compose (MkSubgraph vMor eMor sPrf tPrf) (MkSubgraph vMor' eMor' sPrf' tPrf') =
  MkSubgraph (compose vMor vMor') (compose eMor eMor')
             (Calc $
                |~ g.source . (eMor . eMor')
                ~~ (g.source . eMor) . eMor' ...(composeAssociative g.source eMor eMor')
                ~~ (vMor.morphism . s2.source) . eMor' ...(cong (. eMor') sPrf)
                ~~ vMor.morphism . (s2.source . eMor') ...(sym (composeAssociative vMor.morphism s2.source eMor'))
                ~~ vMor.morphism . (vMor'.morphism . s1.source) ...(cong (vMor.morphism .) sPrf')
                ~~ (vMor.morphism . vMor'.morphism) . s1.source ...(composeAssociative vMor.morphism vMor'.morphism s1.source)
                ~~ (vMor . vMor').morphism . s1.source ...(cong (. s1.source) (composeDistributive vMor vMor')))
             (Calc $
                |~ g.target . (eMor . eMor')
                ~~ (g.target . eMor) . eMor' ...(composeAssociative g.target eMor eMor')
                ~~ (vMor.morphism . s2.target) . eMor' ...(cong (. eMor') tPrf)
                ~~ vMor.morphism . (s2.target . eMor') ...(sym (composeAssociative vMor.morphism s2.target eMor'))
                ~~ vMor.morphism . (vMor'.morphism . s1.target) ...(cong (vMor.morphism .) tPrf')
                ~~ (vMor.morphism . vMor'.morphism) . s1.target ...(composeAssociative vMor.morphism vMor'.morphism s1.target)
                ~~ (vMor . vMor').morphism . s1.target ...(cong (. s1.target) (composeDistributive vMor vMor')))

public export
(.) : {0 s1 : Graph svertex1 sedge1} -> {0 s2 : Graph svertex2 sedge2} -> {0 g : Graph vertex edge}
   -> Subgraph s2 g -> Subgraph s1 s2 -> Subgraph s1 g
(.) = compose

public export
removeEdge : (g : Graph vertex edge) -> Edge g -> (g' : Graph vertex edge ** Subgraph g' g)
removeEdge (MkGraph vertices edges source target) i =
  (MkGraph vertices (drop edges i) (drop source i) (drop target i)
    ** MkSubgraph (identity vertices) (drop (identity edges) i)
                  (rewrite dropLemma source (identity edges) i in
                   rewrite composeRightUnit source in
                   rewrite composeLeftUnit (drop source i) in Refl)
                  (rewrite dropLemma target (identity edges) i in
                   rewrite composeRightUnit target in
                   rewrite composeLeftUnit (drop target i) in Refl))

public export
addEdge : (g : Graph vertex edge) -> (e : edge) -> (s, t : Vertex g) -> (g' : Graph vertex edge ** Subgraph g g')
addEdge (MkGraph vertices edges source target) e s t =
  (MkGraph vertices (e :: edges) (s :: source) (t :: target)
    ** MkSubgraph (identity vertices) (rightShift (identity edges))
                  (rewrite composeLeftUnit source in
                   rewrite shiftLemma {y = e} s source (identity edges) in
                   rewrite composeRightUnit source in Refl)
                  (rewrite composeLeftUnit target in
                   rewrite shiftLemma {y = e} t target (identity edges) in
                   rewrite composeRightUnit target in Refl))

public export
addVertex : (g : Graph vertex edge) -> (v : vertex) -> (g' : Graph vertex edge ** Subgraph g g')
addVertex (MkGraph vertices edges source target) v =
  (MkGraph (v :: vertices) edges (rightShift source) (rightShift target)
    ** MkSubgraph (rightShift (identity vertices)) (identity edges)
                  (rewrite composeRightUnit (rightShift {y = v} source) in
                   rewrite shiftIdentityLemma {y = v} vertices source in Refl)
                  (rewrite composeRightUnit (rightShift {y = v} target) in
                   rewrite shiftIdentityLemma {y = v} vertices target in Refl))

removeEdges : (edges : List edge) -> (source : ListMorphism edges vertices) -> (target : ListMorphism edges vertices)
           -> (i : Pos vertices)
           -> (edges' : List edge ** source' : ListMorphism edges' (drop vertices i)
                                  ** target' : ListMorphism edges' (drop vertices i)
                                  ** mor : ListMorphism edges' edges
                                  ** ( compose source mor = compose (drop (identity vertices) i) source'
                                     , compose target mor = compose (drop (identity vertices) i) target'))
removeEdges [] [] [] i = ([] ** [] ** [] ** [] ** (Refl, Refl))
removeEdges (e :: edges) (s :: source) (t :: target) i with (decEq s i)
  removeEdges (e :: edges) (s :: source) (t :: target) s | Yes Refl =
    let (edges' ** source' ** target' ** mor' ** (sPrf, tPrf)) = Subgraph.removeEdges edges source target s in
        (edges' ** source'
                ** target'
                ** rightShift mor'
                ** ( rewrite shiftLemma {y = e} s source mor' in rewrite sym sPrf in Refl
                   , rewrite shiftLemma {y = e} t target mor' in rewrite sym tPrf in Refl
                   ))
  removeEdges (e :: edges) (s :: source) (t :: target) i | No contraSource with (decEq t i)
    removeEdges (e :: edges) (s :: source) (t :: target) t | No _ | Yes Refl =
      let (edges' ** source' ** target' ** mor' ** (sPrf, tPrf)) = Subgraph.removeEdges edges source target t in
          (edges' ** source'
                  ** target'
                  ** rightShift mor'
                  ** ( rewrite shiftLemma {y = e} s source mor' in rewrite sym sPrf in Refl
                     , rewrite shiftLemma {y = e} t target mor' in rewrite sym tPrf in Refl
                     ))
    removeEdges (e :: edges) (s :: source) (t :: target) i | No contraSource | No contraTarget =
      let (edges' ** source' ** target' ** mor' ** (sPrf, tPrf)) = Subgraph.removeEdges edges source target i in
          (e :: edges' ** dropPos i s contraSource :: source'
                       ** dropPos i t contraTarget :: target'
                       ** Here :: rightShift mor'
                       ** ( rewrite shiftLemma {y = e} s source mor' in rewrite sym sPrf in rewrite sym $ applyIdentityDropLemma vertices i s contraSource in Refl
                          , rewrite shiftLemma {y = e} t target mor' in rewrite sym tPrf in rewrite sym $ applyIdentityDropLemma vertices i t contraTarget in Refl
                          ))

public export
removeVertex : (g : Graph vertex edge) -> Vertex g -> (g' : Graph vertex edge ** Subgraph g' g)
removeVertex (MkGraph vertices edges source target) i =
  let (edges' ** source' ** target' ** mor ** (sPrf, tPrf)) = Subgraph.removeEdges edges source target i in
      (MkGraph (drop vertices i) edges' source' target'
        ** MkSubgraph (drop (identity vertices) i) mor sPrf tPrf)

public export
removeVertices : (g : Graph vertex edge) -> InjectiveListMorphism vertices' g.vertices -> (g' : Graph vertex edge ** Subgraph g' g)
removeVertices g [] = (g ** identity g)
removeVertices (MkGraph vertices edges source target) (v :: vs) =
  let (edges' ** source' ** target' ** mor ** (sPrf, tPrf)) = Subgraph.removeEdges edges source target v
      (g' ** sub) = Subgraph.removeVertices (MkGraph (drop vertices v) edges' source' target') vs in
      (g' ** compose (MkSubgraph (drop (identity vertices) v) mor sPrf tPrf) sub)

public export
removeSubgraph : {0 s : Graph svertex sedge} -> (g : Graph vertex edge) -> Subgraph s g -> (g' : Graph vertex edge ** Subgraph g' g)
removeSubgraph g (MkSubgraph vMor eMor sPrf tPrf) = removeVertices g (getInjective vMor)

public export
append : (g1, g2 : Graph vertex edge) -> (h : Graph vertex edge ** (Subgraph g1 h, Subgraph g2 h))
append (MkGraph v1 e1 s1 t1) (MkGraph v2 e2 s2 t2) =
  (MkGraph (v1 ++ v2) (e1 ++ e2) (append e1 e2 v1 v2 s1 s2) (append e1 e2 v1 v2 t1 t2)
    ** ( MkSubgraph (identityExtRight v1 v2) (identityExtRight e1 e2) ?faslfhaskl ?safklfhas
       , MkSubgraph (identityExtLeft v1 v2) (identityExtLeft e1 e2) ?fdsfasdf ?fsaklhaklsfh)
       )

public export
subgraphEdgeAppendLemma : (sub : Subgraph (MkGraph vs es' ss' ts') (MkGraph vs es ss ts))
                       -> sub.vertexMorphism.morphism = identity vs
                       -> (sub' : Subgraph (MkGraph vs (e :: es') (s :: ss') (t :: ts')) (MkGraph vs (e :: es) (s :: ss) (t :: ts))
                            ** sub'.vertexMorphism.morphism = identity vs)
subgraphEdgeAppendLemma (MkSubgraph vMor eMor srcPrf tgtPrf) prf =
  (MkSubgraph vMor (Here :: rightShift eMor)
              (rewrite sym srcPrf in
               rewrite shiftLemma {y = e} s ss eMor in
               rewrite prf in
               rewrite applyIdentityUnit vs s in Refl)
              (rewrite sym tgtPrf in
               rewrite shiftLemma {y = e} t ts eMor in
               rewrite prf in
               rewrite applyIdentityUnit vs t in Refl)
     ** prf)
