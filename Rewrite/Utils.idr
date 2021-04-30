module Rewrite.Utils

import Data.String
import Data.Graph
import Data.Graph.Morphism
import Data.Graph.Subgraph
import Data.List
import Data.List.CList
import Data.List.InjectiveListMorphism
import Decidable.Equality

%default total

public export
data RewriteError = NotInjective String String
                  | NotHomomorphism String String
                  | IndexOutOfBounds Nat Nat
                  | FailedConversion String String
                  | CommutativeError String String
                  | NotAllowed String String
                  | NonEmptyNegative

export
rewriteErrorMessage : RewriteError -> String
rewriteErrorMessage (NotInjective from to)     = "The morphism \{from} -> \{to} is not injective"
rewriteErrorMessage (NotHomomorphism from to)  = "The morphism \{from} -> \{to} it not homomorphic"
rewriteErrorMessage (IndexOutOfBounds i m)     = "The index \{show i} is out of bounds (max \{show m})"
rewriteErrorMessage (FailedConversion from to) = "Failure trying to build the morphism \{from} -> \{to}"
rewriteErrorMessage (CommutativeError from to) = "Path \{from} and \{to} are not commutative"
rewriteErrorMessage (NotAllowed from to)       = "The morphism \{from} -> \{to} is not allowed"
rewriteErrorMessage NonEmptyNegative           = "There must not be any valid match"

Subset : List a -> Type
Subset xs = CList xs Bool

subLength : Subset xs -> Nat
subLength [] = 0
subLength (True :: bs) = S (subLength bs)
subLength (False :: bs) = subLength bs

flipSubset : Subset xs -> Subset xs
flipSubset [] = []
flipSubset (True :: bs) = False :: flipSubset bs
flipSubset (False :: bs) = True :: flipSubset bs

extractSubset : (xs : List a) -> Subset xs -> (ys : List a ** ListMorphism ys xs)
extractSubset [] [] = ([] ** [])
extractSubset (x :: xs) (True :: bs) = let (ys ** prf) = extractSubset xs bs in (ys ** rightShift prf)
extractSubset (x :: xs) (False :: bs) = let (ys ** prf) = extractSubset xs bs in (x :: ys ** Here :: rightShift prf)

-- extractSubsetMorphism : (xs : List a) -> (sub : CList xs Bool) -> ListMorphism (extractSubset xs sub) xs
-- extractSubsetMorphism [] [] = []
-- extractSubsetMorphism (x :: xs) (True :: bs) = rightShift (extractSubsetMorphism xs bs)
-- extractSubsetMorphism (x :: xs) (False :: bs) = Here :: rightShift (extractSubsetMorphism xs bs)

subsetFromMorphism : (ys : List b) -> ListMorphism xs ys -> Subset ys
subsetFromMorphism ys [] = initialize False
subsetFromMorphism ys (f :: fs) = replaceAt (subsetFromMorphism ys fs) f True

-- extractSubsetFromMorphism : ListMorphism xs ys -> (bs : CList xs Bool) -> ListMorphism (extractSubset xs bs) ys
-- extractSubsetFromMorphism ys [] = []
-- extractSubsetFromMorphism (y :: ys) (True :: bs) = extractSubsetFromMorphism ys bs
-- extractSubsetFromMorphism (y :: ys) (False :: bs) = y :: extractSubsetFromMorphism ys bs

-- removeEdges : (g : Graph vertex edge) -> CList g.edges Bool -> Graph vertex edge
-- removeEdges (MkGraph vertices edges source target) bs =
--   MkGraph vertices (extractSubset edges bs) (extractSubsetFromMorphism edges source bs) (extractSubsetFromMorphism edges target bs)

removeVertices : (g : Graph vertex edge) -> CList g.vertices Bool -> (g' : Graph vertex edge ** Subgraph g' g)
removeVertices g bs = removeVertices g (convert bs)
   where
     convert : (bs : CList xs Bool) -> InjectiveListMorphism (replicate (subLength bs) Z) xs
     convert [] = []
     convert (True :: bs) = Here :: convert bs
     convert (False :: bs) = rawRightShift (convert bs)

missingImages : {0 xs : List a} -> {ys : List b} -> ListMorphism xs ys -> Subset ys
missingImages [] = initialize True
missingImages (x :: xs) = replaceAt (missingImages xs) x False

reverse : {xs : List a} -> {ys : List b} -> ListMorphism xs ys -> CList ys (Maybe (Pos xs))
reverse f = foldr (\i, acc => replaceAt acc (apply f i) (Just i)) (initialize Nothing) (range xs)

transform : {0 xs : List a} -> {0 ys : List b} -> CList xs (Maybe (Pos ys)) -> Maybe (ListMorphism xs ys)
transform [] = pure []
transform (x :: xs) = [| x :: transform xs |]

export
glued : (k, l, g : Graph vertex edge) -> (ktol : Homomorphism k l) -> (ltog : Homomorphism l g)
     -> (d : Graph vertex edge ** Homomorphism d g)
glued k l g ktol ltog =
    let missingEdges = update (missingImages ktol.edgeMorphism) ltog.edgeMorphism
        missingVertices = update (missingImages ktol.vertexMorphism) ltog.vertexMorphism
        (es0 ** ss0 ** ts0 ** sub0 ** _) = removeEdges g missingEdges
        (d ** sub1) = removeVertices (MkGraph g.vertices es0 ss0 ts0) missingVertices
        dtogSub = compose sub0 sub1
     in (d ** toHomomorphism dtogSub)
  where
    update : {0 xs : List a} -> {ys : List b} -> Subset xs -> ListMorphism xs ys -> Subset ys
    update [] [] = initialize False
    update (b :: bs) (f :: fs) = replaceAt (update bs fs) f b

    removeEdges : (g : Graph vertex edge) -> Subset g.edges
               -> (es : List edge
                      ** ss
                      ** ts
                      ** sub : Subgraph (MkGraph g.vertices es ss ts) g
                      ** sub.vertexMorphism.morphism = identity g.vertices)
    removeEdges g@(MkGraph vs [] [] []) [] = ([] ** [] ** [] ** identity g ** Refl)
    removeEdges (MkGraph vs (e :: es) (s :: ss) (t :: ts)) (True :: bs) =
      let (es' ** ss' ** ts' ** sub ** prf) = removeEdges (MkGraph vs es ss ts) bs in
          (es' ** ss' ** ts'
               ** MkSubgraph (identity vs) (rightShift sub.edgeMorphism)
                             (rewrite shiftLemma {y = e} s ss sub.edgeMorphism in
                              rewrite sub.isSourceHomomorphic in
                              rewrite prf in Refl)
                             (rewrite shiftLemma {y = e} t ts sub.edgeMorphism in
                              rewrite sub.isTargetHomomorphic in
                              rewrite prf in Refl)
               ** Refl)
    removeEdges (MkGraph vs (e :: es) (s :: ss) (t :: ts)) (False :: bs) =
      let (es' ** ss' ** ts' ** sub ** prf) = removeEdges (MkGraph vs es ss ts) bs in
          (e :: es' ** s :: ss' ** t :: ts' ** subgraphEdgeAppendLemma sub prf)

export
merge : (k, d, r : Graph vertex edge) -> (ktod : Homomorphism k d) -> (ktor : Homomorphism k r)
     -> (vertex -> vertex) -> (edge -> edge)
     -> Maybe (h : Graph vertex edge ** rtoh : Homomorphism r h ** dtoh : Homomorphism d h ** rtoh . ktor = dtoh . ktod)
merge k d r ktod ktor vertexRelabel edgeRelabel = do
    let reverseVertices = reverse ktor.vertexMorphism
    let (r' ** (sub, mor)) = addMissingVertices reverseVertices vertexRelabel
    mor <- transform mor
    let reverseEdges = update (reverse ktor.edgeMorphism) (compose (toHomomorphism sub) ktod).edgeMorphism
    let (r'' ** (sub', vmor, emor)) = addMissingEdges r' mor reverseEdges sub edgeRelabel
    emor <- transform emor
    hom <- isHomomorphism vmor emor
    let hom1 = toHomomorphism sub'
    let Yes prf = decEq (hom . ktor) (hom1 . ktod)
      | No _ => Nothing
    pure (r'' ** hom ** hom1 ** prf)
  where
    update : CList xs (Maybe (Pos ys)) -> ListMorphism ys zs -> CList xs (Maybe (Pos zs))
    update [] sub = []
    update (x :: xs) sub = map (apply sub) x :: update xs sub

    addVertex' : (g : Graph vertex edge) -> (v : vertex) -> (vertex -> vertex) -> (g' : Graph vertex edge ** (Subgraph g g', NonEmpty g'.vertices))
    addVertex' (MkGraph vertices edges source target) v relabel =
      (MkGraph (relabel v :: vertices) edges (rightShift source) (rightShift target)
        ** ( MkSubgraph (rightShift (identity vertices)) (identity edges)
                        (rewrite composeRightUnit (rightShift {y = relabel v} source) in
                         rewrite shiftIdentityLemma {y = relabel v} vertices source in Refl)
                        (rewrite composeRightUnit (rightShift {y = relabel v} target) in
                         rewrite shiftIdentityLemma {y = relabel v} vertices target in Refl)
           , IsNonEmpty
           ))

    addEdge' : (g : Graph vertex edge) -> (e : edge) -> (edge -> edge) -> (s, t : Vertex g)
            -> (g' : Graph vertex edge ** (Subgraph g g', NonEmpty g'.edges))
    addEdge' (MkGraph vertices edges source target) e relabel s t =
      (MkGraph vertices (relabel e :: edges) (s :: source) (t :: target)
        ** ( MkSubgraph (identity vertices) (rightShift (identity edges))
                        (rewrite composeLeftUnit source in
                         rewrite shiftLemma {y = relabel e} s source (identity edges) in
                         rewrite composeRightUnit source in Refl)
                        (rewrite composeLeftUnit target in
                         rewrite shiftLemma {y = relabel e} t target (identity edges) in
                         rewrite composeRightUnit target in Refl)
           , IsNonEmpty
           ))

    addMissingVertices : CList r.vertices (Maybe (Pos k.vertices)) -> (vertex -> vertex) -> (h : Graph vertex edge ** (Subgraph d h, CList r.vertices (Maybe (Pos h.vertices))))
    addMissingVertices f relabel =
      foldr (\i, (g ** (sub, mor)) =>
                case index f i of
                     Nothing => case addVertex' g (index r.vertices i) relabel of
                                     (g'@(MkGraph [] _ _ _) ** (_, prf)) => absurd prf
                                     (g'@(MkGraph (_ :: _) _ _ _) ** (prf, IsNonEmpty)) =>
                                       (g' ** ( compose prf sub
                                              , replaceAt (update mor prf.vertexMorphism.morphism) i (Just Here)
                                              ))
                     Just p => (g ** (sub, let pos = apply (sub.vertexMorphism.morphism . ktod.vertexMorphism) p
                                            in replaceAt mor i (Just pos))))
            (d ** (identity d, initialize Nothing))
            (range r.vertices)

    addMissingEdges : (g : Graph vertex edge) -> ListMorphism r.vertices g.vertices
                   -> CList r.edges (Maybe (Pos g.edges)) -> Subgraph d g
                   -> (edge -> edge)
                   -> (h : Graph vertex edge ** ( Subgraph d h
                                                , ListMorphism r.vertices h.vertices
                                                , CList r.edges (Maybe (Pos h.edges))
                                                ))
    addMissingEdges g v f sub relabel =
      foldr (\i, (h ** (sub, vmor, emor)) =>
                case index f i of
                     Nothing => case addEdge' h (index r.edges i) relabel (apply (vmor . r.source) i) (apply (vmor . r.target) i) of
                                     (h'@(MkGraph _ [] _ _) ** (_, prf)) => absurd prf
                                     (h'@(MkGraph _ (_ :: _) _ _) ** (prf, IsNonEmpty)) =>
                                       (h' ** ( compose prf sub
                                              , prf.vertexMorphism.morphism . vmor
                                              , replaceAt (update emor prf.edgeMorphism) i (Just Here)
                                              ))
                     Just p => (h ** (sub, vmor, emor)))
            (g ** (sub, v, f))
            (range r.edges)

export
checkInjective : Homomorphism g1 g2 -> Maybe (Subgraph g1 g2)
checkInjective (MkHomomorphism vMor eMor srcPrf tgtPrf) = do
    (inj ** prf) <- check vMor
    pure (MkSubgraph inj eMor (rewrite prf in srcPrf) (rewrite prf in tgtPrf))
  where
    check : (f : ListMorphism xs ys) -> Maybe (inj : InjectiveMorphism xs ys ** inj.morphism = f)
    check f with (isItJust (isInjective f))
      check f | Yes prf = Just (MkInjective f ** Refl)
      check f | No _ = Nothing

export
graphToDot : (Show vertex, Show edge)
          => {default "" id : String}
          -> (g : Graph vertex edge)
          -> {default [] markedVertices : List (Vertex g)}
          -> {default [] markedEdges : List (Edge g)}
          -> String
graphToDot g = unlines $ "subgraph cluster_\{id} {" :: goVertices ++ goEdges ++ ["}"]
  where
    goVertices : List String
    -- goVertices = map (\x => #""\#{id}_\#{show x}" [label="\#{show x}"];"#)
    goVertices = map (\i => let x = index g.vertices i
                                comp = #""\#{id}_\#{show x}""#
                                attributes = if elem i markedVertices
                                                then #"[label="\#{show x}", color=red]"#
                                                else #"[label="\#{show x}"]"#
                             in "\{comp} \{attributes};") (range g.vertices)

    goEdges : List String
    goEdges = map (\i => let src = #""\#{id}_\#{show $ index g.vertices $ apply g.source i}""#
                             tgt = #""\#{id}_\#{show $ index g.vertices $ apply g.target i}""#
                             attributes = if elem i markedEdges
                                             then #"[label="\#{show $ index g.edges i}", color=red]"#
                                             else #"[label="\#{show $ index g.edges i}"]"#
                          in "\{src} -> \{tgt} \{attributes};") (range g.edges)
    -- goEdges vs [] [] [] = []
    -- goEdges vs (e :: es) (s :: ss) (t :: ts) =
    --   #""\#{id}_\#{show (index vs s)}" -> "\#{id}_\#{show (index vs t)}" [label="\#{show e}"];"# :: goEdges vs es ss ts

export
homToDot : (Show lvertex, Show rvertex, Show ledge, Show redge)
        => (left : Graph lvertex ledge) -> (right : Graph rvertex redge)
        -> Homomorphism left right
        -> (leftId, rightId : String)
        -> String
homToDot left right hom leftId rightId =
    let leftDot = graphToDot {id = leftId} left
        rightDot = graphToDot {id = rightId, markedVertices = forget hom.vertexMorphism, markedEdges = forget hom.edgeMorphism} right
        arrows = goVertices leftId rightId left.vertices right.vertices hom.vertexMorphism
     in unlines $ "digraph {" :: leftDot :: rightDot :: arrows ++ ["}"]
  where
    goVertices : (Show a, Show b) => String -> String -> (xs : List a) -> (ys : List b) -> ListMorphism xs ys -> List String
    goVertices lid rid [] ys [] = []
    goVertices lid rid (x :: xs) ys (f :: fs) =
      #""\#{lid}_\#{show x}" -> "\#{rid}_\#{show (index ys f)}" [style=dashed]"# :: goVertices lid rid xs ys fs


-- buildMatchState' : Graph n m vs es -> Graph n' m' vs' es' -> List (Fin n, Fin n') -> VF2State n n'
-- buildMatchState' g1 g2 morph = foldr (\(n, m) => updateState n m g1 g2) initState morph
--
-- buildMatchState : Graph n m vs es -> Graph n' m' vs' es' -> Vect ln (Fin n') -> Vect n (Maybe (Fin ln)) -> VF2State n n'
-- buildMatchState g n lton gtol = buildMatchState' g n (map (\(x, y) => (x, index y lton)) $ catRightMaybes $ toList $ zip range gtol)
