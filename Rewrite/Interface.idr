module Rewrite.Interface

import Data.Vect.Extra
import Data.Vect.Subset
import Data.Graph
import Data.Graph.Morphism
import Data.Graph.Pushout
import Data.Graph.Subgraph
import Data.Graph.VF2
import Rewrite.Utils

%default covering
%access export

||| Applies, if possible, the given interface rewrite rule to the graph.
||| The index `i` select which subgraph to substitute. The index i must be
||| provided before hand.
||| @graph The graph to be matched
||| @rule The simple rewrite rule
||| @j The interface graph
||| @jmap Mapping from the interface to the graph
||| @i The index of the subgraph to be rewritten
singleRewrite : (graph : Graph n m {vertex = String} {edge = String} vs es)
             -> (rule : Rewrite String String)
             -> (j : Graph ni mi {vertex = String} {edge = String} vsi esi)
             -> (jmap : List (String, String)) -> (i : Nat)
             -> Either RewriteError (ExGraph String String)
singleRewrite {vs} g (MkRule {rn} l r k ktol ktor kmap) j jmap i = do
  checkInjective "K" "L" ktol
  jtog <- convertMorph "J" "G" j g jmap
  (ktolMorph ** ktolPrf) <- findMorphism "K" "L" k l ktol
  (ktorMorph ** ktorPrf) <- findMorphism "K" "R" k r ktor
  (jtogMorph ** jtogPrf) <- findMorphism "J" "G" j g jtog

  (ltog', _) <- indexCheck i (match g l)
  ltog <- convertVect "L" "G" ltog'

  (ltogMorph ** ltogPrf) <- findMorphism "L" "G" l g ltog
  let lsubset = vectToSubset ltog'
  let ksubset = fromFins {xs = vs} $ toList $ ltog . ktol
  let kedges = toList $ ltog .*. ktol .*. (edges k)
  let (_ ** _ ** _ ** _ ** sub) = subgraph lsubset g
  let (_ ** _ ** _ ** _ ** (d, dtog)) = gluedGraph lsubset ksubset kedges g

  jtod <- convertVect "J" "D" $ dtog .! jtog
  (jtodMorph ** jtodPrf) <- findMorphism "J" "D" j d jtod

  ktod <- convertVect "K" "D" $ dtog .! ltog . ktol
  (ktodMorph ** ktodPrf) <- findMorphism "K" "D" k d ktod
  (dtogMorph ** dtogPrf) <- findMorphism "D" "G" d g dtog

  let (_ ** _ ** _ ** _ ** (h, rtoh, dtoh)) = merge (mergeMapping ktor ktod) d r

  rtoh <- convertList "R" "H" rtoh
  (rtohMorph ** rtohPrf) <- findMorphism "R" "H" r h rtoh
  (dtohMorph ** dtohPrf) <- findMorphism "D" "H" d h dtoh

  let jtoh = dtoh . jtod
  (jtohMorph ** jtohPrf) <- findMorphism "J" "H" j h jtoh

  checkPath "K -> L -> G" "K -> D -> G" (ltog . ktol) (dtog . ktod)
  checkPath "K -> R -> H" "K -> D -> H" (rtoh . ktor) (dtoh . ktod)
  checkPath "J -> D -> G" "J -> G" (dtog . jtod) jtog
  checkPath "J -> D -> H" "J -> H" (dtoh . jtod) jtoh

  let dp = DP ltogPrf ktodPrf rtohPrf ktolPrf ktorPrf dtogPrf dtohPrf
  let dpi = DPI jtogPrf jtodPrf jtohPrf dp

  pure (_ ** _ ** _ ** _ ** h)
