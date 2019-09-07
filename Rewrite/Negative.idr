module Rewrite.Negative

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

||| Applies, if possible, the given negative rewrite rule to the graph.
||| The index `i` select which subgraph to substitute. The index i must be
||| provided before hand.
||| @graph The graph to be matched
||| @rule The simple rewrite rule
||| @i The index of the subgraph to be rewritten
singleRewrite : (graph : Graph n m {vertex = String} {edge = String} vs es)
             -> (rule : RewriteNeg String String) -> (i : Nat)
             -> Either RewriteError (ExGraph String String)
singleRewrite {m} {vs} g (MkRuleNeg {rn} {km} l r k n ktol ktor lton kmap) i = do
  checkInjective "K" "L" ktol
  (ktolMorph ** ktolPrf) <- findMorphism "K" "L" k l ktol
  (ktorMorph ** ktorPrf) <- findMorphism "K" "R" k r ktor
  (ltonMorph ** ltonPrf) <- findMorphism "L" "N" l n lton

  (ltog', gtol') <- indexCheck i (match g l)
  ltog <- convertVect "L" "G" ltog'
  (ltogMorph ** ltogPrf) <- findMorphism "L" "G" l g ltog

  eitherUnless "N" "G" $ indexCheck 0 $ match' g n $ buildMatchState g n lton gtol'

  let lsubset = vectToSubset ltog'
  let ksubset = fromFins {xs = vs} $ toList $ ltog . ktol
  let kedges = toList $ ltog .*. ktol .*. (edges k)
  let (_ ** _ ** _ ** _ ** sub) = subgraph lsubset g
  let (_ ** _ ** _ ** _ ** (d, dtog)) = gluedGraph lsubset ksubset kedges g

  ktod <- convertVect "K" "D" $ dtog .! ltog .  ktol
  (ktodMorph ** ktodPrf) <- findMorphism "K" "D" k d ktod
  (dtogMorph ** dtogPrf) <- findMorphism "K" "D" d g dtog

  let (_ ** _ ** _ ** _ ** (h, rtoh, dtoh)) = merge (mergeMapping ktor ktod) d r

  rtoh <- convertList "R" "H" rtoh
  (rtohMorph ** rtohPrf) <- findMorphism "R" "H" r h rtoh
  (dtohMorph ** dtohPrf) <- findMorphism "D" "H" d h dtoh

  checkPath "K -> L -> G" "K -> D -> G" (ltog . ktol) (dtog . ktod)
  checkPath "K -> R -> H" "K -> D -> H" (rtoh . ktor) (dtoh . ktod)

  let dp = DP ltogPrf ktodPrf rtohPrf ktolPrf ktorPrf dtogPrf dtohPrf
  let dpn = DPN ltonPrf dp

  pure (_ ** _ ** _ ** _ ** h)
