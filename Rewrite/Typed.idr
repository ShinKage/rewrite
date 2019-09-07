module Rewrite.Typed

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

||| Applies, if possible, the given typed rewrite rule to the graph.
||| The index `i` select which subgraph to substitute. The index i must be
||| provided before hand.
||| @graph The graph to be matched
||| @rule The simple rewrite rule
||| @tmap Mapping from the graph to the type
||| @i The index of the subgraph to be rewritten
singleRewrite : (graph : Graph n m {vertex = String} {edge = String} vs es)
             -> (rule : RewriteTyped String String) -> (tmap : List (String, String))
             -> (i : Nat) -> Either RewriteError (ExGraph String String)
singleRewrite {vs} g (MkRuleTyped {rn} {tn} t l r k ktol ktor ltot rtot ktot kmap) tmap i = do
  checkInjective "K" "L" ktol
  gtot <- convertMorph "G" "T" g t tmap
  (ktolMorph ** ktolPrf) <- findMorphism "K" "L" k l ktol
  (ktorMorph ** ktorPrf) <- findMorphism "K" "R" k r ktor
  (gtotMorph ** gtotPrf) <- findMorphism "G" "T" g t gtot
  (ltotMorph ** ltotPrf) <- findMorphism "L" "T" l t ltot
  (ktotMorph ** ktotPrf) <- findMorphism "K" "T" k t ktot
  (rtotMorph ** rtotPrf) <- findMorphism "R" "T" r t rtot

  (ltog', _) <- indexCheck i (match g l)
  ltog <- convertVect "L" "G" ltog'

  (ltogMorph ** ltogPrf) <- findMorphism "L" "G" l g ltog
  let lsubset = vectToSubset ltog'
  let ksubset = fromFins {xs = vs} $ toList $ ltog . ktol
  let kedges = toList $ ltog .*. ktol .*. (edges k)
  let (_ ** _ ** _ ** _ ** sub) = subgraph lsubset g
  let (_ ** _ ** _ ** _ ** (d, dtog)) = gluedGraph lsubset ksubset kedges g

  let dtot = gtot . dtog
  (dtotMorph ** dtotPrf) <- findMorphism "D" "T" d t dtot

  ktod <- convertVect "K" "D" $ dtog .! ltog . ktol
  (ktodMorph ** ktodPrf) <- findMorphism "K" "D" k d ktod
  (dtogMorph ** dtogPrf) <- findMorphism "D" "G" d g dtog

  let (_ ** _ ** _ ** _ ** (h, rtoh, dtoh)) = merge (mergeMapping ktor ktod) d r

  rtoh <- convertList "R" "H" rtoh
  (rtohMorph ** rtohPrf) <- findMorphism "R" "H" r h rtoh
  (dtohMorph ** dtohPrf) <- findMorphism "D" "H" d h dtoh

  -- htot <- convertVect "H" "T" $ map (\x => map (flip index rtot) (elemIndex x rtoh) <+> map (flip index dtot) (elemIndex x dtoh)) range
  htot <- convertVect "H" "T" $ zipWith (<+>) (rtot .? rtoh .! range) (dtot .? dtoh .! range)
  (htotMorph ** htotPrf) <- findMorphism "H" "T" h t htot

  checkPath "K -> L -> G" "K -> D -> G" (ltog . ktol) (dtog . ktod)
  checkPath "K -> R -> H" "K -> D -> H" (rtoh . ktor) (dtoh . ktod)
  checkPath "K -> L -> T" "K -> T" (ltot . ktol) ktot
  checkPath "K -> R -> T" "K -> T" (rtot . ktor) ktot
  checkPath "D -> G -> T" "D -> T" (gtot . dtog) dtot
  checkPath "D -> H -> T" "D -> T" (htot . dtoh) dtot

  let dp = DP ltogPrf ktodPrf rtohPrf ktolPrf ktorPrf dtogPrf dtohPrf
  let dpi = DPT ltotPrf ktotPrf rtotPrf gtotPrf dtotPrf htotPrf dp

  pure (_ ** _ ** _ ** _ ** h)
