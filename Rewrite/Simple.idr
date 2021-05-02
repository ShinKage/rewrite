module Rewrite.Simple

import Data.Graph
import Data.Graph.Pushout
import Data.Graph.Subgraph
import Data.Graph.VF2
import Rewrite.Utils
import Decidable.Equality

singleRewrite : (g : Graph vertex edge) -> RewriteRule vertex edge
             -> (vertex -> vertex) -> (edge -> edge)
             -> List (DoublePushout vertex edge)
singleRewrite g (MkRewriteRule l k r ktol ktor) vertexRelabel edgeRelabel = do
  -- 1) Check injectivity of K -> L
  ktolSub <- toList $ checkInjective ktol

  -- 2) Find L in G
  ltogSub <- match g l

  let (d ** dtog) = glued k l g ktol (toHomomorphism ltogSub)

  ktodSub <- match d k

  -- 6) Check commutativity
  let Yes leftPrf = decEq ((toHomomorphism ltogSub) . ktol) (dtog . (toHomomorphism ktodSub))
    | No _ => []

  -- 7) Merge
  (h ** rtoh ** dtoh ** rightPrf) <- toList $ merge k d r (toHomomorphism ktodSub) ktor vertexRelabel edgeRelabel

  pure $ MkDoublePushout (MkRewriteRule l k r ktol ktor) g h d
                         dtog dtoh
                         (toHomomorphism ltogSub) (toHomomorphism ktodSub) rtoh
                         leftPrf rightPrf
