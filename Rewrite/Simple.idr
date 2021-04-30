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

testl : Graph Int Int
testl = MkGraph [0,1,2] [0,1,2] [0,0,2] [1,2,1]

testk : Graph Int Int
testk = MkGraph [3,4] [] [] []

testr : Graph Int Int
testr = MkGraph [5,6,7,8] [3,4,5,6] [0,0,2,3] [2,3,1,1]

testg : Graph Int Int
testg = MkGraph [9,10,11,12,13] [7,8,9,10,11,12] [0,0,2,1,0,4] [1,2,1,3,4,3]

testktol : Homomorphism Simple.testk Simple.testl
testktol = MkHomomorphism [0,1] [] Refl Refl

testktor : Homomorphism Simple.testk Simple.testr
testktor = MkHomomorphism [0,1] [] Refl Refl

testrule : RewriteRule Int Int
testrule = MkRewriteRule testl testk testr testktol testktor

-- [MkDoublePushout
--   (MkRewriteRule (MkGraph [0, 1, 2] [0, 1, 2] [0, 0, 2] [1, 2, 1])
--                  (MkGraph [0, 1] [] [] [])
--                  (MkGraph [0, 1, 2, 3] [0, 1, 2, 3] [0, 0, 2, 3] [2, 3, 1, 1])
--                  (MkHomomorphism [0, 1] [] Refl Refl)
--                  (MkHomomorphism [0, 1] [] Refl Refl))
--   (MkGraph [0, 1, 2, 3, 4] [0, 1, 2, 3, 4, 5] [0, 0, 2, 1, 0, 4] [1, 2, 1, 3, 4, 3])
--   (MkGraph [20, 30, 0, 1, 3, 4] [0, 10, 20, 30, 3, 4, 5] [2, 2, 0, 1, 3, 2, 5] [0, 1, 3, 3, 4, 5, 4])
--   (MkGraph [0, 1, 3, 4] [3, 4, 5] [1, 0, 3] [2, 3, 2])
--   (MkHomomorphism [0, 1, 3, 4] [3, 4, 5] Refl Refl)
--   (MkHomomorphism [2, 3, 4, 5] [4, 5, 6] Refl Refl)
--   (MkHomomorphism [0, 1, 2] [0, 1, 2] Refl Refl)
--   (MkHomomorphism [0, 1] [] Refl Refl)
--   (MkHomomorphism [2, 3, 0, 1] [0, 1, 2, 3] Refl Refl)
--   Refl
--   Refl]

test : IO ()
test = do
  let res = singleRewrite testg testrule (id) (id)
  for_ res $ \(MkDoublePushout (MkRewriteRule l k r ktol ktor) g h d dtog dtoh ltog ktod rtoh left right) => do
    -- putStrLn $ toDot {id = "G"} g
    -- putStrLn $ toDot {id = "H"} h
    -- putStrLn $ toDot {id = "D"} d
    putStrLn $ homToDot d g dtog "D" "G"
    putStrLn $ homToDot d h dtoh "D" "H"
