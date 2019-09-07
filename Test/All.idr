module Test.All

import Test.Unit.Runners
import Test.Graph
import Test.Graphviz

%access export

allTests : IO ()
allTests = runTests (join [testGraph, testGraphviz])

{-
import Graph
import SubGraph
import Morphism
import Pushout
import Data.SortedSet
import Data.Vect
import Debug.Trace

%access export

dp_l : Graph 3 3 ["1", "2", "3"] ["a", "b", "c"]
dp_l = Edge 0 1 $ Edge 0 2 $ Edge 2 1 $ Empty

dp_r : Graph 4 4 ["1", "2", "4", "5"] ["a", "b", "c", "d"]
dp_r = Edge 0 2 $ Edge 0 3 $ Edge 2 1 $ Edge 3 1 $ Empty

dp_k : Graph 2 0 {edge = String} ["1", "2"] []
dp_k = Empty

-- dp_k2 : Graph 1 0 {edge = Integer} [1] []
-- dp_k2 = Empty

dp_n : Graph 3 4 ["1", "2", "3"] ["n", "a", "b", "c"]
dp_n = Edge 0 0 dp_l

dp_j : Graph 2 1 ["6", "7"] ["12"]
dp_j = Edge 0 1 Empty

dp_glue : Vect 4 (Maybe (Fin 3))
dp_glue = [Just 0, Just 1, Nothing, Nothing]

-- dp_glue2 : Vect 4 (Maybe (Fin 3))
-- dp_glue2 = [Just 0, Nothing, Nothing, Nothing]

dp_ktol : Vect 2 (Fin 3)
dp_ktol = [0, 1]

-- dp_k2tol : Vect 1 (Fin 3)
-- dp_k2tol = [0]

dp_ktor : Vect 2 (Fin 4)
dp_ktor = [0, 1]

-- dp_k2tor : Vect 1 (Fin 4)
-- dp_k2tor = [0]

dp_lton : Vect 3 (Fin 3)
dp_lton = [0, 1, 2]

dp_jtog : Vect 2 (Fin 5)
dp_jtog = [3, 4]

dp_rule : Rewrite String String
dp_rule = MkRule dp_l dp_r dp_k dp_ktol dp_ktor dp_glue

-- dp_rule2 : Rewrite Integer Integer
-- dp_rule2 = MkRule dp_l dp_r dp_k2 dp_k2tol dp_k2tor dp_glue2

dp_rulen : RewriteNeg String String
dp_rulen = MkRuleNeg dp_l dp_r dp_k dp_n dp_ktol dp_ktor dp_lton dp_glue

dp_g : Graph 5 6 ["1", "2", "3", "6", "7"] ["1", "2", "3", "4", "5", "6"]
dp_g = Edge 0 1 $ Edge 0 2 $ Edge 2 1 $ Edge 0 3 $ Edge 1 4 $ Edge 3 4 $ Empty
-}
