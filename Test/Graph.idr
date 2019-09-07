module Test.Graph

import Test.Unit.Assertions
import Data.Graph
import Data.Graph.Subgraph
import Data.Vect.Subset
import Data.Fin.Extra

%access export

Show (VSub xs) where
  show sub = show $ toFins sub

testMultiedges : IO Bool
testMultiedges = do
  putStrLn "==> Test multiedges"
  let g = addEdge 1 2 3 $ addEdge 0 1 0 $ addEdge 0 1 1 $ addVertex 2 $ addVertex 1 $ addVertex 0 empty
  assertEquals (multiedges 0 1 g) 2

testAddVertex : IO Bool
testAddVertex = do
  putStrLn "==> Test addVertex"
  let g = addVertex 1 $ addVertex 0 $ the (Graph 0 0 {vertex = Integer} {edge = Integer} [] []) empty
  assertEquals (verticesLabels g) [1, 0]

testAddEdge : IO Bool
testAddEdge = do
  putStrLn "==> Test addEdge"
  let g = addEdge 1 0 53 $ addEdge 0 1 42 $ addVertex 1 $ addVertex 0 empty
  labels <- assertEquals (edgesLabels g) [53, 42]
  indices <- assertEquals (edges g) [(1, 0), (0, 1)]
  pure $ labels && indices

testAdjacentVertices : IO Bool
testAdjacentVertices = do
  putStrLn "==> Test adjacentVertices"
  let g = addEdge 2 1 3 $ addEdge 1 2 2 $ addEdge 0 1 1 $ addEdge 0 0 0 $ addVertex 0 $ addVertex 1 $ addVertex 2 empty
  let expectedZero = In $ In $ Out Empty
  let expectedOne = In $ Out $ In Empty
  let expectedTwo = Out $ In $ Out Empty
  zero <- assertTrue (adjacentVertices 0 g == expectedZero)
  one <- assertTrue (adjacentVertices 1 g == expectedOne)
  two <- assertTrue (adjacentVertices 2 g == expectedTwo)
  pure $ zero && one && two

testAdjacentEdges : IO Bool
testAdjacentEdges = do
  putStrLn "==> Test adjacentEdges"
  let g = addEdge 2 1 3 $ addEdge 1 2 2 $ addEdge 0 1 1 $ addEdge 0 0 0 $ addVertex 0 $ addVertex 1 $ addVertex 2 empty
  let expectedZero = Out $ Out $ In $ In Empty
  let expectedOne = In $ In $ In $ Out Empty
  let expectedTwo = In $ In $ Out $ Out Empty
  zero <- assertTrue (adjacentEdges 0 g == expectedZero)
  one <- assertTrue (adjacentEdges 1 g == expectedOne)
  two <- assertTrue (adjacentEdges 2 g == expectedTwo)
  pure $ zero && one && two

testRemoveVertex : IO Bool
testRemoveVertex = do
  putStrLn "==> Test removeVertex"
  let g = the (Graph 1 0 {vertex = Integer} {edge = Integer} [1] []) Empty
  first <- assertEquals (vertexCount (removeVertex 0 g)) 0
  let g = removeVertex 1 $ addEdge 0 2 0 $ addEdge 0 1 1 $ addEdge 1 2 2 $ addVertex 0 $ addVertex 1 $ addVertex 2 empty
  second <- assertEquals (vertexCount g) 2
  third <- assertEquals (toList (edges g)) [(0, 1)]
  pure $ first && second && third

testSubgraph : IO Bool
testSubgraph = do
  putStrLn "==> Test subgraph"
  let (n ** m ** vs ** es ** g) = subgraph Empty (the (Graph 0 0 {vertex = Integer} {edge = Integer} [] []) empty)
  zero <- assertEquals n 0
  zero' <- assertEquals m 0
  let g = addEdge 2 1 () $ addEdge 1 2 () $ addEdge 0 1 () $ addEdge 0 0 () $ addVertex 0 $ addVertex 1 $ addVertex 2 empty
  let (n ** m ** vs ** es ** g) = subgraph (In $ In $ Out Empty) g
  more <- assertEquals n 2
  more' <- assertEquals m 2
  more'' <- assertEquals (sort $ toList $ vs) [0, 1]
  pure $ zero && zero' && more && more' && more''

testIsGlued : IO Bool
testIsGlued = do
  putStrLn "==> Test isGlued"
  let g = addEdge 2 1 () $ addEdge 1 2 () $ addEdge 0 1 () $ addEdge 0 0 () $ addEdge 2 3 () $ addVertex 0 $ addVertex 1 $ addVertex 2 $ addVertex 3 empty
  let sub = In $ In $ Out $ Out Empty
  t <- assertTrue (isGlued sub g 1)
  f <- assertFalse (isGlued sub g 3)
  pure $ f && t

testGluedVertices : IO Bool
testGluedVertices = do
  putStrLn "==> Test gluedVertices"
  let g = addEdge 2 1 () $ addEdge 1 2 () $ addEdge 0 1 () $ addEdge 0 0 () $ addEdge 2 3 () $ addVertex 0 $ addVertex 1 $ addVertex 2 $ addVertex 3 empty
  let sub = In $ In $ Out $ Out Empty
  let expected = Out $ In $ Out $ Out Empty
  assertEquals (gluedVertices sub g) expected

testMerge : IO Bool
testMerge = do
  putStrLn "==> Test merge"
  let from = addEdge 0 2 1 $ addEdge 0 1 0 $ addVertex 2 $ addVertex 1 $ addVertex 0 empty
  let to = addEdge 0 1 10 $ addVertex 11 $ addVertex 10 empty
  let mapping = [Just 0, Nothing]
  let (n ** m ** vs ** es ** (g, map1, map2)) = merge mapping from to
  nCheck <- assertEquals n 4
  mCheck <- assertEquals m 3
  vsCheck <- assertEquals (sort $ toList $ vs) [0, 1, 2, 10]
  esCheck <- assertEquals (sort $ toList $ es) [0, 1, 10]
  pure $ nCheck && mCheck && vsCheck && esCheck

testGraph : List (IO Bool)
testGraph = [ testMultiedges
            , testAddVertex
            , testAddEdge
            , testAdjacentVertices
            , testAdjacentEdges
            , testRemoveVertex
            , testSubgraph
            , testIsGlued
            , testGluedVertices
            , testMerge
            ]
