module Test.Graphviz

import Test.Unit.Assertions
import Data.Graph as G
import Graphviz as GV
import Graphviz.Extra
import Data.Fin.Extra

%access export

Show (Stmt d) where
  show (Node (MkNodeStmt (MkNodeId (StringID x) _) _) _) = "[node " ++ show x ++ "]"
  show (Node (MkNodeStmt (MkNodeId (NumeralID x) _) _) _) = "[node " ++ show x ++ "]"
  show (Node (MkNodeStmt (MkNodeId (StringLiteralID x) _) _) _) = "[node " ++ show x ++ "]"
  show (Node (MkNodeStmt (MkNodeId (HTMLString x) _) _) _) = "[node " ++ show x ++ "]"
  show (Edge (x ** pf) (Just [(StringID "label", StringID y)])) = "[edge " ++ y ++ " - " ++ concat (intersperse " -> " $ map helper x) ++ "]"
    where helper : Either NodeId (Subgraph d) -> String
          helper (Left (MkNodeId (StringID y) _)) = show y
          helper (Left (MkNodeId (NumeralID y) _)) = show y
          helper (Left (MkNodeId (StringLiteralID y) _)) = show y
          helper (Left (MkNodeId (HTMLString y) _)) = show y
          helper (Right r) = "()"
  show (Edge (x ** pf) _) = "[edge ()]"
  show (Attr _) = "[attribute]"
  show (IdEq _ _) = "[identifier equality]"
  show (Sub _) = "[subgraph]"

testToGraphviz : IO Bool
testToGraphviz = do
  putStrLn "==> Test graphToGraphviz"
  let g = addEdge 1 2 "c" $ addEdge 0 2 "b" $ addEdge 0 1 "a" $ addVertex "3" $ addVertex "2" $ addVertex "1" empty
  let (DiGraph Nothing stmts) = graphToGraphviz g | pure False
  sizeCheck <- assertEquals (length stmts) 6
  let [v3, v2, v1, e1, e2, e3] = stmts
  v1Check <- assertEquals v1 (Node (MkNodeStmt (MkNodeId (StringID $ show "1") Nothing) []) Nothing)
  v2Check <- assertEquals v2 (Node (MkNodeStmt (MkNodeId (StringID $ show "2") Nothing) []) Nothing)
  v3Check <- assertEquals v3 (Node (MkNodeStmt (MkNodeId (StringID $ show "3") Nothing) []) Nothing)
  e1Check <- assertEquals e1 (Edge ([(Left $ MkNodeId (StringID $ show "2") Nothing), (Left $ MkNodeId (StringID $ show "1") Nothing)] ** IsNonEmpty) (Just [(StringID "label", StringID $ show "c")]))
  e2Check <- assertEquals e2 (Edge ([(Left $ MkNodeId (StringID $ show "3") Nothing), (Left $ MkNodeId (StringID $ show "1") Nothing)] ** IsNonEmpty) (Just [(StringID "label", StringID $ show "b")]))
  e3Check <- assertEquals e3 (Edge ([(Left $ MkNodeId (StringID $ show "3") Nothing), (Left $ MkNodeId (StringID $ show "2") Nothing)] ** IsNonEmpty) (Just [(StringID "label", StringID $ show "a")]))
  pure $ sizeCheck && v1Check && v2Check && v3Check && e1Check && e2Check && e3Check

testFromGraphviz : IO Bool
testFromGraphviz = do
  putStrLn "==> Test graphToGraphviz"
  let v1 = Node (MkNodeStmt (MkNodeId (StringID "1") Nothing) []) Nothing
  let v2 = Node (MkNodeStmt (MkNodeId (StringID "2") Nothing) []) Nothing
  let v3 = Node (MkNodeStmt (MkNodeId (StringID "3") Nothing) []) Nothing
  let e1 = Edge ([(Left $ MkNodeId (StringID "2") Nothing), (Left $ MkNodeId (StringID "1") Nothing)] ** IsNonEmpty) (Just [(StringID "label", StringID "c")])
  let e2 = Edge ([(Left $ MkNodeId (StringID "3") Nothing), (Left $ MkNodeId (StringID "1") Nothing)] ** IsNonEmpty) (Just [(StringID "label", StringID "b")])
  let e3 = Edge ([(Left $ MkNodeId (StringID "3") Nothing), (Left $ MkNodeId (StringID "2") Nothing)] ** IsNonEmpty) (Just [(StringID "label", StringID "a")])
  let (Right (n ** m ** vs ** es ** g)) = graphvizToGraph (DiGraph Nothing [v3, v2, v1, e1, e2, e3]) | pure False
  vCheck <- assertEquals (toList $ vs) ["1", "2", "3"]
  eCheck <- assertEquals (toList $ es) ["a", "b", "c"]
  stCheck <- assertEquals (map (\(x, y) => (finToInteger x, finToInteger y)) $ toList $ edges g) [(2, 1), (2, 0), (1, 0)]
  pure $ vCheck && eCheck && stCheck

testGraphviz : List (IO Bool)
testGraphviz = [testToGraphviz, testFromGraphviz]
