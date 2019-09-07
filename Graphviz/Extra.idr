module Graphviz.Extra

import Graphviz as GV
import Data.Graph as G

export
data GraphvizParsingError = NonDigraph
                          | MultipleEdges
                          | NodeNotDefined String
                          | Subgraph
                          | Attribute
                          | Equality

export
graphvizParsingErrorMessage : GraphvizParsingError -> String
graphvizParsingErrorMessage NonDigraph = "Non directed graphs are not supported at this time"
graphvizParsingErrorMessage MultipleEdges = "Multiple edges statements are not supported at this time"
graphvizParsingErrorMessage (NodeNotDefined id) = "The node " ++ id ++ " is not previously declared"
graphvizParsingErrorMessage Subgraph = "Subgraphs are not supported at this time"
graphvizParsingErrorMessage Attribute = "Attributes are not supported at this time"
graphvizParsingErrorMessage Equality = "Equalities are not supported at this time"

||| Extracts the vertices of a graph and converts them to the Graphviz format.
||| @g The graph
convertVertices : Show vertex => (g : G.Graph n m {vertex} {edge} vs es) -> List (Stmt Directed)
convertVertices {vs} g
  = map (\v => Node (MkNodeStmt (MkNodeId (StringID $ show v) Nothing) []) Nothing) (toList vs)

||| Extracts the edges of a graph and converts them to the Graphviz format.
||| @g The graph
convertEdges : (Show vertex, Show edge) => (g : G.Graph n m {vertex} {edge} vs es)
            -> List (Stmt Directed)
convertEdges {es = []}        Empty = []
convertEdges {es = (e :: es)} (Edge s t g)
    = let label = Just [(StringID "label", StringID $ show e)] in
          (GV.Edge ([buildNode s, buildNode t] ** IsNonEmpty) label) :: convertEdges g
  where
    buildNode : Fin n -> Either NodeId (Subgraph Directed)
    buildNode x = Left $ MkNodeId (StringID $ show $ index x vs) Nothing

||| Converts a graph to the graphviz format.
||| @g The graph
export
graphToGraphviz : (Show vertex, Show edge) => (g : G.Graph n m {vertex} {edge} vs es) -> GV.Graph
graphToGraphviz g = DiGraph Nothing (convertVertices g ++ convertEdges g)

||| Converts labels identifier from Graphviz format to strings.
||| @id Identifier
extractLabel : (id : ID) -> String
extractLabel (StringID id) = id
extractLabel (NumeralID id) = show id
extractLabel (StringLiteralID id) = id
extractLabel (HTMLString id) = id

||| Converts a node with attributes from Graphviz format to `Graph` adding it to an already
||| existing graph.
||| @node  The node
||| @attrs The node attributes
||| @g     The existing graph
convertNode : (node : NodeStmt) -> (attrs : Maybe AList) -> (g : ExGraph String String)
           -> ExGraph String String
convertNode (MkNodeStmt (MkNodeId node _) _) _ (_ ** _ ** _ ** _ ** g)
  = (_ ** _ ** _ ** _ ** addVertex (extractLabel node) g)

||| Converts an edge with attributes from Graphviz format to `Graph` addint it to an already
||| existing graph.
||| @edge  The edge
||| @attrs The edge attributes
||| @g     The existing graph
convertEdge : (edge : EdgeStmt Directed) -> (attrs : Maybe AList) -> (g : ExGraph String String)
           -> Either GraphvizParsingError (ExGraph String String)
convertEdge ([Left (MkNodeId s _), Left (MkNodeId t _)] ** IsNonEmpty) (Just [(StringID "label", lab)]) (_ ** _ ** vs ** _ ** g) = do
  s' <- maybeToEither (NodeNotDefined (extractLabel s)) $ Vect.elemIndex (extractLabel s) vs
  t' <- maybeToEither (NodeNotDefined (extractLabel t)) $ Vect.elemIndex (extractLabel t) vs
  Right (_ ** _ ** _ ** _ ** addEdge s' t' (extractLabel lab) g)
convertEdge _ _ _ = Left MultipleEdges

||| Converts a Graphviz directed graph statement to `Graph` representation, accumulating on an
||| already existing graph.
||| @stmt The statement
||| @g    The existing graph
convertStatement : (stmt : Stmt Directed) -> (g : ExGraph String String)
                -> Either GraphvizParsingError (ExGraph String String)
convertStatement (Node node attrs) g = pure $ convertNode node attrs g
convertStatement (Edge stmt attrs) g = convertEdge stmt attrs g
convertStatement (Attr _) _ = Left Attribute
convertStatement (IdEq _ _) _ = Left Equality
convertStatement (Sub _) _ = Left Subgraph

||| Converts a list of Graphviz statements to `Graph` representation, if possible.
||| @stmts The list of statements
convertStatements : (stmts : List (Stmt Directed)) -> Either GraphvizParsingError (ExGraph String String)
convertStatements [] = pure (_ ** _ ** _ ** _ ** empty)
convertStatements (x :: xs) = convertStatements xs >>= convertStatement x

||| Given a graph in the graphviz format tries to convert it to the inductive representation.
||| @g The graphviz graph
export
graphvizToGraph : (g : GV.Graph) -> Either GraphvizParsingError (ExGraph String String)
graphvizToGraph (DiGraph _ xs) = convertStatements (reverse xs)
graphvizToGraph (UndiGraph x xs) = Left NonDigraph
