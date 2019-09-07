module Data.Graph.TypedGraph

import public Data.Graph
import public Data.Graph.Morphism

%default total
%access public export

data TypedGraph : (g : Graph n m vs es)
               -> (t : Graph n' m' vs' es')
               -> (mor : Morphism g t)
               -> Type where
  Typed : {auto prf : Homomorphism g t mor} -> TypedGraph g t mor

%name TypedGraph g,h
