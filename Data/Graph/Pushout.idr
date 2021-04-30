||| Various types of double pushouts in the category of directed multi-graphs.
module Data.Graph.Pushout

import public Data.Graph
import public Data.Graph.Morphism
import public Data.Graph.TypedGraph

%default total

public export
record RewriteRule vertex edge where
  constructor MkRewriteRule
  pre : Graph vertex edge
  glue : Graph vertex edge
  post : Graph vertex edge
  glueToPreMorphism : Homomorphism glue pre
  glueToPostMorphism : Homomorphism glue post

public export
record NegRewriteRule vertex edge where
  constructor MkNegRewriteRule
  pre : Graph vertex edge
  glue : Graph vertex edge
  post : Graph vertex edge
  neg : Graph vertex edge
  glueToPreMorphism : Homomorphism glue pre
  glueToPostMorphism : Homomorphism glue post
  preToNegMorphism : Homomorphism pre neg

public export
record DoublePushout vertex edge where
  constructor MkDoublePushout
  rule : RewriteRule vertex edge
  from : Graph vertex edge
  to : Graph vertex edge
  glue : Graph vertex edge
  glueToFromMorphism : Homomorphism glue from
  glueToToMorphism : Homomorphism glue to
  preMorphism : Homomorphism rule.pre from
  glueMorphism : Homomorphism rule.glue glue
  postMorphism : Homomorphism rule.post to
  0 preComposition : preMorphism . rule.glueToPreMorphism = glueToFromMorphism . glueMorphism
  0 postComposition : postMorphism . rule.glueToPostMorphism = glueToToMorphism . glueMorphism

public export
record DoublePushoutNeg vertex edge where
  constructor MkDoublePushoutNeg
  rule : NegRewriteRule vertex edge
  from : Graph vertex edge
  to : Graph vertex edge
  glue : Graph vertex edge
  glueToFromMorphism : Homomorphism glue from
  glueToToMorphism : Homomorphism glue to
  glueMorphism : Homomorphism rule.glue glue
  preMorphism : Homomorphism rule.pre from
  postMorphism : Homomorphism rule.post to
  0 dontPreserve : Not (Homomorphism rule.neg from)

public export
record DoublePushoutInterface vertex edge where
  constructor MkDoublePushoutInterface
  pushout : DoublePushout vertex edge
  interface_ : Graph vertex edge
  interfaceToFromMorphism : Homomorphism interface_ pushout.from
  interfaceToGlueMorphism : Homomorphism interface_ pushout.glue
  interfaceToToMorphism : Homomorphism interface_ pushout.to
  0 preComposition : interfaceToFromMorphism = pushout.glueToFromMorphism . interfaceToGlueMorphism
  0 postComposition : interfaceToToMorphism = pushout.glueToToMorphism . interfaceToGlueMorphism

public export
record TypedRewriteRule vertex edge (0 type : Graph vertex edge) where
  constructor MkTypedRewriteRule
  pre : TypedGraph vertex edge type
  glue : TypedGraph vertex edge type
  post : TypedGraph vertex edge type
  glueToPreMorphism : Homomorphism glue pre
  glueToPostMorphism : Homomorphism glue post

public export
record TypedDoublePushout vertex edge (0 type : Graph vertex edge) where
  constructor MkTypedDoublePushout
  rule : TypedRewriteRule vertex edge type
  from : TypedGraph vertex edge type
  to : TypedGraph vertex edge type
  glue : TypedGraph vertex edge type
  glueToFromMorphism : Homomorphism glue from
  glueToToMorphism : Homomorphism glue to
  preMorphism : Homomorphism rule.pre from
  glueMorphism : Homomorphism rule.glue glue
  postMorphism : Homomorphism rule.post to
  0 preComposition : preMorphism . rule.glueToPreMorphism = glueToFromMorphism . glueMorphism
  0 postComposition : postMorphism . rule.glueToPostMorphism = glueToToMorphism . glueMorphism
