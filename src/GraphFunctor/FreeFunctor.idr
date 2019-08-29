module GraphFunctor.FreeFunctor

import Basic.Category
import Basic.Functor
import GraphFunctor.Graph

%access public export
%default total

record GraphEmbedding (g : Graph) (cat : Category) where
  constructor MkGraphEmbedding
  mapVertices : vertices g -> obj cat
  mapEdges    : (i, j : vertices g) -> edges g i j -> mor cat (mapVertices i) (mapVertices j)

foldPath :
     (g : Graph)
  -> (ge : GraphEmbedding g cat)
  -> Path g i j
  -> mor cat (mapVertices ge i) (mapVertices ge j)
foldPath _ {cat} ge {i} []              = identity cat (mapVertices ge i)
foldPath g {cat} ge {i} ((::) {j} x xs) = compose cat _ _ _ (mapEdges ge i j x) (foldPath g ge xs)

freeFunctorCompose :
     (g : Graph)
  -> (ge : GraphEmbedding g cat)
  -> (i, j, k : vertices g)
  -> (f : Path g i j)
  -> (h : Path g j k)
  -> foldPath g ge {i} {j = k} (joinPath f h)
   = compose cat
             (mapVertices ge i)
             (mapVertices ge j)
             (mapVertices ge k)
             (foldPath g ge {i} {j} f)
             (foldPath g ge {i = j} {j = k} h)
freeFunctorCompose g {cat} ge j j k [] h = sym $ leftIdentity cat
                                                              (mapVertices ge j)
                                                              (mapVertices ge k)
                                                              (foldPath g ge h)
freeFunctorCompose g {cat} ge i j k ((::) {j=l} x xs) h =
  trans (cong {f = compose cat _ _ _ (mapEdges ge i l x)} $ freeFunctorCompose g ge _ _ _ xs h)
        (associativity cat _ _ _ _ (mapEdges ge i l x) (foldPath g ge xs) (foldPath g ge h))

freeFunctor : (g : Graph) -> GraphEmbedding g cat -> CFunctor (pathCategory g) cat
freeFunctor g ge = MkCFunctor
  (mapVertices ge)
  (\i, j, p => foldPath g ge {i} {j} p)
  (\_ => Refl)
  (freeFunctorCompose g ge)