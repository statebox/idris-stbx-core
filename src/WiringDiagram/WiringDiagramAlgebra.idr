module WiringDiagram.WiringDiagramAlgebra

import PointedTypes.PointedTypesCategory
import WiringDiagram.WiringDiagram

%access public export
%default total

-- SEMANTICS
-- A lax monoidal functor (W_C, \tensor, I) -> (Cat, \times, 1) takes boxes and assigns a category of inhabitants
-- X = (X_1, X_2) -> F X
-- given a wiring diagram \phi, F X \times F Y \times F Z -- laxator -> F (X \tensor Y \tensor Z) -> F \phi

-- Standard types and functions do not work with this

-- functionsFunctorOnObjects : (Type, Type) -> Type
-- functionsFunctorOnObjects (a, b) = a -> b
--
-- functionsFunctorOnMorphisms : (a, b : (Type, Type)) -> WiringDiagramMorphism a b -> ((functionsFunctorOnObjects a) -> (functionsFunctorOnObjects b))
-- functionsFunctorOnMorphisms
--   (a1, a2)
--   (b1, b2)
--   (MkWiringDiagramMorphism f1 f2)
--   g
--   = ?functionsFunctorOnMorphisms_rhs_2 -- we have only a b_1, we need also an a_2 to apply f_1
--
-- functionsFunctor : CFunctor WiringDiagram.wiringDiagramCategory TypesAsCategory.typesAsCategory
-- functionsFunctor = MkCFunctor
--   functionsFunctorOnObjects
--   functionsFunctorOnMorphisms

-- next we try with pointed types
-- in this case we use C in W_C to be the category on PointedTypes

pointedTensor : PointedObject -> PointedObject -> PointedObject
pointedTensor (a' ** x) (b' ** y) = ((a', b') ** (x, y))

data PointedWiringDiagramMorphism : (PointedObject, PointedObject) -> (PointedObject, PointedObject) -> Type where
  MkPointedWiringDiagramMorphism :
       {a, b : (PointedObject, PointedObject)}
    -> PointedMorphism (pointedTensor (fst b) (snd a)) (fst a)
    -> PointedMorphism (snd a) (snd b)
    -> PointedWiringDiagramMorphism a b

pointedFunctorOnObjects : (a : (PointedObject, PointedObject)) -> Type
pointedFunctorOnObjects (a1, a2) = PointedMorphism a1 a2

pointedFunctorOnMorphisms : (a, b : (PointedObject, PointedObject)) -> PointedWiringDiagramMorphism a b -> (pointedFunctorOnObjects a) -> (pointedFunctorOnObjects b)
pointedFunctorOnMorphisms
  ((a1' ** x1), (a2' ** x2))
  ((b1' ** y1), (b2' ** y2))
  (MkPointedWiringDiagramMorphism
    (MkPointedMorphism (y1, x2) x1 f1 f1x1y1x2)
    (MkPointedMorphism x2 y2 f2 f2x2y2)
  )
  (MkPointedMorphism x1 x2 g gx1x2)
  = MkPointedMorphism
    y1
    y2
    (\z => (f2 . g . f1) (z, x2))
    (trans (cong {f = f2} (trans (cong {f = g} f1x1y1x2) gx1x2)) f2x2y2)
