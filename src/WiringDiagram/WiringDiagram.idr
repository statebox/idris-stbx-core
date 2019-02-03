module WiringDiagram.WiringDiagram

-- inspired by the talk Systems as Wiring Diagram Algebras by Christina Vasilakopoulou
-- https://www.youtube.com/watch?v=dEDtaJhgQOY

import Category
import Utils

%access public export
%default total

-- W_C symmetric monoidal category of C-labeled boxes and wiring diagrams

-- fix C finitely complete category (finite products are enough). We are going to use Types and functions as our category C

-- objects are pairs X = (X_1, X_2) \in C \times C

-- morphisms \phi : (X_1, X_2) -> (Y_1, Y_2) are pairs of morphisms in C
-- \phi_1 : Y_1 \times X_2 -> X_1
-- \phi_2 : X_2 -> Y_2

data WiringDiagramMorphism : (Type, Type) -> (Type, Type) -> Type where
  MkWiringDiagramMorphism :
       {a, b : (Type, Type)}
    -> ((fst b, snd a) -> fst a)
    -> (snd a -> snd b)
    -> WiringDiagramMorphism a b

-- composition between two morphisms \phi = (\phi_1, \phi_2) : (X_1, X_2) -> (Y_1, Y_2) and \psi = (\psi_1, \psi_2) : (Y_1, Y_2) -> (Z_1, Z_2) is given by
-- (\phi ; \psi)_1 = 1 \times \Delta ; 1 \times \phi_2 \times 1 ; \psi_2 \times id ; \phi_2
-- (\phi ; \psi)_2 = \phi_2 ; \psi_2

delta : a -> (a, a)
delta x = (x, x)

pairMorphism : (a -> b) -> (c -> d) -> ((a, c) -> (b, d))
pairMorphism f g (x, y) = (f x, g y)

tupleAssociativity : (a, b ,c) -> ((a, b), c)
tupleAssociativity (x, y, z) = ((x, y), z)

compose :
     (a, b, c : (Type, Type))
  -> (f : WiringDiagramMorphism a b)
  -> (g : WiringDiagramMorphism b c)
  -> WiringDiagramMorphism a c
compose _ _ _ (MkWiringDiagramMorphism f1 f2) (MkWiringDiagramMorphism g1 g2)
  = MkWiringDiagramMorphism
    (f1 . (pairMorphism g1 id) . tupleAssociativity . (pairMorphism id (pairMorphism f2 id)) . (pairMorphism id delta))
    (g2 . f2)

-- the identity on (X_1, X_2) is (fst, id)

identity : (a : (Type, Type)) -> WiringDiagramMorphism a a
identity a = MkWiringDiagramMorphism fst id

-- this componition and identity form a category

wiringDiagramCategory : Category (Type, Type) WiringDiagramMorphism
wiringDiagramCategory = MkCategory identity compose

-- the tensor product between object is given by parallel placement of boxes

tensor : (a, b : (Type, Type)) -> (Type, Type)
tensor (a1, a2) (b1, b2) = ((a1, b1), (a2, b2))

-- tensor unit is given by (Unit, Unit)

unit : (Type, Type)
unit = ((), ())

-- serial composition
-- suppose X = (A, B) and Y = (B, C), we want to obtain a wiring diagram going to Z = (A, C) which represents the serial composition of X and Y
-- we do that by placing the two boxes in parallel and using the output of the first as feedback of the second
-- \phi : X \tensor Y -> Z
-- with
-- \phi_1 = \pi_12
-- \phi_2 = \pi_2

serial : (a, b, c : Type) -> WiringDiagramMorphism ((a, b), (b, c)) (a, c)
serial a b c = MkWiringDiagramMorphism (map fst) snd
