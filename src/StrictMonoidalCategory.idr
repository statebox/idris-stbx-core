module MonoidalCategory

import Category
import Functor
import ProductCategory

%access public export
%default total

data StrictMonoidalCategory : (obj : Type) -> (mor : obj -> obj -> Type) -> Type where
  MkStrictMonoidalCategory :
       (cat : VerifiedCategory obj mor)
    -> (tfun : CFunctor (productVerifiedCategory cat cat) cat)
    -> (unit : obj)
    -> (tensorIsLUnital : (a : obj) -> (mapObj tfun) (unit, a) = a)
    -> (tensorIsRUnital : (a : obj) -> (mapObj tfun) (a, unit) = a)
    -> (tensorIsAssociativeObj : (a, b, c : obj) -> let m = mapObj tfun in
                                 m (a, m (b, c)) = m (m (a, b), c))
    -> (tensorIsAssociativeMor : (a, b, c, d, e, f : obj)
                              -> (g : mor a b)
                              -> (h : mor c d)
                              -> (k : mor e f)
                              -> let
                                   mo = mapObj tfun
                                   mm = mapMor tfun
                                  in
                                mm (a, mo (c,e)) (b, mo (d,f)) (MkProductMorphism g (mm (c,e) (d,f) (MkProductMorphism h k)))
                              = mm (mo (a,c), e) (mo (b,d), f) (MkProductMorphism (mm (a,c) (b,d) (MkProductMorphism g h)) k)
                              )
    -> StrictMonoidalCategory obj mor
