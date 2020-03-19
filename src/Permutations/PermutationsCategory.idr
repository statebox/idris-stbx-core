module Permutations.PermutationsCategory

import Basic.Category

import Permutations.Sandwich
import Permutations.Permutations

%access public export
%default total

permCompLeftId : (ab : Perm as bs) -> permComp (permId as) ab = ab
permCompLeftId  Nil         = Refl
permCompLeftId (Ins ab' sw) = cong {f=\p => Ins p sw} (permCompLeftId ab')

shuffleId : (aab : Sandwich (a::as) bs) -> shuffle aab (permId bs) = Ins (permId as) aab
shuffleId  HereS      = Refl
shuffleId (ThereS {bs} aab) with (shuffle aab (permId bs)) proof shprf
  | Ins ay ayb = case insInjective $ trans shprf (shuffleId aab) of (Refl, Refl, Refl) => Refl

permCompRightId : (ab : Perm as bs) -> permComp ab (permId bs) = ab
permCompRightId  Nil                 = Refl
permCompRightId {bs} (Ins ab' sw) with (shuffle sw (permId bs)) proof shprf
  | Ins bc' sw' = case insInjective $ trans shprf (shuffleId sw) of
    (Refl, Refl, Refl) => rewrite permCompRightId ab' in Refl

shuffleComp : (ab : Sandwich as bs) -> (bc : Perm bs cs) -> (cd : Perm cs ds)
           -> Ins bc' acc = shuffle abb bc
           -> Ins {ys=ds1} cd' ad'd = shuffle acc cd
           -> Ins {ys=ds2} bd' add = shuffle abb (permComp bc cd)
           -> (ds1 = ds2, bd' = permComp bc' cd', add = ad'd)
-- shuffleComp HereS       (Ins _ HereS)        (Ins _ _)    Refl Refl Refl = (Refl, Refl, Refl)
-- shuffleComp HereS       (Ins _ (ThereS swx)) (Ins cd1 sc) Refl eq1  eq2 with (shuffle cd1 swx)
--   | Ins _ sb with (swComb sc sb)
--     | BA _ _ Refl with (eq1, eq2)
--       | (Refl, Refl) = (Refl, Refl, Refl, Refl)
--     | AB _ _ Refl with (eq1, eq2)
--       | (Refl, Refl) = (Refl, Refl, Refl, Refl)
-- shuffleComp (ThereS swx) (Ins bc1 HereS)       (Ins cd1 sc) eq1  eq2  eq3 with (shuffle bc1 swx) proof bcPrf
--   | Ins bc2 swbc1 with (swEq swbc1)
--     | Refl with (eq1)
--       | Refl with (shuffle cd1 swbc1) proof cdPrf
--         | Ins cd2 swcd1 with (swComb sc swcd1)
--           | BA _ _ Refl Refl with (eq2)
--             -- | Refl with (shuffle (permComp bc1 cd1) swx) proof bdPrf
--             --   | Ins bd2 sw2 with (permComp bc1 cd1)
--             --     | Ins bd3 sw3 with (swComb sc sw2)
--             --       | BA _ _ refl Refl = ?dd11
--             --       | AB _ _ Refl Refl with (eq3)
--                     | Refl = ?dd12
--           | AB _ _ Refl Refl = ?dd2
-- shuffleComp (ThereS swx) (Ins bc1 HereS)       (Ins cd1 sc) eq1  eq2  eq3 {cd'} with (shuffle bc1 swx) proof bcPrf
--   | Ins bc2 swbc1 with (shuffle cd1 swbc1) proof cdPrf
--     | Ins cd2 swcd1 with (shuffle (permComp bc1 cd1) swx) proof bdPrf
--       | Ins bd2 sw2 with (swComb sc sw2)
--         | BA sa sb Refl Refl with (eq3)
--           | Refl with (swEq swbc1)
--             | Refl with (eq1)
--               | Refl with (cd')
--                 | Ins cd'' swcd'' = let (Refl, Refl, Refl, Refl) = shuffleComp swx bc1 cd1 bcPrf cdPrf bdPrf in ?dd
--         | AB sa sb Refl Refl with (eq3)
--           | Refl with (swEq swbc1)
--             | Refl with (eq1)
--               | Refl with (cd')
--                 | Ins cd'' swcd'' = ?dd1
-- shuffleComp {swbc} (ThereS sw1) (Ins bc1 swx) (Ins cd1 sc) eq1    eq2    eq3    with (shuffle bc1 sw1) proof bcPrf
--   | Ins bc2 swbc1 with (swComb swx swbc1)
--     | BA _ _ Refl Refl with (eq1)
--       | Refl = ?dd2
--     | AB _ _ Refl Refl = ?dd3

-- shuffleComp  _ _ _  _    _    _    = ?catchall

permAssoc : (ab : Perm aas bbs) -> (bc : Perm bbs ccs) -> (cd : Perm ccs dds)
         -> permComp ab (permComp bc cd) = permComp (permComp ab bc) cd
permAssoc Nil bc cd = Refl
permAssoc (Ins {xs=as} {ys=bs} ab' abb) bc cd with (shuffle abb (permComp bc cd)) proof bdPrf
  | Ins {ys=ds} bd' add with (shuffle abb bc) proof bcPrf
    | Ins {ys=cs} bc' acc with (shuffle acc cd) proof cdPrf
      | Ins {ys=ds1} cd1 ad1d =
        let (Refl, Refl, Refl) = shuffleComp abb bc cd bcPrf cdPrf bdPrf in
        insCong Refl Refl Refl (permAssoc ab' bc' cd1) Refl

permutationsCat : (o : Type) -> Category
permutationsCat o = MkCategory
  (List o)
  Perm
  permId
  (\as, bs, cs => permComp {as} {bs} {cs})
  (\_, _ => permCompLeftId)
  (\_, _ => permCompRightId)
  (\_, _, _, _ => permAssoc)
