module Permutations.PermutationsCategory

import Basic.Category

import Permutations.Sandwich
import Permutations.Permutations

%access public export
%default total

permCompLeftId : (ab : Perm as bs) -> permComp (permId as) ab = ab
permCompLeftId  Nil         = Refl
permCompLeftId (Ins ab' sw) = cong {f=\p => Ins p sw} (permCompLeftId ab')

shuffleId : (sw : Sandwich l a r bs) -> shuffle (permId bs) sw = Ins (permId (l ++ r)) sw
shuffleId  HereS      = Refl
shuffleId (ThereS {ls} {rs} {lars} sw) with (shuffle {l=ls} {r=rs} (permId lars) sw) proof shprf
  shuffleId (ThereS {ls} {rs} {lars} sw) | Ins {l=ll} {r=rr} bc' sa with (swEq sa)
    shuffleId (ThereS {ls} {rs} {lars=ll ++ a :: rr} sw) | Ins bc' sa | Refl =
      let (Refl, Refl, Refl, Refl) = insInjective $ trans shprf (shuffleId sw) in Refl

permCompRightId : (ab : Perm as bs) -> permComp ab (permId bs) = ab
permCompRightId  Nil                 = Refl
permCompRightId {bs} (Ins {l} {r} ab' sw) with (shuffle (permId bs) sw) proof shprf
  | Ins bc' sw' =
    let (Refl, Refl, Refl, Refl) = insInjective $ trans shprf (shuffleId sw) in
      rewrite permCompRightId ab' in Refl

shuffleComp : (sw : Sandwich l a r bs) -> (bc : Perm bs cs) -> (cd : Perm cs ds)
           -> Ins bc' swbc = shuffle bc sw
           -> Ins {l=lcd} {r=rcd} cd' swcd = shuffle cd swbc
           -> Ins {l=lbd} {r=rbd} bd' sw' = shuffle (Permutations.permComp bc cd) sw
           -> (lbd = lcd, rbd = rcd, bd' = permComp bc' cd', sw' = swcd)
shuffleComp HereS       (Ins _ HereS)        (Ins _ _)    Refl Refl Refl = (Refl, Refl, Refl, Refl)
shuffleComp HereS       (Ins _ (ThereS swx)) (Ins cd1 sc) Refl eq1  eq2 with (shuffle cd1 swx)
  | Ins _ sb with (swComb sc sb)
    | BA _ _ Refl Refl with (eq1, eq2)
      | (Refl, Refl) = (Refl, Refl, Refl, Refl)
    | AB _ _ Refl Refl with (eq1, eq2)
      | (Refl, Refl) = (Refl, Refl, Refl, Refl)
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

shuffleComp  _ _ _  _    _    _    = ?catchall

permAssoc : (ab : Perm as bs) -> (bc : Perm bs cs) -> (cd : Perm cs ds)
         -> permComp ab (permComp bc cd) = permComp (permComp ab bc) cd
permAssoc Nil bc cd = Refl
permAssoc (Ins ab' sw) bc cd with (shuffle bc sw) proof bcPrf
  | Ins bc' swbc with (shuffle cd swbc) proof cdPrf
    | Ins cd' swcd with (shuffle (permComp bc cd) sw) proof bdPrf
      | Ins bd' sw' =
        let (Refl, Refl, Refl, Refl) = shuffleComp sw bc cd bcPrf cdPrf bdPrf in
        insCong Refl Refl Refl (permAssoc ab' bc' cd') Refl

permutationsCat : (o : Type) -> Category
permutationsCat o = MkCategory
  (List o)
  Perm
  permId
  (\as, bs, cs => permComp {as} {bs} {cs})
  (\_, _ => permCompLeftId)
  (\_, _ => permCompRightId)
  (\_, _, _, _ => permAssoc)
