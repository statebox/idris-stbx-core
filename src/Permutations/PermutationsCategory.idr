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
  permCompRightId (Ins {l} {r} ab' sw) | Ins bc' sw' =
    let (Refl, Refl, Refl, Refl) = insInjective $ trans shprf (shuffleId sw) in
      rewrite permCompRightId ab' in Refl

shuffleComp : (sw : Sandwich l a r bs) -> (bc : Perm bs cs) -> (cd : Perm cs ds)
           -> Ins {l=lbd} {r=rbd} bd' sw' = shuffle (permComp bc cd) sw
           -> Ins bc' swbc = shuffle bc sw
           -> Ins {l=lcd} {r=rcd} cd' swcd = shuffle cd swbc
           -> (lbd = lcd, rbd = rcd, bd' = permComp bc' cd', sw' = swcd)
shuffleComp HereS (Ins _ HereS) (Ins _ _) Refl Refl Refl = (Refl, Refl, Refl, Refl)
shuffleComp HereS (Ins _ (ThereS swx)) (Ins _ _) _ Refl _ = ?c -- (Refl, Refl, Refl, Refl)
shuffleComp (ThereS swx) (Ins _ _) (Ins _ _) _ _ _ = ?d

permAssoc : (ab : Perm as bs) -> (bc : Perm bs cs) -> (cd : Perm cs ds)
         -> permComp ab (permComp bc cd) = permComp (permComp ab bc) cd
permAssoc Nil bc cd = Refl
permAssoc (Ins ab' sw) bc cd with (shuffle (permComp bc cd) sw) proof bdPrf
  | Ins bd' sw' with (shuffle bc sw) proof bcPrf
    | Ins bc' swbc with (shuffle cd swbc) proof cdPrf
      | Ins cd' swcd = let (Refl, Refl, Refl, Refl) = shuffleComp sw bc cd bdPrf bcPrf cdPrf in
        insCong Refl Refl Refl (permAssoc ab' bc' cd') Refl

permAddNilRightNeutral : (ab : Perm as bs) -> permAdd ab Nil = ab
permAddNilRightNeutral Nil = Refl
permAddNilRightNeutral {as=a::as1} (Ins {r} p s) =
  insCong (appendNilRightNeutral as1)
          Refl
          (appendNilRightNeutral r)
          (rewriteRightIgnore (permAddNilRightNeutral p))
          (appendedNilRightNeutral s)

permutationsCat : (o : Type) -> Category
permutationsCat o = MkCategory
  (List o)
  Perm
  permId
  (\_, _, _ => permComp)
  (\_, _ => permCompLeftId)
  (\_, _ => permCompRightId)
  (\_, _, _, _ => permAssoc)
