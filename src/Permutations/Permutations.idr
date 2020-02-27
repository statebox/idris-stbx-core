module Permutations.Permutations

import Permutations.Sandwich

%access public export
%default total

data Perm : {o : Type} -> List o -> List o -> Type where
  Nil : Perm [] []
  Ins : Perm as (l++r) -> Sandwich l a r lar -> Perm (a::as) lar

insInjective: Ins {l=l1} {r=r1} p1 s1 = Ins {l=l2} {r=r2} p2 s2 -> (l1 = l2, r1 = r2, p1 = p2, s1 = s2)
insInjective Refl = (Refl, Refl, Refl, Refl)

insCong : (as1 = as2) -> (l1 = l2) -> (r1 = r2) -> {p1 : Perm as1 (l1++r1)} -> {p2 : Perm as2 (l2++r2)} -> (p1 = p2)
       -> {s1 : Sandwich l1 a r1 lar1} -> {s2 : Sandwich l2 a r2 lar2} -> (s1 = s2)
       -> Ins {l=l1} {r=r1} p1 s1 = Ins {l=l2} {r=r2} p2 s2
insCong Refl Refl Refl Refl {s1} {s2} s = case (swEq s1, swEq s2, s) of
  (Refl, Refl, Refl) => Refl

rewriteRight : cs = bs -> Perm as bs -> Perm as cs
rewriteRight Refl p = p

rewriteRightIgnore : {p1 : Perm as bs} -> {p2 : Perm cs ds} -> p1 = p2 -> rewriteRight prf p1 = p2
rewriteRightIgnore Refl {prf=Refl} = Refl

rewriteRightIgnoreR : {p1 : Perm as bs} -> {p2 : Perm cs ds} -> p1 = p2 -> p1 = rewriteRight prf p2
rewriteRightIgnoreR Refl {prf=Refl} = Refl

rewriteLeft : cs = as -> Perm as bs -> Perm cs bs
rewriteLeft Refl p = p

rewriteLeftIgnore : {p1 : Perm as bs} -> {p2 : Perm cs ds} -> p1 = p2 -> rewriteLeft prf p1 = p2
rewriteLeftIgnore Refl {prf=Refl} = Refl

rewriteLeftIgnoreR : {p1 : Perm as bs} -> {p2 : Perm cs ds} -> p1 = p2 -> p1 = rewriteLeft prf p2
rewriteLeftIgnoreR Refl {prf=Refl} = Refl

permId : (as : List o) -> Perm as as
permId []      = Nil
permId (a::as) = Ins (permId as) HereS

swap : (l : List o) -> (r : List o) -> Perm (l ++ r) (r ++ l)
swap []      r = rewriteRight (appendNilRightNeutral r) (permId r)
swap (l::ls) r = Ins (swap ls r) (sandwich r)

swapAddIdR : (l : List o) -> (r : List o) -> (t : List o) -> Perm (l ++ r ++ t) (r ++ l ++ t)
swapAddIdR []      r t = permId (r ++ t)
swapAddIdR (l::ls) r t = Ins (swapAddIdR ls r t) (sandwich r)

permAdd : Perm as bs -> Perm cs ds -> Perm (as ++ cs) (bs ++ ds)
permAdd       Nil                p  = p
permAdd {ds} (Ins {l} {r} ab sw) cd = Ins {l=l} {r=r++ds} (rewriteRight (appendAssociative l r ds) $ permAdd ab cd) (appended ds sw)

permAddIdL : (as : List o) -> Perm bs cs -> Perm (as ++ bs) (as ++ cs)
permAddIdL  []     bc = bc
permAddIdL (a::as) bc = Ins (permAddIdL as bc) HereS

shuffle : Perm bs cs -> Sandwich l a r bs -> Perm (a :: l ++ r) cs
shuffle p            HereS      = p
shuffle (Ins bc sb) (ThereS sw) with (shuffle bc sw)
  | Ins bc' sa with (swComb sb sa)
    | BA {lb} {m} {ra} sa' sb' Refl = Ins (Ins (rewriteRight (      appendAssociative lb m ra) bc') sb') sa'
    | AB {la} {m} {rb} sa' sb' Refl = Ins (Ins (rewriteRight (sym $ appendAssociative la m rb) bc') sb') sa'

permComp : Perm as bs -> Perm bs cs -> Perm as cs
permComp  Nil         p  = p
permComp (Ins ab' sw) bc with (shuffle bc sw)
  | Ins bc' sw' = Ins (permComp ab' bc') sw'

permCompCong5 : as1 = as2 -> bs1 = bs2 -> cs1 = cs2
            -> {p1 : Perm as1 bs1} -> {p2 : Perm as2 bs2} -> {p3 : Perm bs1 cs1} -> {p4 : Perm bs2 cs2}
            -> p1 = p2 -> p3 = p4 -> permComp p1 p3 = permComp p2 p4
permCompCong5 Refl Refl Refl Refl Refl = Refl

permAddCong6 : as1 = as2 -> bs1 = bs2 -> cs1 = cs2 -> ds1 = ds2
            -> {p1 : Perm as1 bs1} -> {p2 : Perm as2 bs2} -> {p3 : Perm cs1 ds1} -> {p4 : Perm cs2 ds2}
            -> p1 = p2 -> p3 = p4 -> permAdd p1 p3 = permAdd p2 p4
permAddCong6 Refl Refl Refl Refl Refl Refl = Refl

permAddIdLCong4 : as1 = as2 -> bs1 = bs2 -> cs1 = cs2
               -> {p1 : Perm bs1 cs1} -> {p2 : Perm bs2 cs2}
               -> p1 = p2 -> permAddIdL as1 p1 = permAddIdL as2 p2
permAddIdLCong4 Refl Refl Refl Refl = Refl
