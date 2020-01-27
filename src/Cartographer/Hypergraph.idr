module Cartographer.Hypergraph

import Data.Fin
import Data.List

%access public export
%default total

--== Sandwich ==--

data Sandwich : List t -> t -> List t -> List t -> Type where
  HereS  : Sandwich [] a rs (a::rs)
  ThereS : Sandwich ls a rs lars -> Sandwich (l::ls) a rs (l::lars)

Uninhabited (Sandwich ls a rs []) where
  uninhabited HereS impossible
  uninhabited (ThereS s) impossible

swEq : Sandwich l a r lar -> l ++ [a] ++ r = lar
swEq  HereS      = Refl
swEq (ThereS sw) = cong (swEq sw)

sandwich : (l : List t) -> Sandwich l a r (l ++ [a] ++ r)
sandwich []      = HereS
sandwich (l::ls) = ThereS (sandwich ls)

appended : Sandwich l a r lar -> Sandwich l a (r ++ s) (lar ++ s)
appended  HereS      = HereS
appended (ThereS sw) = ThereS (appended sw)

-- Sandwich2 lb b rb la a ra cs means lb ++ [b] ++ rb = cs and la ++ [a] ++ ra = lb ++ rb (i.e. cs without b)
-- It contains 2 sandwiches, one which points to `a` into `cs` and one which points to `b` into `cs` without `a`
-- So it swaps the order of inserting of `b` and `a`
data Sandwich2 : List t -> t -> List t -> List t -> t -> List t -> List t -> Type where
  -- cs = lb ++ [b] ++ m ++ [a] ++ ra
  BA : Sandwich (lb ++ [b] ++ m) a ra cs
    -> Sandwich lb b (m ++ ra) ((lb ++ [b] ++ m) ++ ra)
    -> m ++ [a] ++ ra = rb
    -> lb ++ m = la
    -> Sandwich2 lb b rb la a ra cs
  -- cs = la ++ [a] ++ m ++ [b] ++ rb
  AB : Sandwich la a (m ++ [b] ++ rb) cs
    -> Sandwich (la ++ m) b rb (la ++ (m ++ [b] ++ rb))
    -> la ++ [a] ++ m = lb
    -> m ++ rb = ra
    -> Sandwich2 lb b rb la a ra cs

swComb : Sandwich lb b rb cs -> Sandwich la a ra (lb ++ rb) -> Sandwich2 lb b rb la a ra cs
swComb                          HereS       sa         = BA (ThereS sa) HereS (swEq sa) Refl
swComb {lb=a::lb'}             (ThereS sb)  HereS      = case swEq sb of Refl => AB HereS sb Refl Refl
swComb {lb=x::lb'} {la=x::la'} (ThereS sb) (ThereS sa) = case swComb sb sa of
  BA sa sb Refl Refl => BA (ThereS sa) (ThereS sb) Refl Refl
  AB sa sb Refl Refl => AB (ThereS sa) (ThereS sb) Refl Refl

--== Perm ==--

data Perm : {o : Type} -> List o -> List o -> Type where
  Nil : Perm [] []
  Ins : Perm as (l++r) -> Sandwich l a r lar -> Perm (a::as) lar

insInjective: Ins {l=l1} {r=r1} p1 s1 = Ins {l=l2} {r=r2} p2 s2 -> (l1 = l2, r1 = r2, p1 = p2, s1 = s2)
insInjective Refl = (Refl, Refl, Refl, Refl)

permId : (as : List o) -> Perm as as
permId []      = Nil
permId (a::as) = Ins (permId as) HereS

swap : (l : List o) -> (r : List o) -> Perm (l ++ r) (r ++ l)
swap []      r = rewrite appendNilRightNeutral r in permId r
swap (l::ls) r = Ins (swap ls r) (sandwich r)

permAdd : Perm as bs -> Perm cs ds -> Perm (as ++ cs) (bs ++ ds)
permAdd       Nil                p  = p
permAdd {ds} (Ins {l} {r} ab sw) cd = Ins {l=l} {r=r++ds} (rewrite appendAssociative l r ds in permAdd ab cd) (appended sw)

rewriteRight : cs = bs -> Perm as bs -> Perm as cs
rewriteRight Refl p = p

shuffle : Perm bs cs -> Sandwich l a r bs -> Perm (a :: l ++ r) cs
shuffle (Ins bc sw)  HereS      = Ins bc sw
shuffle (Ins bc sb) (ThereS sw) with (shuffle bc sw)
  | Ins bc' sa with (swComb sb sa)
    | BA {lb} {m} {ra} sa' sb' Refl Refl = Ins (Ins (rewriteRight (      appendAssociative lb m ra) bc') sb') sa'
    | AB {la} {m} {rb} sa' sb' Refl Refl = Ins (Ins (rewriteRight (sym $ appendAssociative la m rb) bc') sb') sa'

permComp : Perm as bs -> Perm bs cs -> Perm as cs
permComp  Nil         p  = p
permComp (Ins ab' sw) bc =
  case shuffle bc sw of Ins bc' sw' => Ins (permComp ab' bc') sw'

permCompLeftId : (ab : Perm as bs) -> permComp (permId as) ab = ab
permCompLeftId  Nil         = Refl
permCompLeftId (Ins ab' sw) = cong {f=\p => Ins p sw} (permCompLeftId ab')

shuffleId : (sw : Sandwich l a r bs) -> shuffle (permId bs) sw = Ins (permId (l ++ r)) sw
shuffleId  HereS      = Refl
shuffleId (ThereS {ls} {rs} {lars} sw) with (shuffle {l=ls} {r=rs} (permId lars) sw) proof shprf
  shuffleId (ThereS {ls} {rs} {lars} sw) | Ins {l=ll} {r=rr} bc' sa with (swEq sa)
    shuffleId (ThereS {ls} {rs} {lars=ll ++ a :: rr} sw) | Ins {l=ll} {r=rr} bc' sa | Refl =
      let (Refl, Refl, Refl, Refl) = insInjective $ trans shprf (shuffleId sw) in Refl

permCompRightId : (ab : Perm as bs) -> permComp ab (permId bs) = ab
permCompRightId  Nil                 = Refl
permCompRightId {bs} (Ins {l} {r} ab' sw) with (shuffle (permId bs) sw) proof shprf
  permCompRightId (Ins {l} {r} ab' sw) | Ins bc' sw' =
    let (Refl, Refl, Refl, Refl) = insInjective $ trans shprf (shuffleId sw) in
      rewrite permCompRightId ab' in Refl

--== Hypergraph ==--

sumArity : {h : Nat} -> (f : Fin h -> List o) -> List o
sumArity {h=Z}   _ = []
sumArity {h=S n} f = f FZ ++ sumArity {h=n} (f . FS)

record Hypergraph (sigma : Type) (arityIn : sigma -> List o) (arityOut : sigma -> List o) (k : List o) (m : List o) where
  constructor MkHypergraph
  -- HyperEdge count
  h : Nat
  Typ : Fin h -> sigma
  wiring : Perm (k ++ sumArity (arityOut . Typ)) (m ++ sumArity (arityIn . Typ))

singleton : {s : Type} -> {ai, ao : s -> List o} -> (edge : s) -> Hypergraph s ai ao (ai edge) (ao edge)
singleton edge = MkHypergraph 1 (const edge) perm
  where
    perm : Perm (ai edge ++ ao edge ++ []) (ao edge ++ ai edge ++ [])
    perm = rewrite appendNilRightNeutral (ao edge) in
           rewrite appendNilRightNeutral (ai edge) in
             swap (ai edge) (ao edge)

identity : {s : Type} -> {ai, ao : s -> List o} -> (n : List o) -> Hypergraph s ai ao n n
identity n = MkHypergraph 0 FinZElim (rewrite appendNilRightNeutral n in permId n)

coprodFin : {m : Nat} -> {n : Nat} -> (Fin m -> a) -> (Fin n -> a) -> Fin (m + n) -> a
coprodFin {m = Z}    _ r   i    = r i
coprodFin {m = S m'} l r  FZ    = l FZ
coprodFin {m = S m'} l r (FS i) = coprodFin {m = m'} (l . FS) r i

coprod
   : {s : Type} -> {a : s -> List o} -> {h1 : Nat} -> {h2 : Nat} -> {t1 : Fin h1 -> s} -> {t2 : Fin h2 -> s}
  -> sumArity (a . t1) ++ sumArity (a . t2) = sumArity (a . coprodFin t1 t2)
coprod {h1=Z}   {a} {t2} = Refl
coprod {h1=S h}     {t1} = sym (appendAssociative _ _ _) `trans` cong (coprod {h1=h} {t1=t1 . FS})

compose : (g1 : Hypergraph s ai ao k m) -> (g2 : Hypergraph s ai ao m n) -> Hypergraph s ai ao k n
compose (MkHypergraph h1 t1 c1) (MkHypergraph h2 t2 c2) = MkHypergraph
  (h1 + h2)
  (coprodFin t1 t2)
  perm
  where
    helper2 : Perm (m ++ s2) (n ++ f2) -> Perm ((m ++ f1) ++ s2) (n ++ (f2 ++ f1))
    helper2 {s2} {f1} {f2} c2 =
      rewrite sym $ appendAssociative m f1 s2 in
      rewrite appendAssociative n f2 f1 in
        permComp (permId m `permAdd` swap f1 s2)
        (rewrite appendAssociative m s2 f1 in
          c2 `permAdd` permId f1)

    helper : Perm (k ++ s1) (m ++ f1) -> Perm (m ++ s2) (n ++ f2) -> s1 ++ s2 = s12 -> f1 ++ f2 = f12 -> Perm (k ++ s12) (n ++ f12)
    helper {s1} {s2} {f1} {f2} c1 c2 cps cpf =
      rewrite sym cps in
      rewrite sym cpf in
      rewrite appendAssociative k s1 s2 in
        (c1 `permAdd` permId s2) `permComp` helper2 c2 `permComp` (permId n `permAdd` swap f2 f1)

    perm : Perm (k ++ sumArity (ao . coprodFin t1 t2)) (n ++ sumArity (ai . coprodFin t1 t2))
    perm = helper c1 c2 coprod coprod

zero : {s : Type} -> {ai, ao : s -> List o} -> Hypergraph s ai ao [] []
zero = identity []

add : Hypergraph s ai ao k l -> Hypergraph s ai ao m n -> Hypergraph s ai ao (k ++ m) (l ++ n)
add {k} {l} {m} {n} (MkHypergraph h1 t1 c1) (MkHypergraph h2 t2 c2) = MkHypergraph
  (h1 + h2)
  (coprodFin t1 t2)
  perm
  where
    helper2 : Perm ((a ++ b) ++ (c ++ d)) ((a ++ c) ++ (b ++ d))
    helper2 {a} {b} {c} {d} =
      rewrite appendAssociative (a ++ b) c d in
      rewrite appendAssociative (a ++ c) b d in
      rewrite sym $ appendAssociative a b c in
      rewrite sym $ appendAssociative a c b in
      (permId a `permAdd` swap b c) `permAdd` permId d

    helper : Perm (k ++ s1) (l ++ f1) -> Perm (m ++ s2) (n ++ f2) -> s1 ++ s2 = s12 -> f1 ++ f2 = f12 -> Perm ((k ++ m) ++ s12) ((l ++ n) ++ f12)
    helper {s1} {s2} {f1} {f2} c1 c2 cps cpf =
      rewrite sym cps in
      rewrite sym cpf in
        helper2 `permComp` ((c1 `permAdd` c2) `permComp` helper2)

    perm : Perm ((k ++ m) ++ sumArity (ao . coprodFin t1 t2)) ((l ++ n) ++ sumArity (ai . coprodFin t1 t2))
    perm = helper c1 c2 coprod coprod
