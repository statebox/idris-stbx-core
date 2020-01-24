module Cartographer.Hypergraph

import Data.Fin
import Data.List

%access public export
%default total


--== Perm ==--

data Sandwich : List t -> t -> List t -> List t -> Type where
  HereS  : Sandwich [] a rs (a::rs)
  ThereS : Sandwich ls a rs lars -> Sandwich (l::ls) a rs (l::lars)

swEq : Sandwich l a r lar -> l ++ [a] ++ r = lar
swEq HereS = Refl
swEq (ThereS sw) = cong (swEq sw)

sandwich : (l : List t) -> Sandwich l a r (l ++ [a] ++ r)
sandwich []      = HereS
sandwich (l::ls) = ThereS (sandwich ls)

appended : Sandwich l a r lar -> Sandwich l a (r ++ s) (lar ++ s)
appended HereS = HereS
appended (ThereS sw) = ThereS (appended sw)

-- Sandwich2 ll l rl la a ra cs means ll ++ [l] ++ rl = cs and la ++ [a] ++ ra = ll ++ rl (i.e. cs without l)
data Sandwich2 : List t -> t -> List t -> List t -> t -> List t -> List t -> Type where
  There2 : Sandwich2 ll l rl la a ra cs -> Sandwich2 (x::ll) l rl (x::la) a ra (x::cs)
  HereL  : Sandwich la a ra cs -> Sandwich2 [] l cs la a ra (l::cs)
  HereA  : Sandwich ll l rl cs -> Sandwich2 (a::ll) l rl [] a (ll ++ rl) (a::cs)

swMerge : Sandwich ll l rl cs -> Sandwich la a ra (ll ++ rl) -> Sandwich2 ll l rl la a ra cs
swMerge HereS sa = HereL sa
swMerge {ll=a::ll'} (ThereS sl) HereS = HereA sl
swMerge {ll=x::ll'} {la=x::la'} (ThereS sl) (ThereS sa) = There2 (swMerge sl sa)

data Combined : List t -> t -> List t -> List t -> t -> List t -> List t -> Type where
  LA : Sandwich (ll ++ [l] ++ m) a ra cs
    -> Sandwich ll l (m ++ ra) ((ll ++ [l] ++ m) ++ ra)
    -> m ++ [a] ++ ra = rl
    -> ll ++ m = la
    -> Combined ll l rl la a ra cs
  AL : Sandwich la a (m ++ [l] ++ rl) cs
    -> Sandwich (la ++ m) l rl (la ++ (m ++ [l] ++ rl))
    -> la ++ [a] ++ m = ll
    -> m ++ rl = ra
    -> Combined ll l rl la a ra cs

sandwich2Combined : Sandwich2 ll l rl la a ra cs -> Combined ll l rl la a ra cs
sandwich2Combined (HereL sa) = LA (ThereS sa) HereS (swEq sa) Refl
sandwich2Combined (HereA sl) = case swEq sl of Refl => AL HereS sl Refl Refl
sandwich2Combined (There2 s2) = case sandwich2Combined s2 of
  LA sa sl Refl Refl => LA (ThereS sa) (ThereS sl) Refl Refl
  AL sa sl Refl Refl => AL (ThereS sa) (ThereS sl) Refl Refl

data Perm : {o : Type} -> List o -> List o -> Type where
  Nil : Perm [] []
  Ins : Perm as (l++r) -> Sandwich l a r lar -> Perm (a::as) lar

permId : (as : List o) -> Perm as as
permId []      = Nil
permId (a::as) = Ins (permId as) HereS

swap : (l : List o) -> (r : List o) -> Perm (l ++ r) (r ++ l)
swap []      r = rewrite appendNilRightNeutral r in permId r
swap (l::ls) r = Ins (swap ls r) (sandwich r)

permAdd : Perm as bs -> Perm cs ds -> Perm (as ++ cs) (bs ++ ds)
permAdd Nil p = p
permAdd {ds} (Ins {l} {r} {a} ab sw) cd = Ins {l=l} {r=r++ds} (rewrite appendAssociative l r ds in permAdd ab cd) (appended sw)

data Deleted : List t -> t -> List t -> List t -> Type where
  Del : Perm (l ++ r) (l' ++ r') -> Sandwich l' a r' cs -> Deleted l a r cs

rewriteRight : bs = cs -> Perm as bs -> Perm as cs
rewriteRight r p = rewrite sym r in p

delete : Sandwich l a r bs -> Perm bs cs -> Deleted l a r cs
delete HereS       (Ins bc sw) = Del bc sw
delete (ThereS sw) (Ins bc sl) =
  case delete sw bc of
    Del bc' sa =>
      case sandwich2Combined (swMerge sl sa) of
        LA {ra} {m} {ll} sa' sl' Refl Refl => Del (Ins (rewriteRight (sym $ appendAssociative ll m ra) bc') sl') sa'
        AL {la} {m} {rl} sa' sl' Refl Refl => Del (Ins (rewriteRight (      appendAssociative la m rl) bc') sl') sa'

permComp : {o : Type} -> Perm {o} as bs -> Perm bs cs -> Perm as cs
permComp Nil p = p
permComp (Ins ab' sw) bc =
  case delete sw bc of Del bc' sw' => Ins (permComp ab' bc') sw'

--== Hypergraph ==--

sumArity : {h : Nat} -> (f : Fin h -> List o) -> List o
sumArity {h=Z} _ = []
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
coprodFin {m = Z} _ r i = r i
coprodFin {m = S m'} l r FZ = l FZ
coprodFin {m = S m'} l r (FS i) = coprodFin {m = m'} (l . FS) r i

coprod
   : {s : Type} -> {a : s -> List o} -> {h1 : Nat} -> {h2 : Nat} -> {t1 : Fin h1 -> s} -> {t2 : Fin h2 -> s}
  -> sumArity (a . t1) ++ sumArity (a . t2) = sumArity (a . coprodFin t1 t2)
coprod {h1=Z} {a} {t2} = Refl
coprod {h1=S h} {t1} = sym (appendAssociative _ _ _) `trans` cong (coprod {h1=h} {t1=t1 . FS})

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
