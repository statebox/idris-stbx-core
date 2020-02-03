module Permutations.Sandwich

%access public export
%default total

data Sandwich : List t -> t -> List t -> List t -> Type where
  HereS  : Sandwich [] a rs (a::rs)
  ThereS : Sandwich ls a rs lars -> Sandwich (l::ls) a rs (l::lars)

Uninhabited (Sandwich ls a rs []) where
  uninhabited HereS impossible
  uninhabited (ThereS s) impossible

swEq : Sandwich l a r lar -> l ++ [a] ++ r = lar
swEq  HereS      = Refl
swEq (ThereS sw) = cong (swEq sw)

congHereS : (rs1 = rs2) -> (HereS {a} {rs=rs1} = HereS {a} {rs=rs2})
congHereS Refl = Refl

congThereS : {t : Type} -> {l : t} -> (ls1 = ls2) -> (rs1 = rs2) -> (lars1 = lars2)
          -> {sw1 : Sandwich ls1 a rs1 lars1} -> {sw2 : Sandwich ls2 a rs2 lars2}
          -> (sw1 = sw2) -> ThereS {ls=ls1} {a} {rs=rs1} {lars=lars1} {l} sw1 = ThereS {ls=ls2} {a} {rs=rs2} {lars=lars2} {l} sw2
congThereS Refl Refl Refl Refl = Refl

sandwich : (l : List t) -> Sandwich l a r (l ++ [a] ++ r)
sandwich []      = HereS
sandwich (l::ls) = ThereS (sandwich ls)

appended : (s : List t) -> Sandwich l a r lar -> Sandwich l a (r ++ s) (lar ++ s)
appended _  HereS      = HereS
appended s (ThereS sw) = ThereS (appended s sw)

appendedNilNeutral : (sw: Sandwich l a r lar) -> appended [] sw = sw
appendedNilNeutral (HereS {rs}) = congHereS (appendNilRightNeutral rs)
appendedNilNeutral (ThereS {lars} {rs} sw) =
  congThereS Refl (appendNilRightNeutral rs) (appendNilRightNeutral lars) (appendedNilNeutral sw)

appendedAppendDistr : (as, bs : List t) -> (sw: Sandwich l a r lar) -> appended (as ++ bs) sw = appended bs (appended as sw)
appendedAppendDistr as bs (HereS {rs}) = congHereS (appendAssociative rs as bs)
appendedAppendDistr as bs (ThereS {rs} {lars} sw) =
  congThereS Refl (appendAssociative rs as bs) (appendAssociative lars as bs) (appendedAppendDistr as bs sw)

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
