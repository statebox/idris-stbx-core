module Permutations.Sandwich

%access public export
%default total

data Sandwich : List t -> List t -> Type where
  HereS  : Sandwich (a::as) (a::as)
  ThereS : Sandwich (a::as) bs -> Sandwich (a::b::as) (b::bs)

congHereS : (as1 = as2) -> (HereS {a} {as=as1} = HereS {a} {as=as2})
congHereS Refl = Refl

congThereS : {t : Type} -> {b : t} -> (as1 = as2) -> (bs1 = bs2)
          -> {sw1 : Sandwich (a::as1) bs1} -> {sw2 : Sandwich (a::as2) bs2}
          -> (sw1 = sw2) -> ThereS {a} {b} {as=as1} {bs=bs1} sw1 = ThereS {a} {b} {as=as2} {bs=bs2} sw2
congThereS Refl Refl Refl = Refl

sandwich : (l : List t) -> Sandwich ([a] ++ l ++ r) (l ++ [a] ++ r)
sandwich []      = HereS
sandwich (l::ls) = ThereS (sandwich ls)

appended : (s : List t) -> Sandwich as bs -> Sandwich (as ++ s) (bs ++ s)
appended _  HereS      = HereS
appended s (ThereS sw) = ThereS (appended s sw)

appendedNilNeutral : (sw: Sandwich as bs) -> appended [] sw = sw
appendedNilNeutral (HereS {as}) = congHereS (appendNilRightNeutral as)
appendedNilNeutral (ThereS {as} {bs} sw) =
  congThereS (appendNilRightNeutral as) (appendNilRightNeutral bs) (appendedNilNeutral sw)

appendedAppendDistr : (xs, ys : List t) -> (sw: Sandwich as bs) -> appended (xs ++ ys) sw = appended ys (appended xs sw)
appendedAppendDistr xs ys (HereS {as}) = congHereS (appendAssociative as xs ys)
appendedAppendDistr xs ys (ThereS {as} {bs} sw) =
  congThereS (appendAssociative as xs ys) (appendAssociative bs xs ys) (appendedAppendDistr xs ys sw)

data Sandwich2 : t -> t -> List t -> List t -> Type where
  SW2 : Sandwich (b :: xs) ys -> Sandwich (a :: ys) zs -> Sandwich2 a b xs zs

swComb : Sandwich (a :: xs) ys -> Sandwich (b :: ys) zs -> Sandwich2 a b xs zs
swComb         axy   HereS       = SW2 HereS (ThereS axy)
swComb  HereS       (ThereS bxy) = SW2 bxy    HereS
swComb (ThereS axy) (ThereS byz) = let SW2 bxy ayz = swComb axy byz in SW2 (ThereS bxy) (ThereS ayz)
