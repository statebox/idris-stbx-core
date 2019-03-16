> module Utils
>
> %access public export
> %default total
>
> cong2 : {f : t -> u -> v} -> a = b -> c = d -> f a c = f b d
> cong2 Refl Refl = Refl
>
> cong3 : {f : t -> u -> v -> w} -> a = b -> c = d -> e = g -> f a c e = f b d g
> cong3 Refl Refl Refl = Refl
