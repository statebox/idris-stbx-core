> module Monoid.MonoidAsCategory
> 
> import Category
> 
> -- contrib
> import Interfaces.Verified
> 
> %access public export
> %default total
> 
> MonoidMorphism : (monoid : Type) -> Unit -> Unit -> Type
> MonoidMorphism monoid _ _ = monoid
> 
> monoidAsCategory : VerifiedMonoid monoid => Category
> monoidAsCategory {monoid} = MkCategory
>   Unit
>   (MonoidMorphism monoid)
>   (\_ => Algebra.neutral)
>   (\_, _, _, f, g => f <+> g)
>   (\_, _, f => monoidNeutralIsNeutralR f)
>   (\_, _, f => monoidNeutralIsNeutralL f)
>   (\_, _, _, _, f, g, h => semigroupOpIsAssociative f g h)
