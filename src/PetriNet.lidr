> module PetriNet
>
> multiSet : Type -> Type -- should we impose that it is non-zero only on a finite number on inputs?
> multiSet x = x -> Nat
>
> interface PetriNet places transitions where
>   input  : transition -> multiSet places
>   output : transition -> multiSet places
