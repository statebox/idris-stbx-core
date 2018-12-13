# Statebox core

## Free symmetric monoidal categories

- definition of monoidal category (see Definition 3.3.1 in the monograph). For the moment we will assume that all our monoidal categories are strict (associator and unitors are identities)

```
interface Category object morphism => MonoidalCategory object (morphism : object -> object -> Type)
```

- definition of symmetric monoidal category (see Definition 3.3.7 in the monograph)

```
interface MonoidalCategory object morphism => SymmetricMonoidalCategory object (morphism : object -> object -> Type)
```

## Petri nets

- definition of a Petri net (see definition 2.3.1 in the monograph).

```
interface PetriNet places transitions
```

## Executions of Petri nets

- interpret a Petri net as a category. Define its category of executions (see definition 4.4.7 in the monograph).

```
PetriNet places transitions => SymmetricMonoidalCategory (ExPetri places transitions)
```

Once we have this, we can see an object of the category of executions (something of the form `A ⊗ B ⊗ C ⊗ A`) as a distribution of tokens into the places of a Petri net. Morphisms in the category of executions (something like `f : A ⊗ B ⊗ C ⊗ A -> D ⊗ B ⊗ E`) can be seen as sequences of transitions of the Petri net.

We can also see the state of our Petri net as a morphism in the category of executions, starting from the monoidal unit (see remark 4.1.3 in the monograph).

In this fashion the firing of a transition can be seen as the composition of the state with the transition itself

```
firing : (transition : Hom(ExPetri) P T) -> (state : Hom(ExPetri) I P) -> Hom(ExPetri) I T
```

where `A` and `B` are objects of the category of executions.

Actually this is not going to work in practice, because we would like to be able to compose also a state with a transition whenever the target of the state contains a permutation of the source of the transition (consider for example a state `I -> A ⊗ B ⊗ B ⊗ C` and a transition `B ⊗ A -> D`). See details [here](https://github.com/statebox/idris-stbx-core/issues/3).

To do this we need to add one more argument to our `firing` function. This could look like

```
firing : (transition : Hom(ExPetri) P T) -> (state : Hom(ExPetri) I P') -> (pointer : Vect (length P) Int) -> Hom(ExPetri) I T'
```

where `pointer` is a vector, of length `length P` (since `ExPetri` is a free symmetric monoidal category, we can define a length of an object `P` as the number of generating addends we use to write `P`), which is indicating which addends of `P'` correspond to the addends of `P`. For example, if the state is `I -> A ⊗ B ⊗ B ⊗ C` and the transition is `B ⊗ A -> D`, `pointer` could be either `[1, 0]` (the added in position `1` of `P'` correspond to the first addend of `P`, and the addend in position `0` correspond to the second addend of `P`) or `[2, 0]`. At this point `pointer` could be used to define a morphism `σ : P' -> P''` in `ExPetri`, where `P'' = P ⊗ P'''`. At this point we are able to compute the output of `firing` as `state ;  σ ; (transition ⊗ id_P''')`.

If we want to store the history of the execution of our net, we then have to store both the transitions which were fired and the `pointer`s used to select which tokens to act on.
