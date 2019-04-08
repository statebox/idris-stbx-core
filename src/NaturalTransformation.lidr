== The module |NaturalTransformation|

Perhaps unsurprisingly, after having defined categories and functors we switch to the next basic element of category theory, natural transformations. Natural transformations are defined between functors, and hence we start by importing what we did up to now, namely the modules |Category| and |Functor|.

> module NaturalTransformation
>
> import Category
> import Functor
>
> %access public export
> %default total

As we did for the previous modules, to implement |NaturalTransformation| we will resort again to records and constructors. In the following snippet, you can see how the record |NaturalTransformation| is specified by two categories $\mathcal{C}, \mathcal{D}$, implemented as |cat1| and |cat2| respectively, and two functors $F,G:\mathcal{C} \to \mathcal{D}$ between them, implemented as |func1| and |func2|.

> record NaturalTransformation
>   (cat1 : Category)
>   (cat2 : Category)
>   (func1 : CFunctor cat1 cat2)
>   (func2 : CFunctor cat1 cat2)
>   where
>     constructor MkNaturalTranformation

=== The components
Recall that, given functors $F,G: \mathcal{C} \to \mathcal{D}$, a natural transformation $\alpha: F \to G$ is defined by specifying, for each object $A$ of $\mathcal{C}$, a morphism $\alpha_A: FA \to GA$ in $\mathcal{D}$, subject to some properties we will get to later. We define the components of a natural transformation, for each object |a| of |cat1|, as follows:

>     component : (a : obj cat1) -> mor cat2 (mapObj func1 a) (mapObj func2 a)

|mapObj func1 a| means that we are applying |func1| to the object |a|. This is akin to consider $FA$. Similarly, |mapObj func2 a| is akin to consider $GA$. These two objects, belonging to |cat2| (standing for $\mathcal{D}$ in our mathematical definition), get fed to |mor| producing the homset of morphisms from $FA$ to $GA$. a term of this type is just the implementation of a morphism $FA \to GA$, and it is precisely what we associate to an object |a|.

=== The laws

Up to now, we defined, for a natural transformation $\alpha:F \to G$, its components $\alpha_A: FA \to GA$ for each $A$ object of $\mathcal{C}$. These components have to be related with each other by a property, stating that for each morphism $f:A \to B$ in $\mathcal{C}$ the following square commutes:

\begin{center}
  \begin{tikzcd}
    FA \arrow[d, "\alpha_A"']\arrow[r, "Ff"] & FB\arrow[d, "\alpha_B"]\\
    FB \arrow[r, "Gf"']& GB
  \end{tikzcd}
\end{center}

This property lets us interpret a natural transformation as a way to link the result of applying $F$ to the result of applying $G$ in a way that cooperates with the structure, namely morphism composition: In fact, notice how the commutative square above guarantees that given $f:A \to B$ and $g: B \to C$ in $\mathcal{C}$, applying the natural transformation law above to $f;g$ has the same effect of pasting together the commutative squares for $f$ and $g$, that is, the following diagram commutes:

\begin{center}
  \begin{tikzcd}
    FA \arrow[d, "\alpha_A"']\arrow[r, "Ff"]\arrow[rr, bend left, "F(f;g)"] & FB\arrow[d, "\alpha_B"]\arrow[r, "Fg"] & FC\arrow[d,"\alpha_C"]\\
    FB \arrow[r, "Gf"']\arrow[rr, bend right, "G(f;g)"']& GB\arrow[r, "Gg"'] &GC
  \end{tikzcd}
\end{center}

In Idris, as we expect, this property  is expressed by returning a proof of the equation expressed by the diagram above for each morphism $f$:

>     commutativity : {a, b : obj cat1}
>                  -> (f : mor cat1 a b)
>                  -> compose cat2
>                       (mapObj func1 a)
>                       (mapObj func2 a)
>                       (mapObj func2 b)
>                       (component a)
>                       (mapMor func2 a b f)
>                   = compose cat2
>                       (mapObj func1 a)
>                       (mapObj func1 b)
>                       (mapObj func2 b)
>                       (mapMor func1 a b f)
>                       (component b)

Here, we specify a morphism |f| from |a| to |b| in |cat1|. From this, we can consider $Ff: FA \to FB$, specified by |mapMor func1 a b f|, and $Gf: GA \to GB$, specified by |mapMor func2 a b f|. The equation modeled by the diagram above reads:

$$
    \alpha_A;Gf = Ff;\alpha_B
$$

$\alpha_A$ and $\alpha_B$ are respectively |component a| and |component b| in our implementation. We can then apply |compose| to obtain the two sides of the equation, leading to the type

< compose cat2
<   (mapObj func1 a)
<   (mapObj func2 a)
<   (mapObj func2 b)
<   (component a)
<   (mapMor func2 a b f)
< = compose cat2
<   (mapObj func1 a)
<   (mapObj func1 b)
<   (mapObj func2 b)
<   (mapMor func1 a b f)
<   (component b)

=== Conclusion

The code above is everything we need to define what a natural transformation is. In the next sections, we will proceed by making this definition more specific and obtain a natural isomorphism. The code of this section, presented as a unique block, can be found below.

< module NaturalTransformation
<
< import Category
< import Functor
<
< %access public export
< %default total
< record NaturalTransformation
<   (cat1 : Category)
<   (cat2 : Category)
<   (func1 : CFunctor cat1 cat2)
<   (func2 : CFunctor cat1 cat2)
<   where
<     constructor MkNaturalTranformation
<     component : (a : obj cat1) -> mor cat2 (mapObj func1 a) (mapObj func2 a)
<     commutativity : {a, b : obj cat1}
<                  -> (f : mor cat1 a b)
<                  -> compose cat2
<                       (mapObj func1 a)
<                       (mapObj func2 a)
<                       (mapObj func2 b)
<                       (component a)
<                       (mapMor func2 a b f)
<                   = compose cat2
<                       (mapObj func1 a)
<                       (mapObj func1 b)
<                       (mapObj func2 b)
<                       (mapMor func1 a b f)
<                       (component b)
