Before starting to develop the Statebox dependently typed core, we need to implement some basic categorical definitions which will allow  us to stay as faithful as possible to the categorical model outlined in the Statebox Monograph. This section is devoted precisely to this task. Every subsection will document in detail how a module has been implemented.
%
%
%
\subsection{The module |Category|}
%
%
We start with the most basic thing we can do, namely the definition of category. First things first, we start by defining our module.
%
%
> module Category
>
> %access public export
> %default total
%
We will just declare |Category| as a new type in our program, so that we could be able to define new values for that type:
%
%
> record Category where
%
A |record| in Idirs is just the product type of several values, which are called the fields of the record. It's a convenient syntax because Idris provides field access and update functions automatically for us. We add also the constructor |MkCategory| to be able to construct concrete values of type |Category|:
%
%
>   constructor MkCategory
%
%
%
\subsubsection{The elements}
%
%
At its most basic level, a category is a collection of things, called \emph{objects}. To specify what these things are, we add to our definition a field to keep track of them:
%
%
>   obj : Type
%
You can think about |obj| as a collection of dots, which will be items we want to talk about in our category.

Next thing up, we need ways to go from one dot to the other, so that we can wander around our objects. This introduces some dynamics inside our category, which allows us to talk about movement and evolution of systems.

In practice, we need to describe, for any pair of objects $a$ and $b$, the collection of \emph{arrows} (also called \emph{morphisms}) going from $a$ to $b$. An arrow from $a$ to $b$ is sometimes mathematically denoted as $f:a \to b$ or more compactly as $a \xrightarrow{f} b$. 
Moreover, if we denote a category as $\mathcal{C}$, a convenient notation to denote \emph{all} the arrows from object $a$ to object $b$ is $\mathcal{C}(a,b)$.

To translate this to Idris, let's add another field to our Category:
%
%
>   mor : obj -> obj -> Type
%
Now, for any pair of objects |a, b : obj|, we can talk about the collection |mor a b| of arrows going from $a$ to $b$. This faithfully models, on the implementation side, what $\mathcal{C}(a,b)$ is on the theoretical side.
%
%
%
\subsubsection{The operations}
%
%
Now that we have arrows in our category, allowing us to go from one object to the other, we would like to start following consecutive arrows; I mean, if an arrow leads us to $b$, we would like to continue our journey by taking any other arrow starting at $b$. Nobody stops us from doing that, but it would be really cumbersome if we must keep track of every single arrow whenever we want to describe a path from one dot to another. The definition of category comes in our help here, providing us with an operation to obtain arrows from paths, called \emph{composition}.

In practice, whenever we have two consecutive arrows $f:a \to b$ and $g: b \to c$ (notice how b is the target of the first arrow and the origin of the second, they must necessarily coincide!) we are able to obtain an arrow $f;g: a \to c$ which is the same thing as following first $f$ and then $g$. In category theory, composition is often expressed graphically by using \emph{commutative diagrams}, as follows:
%
%
\begin{center}
  \begin{tikzcd}
    a \arrow[d, "f"']\arrow[dr, "f;g"]\\
    b \arrow[r, "g"']& c\\
  \end{tikzcd}
\end{center}
%
%
The way to read a commutative diagram is that paths having the same endpoints coincide. So, in this case, going first through $f$ and then through $g$ is the same as going through $f;g$.

We implement morphism composition in Idris as:
%
%
>   compose : (a, b, c : obj)
>          -> (f : mor a b)
>          -> (g : mor b c)
>          -> mor a c
%
Translating it in human language, this says that whenever we have three objects |a|, |b| and |c| and morphisms |f|, from |a| to |b|, and |g|, from |b| to |c|, we can construct a morphism |f ; g| which goes directly from |a| to |c|.

The other basic ingredient we have in a category are \emph{identity arrows}. This amounts to say that for any object $a$ we have a specific arrow going from $a$ to $a$, denoted $id_a$. The identity arrow is a way to ensure that we can always go from one object to itself, doing a trivial move. This could seem a bit pointless in itself, but it's actually not if you think, for instance, what it means for the composition of two arrows to be an identity arrow! We define this in Idris as follows:
%
%
>   identity : (a : obj) -> mor a a
%
simply stating that for any object |a| we have a morphism |identity a| going from |a| to |a|.

If we stopped here with our definition, we would have all the basic components, but we would not have any assurance that they behave in any sensible manner. This means that we would have problems to attach an easy and meaningful semantics to our basic elements.

To overcome this we need to impose some laws on our elements, so that we have an assurance that they behave as we expect. Notice that this is one of the point where having a dependently typed language really helps!
%
%
%
\subsubsection{The laws}
%
%
We would like to interpret the identity morphism of any object as an arrow which doesn't do anything, which keeps everything as is. We can formalise this by saying that whenever we compose an identity morphism with any other morphism $f$, what we obtain is extactly $f$. In other terms, whenever we have an identity morphism, the result will be the same if we remove it. Or, from the other perspective, wherever we have a morphism, we can compose it with an identity without modifying the global behaviour. On the theory side, we can state this using commutative diagrams (note how it is commonplace to denote identity arrows in commutative diagrams with parallel bars):
%
%
\begin{center}
  \begin{tikzcd}
    a \arrow[d,equal]\arrow[dr, "f"]\\
    a \arrow[r, "f"']& b\\
  \end{tikzcd}
  %
  \hspace{3em}
  %
  \begin{tikzcd}
    a \arrow[r,"f"]\arrow[dr, "f"'] & b\arrow[d,equal]\\
    & b\\
  \end{tikzcd}
\captionof{figure}{The identity laws $id_a ; f=f$ and $f;id_b = f$}
\end{center}
%
In Idris, we can state the two identity laws as follows:
%
%
>   leftIdentity  : (a, b : obj)
>                -> (f : mor a b)
>                -> compose a a b (identity a) f = f
%
and
%
%
>   rightIdentity : (a, b : obj)
>                -> (f : mor a b)
>                -> compose a b b f (identity b) = f
%
In short, this amounts to say that |(identity a) ; f = f = f ; (identity b)| for any morphism |f : a -> b|. As a technical side note, I'd like to emphasise here how Idris allows us to encode equality in the type system; from a practial point of view, equality in Idris is a type which has only one inhabitant, called |Refl|, which corresponding to reflexivity, and stating that |x = x| for any possible |x|.

There is another law which we need to add, concerning the composition of multiple arrows. In fact, considering what we have up to now, we know that we can compose two consecutive arrows, but what about if we have three? Suppose we had $f: a \to b$, $g: b \to c$ and $h: c \to d$: we could compose the first two, $f$ and $g$, and then compose the result $f ; g$ with $h$. ...Or we could compose first $g$ and $h$ and then compose $f$ with the result $g ; h$. In this way we would obtain two morphisms, which are a priori different. What we want is actually to impose that they must be equal, so that we should not keep track of the order with which we perform the composition, but consider just the resulting path. This axiom is called \emph{associativity}, and is caputred by the following commutative diagram:
%
%
\begin{center}
  \begin{tikzcd}
    a \arrow[r, "f"]\arrow[dr,"f;g"']&b\arrow[d, "g"]\arrow[dr, "g;h"]&\\
    &c\arrow[r, "h"']& d\\
  \end{tikzcd}
\captionof{figure}{The associativity law $f;(g;h)=(f;g);h$}
\end{center}
%
Which we render in Idris as
%
%
>   associativity : (a, b, c, d : obj)
>                -> (f : mor a b)
>                -> (g : mor b c)
>                -> (h : mor c d)
>                -> compose a b d f (compose b c d g h)
>                = compose a c d (compose a b c f g) h
%
%
%
\subsubsection{Conclusion}
%
%
Summing up and putting it all together, our definition of |Category| now looks like this:
%
%
< record Category where
<   constructor MkCategory
<   obj           : Type
<   mor           : obj -> obj -> Type
<   identity      : (a : obj) -> mor a a
<   compose       : (a, b, c : obj) 
<                -> (f : mor a b) 
<                -> (g : mor b c) 
<                -> mor a c
<   leftIdentity  : (a, b : obj) 
<                -> (f : mor a b) 
<                -> compose a a b (identity a) f = f
<   rightIdentity : (a, b : obj) 
<                -> (f : mor a b) 
<                -> compose a b b f (identity b) = f
<   associativity : (a, b, c, d : obj)
<                -> (f : mor a b)
<                -> (g : mor b c)
<                -> (h : mor c d)
<                -> compose a b d f (compose b c d g h) = compose a c d (compose a b c f g) h