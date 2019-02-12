Before starting to develop the Statebox dependently typed core, we need to implement some basic categorical definitions which will allow  us to stay as faithful as possible to the categorical model outlined in the Statebox Monograph. This section is devoted precisely to this task. Every subsection will document in detail how a module has been implemented.

\subsection{The module |Category|}

We start with the most basic thing we can do, namely the definition of category. First things first, we start by defining our module.
%
%
\begin{code}
module Category

%access public export
%default total
\end{code}
%
Then, we implement the basic elements a category consists of.
%
%
\begin{code}
data Category : (obj : Type) -> (mor : obj -> obj -> Type) -> Type where
  MkCategory :
    {obj : Type}
    -> {mor : obj -> obj -> Type}
    -> (identity : (a : obj) -> mor a a)
    -> (compose : (a, b, c : obj) -> (f : mor a b) -> (g : mor b c) -> mor a c)
    -> Category obj mor
\end{code}
%
We define a category as a type. The main ingredients of a category are objects and morphisms: We give objects a type |obj| and morphisms a type |obj -> obj -> Type| -- that is, morphisms are interpreted as functions that take two objects representing domain and codomain and return a type. 

The |data| definition above means that a category is specified by its objects and morphisms. Furthermore, |Category| has one constructor, |MkCategory|, which asks to determine:
%
%
\begin{itemize}
  \item For each object, a selected identity morphism. This is represented by |(identity : (a : obj) -> mor a a)|;
  \item For each couple of morphisms such that their domain and codomain match up, their composition. This is represented by |compose : (a, b, c : obj) -> (f : mor a b) -> (g : mor b c) -> mor a c|.
\end{itemize}
%
At the moment we have defined the main ingredients that make up a category, but nothing ensures that the category axioms hold. For instance, there is nothing in principle that tells us that composing an identity with a morphism returns the morphism itself. The next goal is to define a version of |Category| where such axioms are enforced.

To do this, we start by implementing the categorical laws separatedly, starting from the left identity law:
%
%
\begin{code}
LeftIdentity :
     {obj : Type}
  -> {mor : obj -> obj -> Type}
  -> {a, b : obj}
  -> (f : mor a b)
  -> Category obj mor
  -> Type
LeftIdentity {obj} {mor} {a} {b} f (MkCategory identity compose) =
  compose a a b (identity a) f = f
\end{code}
%
|LeftIdentity| takes a Category (specified as |Category obj mor|) and one of its morphisms (specified as |f: mor a b|) and produces an equation proving that composing the morphism on the left with the identity on its domain amounts to doing nothing. This is akin to the familiar equation:
%
%
\begin{equation*}
  A \xrightarrow{id} A \xrightarrow{f} B = A \xrightarrow{f} B
\end{equation*}
%
Right identity law is defined analogously below, modelling the equation:
%
%
\begin{equation*}
  A \xrightarrow{f} B \xrightarrow{id} B = A \xrightarrow{f} B
\end{equation*}
%
%
\begin{code}
RightIdentity :
     {obj : Type}
  -> {mor : obj -> obj -> Type}
  -> {a, b : obj}
  -> (f : mor a b)
  -> Category obj mor
  -> Type
RightIdentity {obj} {mor} {a} {b} f (MkCategory identity compose) =
  compose a b b f (identity b) = f
\end{code}
%
It remains to implement associativity, which is done as follows:
%
%
\begin{code}
Associativity :
     {obj : Type}
  -> {mor : obj -> obj -> Type}
  -> {a, b, c, d : obj}
  -> {f : mor a b}
  -> {g : mor b c}
  -> {h : mor c d}
  -> Category obj mor
  -> Type
Associativity {obj} {mor} {a} {b} {c} {d} {f} {g} {h} (MkCategory identity compose) =
  compose a b d f (compose b c d g h) = compose a c d (compose a b c f g) h
\end{code}
%
Unsurprisingly, associativity takes a category and produces a proof that for each triple of morphisms with matching domains and codomains, the order of composition does not matter. This models the familiar equation:
%
%
\begin{equation*}
  f;(g;h) = (f;g);h
\end{equation*}
%
We can now combine the |Category| type with the laws just implemented to obtain a |VerifiedCategory| type, which is a |Category| obeying the unit and associativity laws.
%
%
\begin{code}
data VerifiedCategory : (obj : Type) -> (mor : obj -> obj -> Type) -> Type where
  MkVerifiedCategory :
       (cat : Category obj mor)
    -> ((a, b : obj) -> (f : mor a b) -> LeftIdentity f cat)
    -> ((a, b : obj) -> (f : mor a b) -> RightIdentity f cat)
    -> ((a, b, c, d : obj) -> (f : mor a b) -> (g : mor b c) -> (h : mor c d) -> Associativity {f} {g} {h} cat)
    -> VerifiedCategory obj mor
\end{code}
%
As you can see, here the constructor requires that morphisms obey the |LeftIdentity|, |RightIdentity| and |Associativity| laws we defined before. 

We conclude the section by defining |InnerCategory|, which strips the verified part of |VerifiedCategory| away producing the its underlying |Category| type. |InnerCategory| will greatly simplify life when we will have to define more complicated mathematical objects such as functors.
%
%
\begin{code}
innerCategory : VerifiedCategory obj mor -> Category obj mor
innerCategory (MkVerifiedCategory cat _ _ _) = cat
\end{code}
%