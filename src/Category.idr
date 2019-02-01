module Category

%access public export
%default total

data Category : (obj : Type) -> (mor : obj -> obj -> Type) -> Type where
  MkCategory :
       {obj : Type}
    -> {mor : obj -> obj -> Type}
    -> (identity : (a : obj) -> mor a a)
    -> (compose : (a, b, c : obj) -> (f : mor a b) -> (g : mor b c) -> mor a c)
    -> Category obj mor

LeftIdentity :
     {obj : Type}
  -> {mor : obj -> obj -> Type}
  -> {a, b : obj}
  -> (f : mor a b)
  -> Category obj mor
  -> Type
LeftIdentity {obj} {mor} {a} {b} f (MkCategory identity compose) =
  compose a a b (identity a) f = f

RightIdentity :
     {obj : Type}
  -> {mor : obj -> obj -> Type}
  -> {a, b : obj}
  -> (f : mor a b)
  -> Category obj mor
  -> Type
RightIdentity {obj} {mor} {a} {b} f (MkCategory identity compose) =
  compose a b b f (identity b) = f

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

data VerifiedCategory : (obj : Type) -> (mor : obj -> obj -> Type) -> Type where
  MkVerifiedCategory :
       (cat : Category obj mor)
    -> ((a, b : obj) -> (f : mor a b) -> LeftIdentity f cat)
    -> ((a, b : obj) -> (f : mor a b) -> RightIdentity f cat)
    -> ((a, b, c, d : obj) -> (f : mor a b) -> (g : mor b c) -> (h : mor c d) -> Associativity {f} {g} {h} cat)
    -> VerifiedCategory obj mor

innerCategory : VerifiedCategory obj mor -> Category obj mor
innerCategory (MkVerifiedCategory cat _ _ _) = cat
