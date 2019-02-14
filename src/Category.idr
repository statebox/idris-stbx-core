module Category

%access public export
%default total

record Category where
  constructor MkCategory
  obj           : Type
  mor           : obj -> obj -> Type
  identity      : (a : obj) -> mor a a
  compose       : (a, b, c : obj) -> (f : mor a b) -> (g : mor b c) -> mor a c
  leftIdentity  : (a, b : obj) -> (f : mor a b) -> compose a a b (identity a) f = f
  rightIdentity : (a, b : obj) -> (f : mor a b) -> compose a b b f (identity b) = f
  associativity : (a, b, c, d : obj)
               -> (f : mor a b)
               -> (g : mor b c)
               -> (h : mor c d)
               -> compose a b d f (compose b c d g h) = compose a c d (compose a b c f g) h

syntax "<" [cat] ">" [lobj] "~>" [robj] = mor cat lobj robj
syntax "<" [cat] [a] [b] [c] ">" [lmor] "~>" [rmor] = compose cat a b c lmor rmor


-- Examples ----

functions : Type -> Type -> Type
functions argument return = (argument -> return)

f_identity : (a : Type) -> a -> a
f_identity t v = v

f_compose : (a, b, c : Type) -> (a -> b) -> (b -> c) -> a -> c
f_compose t1 t2 t3 f1 f2 = f2 . f1


f_left_id : (a, b : Type) -> (f : a -> b) -> f_compose a a b (f_identity a) f = f
f_left_id a b f = Refl

f_right_id : (a : Type) -> (b : Type) -> (f : functions a b) -> f_compose a b b f (f_identity b) = f
f_right_id a b f = Refl

f_assoc : (a, b, c, d : Type) -> (f : a -> b) -> (g : b -> c) -> (h : c -> d) 
       -> f_compose a b d f (f_compose b c d g h) 
        = f_compose a c d (f_compose a b c f g) h
f_assoc a b c d f g h = Refl

SimpleTypes : Category
SimpleTypes = MkCategory Type functions f_identity f_compose f_left_id f_right_id f_assoc

