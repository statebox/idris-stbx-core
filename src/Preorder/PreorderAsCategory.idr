module Preorder.PreorderAsCategory

import Category
import Preorder.UniquePreorder

-- contrib
import Decidable.Order

%access public export
%default total

leftIdentity : UniquePreorder t po
  => (a, b : t)
  -> (f : po a b)
  -> LeftIdentity f (MkCategory {obj = t} {mor = po} Decidable.Order.reflexive Decidable.Order.transitive)
leftIdentity a b f = unique a b (Decidable.Order.transitive a a b (Decidable.Order.reflexive a) f) f

rightIdentity : UniquePreorder t po
  => (a, b : t)
  -> (f : po a b)
  -> RightIdentity f (MkCategory {obj = t} {mor = po} Decidable.Order.reflexive Decidable.Order.transitive)
rightIdentity a b f = unique a b (Decidable.Order.transitive a b b f (Decidable.Order.reflexive b)) f

associativity : UniquePreorder t po
  => (a, b, c, d : t)
  -> (f : po a b)
  -> (g : po b c)
  -> (h : po c d)
  -> Associativity {f} {g} {h} (MkCategory {obj = t} {mor = po} Decidable.Order.reflexive Decidable.Order.transitive)
associativity a b c d f g h = unique a d
  (Decidable.Order.transitive a b d f (Decidable.Order.transitive b c d g h))
  (Decidable.Order.transitive a c d (Decidable.Order.transitive a b c f g) h)

preorderAsCategory : UniquePreorder t po => VerifiedCategory t po
preorderAsCategory {t} {po} = MkVerifiedCategory
  (MkCategory
    {obj = t}
    {mor = po}
    reflexive
    transitive
  )
  (leftIdentity {t} {po})
  (rightIdentity {t} {po})
  (associativity {t} {po})
