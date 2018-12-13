module SymmetricMonoidalCategory

import MonoidalCategory

interface MonoidalCategory object morphism => SymmetricMonoidalCategory object (morphism : object -> object -> Type) where
