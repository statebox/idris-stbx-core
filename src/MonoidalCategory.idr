module MonoidalCategory

import Category

interface Category object morphism => MonoidalCategory object (morphism : object -> object -> Type) where
