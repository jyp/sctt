{-# LANGUAGE GADTs, DeriveFunctor, TemplateHaskell, OverloadedStrings, RecordWildCards #-}

module TermsInstances where
import Data.Bitraversable
import Data.Bifoldable
import Data.Bifunctor
import Data.Generics.Genifunctors
import Terms

instance Bitraversable Val where  bitraverse = $(genTraverse ''Val)
instance Bitraversable Term where  bitraverse = $(genTraverse ''Term)
instance Bifoldable Val where  bifoldMap = bifoldMapDefault
instance Bifunctor Val where  bimap = bimapDefault
instance Bifoldable Term where  bifoldMap = bifoldMapDefault
instance Bifunctor Term where  bimap = bimapDefault
