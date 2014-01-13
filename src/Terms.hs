{-# LANGUAGE GADTs, DeriveFunctor, TemplateHaskell, OverloadedStrings, RecordWildCards #-}


module Terms where

import Data.Bitraversable
import Data.Bifoldable
import Data.Bifunctor
import Data.Generics.Genifunctors
import Display
import Data.Monoid

type Hyp a = a
type Conc a = a
type Tag = String

data Proj = First | Second
     deriving (Eq, Ord, Show)

instance Pretty Proj where
   pretty Terms.First = ".1"
   pretty Terms.Second = ".2"

data Branch n r = Br Tag (Term n r)
    deriving (Show, Functor)

instance Bifoldable Term where  bifoldMap = bifoldMapDefault
instance Bifunctor Term where  bimap = bimapDefault
instance Bitraversable Term where  bitraverse = $(genTraverse ''Term)

data Term n r where
  Destr  :: Hyp n  -> Destr r -> Term n r -> Term n r
  Case   :: Hyp r  -> [Branch n r] -> Term n r
  Constr :: Conc n -> Constr n r -> Term n r -> Term n r
  Conc   :: Conc r -> Term n r  -- ^ Conclude
    deriving (Show, Functor)

data Destr r where
  -- Tag' :: String -> Destr r -- TODO: probably not needed after all ...
  App :: Hyp r -> Conc r -> Destr r
  Proj :: Hyp r -> Proj -> Destr r
  Cut :: Conc r -> Conc r {-^ the type-} -> Destr r
    deriving (Show, Eq, Ord, Functor)

data Constr n r where
  Hyp :: Hyp r -> Constr n r
  Rec :: Hyp n -> Term n r -> Constr n r
  Lam :: Hyp n -> Term n r -> Constr n r
  Pi :: Hyp n -> Conc r -> Term n r -> Constr n r
  Sigma :: Hyp n -> Conc r -> Term n r -> Constr n r
  Pair :: Conc r -> Conc r -> Constr n r
  Tag :: Tag -> Constr n r
  Fin :: [Tag] -> Constr n r
  Universe :: Int -> Constr n r
    deriving (Show, Functor)

instance (Pretty r, Pretty n) => Pretty (Term n r) where
  pretty (Destr x v t) = pretty x <+> "=" $$+ pretty v <+> ";" $$ pretty t
  pretty (Constr x v t) = pretty x <+> "=" $$+ pretty v <+> ";" $$ pretty t
  pretty (Case x bs) =
      "case " <> pretty x <> " of" $$+
        (braces $ sep $ punctuate "." $ map pretty bs)
  pretty (Conc x) = pretty x

instance (Pretty r, Pretty n) => Pretty (Branch n r) where
  pretty (Br tag t) = "'" <> text tag <> "->" $$+ pretty t

instance Pretty r => Pretty (Destr r) where
  -- pretty (Tag' v) = "'" <> text v
  pretty (App f x) = pretty f <> " " <> pretty x
  pretty (Proj x p) = pretty x <> pretty p
  pretty (Cut x t) = pretty x <> ":" <> pretty t

instance (Pretty r, Pretty n) => Pretty (Constr n r) where
  pretty (Hyp h) = pretty h
  pretty (Rec x b) = ("rec " <> pretty x <> " ->") $$+ (pretty b)
  pretty (Lam x b) = ("\\" <> pretty x <> " ->") $$+ (pretty b)
  pretty (Pi x t b) =
      (parens (pretty x <>":"<>pretty t) <> " ->")
      $$+ (pretty b)
  pretty (Sigma x t b) =
      (parens (pretty x <>":"<>pretty t) <> " ×")
      $$+ (pretty b)
  pretty (Pair a b) = parens $ pretty a <> "," <> pretty b
  pretty (Tag t) = "'" <> text t
  pretty (Fin ts) = braces $ sep $ punctuate "," $ map text ts
  pretty (Universe x) = "*" <> subscriptPretty x
