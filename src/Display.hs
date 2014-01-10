{-# LANGUAGE PackageImports, GADTs, KindSignatures, StandaloneDeriving, EmptyDataDecls, FlexibleInstances, OverloadedStrings, OverlappingInstances #-}

module Display (Pretty(..), Doc, ($$), (<+>), text, hang, vcat, parensIf, sep, comma, nest, parens, braces, int,
                subscriptPretty, superscriptPretty, subscriptShow, render, punctuate) where

import Prelude hiding (length, reverse)
import Text.PrettyPrint.HughesPJ
import Numeric (showIntAtBase)
import qualified Data.Map as M
class Pretty a where
  pretty :: a -> Doc

instance Pretty x => Pretty [x] where
  pretty x = brackets $ sep $ punctuate comma (map pretty x)

instance Pretty Int where
  pretty = int

instance Pretty Bool where
  pretty = text . show

instance (Pretty a, Pretty b) => Pretty (Either a b) where
  pretty (Left a) = "◂ " <> pretty a
  pretty (Right a) = "▸ " <> pretty a

instance (Pretty a, Pretty b) => Pretty (a,b) where
  pretty (a,b) = "(" <> pretty a <> "," <> pretty b <> ")"

instance (Pretty k, Pretty v) => Pretty (M.Map k v) where
  pretty m = sep $ punctuate ";" [pretty k <> " ↦ " <> pretty v | (k,v) <- M.toList m]

instance Pretty a => (Pretty (Maybe a)) where
  pretty Nothing = "¿"
  pretty (Just x) = "¡" <> pretty x
instance Pretty String where
  pretty = text
  
scriptPretty :: String -> Int -> Doc
scriptPretty s = text . scriptShow s

scriptShow ::  (Integral a, Show a) => [Char] -> a -> [Char]
scriptShow []             _ = error "scriptShow on empty list"
scriptShow (minus:digits) x = if x < 0 then minus : sho (negate x) else sho x
  where sho z = showIntAtBase 10 (\i -> digits !! i) z []

superscriptPretty ::  Int -> Doc
superscriptPretty = scriptPretty "⁻⁰¹²³⁴⁵⁶⁷⁸⁹"

subscriptPretty ::  Int -> Doc
subscriptPretty   = scriptPretty "-₀₁₂₃₄₅₆₇₈₉"

subscriptShow :: Int -> String
subscriptShow     = scriptShow "-₀₁₂₃₄₅₆₇₈₉"

parensIf :: Bool -> Doc -> Doc
parensIf True  = parens
parensIf False = id

