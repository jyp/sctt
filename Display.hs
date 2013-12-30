{-# LANGUAGE PackageImports, GADTs, KindSignatures, StandaloneDeriving, EmptyDataDecls, FlexibleInstances, OverloadedStrings #-}

module Display (Pretty(..), Doc, ($$), (<+>), text, hang, vcat, parensIf, sep, comma, nest, parens, braces, int,
                subscriptPretty, superscriptPretty, subscriptShow, render, punctuate) where

import Prelude hiding (length, reverse)
import Text.PrettyPrint.HughesPJ
import Numeric (showIntAtBase)

class Pretty a where
  pretty :: a -> Doc

instance Pretty x => Pretty [x] where
  pretty x = brackets $ sep $ punctuate comma (map pretty x)

instance Pretty Int where
  pretty = int

instance Pretty Bool where
  pretty = text . show

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

