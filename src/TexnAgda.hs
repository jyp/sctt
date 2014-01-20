{-# LANGUAGE OverloadedStrings #-}
module TexnAgda where

import Terms
import Ident

import MarXup
import MarXup.Tex
import MarXup.Latex
import MarXup.Latex.Math
import MarXup.DerivationTrees

import Data.List
import Data.Monoid


punctuate ::  Monoid c => c -> [c] -> c
punctuate p = mconcat . intersperse p

sep :: [TeX] -> TeX
sep = punctuate " "

sepp :: [TeX] -> TeX
sepp = punctuate space

keyword :: String -> TeX
keyword = math . mathsf . tex

(<+>) :: TeX -> TeX -> TeX
a <+> b = a <> " " <> b

(<++>) :: TeX -> TeX -> TeX
a <++> b = a <> space <> b

symi :: String -> TeX -> TeX  -> TeX
symi s a b = a <> keyword s <> b

(<=>) :: TeX -> TeX  -> TeX
(<=>) = symi "="

(</>) :: TeX -> TeX  -> TeX
(</>) = symi ";"

(<:>) :: TeX -> TeX  -> TeX
(<:>) = symi ":"

(<//>) :: TeX -> TeX  -> TeX
a <//> b = a <> newline <> b

(→) :: TeX -> TeX -> TeX
a → b = a <+> cmd0 "to" <+> b

(×) :: TeX -> TeX -> TeX
a × b = a <+> cmd0 "cross" <+> b

texTerm :: Term Id Id -> TeX
texTerm term =
    case term of
      Destr x v t -> texHyp x <=> texDestr v </> texTerm t
      Case x brs ->
          keyword "case" <+> texHyp x <+> keyword "of" <+>
                  brackets (sep $ map texBranch brs)
      Constr x c t -> texConc x <=> texConstr c </> texTerm t
      Concl x -> texConc x


texBranch :: Branch Id Id -> TeX
texBranch (Br tag t) =
    textual tag → texTerm t <+> keyword "."

texDestr :: Destr Id -> TeX
texDestr d =
    case d of
      App f x -> texHyp f <+> texConc x
      Cut t ty -> texConc t <+> keyword ":" <+> texConc ty

texConstr :: Constr Id Id -> TeX
texConstr constr =
    case constr of
      Hyp x -> texHyp x
      Lam x t -> keyword "λ" <> texHyp x <> keyword "." <> texTerm t
      Rec x t -> keyword "rec" <+> texHyp x <> keyword "." <> texTerm t
      Pi x tyA tyB -> paren (texHyp x <:> texConc tyA) → texTerm tyB
      Sigma x tyA tyB -> paren (texHyp x <:> texConc tyA) × texTerm tyB
      Pair x y -> paren (texConc x <+> keyword "," <+> texConc y)
      Tag t -> textual t
      Fin ts -> brackets (punctuate "; " $ map textual ts)
      Universe i -> cmd0 "star" <> textual "_" <> (textual $ show i)

texHyp :: Id -> TeX
texHyp x = textual $ show x

texConc :: Conc Id -> TeX
texConc (Conc x) = cmd "overline" (textual $ show x)
