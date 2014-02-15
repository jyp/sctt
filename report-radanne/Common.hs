{-# OPTIONS_GHC -i../src/ -XTypeSynonymInstances -XOverloadedStrings -XRecursiveDo -pgmF marxup3 -F #-}
module Common where

import MarXup
import MarXup.Latex
import MarXup.Latex.Math
import MarXup.Latex.Bib
import MarXup.Tex

import Control.Monad
import Control.Monad.Fix (MonadFix,mfix)
import Control.Applicative
import Data.Monoid
import Data.List (sort,intersperse)
import Data.String



bibliographyAll :: TeX
bibliographyAll = do
  bibliographystyle "abbrvnat"
  bibliography "../PaperTools/bibtex/jp"

authors ::  [AuthorInfo]
authors = [AuthorInfo "Gabriel Radanne" "gabriel.radanne@zoho.com" "Under the supervision of Jean-Philippe Bernardy"]


texttt = text . (cmd "texttt")

na :: TeX
na = «nano-Agda»

item' x = cmd "item" (cmd "textbf" x)
description = env "description"

-- | Math commands :
γ = Con $ cmd "gamma" nil
γ' = Con $ cmd "gamma'" nil
γty = Con $ cmd "Gamma" nil
γty' = Con $ cmd "Delta" nil
γc = Con $ cmd "gamma_c" nil
γa = Con $ cmd "gamma_a" nil
γd = Con $ cmd "gamma_d" nil
γd' = Con $ cmd "gamma_d'" nil
h = text "h"
h' = prim h
h'' = prim $ h'

bot = Con $ cmd "bot" nil
λ = Con $ cmd "lambda" nil
π = Con $ cmd "Pi" nil
σ = Con $ cmd "Sigma" nil
nat = Con "ℕ"

fa = Con $ cmd "forall" nil

mparen = outop "(" ")"
mbracket = outop "{" "}"
mbrac = outop "[" "]"

quad = cmd0 "quad"
qquad = cmd0 "qquad"

app f x = f <-> mparen x
(\=) = binop 1 "="
(=/=) = binop 1 "≠"
(≡) = binop 1 (cmd0 "equiv")
(≅) = binop 1 (cmd0 "cong")
(</>) = binop 1 space
(<->) = binop 1 nil
(<^>) = binop 1 ","
(<.>) = binop 1 "."
(<:>) = binop 1 ":"
(//) = binop 1 "/"
(∨) = binop 1 "∨"
(∧) = binop 1 "∧"
(≠) = binop 1 (cmd0 "neq")
a \== b = mparen $ a \= b
(∈) = binop 1 (cmd0 "in")
(→) = binop 1 (cmd0 "to")
(←) = binop 1 (cmd0 "gets")
(×)= binop 1 (cmd0 "times")
(|->) = binop 1 (cmd0 "mapsto")
concl = UnOp 1 (cmd "overline") 1
iff = UnOp 1 (\s -> mathsf "if " <> space <> s ) 1
proj p = UnOp 1 (\s -> s <> mathsf ("." <> p) ) 1
proj1 = proj "1"
proj2 = proj "2"
prim = UnOp 1 (\s -> s <> "'") 1

squig = Con $ cmd0 "rightsquigarrow"
(~>) = binop 1 $ cmd0 "rightsquigarrow"
(~/>) = binop 1 $ cmd0 "not \\rightsquigarrow"
(~~>) = binop 1 $ (backslash <> tex "rightsquigarrow" <> (element $ indice $ text "c"))
(~>*) = binop 1 $ ((backslash <> tex "rightsquigarrow") ^^^ tex "*")
(#) = binop 1 ", "
subst t x y = t <-> mbrac ( x // y )
(==>) = binop 1 $ cmd0 "Rightarrow"

indice = UnOp 1 (\ x -> tex "_" <> braces x) 1

(@-) = BinOp 1 (\ x y -> x <> tex "_" <> braces y) 1 1

(⊢) = binop 1 (cmd0 "vdash")
(\::=) = binop 1 "::="

(<@) = binop 1 (cmd0 "leftleftarrows")
(@>) = binop 1 (cmd0 "rightrightarrows")


x,y,z,c,d,l,l2,t :: Math
x = text "x"
y = text "y"
x' = prim x
y' = prim y
z = text "z"
z' = prim z
w = text "w"

c = text "c"
cty = text "C"
d = text "d"
d' = prim $ text "d'"

xty = text "X"
xty' = prim xty
yty = text "Y"
zty = text "Z"

i = text "i"
j = text "j"

l = text "`l"
l2 = text "`m"
n = text "n"
t = text "t"
u = text "u"
t' = prim $ t
t'' = prim $ t'
tty = text "T"
tty' = prim $ text "T"

lra = cmd0 "longrightarrow"
star = Con $ cmd0 "star"
kind = ( star @- )

pair_ x y = mparen $ binop 1 "," x y
lambda_ x t = λ <-> x <.> t
let_ x a t = texttt«let» </> x \= a </> texttt«in» </> t
case_ x l =
    let l' = text $ mconcat $ intersperse ", " l in
    texttt«case» </> x </> texttt«of» </> mbracket l'
pi_ x y t = mparen ( x <:> y ) → t
sigma_ x y t = mparen ( x <:> y ) × t
fin_ l = mbracket l
cut_ x y = mparen (x <:> y)

figure'' :: TeX -> Tex a -> Tex (SortedLabel, a)
figure'' caption body = env' "figure" ["!h"] $ do
  l<-body
  cmd "caption" caption
  l'<-label "Fig."
  vspace"-0.3cm"
  return (l',l)

figure' :: TeX -> TeX -> Tex SortedLabel
figure' c b = do { (l,_) <- figure'' c b ; return l }

align' :: [[TeX]] -> Tex SortedLabel
align' body = env "align" $ do
            mkrows $ map mkcols body
            label "Eq."

centering = cmd0 "centering"
footnote = cmd "footnote"

minipage :: String -> TeX -> Tex a -> Tex a
minipage align length =
    env'' "minipage" [align] [length <> cmd0 "linewidth"]

subfigure :: String -> TeX -> TeX -> TeX -> Tex SortedLabel
subfigure align length caption body =
    env'' "subfigure" [align] [length <> cmd0 "linewidth"] $ do
      body
      cmd "caption" caption
      label "Fig."



-- | Mathpartir

rule name pre conc =
    cmdm "inferrule" [name] [mkrows pre, conc]

ruleref = cmd "textsc"

-- | Lstlistings

data Listing a = Listing {fromListing::String, value::a}

instance Textual Listing where
    textual s = Listing s ()

instance Monad Listing where
    return x = Listing "" x
    (Listing s0 x) >>= f =
        Listing (s0 ++ s1) y
        where Listing s1 y = f x

instance MonadFix Listing where
    mfix f =
        let Listing _ x = f x in
        f x

agdai :: Listing () -> TeX
agdai = lstinline ["language=Agda"]

nai :: Listing () -> TeX
nai = lstinline ["language=nanoAgda"]

listing :: [String] -> Listing () -> TeX
listing opt (Listing s _) =
    env' "lstlisting" opt (tex s)

lstinline :: [String] -> Listing () -> TeX
lstinline opt (Listing s _) =
    let sep = tex "$"
        opt' = tex $ mconcat . intersperse ", "
               $ "basicstyle=\\ttfamily" :  opt in
    backslash <> "lstinline" <> brackets opt' <> sep <> tex s <> sep

agdacode :: Listing () -> TeX
agdacode code =
    listing ["language=Agda"] code

nacode :: String -> TeX
nacode file =
    cmd' "lstinputlisting" ["language=nanoAgda"] $ tex file

-- | Presentation stuff

blockB :: TeX -> Tex a -> Tex a
blockB a content = env'' "block" [] [a] content

columns :: String -> Tex a -> Tex a
columns a content =
    env' "columns" [a] content

columnE :: String -> TeX -> Tex a -> Tex a
columnE a size content =
    env'' "column" [a] [size <> cmd0 "linewidth"] content

column :: TeX -> TeX
column size =
    cmd "column" $ size <> cmd0 "linewidth"
