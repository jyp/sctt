{-# OPTIONS_GHC -i../src/ -XTypeSynonymInstances -XOverloadedStrings -XRecursiveDo -pgmF marxup3 -F #-}

import MarXup
import MarXup.Latex
import MarXup.Latex.Math
import MarXup.Tex

import qualified Terms as T
import qualified TexnAgda as TA
import qualified Ident

import Control.Monad
import Control.Applicative
import Data.Monoid
import Data.List (sort,intersperse)

classUsed ::  ClassFile
classUsed = LNCS

classFile LNCS = "llncs"

preamble :: Bool -> Tex ()
preamble inMetaPost = do
  if inMetaPost
      then documentClass "article" ["11pt"]
      else documentClass (classFile classUsed) [] -- ["authoryear","preprint"]
  stdPreamble
  mathpreamble classUsed
  -- cmd "input" (tex "../PaperTools/latex/unicodedefs")
  unless inMetaPost $ do
    usepackage "natbib" ["sectionbib"]
    usepackage "tikz" []
    usepackage "mathpartir" []
    cmd "usetikzlibrary" $ tex "shapes,arrows"
    usepackage "tabularx" []

    title "A sequent-calculus presentation of type-theory"
    authorinfo classUsed authors

bibliographyAll :: TeX
bibliographyAll = do
  cmd "bibliographystyle" $ textual "abbrvnat"
  cmd "bibliography" $ textual "../PaperTools/bibtex/jp"

authors ::  [AuthorInfo]
authors = [AuthorInfo "Gabriel Radanne" "gabriel.radanne@zoho.com" "Under the supervision of Jean-Philippe Bernardy"]

todo s = emph $ color "red" $ "TODO : " <> s

texttt = text . (cmd "texttt")

na = «nano-Agda»

-- | Math commands :
γ = Con $ cmd "gamma" nil
γty = Con $ cmd "Gamma" nil
γc = Con $ cmd "gamma_c" nil
γa = Con $ cmd "gamma_a" nil
γd = Con $ cmd "gamma_d" nil
γd' = Con $ cmd "gamma_d'" nil

bot = Con $ cmd "bot" nil
λ = Con $ cmd "lambda" nil
π = Con $ cmd "Pi" nil
σ = Con $ cmd "Sigma" nil

fa = Con $ cmd "forall" nil

mparen = outop "(" ")"
mbracket = outop "{" "}"

(\=) = binop 1 "="
(</>) = binop 1 space
(<->) = binop 1 nil
(<.>) = binop 1 "."
(≠) = binop 1 (cmd0 "neq")
a \== b = mparen $ a \= b
(∈) = binop 1 (cmd0 "in")
(→) = binop 1 (cmd0 "to")
(×)= binop 1 (cmd0 "times")
(|->) = binop 1 (cmd0 "mapsto")
concl = UnOp 1 (cmd "overline") 1
iff = UnOp 1 (\s -> mathsf "if " <> space <> s ) 1
proj p = UnOp 1 (\s -> s <> mathsf ("." <> p) ) 1
proj1 = proj "1"
proj2 = proj "2"

indice = UnOp 1 (\ x -> tex "_" <> braces x) 1

(⊢) = binop 1 (cmd0 "vdash")
(\:) = binop 1 ":"
(\::=) = binop 1 "::="

(<@) = binop 1 (cmd0 "leftleftarrows")
(@>) = binop 1 (cmd0 "rightrightarrows")


x,y,z,c,d,l,l2,t :: Math
x = text "x"
y = text "y"
z = text "z"
b = text "b"
c = text "c"
d = text "d"
ci = Con $ «C @(indice i)»

i = text "i"

l = text "`l"
l2 = text "`m"
li = Con $ «@l @(indice i)»
t = text "t"
ti = Con $ «@t @(indice i)»

star = Con $ cmd0 "star"

pair_ x y = mparen $ binop 1 "," x y
lambda_ x t = λ <-> x <.> t
let_ x a t = texttt«let» </> x \= a </> texttt«in» </> t
case_ x l =
    let l' = text $ mconcat $ intersperse ", " l in
    texttt«case» </> x </> texttt«of» </> mbracket l'
pi_ x y t = mparen ( x \: y ) → t
sigma_ x y t = mparen ( x \: y ) × t
fin_ l = mbracket l

minipage :: String -> TeX -> Tex a -> Tex a
minipage align length =
    env'' "minipage" [align] [«@length @(cmd0 "linewidth") »]

-- | Mathpartir

rule name pre conc =
    cmdm "inferrule" [name] [mkrows pre, conc]

-- | Document

abstract = env "abstract" « »

header = do
  maketitle
  abstract
  keywords classUsed $ sort
    [ ]

main = renderToDisk' SVG "Report" $ latexDocument preamble $ «

@header

@intro<-section«Introduction»

@deptype<-subsection«Dependent types»

In a regular programming language, terms and types live in two different worlds : you can't talk about terms in types and you can't manipulate type as you can manipulate terms. In a dependently typed programming language, types can depends on terms. This addition sounds quite small at first, but it makes the language significantly more powerful ... and significantly harder to typecheck.

Let's look at a simple example of dependent types using Agda. The syntax should be familiar enough if you know any typed functional language (like OCaml or Haskell).

@todo«Add an example : dependently typed vectors ? a bit simple and well known»

A language like Agda can be seen as a concrete form of the curry-howard isomorphism : you express a property as a type and give a term that will prove this property. This discipline is a bit different than the one used in Coq where proofs and programs are clearly separated.
@todo«A small example of proof, addition commutativity ?»
This means the type checking of a dependently type programs is actually quite equivalent to the task of theorem proving. This also means that the type checker will have to evaluate terms.

@subsection«Limitations of current implementations»

The Agda type checkers contains some well known issues that the dependent type theory community as been trying to solve :
@itemize«
  @item The ``case decomposition'' issue @todo«Show the incriminated piece of code».
  @item Since the Agda type checker is using a natural deduction style, the evaluation make terms grow in size very fast which implies import efficiency issues.
»

@todo«Some various attempts.»

A particular language, PiSigma @todo«Ref» is especially interesting since it tackle those problems by putting some constructions of the language in sequent calculus style, as explained in the next section. Unfortunately, even if this solve some issues, it creates some new ones, in particular the lack of subject reduction. We believe that those issues are present because part of the language is still in natural deduction style.


@subsection«Sequent calculus Presentation»

There is various presentation of what is Sequent calculus. In this article, we mean that every intermediate results or subterms is bind to a variable.
Sequent calculus is a well known presentation for classical logic but as not been evaluated as a presentation of a type theory.
According to @todo«REF», the translation from natural deduction to sequent calculus is mechanical, but it does seems interesting to actually look at the result.

@itemize«
  @item It's low-level, which make it suitable as backend for dependently-typed languages.
  @item Sharing is expressible (J. Launchbury - A Natural Semantics for Lazy Evaluation) @todo«REF». This would help solve some efficiency issues encountered in Agda, for example.
»

@todo«More details ?»

@subsection«Goals»

We aim to construct a type-theory which can be used as a backend for dependently-typed languages such as Agda or Coq. Such a language should be:
@itemize«
  @item A type-theory: correctness should be expressible via types.
  @item Low-level: one should be able to translate various high-level languages into this language while retaining properties such as run-time behaviour, etc.
  @item Minimal: the type-checking program should be amenable to verification.
»

@sec_lang<-section«Description of the language»

As explained @intro, every variable is binded. We can separate element of the langages, presentend figure @grammar_na, into various categories :

@paragraph«Variables» are separated in two categories : conclusion and hypothesis.

@paragraph«Hypothesis» are what is available in the beginning of the program or the result of an abstraction. It's not possible to construct an hypothesis.

@paragraph«Conclusions» are either an hypothesis or the result of a construction of conclusions. We mark conclusions by a bar on the top, like @(concl x) .

@paragraph«Destructions», marked by the letter @d, can be either a @texttt«case» or of the form @d, an application, a projection or a cut. We don't need to bind the results of a @texttt«case», as opposed to other destructions.

@paragraph«Dependant functions and products» are both of the same form : @(pi_ x (concl y) t) and @(sigma_ x (concl y) t) . The type on the left hand side can be a conclusion, since it doesn't depend on the type witness @x (@todo«right term ?»), hence it's possible to bind it before. On the other hand, the right hand side must be a term, since it will depend on @x .

@paragraph«Enumerations» are a set of scopeless and non-unique labels. Labels are plain strings starting with a `. We will note them @l, @l2.

@paragraph«Universes» are arangered in a tower of universes, starting at 0. We will use the usual notation @star = @star @indice(0) .

@paragraph«Constructions», marked by the letter @c, are either a conclusion, a universe, a type or a construction of pair, enum or function. As with destruction, the result must be bound to a conclusion.

@grammar_na<-figure«Grammar for @na»«
@minipage"t"«0.4»«@align(
  (\(x:xs) -> [ «@t ::=@space», x ] : map (\y -> [ « |@space»  , y ]) xs)
  [ «@(concl x)»,
    «@(let_ x d t)» ,
    «@(case_ x [ «@(mparen $ l → t) @text«*»» ])» ,
    «@(let_ (concl x) c t)»
  ]
  ++ [ «» ] :
  (\(x:xs) -> [ «@d ::=@space», x ] : map (\y -> [ « |@space»  , y ]) xs)
  [ «@x @space @(concl y)» ,
    «@(proj1 x) @space | @space @(proj2 x) » ,
    «@(color "red" «@(concl x \: concl y)»)»
  ]
)»
@minipage"t"«0.4»«@align(
  (\(x:xs) -> [ «@c ::=@space», x ] : map (\y -> [ «|@space»  , y ]) xs) $
  map (mconcat . intersperse «@space|@space»)
  [ [ «@x» ],
    [ «@λ @x . @t»,             «@(pi_ x (concl y) t)» ],
    [ «(@(concl x),@(concl y))»,«@(sigma_ x (concl y) t)» ],
    [ «@l»,                     «@(fin_ l)» ],
    [ «@star @(indice i)» ]
  ]
)»
»

Conclusions are the result of constructions of conclusion or an hypothesis. An hypothesis is the result of a destruction of hypothesis or an abstraction. This means that we can only produce constructions of destructions, hence there is no reduction possible and the program is in normal form.

 Obviously we don't want to write programs already in normal form, so we need a way to construct hypotheses from conclusions. That is what the cut construction, in red in @grammar_na, is for. It allows to declare a new hypothesis, given a conclusion and its type. The type is needed for type checking purposes.


@sec_heap<-section«The Heap»

Since the language is based on variables and bindings, we need a notion of environment. This notion is captured in a heap composed of several mapping :

@itemize«
  @item @γty   @(x |-> concl y ) : The context heap, containing the type of hypotheses.
  @item @γc  @(concl x |-> c)  : The heap for constructions.
  @item @γa  @(x |-> y) : The heap for aliases.
  @item @γd  @(x |-> d) : The heap for cuts and destructions.
  @item @γd' @(d |-> x) : The reverse map from destruction to hypotheses.
»

We have @γ = (@γty, @γc, @γa, @γd, @γd').

The details of how to update the heap will be explained @sec_typecheck.

@subsection«A bit of sugar»

Of course, it's impossible to write reasonable programs with this syntax, it's far too much verbose and tedious for humans. We introduced another simpler syntax that you can see below. It's possible to translate this new syntax to the low-level one and this translation is purely syntactic.

@fig_syntaxes<-figure«Regular and low-level syntax.»«
  @todo«Two columns comparison of the two syntax.»
»

@fig_syntaxes is an example of a program in regular syntax and the translation to the low-level syntax. As you can see, the low-level version is very verbose, which shows the need for the regular one.

@subsection«Examples»

@sec_type<-section«Type system»

The type rules for @na are quite usual, most of the cleverness is contained in the way the heap is updated. Hence we will start by presenting environment extensions.

@subsection«Environment extensions»

We will use the same notation as in @sec_heap : @x for hypotheses, @(concl x) for conclusions, @c for constructions and @d for destructions.
@align[
  [ «@(γ + x)», «= @γ, @x», «@text«new hypothesis»» ]
]

When adding a destruction definition, we check if a similar destruction definition exist using @γd. This allows sharring for multiple application of a function on the same argument.
@align[
  [ «@(γ + (x \== d))», «= @γ , @(x \== y)», «@(iff $ (y \== d) ∈ γ)» ],
  [ «»                , «= @γ , @(x \== d)», «@text«otherwise»»       ]
]

@todo«Do we actually handle this ?»
@align[
  [ «@γ + @(concl x \== c)», «= @γ, @(concl x \== concl y)», «@(iff $ concl y \== c ∈ γ)» ],
  [ «»                     , «= @γ, @(concl x \== c)»      , «@text«otherwise»»           ]
]

During a case, we keep track of constraints on the variable decomposed by the case, Allowing us to know inside the body of a case which branch we took. Of course, if two imcompatible branches are taken, we stop the typechecking immediatly, since the context is inconsistent.
@align[
  [ «@γ + @(l \== x)», «= @γ»            , «@(iff $ l \== x ∈ γ)»                         ],
  [ «»               , «= @bot»          , «@(iff $ l2 \== x ∈ γ) @text" for " @(l ≠ l2)» ],
  [ «»               , «= @γ, @(l \== x)», «@text«otherwise»»                             ]
]

@typerule<-subsection«Typing rules»

@(γ ⊢ d) : check a destruction.
@mathpar[[
  «@(rule «» [
      «@(γ ⊢ y @> (pi_ z (text«A») (text«B»)))»,
      «@(γ ⊢ concl z <@ text«A»)»
     ]
     «@(γ ⊢ y </> concl z)») »,
  «@(rule «» [
      «@(γ ⊢ y @> (sigma_ z (text«A») (text«B»)))»
     ]
    «@(γ ⊢ proj1 y)») »,
  «@(rule «» [
      «@(γ ⊢ y @> (sigma_ z (text«A») (text«B»)))»
     ]
    «@(γ ⊢ proj2 y)») »,
  «@(rule «» [
      «@(γ ⊢ concl x <@ concl (text«A»))»
     ]
     «@(γ ⊢ concl x \: concl (text«A»))») »,
  «@(rule «@todo«Why is this in destruction category ?»» [ « » ]
     «@(γ ⊢ concl x \= c)») »
]]

@(γ ⊢ x @> text«A») : infer the type of an hypothesis
@mathpar[[
  «@(rule «» [
      «@γty (@x) = @text«A»»
     ]
     «@(γ ⊢ x @> (text«A»))») »,
  «@(rule «» [
      «@γd (@x) = @(y </> concl z)»,
      «@(γ ⊢ y @> (pi_ z (text«A») (text«B»)))»
     ]
     «@(γ ⊢ x @> let_ z (concl z) (text«B»))») »,
  «@(rule «» [
      «@γd (@x) = @(proj1 y)»,
      «@(γ ⊢ y @> (sigma_ z (text«A») (text«B»)))»
     ]
     «@(γ ⊢ x @> concl (text«A»))») »,
  «@(rule «» [
      «@γd (@x) = @(proj2 y)»,
      «@(γ ⊢ y @> (pi_ z (text«A») (text«B»)))»
     ]
     «@(γ ⊢ x @> let_ z (proj1 y) (text«B»))») »,
  «@(rule «» [
      «@γd (@(concl x)) = @(mparen (concl x \: concl (text«A»)))»
     ]
     «@(γ ⊢ concl x @> concl (text«A»))») »
]]

@(γ ⊢ t <@ text«C») : check a term or a normal form.
@mathpar[[
  «@(rule «@todo«How do I do indices ?»» [
      «@(fa </> i) @(cmd0 "quad") @(γ + (li \== x) ⊢ ti <@ text«C»)»,
      «@γty (x) = @(fin_ li)»
     ]
     «@(γ ⊢ case_ x [«@(li |-> ti)»] <@ (text«C»))») »,
  «@(rule «» [
      «@(γ + (x \== d) ⊢ t <@ (text«C»))»,
      «@(γ ⊢ d)»
     ]
     «@(γ ⊢ let_ x d t <@ (text«C»))») »,
  «@(rule «@(todo«seems fishy»)» [
      «@γa (@z) = @x»,
      «@(γ ⊢ x @> (text«A»))»,
      «@(γ ⊢ (text«A») <@ (text«C»))»
     ]
     «@(γ ⊢ z <@ (text«C»))») »,
  «@(rule «» [
      «@γc (@x) = @c»,
      «@(γ ⊢ c @> (text«C»))»
     ]
     «@(γ ⊢ x <@ (text«C»))») »
]]
@todo«Isn't the (trivial) rule to verify stuff in the form "let x = c in t" missing here ?»

@(γ ⊢ c <@ text«C») : check a construction
@mathpar[[
  «@(rule «» [
      «@(γ + (x \== d) ⊢ c <@ (text«C») )»
     ]
     «@(γ ⊢ c <@ (let_ x d (text«C»)) )») »,
  «@(rule «@todo«How do I do indices ?»» [
      «@(fa </> i) @(cmd0 "quad") @(γ + (li \== x) ⊢ c <@ ci)»,
      «@γty (x) = @(fin_ li)»
     ]
     «@(γ ⊢ c <@ case_ x [«@(li |-> ci)»] )») »,
  «@(rule «» [
      «@γc (@x) = @(text«C»)»,
      «@(γ ⊢ c <@ (text«C»))»
     ]
     «@(γ ⊢ c <@ concl x)») »,
  «@(rule «» [
      «@(γ ⊢ concl y <@ concl (text«A»))»,
      «@(γ +  x \== (concl y \: concl (text«A»)) ⊢ concl z <@ (text«B»))»
     ]
     «@(γ ⊢ pair_ (concl y) (concl z) <@ sigma_ x (concl (text«A»)) (text«B»))») »,
  «@(rule «@todo«Isn't that suposed not to work ?»» [
      «@(γ + mparen (y \: concl (text«A»)) ⊢ t <@ let_ x y (text«B»))»
     ]
     «@(γ ⊢ (lambda_ y t) <@ pi_ x (concl (text«A»)) (text«B»))») »
]]


@sec_typecheck<-section«Typechecking and evaluation strategy»

@subsection«A generic approach»

@todo«Talk about the continuation passing style thingy.»


@subsection«Evaluation : lazy or strict ?»


@section«Results»


»
