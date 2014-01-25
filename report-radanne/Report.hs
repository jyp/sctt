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
  unless inMetaPost $ do
    usepackage "natbib" ["sectionbib"]
    usepackage "tikz" []
    cmd "usetikzlibrary" $ tex "shapes,arrows"
    usepackage "tabularx" []

    -- title "Explaining Classical Linear Logic's Concurrency by Going to Continuations and Coming Back"
    title "A sequent-calculus presentation of type-theory"
    authorinfo classUsed authors

authors ::  [AuthorInfo]
authors = [AuthorInfo "Gabriel Radanne" "gabriel.radanne@zoho.com" "Under the supervision of Jean-Philippe Bernardy"]

todo s = emph $ color "red" $ "TODO : " <> s

texttt = text . (cmd "texttt")

na = «nano-Agda»

-- Math commands :
γ = Con $ cmd "Gamma" nil
γc = Con $ cmd "Gamma_c" nil
γa = Con $ cmd "Gamma_a" nil
γd = Con $ cmd "Gamma_d" nil
γd' = Con $ cmd "Gamma_d'" nil

λ = Con $ cmd "lambda" nil

(|->) = binop 1 (cmd0 "mapsto")
concl = UnOp 1 (cmd "overline") 1

x,y,c,d :: Math
x = text "x"
y = text "y"
b = text "b"
c = text "c"
d = text "d"

l = text "'l"
t = text "t"

star = cmd0 "star"

llet x a t = «@texttt«let » @x = @a @texttt« in » @t»
cpi x y t = «@(cmd "Pi" nil) ( @x : @y ) @t»
csig x y t = «@(cmd "Sigma" nil) ( @x : @y ) @t»
cfin l = «{ @l s }»

(/::=) = binop 1 "::="

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
@todo«A small example of proof, addition conductivity ?»
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

@section«Description of the language»

The language contains three constructions : functions, pairs and finite enumeration. Each of those have constructors, destructors and types.
Variables are separated in two categories : conclusion and hypothesis.
Hypothesis are what is available in the beginning of the program or the result of an abstraction. It's not possible to construct an hypothesis.
A conclusion is either an hypothesis or the result of a construction of conclusions.
This means that we can only produce constructions of destructions, hence there is no reduction possible and the program is in normal form.

 Obviously we don't want to write programs already in normal form, so we need a way to construct hypothesis from conclusion. That is what the cut construction in for. The cut construction is quite simple, it allows to declare a new hypothesis, given a conclusion and its type. The type is needed for type checking purposes.

@figure«Grammar for @na»«
@align(
  (\(x:xs) -> [ «@t ::=@space», x ] : map (\y -> [ « |@space»  , y ]) xs)
  [ «@(concl x)»,
    «@(llet x d t)» ,
    «@texttt«case » @x @texttt« of » @b @text«*»» ,
    «@(llet (concl x) c t)»
  ]
  ++ [ «» ] :
  (\(x:xs) -> [ «@d ::=@space», x ] : map (\y -> [ « |@space»  , y ]) xs)
  [ «@x @space @(concl y)» ,
    «@x @texttt«.1» @space | @space @x @texttt«.2»» ,
    «@(color "red" «@(concl x) : @(concl y)»)»
  ]
)
@todo«make it two columns»
@align(
  (\(x:xs) -> [ «@d ::=@space», x ] : map (\y -> [ «|@space»  , y ]) xs) $
  map (mconcat . intersperse «@space|@space»)
  [ [ «@x» ],
    [ «@λ @x . @t»,             «@(cpi x (concl y) t)» ],
    [ «(@(concl x),@(concl y))»,«@(csig x (concl y) t)» ],
    [ «@l»,                     «@(cfin l)» ],
    [ «@star» ]
  ]
)
»


@section«The Heap»

Since the language is based on variables and bindings, we need a notion of environment. This notion is captured in a heap composed of several mapping :

@itemize«
  @item @γ   @(x |-> concl y ) : The context heap, containing the type of hypotheses.
  @item @γc  @(concl x |-> c)  : The heap for constructions.
  @item @γa  @(x |-> y) : The heap for aliases.
  @item @γd  @(x |-> d) : The heap for cuts and destructions.
  @item @γd' @(d |-> x) : The reverse map from destruction to hypotheses.
»


The details of how to update the heap will be explained @sec_typecheck.

@subsection«A bit of sugar»

Of course, it's impossible to write reasonable programs with this syntax, it's far too much verbose and tedious for humans. We introduced another simpler syntax that you can see below. It's possible to translate this new syntax to the low-level one and this translation is purely syntactic.

@fig_syntaxes<-figure«Regular and low-level syntax.»«
  @todo«Two columns comparison of the two syntax.»
»

@fig_syntaxes is an example of a program in regular syntax and the translation to the low-level syntax. As you can see, the low-level version is very verbose, which shows the need for the regular one.

@subsection«Examples»

@sec_typecheck<-section«Typechecking and evaluation strategy»

@subsection«A generic approach»

@todo«Talk about the continuation passing style thingy.»


@subsection«Evaluation : lazy or strict ?»


@section«Results»

»
