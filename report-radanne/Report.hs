{-# OPTIONS_GHC -i../src/ -XTypeSynonymInstances -XOverloadedStrings -XRecursiveDo -pgmF marxup3 -F #-}

import MarXup
import MarXup.Latex
import MarXup.Latex.Math
import MarXup.Latex.Bib
import MarXup.Tex

import qualified Terms as T
import qualified TexnAgda as TA
import qualified Ident

import Control.Monad
import Control.Monad.Fix (MonadFix,mfix)
import Control.Applicative
import Data.Monoid
import Data.List (sort,intersperse)
import Data.String

classUsed ::  ClassFile
classUsed = LNCS

classFile LNCS = "llncs"

preamble :: Bool -> Tex ()
preamble inMetaPost = do
  if inMetaPost
  then documentClass "article" ["13pt"]
  else documentClass (classFile classUsed) [] -- ["authoryear","preprint"]
  stdPreamble
  mathpreamble classUsed
  cmd "input" (tex "../PaperTools/latex/unicodedefs")
  unless inMetaPost $ do
    usepackage "natbib" ["sectionbib"]
    usepackage "tikz" []
    usepackage "fullpage" []
    usepackage "mathpartir" []
    usepackage "subcaption" []
    usepackage "listings" []
    cmd "input" (tex "lst")
    usepackage "hyperref" ["colorlinks","citecolor=blue"]
    cmd "usetikzlibrary" $ tex "shapes,arrows"
    usepackage "tabularx" []

    title "A sequent-calculus presentation of type-theory"
    authorinfo classUsed authors

bibliographyAll :: TeX
bibliographyAll = do
  bibliographystyle "abbrvnat"
  bibliography "../PaperTools/bibtex/jp"

authors ::  [AuthorInfo]
authors = [AuthorInfo "Gabriel Radanne" "gabriel.radanne@zoho.com" "Under the supervision of Jean-Philippe Bernardy"]

todo s = emph $ color "red" $ "TODO: " <> s

texttt = text . (cmd "texttt")

na :: TeX
na = «nano-Agda»

item' x = cmd "item" (cmd "textbf" x)
description = env "description"

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
nat = Con "ℕ"

fa = Con $ cmd "forall" nil

mparen = outop "(" ")"
mbracket = outop "{" "}"
mbrac = outop "[" "]"

quad = cmd0 "quad"

app f x = f <-> mparen x
(\=) = binop 1 "="
(≡) = binop 1 (cmd0 "equiv")
(≅) = binop 1 (cmd0 "cong")
(</>) = binop 1 space
(<->) = binop 1 nil
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

indice = UnOp 1 (\ x -> tex "_" <> braces x) 1

(@-) = BinOp 1 (\ x y -> x <> tex "_" <> braces y) 1 1

(⊢) = binop 1 (cmd0 "vdash")
(\::=) = binop 1 "::="

(<@) = binop 1 (cmd0 "leftleftarrows")
(@>) = binop 1 (cmd0 "rightrightarrows")


x,y,z,c,d,l,l2,t :: Math
x = text "x"
y = text "y"
x' = text "x'"
y' = text "y'"
z = text "z"
w = text "w"

c = text "c"
cty = text "C"
d = text "d"

xty = text "X"
xty' = text "X'"
yty = text "Y"
zty = text "Z"

i = text "i"
j = text "j"

l = text "`l"
l2 = text "`m"
t = text "t"
t' = text "t'"
tty = text "T"
tty' = text "T'"

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

centering = cmd0 "centering"

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

-- | Document

abstract :: TeX
abstract = env "abstract" « »

header = do
  maketitle
  abstract
  keywords classUsed $ sort
    [ ]


main = renderToDisk' EPS "Report" $ latexDocument preamble $ «

@header

@intro<-section«Introduction»

This report aims to present the work accomplished during my 6 month internship in Chalmers, under the supervision of Jean-Philippe Bernardy and with the collaboration of Guilhem Moulin and Andreas Abel.

This report presuppose some familiarity with a statically typed functionnal language like OCaml or Haskell, but no extra knowledge on type theory or dependent types is required.

@deptype<-subsection«Dependent types»

In most programming languages, terms and types live in two different worlds: one can not refer to terms in types and types can not be manipulatep like terms. In a dependently typed programming language, types can depends on terms. This addition may sound quite small at first, but it makes the language significantly more powerful... and significantly harder to typecheck. Dependent types were previously mostly used for theorem proving (in Coq, for example). However they have since gain some popularity as a base for programming languages with Agda @citep"norell_practical_2007", Idris @citep"brady_idris_2013" or ATS @citep"chen_ats_2005". It is also related to the addition of new features in more mainstream programming languages, like the addition of GADTs in OCaml or Haskell.

GADTs, or Generalized Algebraic Datatypes, @citep"xi_guarded_2003" allows to encode some properties in a non dependent type systems that would usually need dependent types. For example it is possible to use GADTs to encode vectors shown @example. In the presence of GADTs, terms and types still live in two different words. GADTs are not as powerful as dependent types, as shown in the example @example.

@example<-subsection«An example in Agda»

Numerous examples have been presented to motivate the use of dependent types in mainstream programming @citep"oury_power_2008" @todo«add more». We give here a short and simple example to outline the specificity of dependent type languages from the user point of view but also from the typechecking point of view.

For this example, we use Agda. The syntax should be familiar enough given some knowledge of a statically-typed functional language.

Let us first define the @agdai«Nat» datatype.
@agdacode«
data Nat : Set where
  Zero : Nat
  Succ : Nat -> Nat
»
This definition is very similar to a definition using GADTs in OCaml or Haskell. @agdai«Set» show that @agdai«Nat» is a base type, as @agdai«Int» or @agdai«Char» would be in OCaml or Haskell.

Let us now move on to a more interesting datatype: vectors with fixed length.
@agdacode«
data Vec (A : Set) : Nat -> Set where
  Nil : Vec A Zero
  Cons : {n : Nat} -> A -> Vec A n -> Vec A (Succ n)
»
One can see in the signature of the type that @agdai«Vec» takes a type @agdai«A», the type of the elements, and a natural number which is the length of the vector. The declaration of @agdai«Cons» exhibit a very useful feature of Agda: the argument @agdai«{n : Nat}» is implicit. The compiler infers this argument whenever possible and the length of the vector we are consing to is not needed. Providing the length every call of @agdai«Cons» would have been quite cumbersome.

We can use this type information to implement a type-safe @agdai«head» function:
@agdacode«
head : {A : Set} { n : Nat } -> Vec A (Succ n) -> A
head (Cons x xs) = x
»
The compiler knows that the @agdai«Nil» case can not happen since the length of the provided vector is at least one. Any call to @agdai«head» with a empty vector argument do not typecheck.

Assuming an infix addition function @agdai«(+): Nat -> Nat -> Nat», we can also implement the append function, which requires us to manipulate the natural numbers embedded in the type:
@agdacode«
append : forall { n m A } -> Vec A n -> Vec A m -> Vec A (n + m)
append Nil ys = ys
append (Cons x xs) ys = Cons x (append xs ys)
»
In the type, we assert that the length of the results is the sum of the lengths of the operands. We use the @agdai«forall» quantifier to declare the implicit arguments without specifying their types, as Agda can infer them.

For now, we have seen that dependent types can be useful to assert properties on some datatype. Those simple examples could be encoded with GADTs even if it would need additional burden and be far less easy to manipulate. We could go on and declare some other functions on vectors, however, we look at something difficult or impossible to do using GADTs.

We present an embedding of relational algebra that was first discussed by @citet"oury_power_2008". A typed embedded DSL for relational databases present interesting difficulties: relation algebra operators are hard to type, especially join and cartesian product, and type safety usually relies on the static declaration of a schema. We use dependent types to overcome those two issues.

Let us first considerate the definition of a table schema:
@agdacode«
data U : Set where
  BOOL : U
  CHAR : U
  NAT : U
  VEC : U -> Nat -> U

Schema : Set
Schema = List (String xx U)
»
Here, @agdai«xx» is simply the type of pairs. The @agdai«U» type is the universe type for the values inside our database. Databases are restricted in what type of value they can handle so this restriction is perfectly valid. A Schema here is simply a list of columns with a name and a type.

We need to link the constructors of @agdai«U» to their representation as Agda types:
@agdacode«
el : U -> Set
el BOOL = Bool
el CHAR = Char
el NAT = Nat
el (VEC x n) = Vec (el x) n
»

A table is composed of rows which follow a schema.
@agdacode«
data Row : Schema -> Set where
  EmptyRow : Row []
  ConsRow : forall {name u s} -> el u -> Row s -> Row ((name , u) :: s)

Table : Schema -> Set
Table s = List (Row s)
»
A Row is a list with added type information about the schema. Notice how the table is parametrized by the schema it instantiate.

We can now define a relational algebra expression:
@agdacode«
data RA : Schema -> Set where
  Read : forall { s } -> Table s -> RA s
  Union : forall { s } -> RA s -> RA s -> RA s
  Product : forall { s s' } -> {So (disjoint s s')} -> RA s -> RA s' -> RA (s ++ s')
  Select : forall { s } -> Expr s BOOL -> RA s -> RA s
  ...
»
The first two constructors are quite straightforward, @agdai«Read» read a given table and @agdai«Union» merge two tables following the same schema. The @agdai«Product» constructor, however, is much more interesting. To be able to compute the cartesian product of two table, they must have disjoint columns. We can quite easily provide a function checking that two schema are disjoint, of type:
@agdacode«
disjoint : Schema -> Schema -> Bool
»
We now want to ensure that this property is checked at the type level. In order to do so, we define a bridge from @agdai«Bool» to types:
@agdacode«
So : Bool -> Set
So false = Empty
So true = Unit
»
@agdai«So» takes a @agdai«Bool» and returns a type. The @agdai«Empty» type is, as its names indicates, a type with no elements. @agdai«Unit» being the type with only one element. Hence, in order to typecheck, @agdai«So x» must be @agdai«Unit» and @agdai«x» must be @agdai«true».

The @agdai«Product» constructor takes @agdai«So (disjoint s s')» as argument: this is a proof that @agdai«s» and @agdai«s'»  are indeed disjoint.

Finally we define expressions used by selects:
@agdacode«
data Expr : Schema -> U -> Set where
  _!_ : (s : Schema) -> (column : String) -> {p : So (occurs column s)} -> Expr s (lookup column s p)
  equal : forall { u s } -> Expr s u -> Expr s u -> Expr s BOOL
  literal : forall { u s } -> el u -> Expr s u
  ...
»
Constructors @agdai«equal» and @agdai«literal» are quite simple and could be encoded easily with GADTs. However, the @agdai«_!_» constructor, which allows to get the value of a column, take as argument @agdai«So (occurs column s)». This is a proof that the column appears in the schema. The @agdai«occurs» function would have the type:
@agdacode«
occurs : String -> Schema -> Bool
»
We want the @agdai«_!_» constructor to return an expression of the type of the return column, hence we could be tempted to use a mere lookup operator:
@agdacode«
lookup : (col : String) -> (s : Schema) -> U
»
However, Agda only accept terminating function to be executed at the type level. The @agdai«lookup» function, as defined here, is not guarantee to terminate. Hopefully, we know that, in the context of selects, this lookup always terminate thanks to the proof object @agdai«{p : So (occurs column s)}». Hence we define the lookup function with this type instead:
@agdacode«
lookup : (col : String) -> (s : Schema) -> So (occurs col s) -> U
»

We can see in this example multiple characteristics of dependently typed programming languages.
First, types and terms evolve in the same word and there is little to no distinction between them.
Secondly, terms inhabiting a type are proofs of the proposition expressed by this type. It is a very literal translation of the Curry-Howard isomorphism. This is quite different than in a theorem prover, like Coq, where the proof part and the programming part are usually separated.

Finally, the typechecker must evaluate terms in order to typecheck.
This make the typechecking more complicated and is the source of some limitation in current typecheckers. It is also part of the focus of this work.

@subsection«Limitations of current implementations»

The Agda typechecker contains some well known issues that the dependent type theory community has been trying to solve:
@itemize«
  @item The ``case decomposition'' issue, which is presentend later on, @example_ulf. This issue come from the fact that natural deduction style makes propagating typing constraints to subterms difficult.
  @item Since the Agda type checker is using a natural deduction style, The typechecker suffer efficiency issues. The inference copies part of terms and those parts cannot be shared in the Agda core representation of terms. Since the terms are not shared anymore, the typechecking must be done multiple time, causing performance penalties.
»

@todo«Some various attempts.»

A particular language, PiSigma @citep"AltenkirchDLO10" is especially interesting since it tackles those problems by putting some constructions of the language in sequent calculus style, as explained in the next section. Unfortunately, although this solve some issues, other are introduced. In particular, the language lacks subject reduction (evaluation does not preserve typechecking). We believe that those issues are present because part of the language is still in natural deduction style.

@subsection«Sequent calculus presentation»

There are various definitions of sequent calculus. In this report, we mean that every intermediate results or sub-terms are bind to a variable.
Sequent calculus is a well known presentation for classical logic but as not so far been evaluated as a presentation of a type theory.
The translation from natural deduction to sequent calculus is mechanical @citep"Puech_proof-upside_2013" but it does seems interesting to actually look at the result, since it presents interesting properties:
@itemize«
  @item It is low-level, which makes it suitable as back-end for dependently-typed languages.
  @item Sharing is expressible @citep"Launchbury_sharing_1993". In natural deduction style, we can't express the fact that two subterms are the same. This would help solve some efficiency issues encountered in Agda, for example.
»

@todo«More details ?»

@subsection«Goals»

We aim to construct a type-theory which can be used as a back-end for dependently-typed languages such as Agda or Coq. Such a language, that we will call @na, should be:
@itemize«
  @item A type-theory: correctness should be expressible via types.
  @item Low-level: one should be able to translate various high-level languages into this language while retaining properties such as run-time behaviour, etc.
  @item Minimal: It should be possible to formerly verify the type-checking program.
»

@sec_lang<-section«Description of the language»

Before describing the language itself, we define some common notion in type theory that we manipulate in the rest of this report.

@subsection«Preliminary vocabulary»

@paragraph«Constructor and destructors@newline»
A language is often separated into destructors (also called eliminations) and constructors. For example in the lambda calculus, lambda abstractions are constructors and applications are destructors. A destruction of construction can be reduced through β-reduction. In a more complicated language (including @na) we have pairs (constructors) and projections (destructors). The projection of a pair can be similarly β-reduced.

@paragraph«Universes@newline»
In regular programming languages, one has types and the set of types. You can not manipulate this set itself but since you can not use terms as types (and vice-versa), this is not an issue. However, in a dependently typed programming language, terms and types live together, and you can theoretically manipulate the set of types. Is this set of types a type itself ? For technical reasons @citep"benke_universes_2003" and in order to preserve the consistency of the type system, the answer must be no.

Types are classified in universes (also called ``sorts'' or ``kinds'') indexed by natural numbers.
We note those universes @(kind i) with @i ∈ @nat.
Base types, like @agdai«Int», are in @(kind 0). @(kind i) is in @(kind (i + 1)).
Types composed of other types live in the highest univers of their components. For example @texttt«(Char, Int)» live in @(kind 0) but @texttt«(Int, *0)» is in @(kind 1).  Finally, for ease of manipulation, any element in @(kind i) is in @(kind j) whenever @i ≤ @j. In the case of @na, typing rules for universes are given @tr_constr_concl.

@subsection«@na»

As explained @intro, every variable is bound. We can separate elements of the languages, presented figure @grammar_na, into various categories:

@description«

@item'«Variables» are separated in two categories: conclusions and hypotheses.
  @description«
  @item'«Hypotheses» are available in the beginning of the program or are the result of an abstraction. It is not possible to construct an hypothesis.

  @item'«Conclusions» are either an hypothesis or the result of a construction of conclusions. We mark conclusions by a bar on the top: @(concl x) .
»
@item'«Destructions», marked by the letter @d in @grammar_na, can be either a @texttt«case» (a pattern match) or of the form @d as shown in @grammar_na (@todo«can not do ref to internal labels»): an application, a projection or a cut. We do not need to bind the result of a @texttt«case», as opposed to other destructions.

@item'«Dependent functions and products» are both of the same form: @(pi_ x (concl y) t) and @(sigma_ x (concl y) t) . The type on the left hand side can be a conclusion, since it does not depend on the type witness @x (@todo«right term ?»), hence it is possible to bind it before. However, the right hand side must be a term, since it depends on @x. @x is an hypothesis since it is abstract here.

@item'«Enumerations» are a set of scopeless and non-unique labels. Labels are plain strings starting with an apostrophe. We note them @l, @l2.

@item'«Universes» are arranged in a tower, starting at 0, as explained above. We additionnaly use the shorthand @star = @star @indice(0).

@item'«Constructions», marked by the letter @c and detailed @grammar_na (@todo«can not do ref to internal labels»), are either a conclusion, a universe, a type or a construction of pair, enum or function. The result must be bound to a conclusion.
»
@grammar_na<-figure«Abstract syntax for @na»«
  @grammar_term<-subfigure"b"«0.3»«Terms»«@align(
  (\(x:xs) -> [ «@t ::=@space», x ] : map (\y -> [ « |@space»  , y ]) xs)
  [ «@(concl x)»,
    «@(let_ x d t)» ,
    «@(case_ x [ «@(mparen $ l → t) @text«*»» ])» ,
    «@(let_ (concl x) c t)»
  ])»
  @grammar_destr<-subfigure"b"«0.3»«Destructions»«@align(
  (\(x:xs) -> [ «@d ::=@space», x ] : map (\y -> [ « |@space»  , y ]) xs)
  [ «@x @space @(concl y)» ,
    «@(proj1 x) @space | @space @(proj2 x) » ,
    «@(color "red" «@(concl x <:> concl y)»)»
  ])»
  @grammar_Constr<-subfigure"b"«0.3»«Constructions»«@align(
  (\(x:xs) -> [ «@c ::=@space», x ] : map (\y -> [ «|@space»  , y ]) xs) $
  map (mconcat . intersperse «@space|@space»)
  [ [ «@x» ],
    [ «@λ @x . @t»,             «@(pi_ x (concl y) t)» ],
    [ «(@(concl x),@(concl y))»,«@(sigma_ x (concl y) t)» ],
    [ «@l»,                     «@(fin_ l)» ],
    [ «@star @(indice i)» ]
  ])»
»

Conclusions are the result of constructions of conclusions and hypothesis is the base case of constructions. An hypothesis is the result of destructions of hypotheses. This means that we can only produce constructions of destructions, hence there is no reduction possible and the program is in normal form.

 Obviously we do not only want to write programs already in normal form, so we need a way to construct hypotheses from conclusions. That is what the cut construction, in red in @grammar_na, is for. It allows to declare a new hypothesis, given a conclusion and its type. The type is needed for type checking purposes.

@subsection«A bit of sugar»

Of course, it is tedious to write reasonable programs with this syntax, it is far too verbose and tedious for humans. We introduce another simpler syntax that can be seen below. It is possible to translate this new syntax to the one defined in the previous section. The translation can be done even on type-incorrect terms and hence do not need preliminary typechecking. It is similar to CPS transformation @citep"plotkin_call-by-name_1975".

Every program in the high level syntax is composed of two parts: a term and a type. The typechecker check the term against the type.
@fig_syntaxes is an example of a program in high-level syntax and the translation to the low-level syntax. The low-level version is very verbose, which argues for the need of a high-level one.

@fig_syntaxes<-figure«The polymorphic identity, in high-level and low-level syntax.»«
  @minipage"c"«0.3»«@nacode"../examples/010-Lam.ma"»
  @minipage"c"«0.3»«@nacode"../examples/010-Lam.na"»
  @centering
»

@subsection«An interesting example»

Before giving the details of the type system and the evaluation strategy, let us consider a small example: we want to create a non-dependent datatype, as used in Agda, Haskell or OCaml, in @na. We only have enumerations, dependent products and dependent functions but this is enough to encode datatypes. @fig_iex shows a very simple Agda datatype and the equivalent code in @na.

The trick in this encoding is to separate the tag part (@nai«Foo» and @nai«Bar») from the type part. The tag part can be easily encoded in a enumeration. For the type part, we take advantage of the dependent product to pattern match the tag and return the appropriate type. In this case, we have a datatype with a parameter, which is translated into a simple function.

@fig_iex<-figure«A datatype in Agda and @na.»«
@minipage"c"«0.4»«
@agdacode«
data MyDatatype (s : Set) : Set where
  Foo : s -> MyDatatype s
  Bar : MyDatatype s
»»
@minipage"c"«0.4»«@nacode"../examples/datatype.ma"»
@centering

@todo«Not completely sure about the fact that in @na, the branches return @(kind 0).»»

This example shows the fact that, in a dependently typed programming language, enumerations are enough to simulate datatypes, which is clearly not possible in a non dependently typed programming language. Here, a more powerful type system allows to use a simpler core language.



@sec_type<-section«Type system»

The type rules for @na are quite usual, most of the cleverness is contained in the way the environment is updated. Hence we start by presenting environment and environment extensions.

We use the same notation as in @sec_heap: @x for hypotheses, @(concl x) for conclusions, @c for constructions and @d for destructions. For clarity, elements used as types are capitalized.

@sec_heap<-subsection«The Heap»

Because the language is based on variables and bindings, we need a notion of environment. This notion is captured in a heap composed of several mapping:

@itemize«
  @item @γty @(x |-> concl y ) : The context heap, containing the type of hypotheses.
  @item @γc  @(concl x |-> c)  : The heap for constructions.
  @item @γa  @(x |-> y) : The heap for aliases.
  @item @γd  @(x |-> d) : The heap for cuts and destructions.
  @item @γd' @(d |-> x) : The reverse map from destruction to hypotheses. @todo«do we really talk about this one ?»
»

We have @γ = (@γty, @γc, @γa, @γd, @γd').

@envext<-subsection«Environment extensions»

Here are details of how to update the heap when registering new information. We use the @(math $ cmd0 "gets")operator to denote an update.

When typechecking abstractions, like lambda or dependent functions and products, we need to introduce new hypotheses in the context without any value.
@align[
  [ «@(γ + cut_ x (concl yty))», «= @γ @text« with » @(γty ← cut_ x (concl yty))» ]
]

When adding a destruction definition, we check if a similar destruction definition exist using @γd. This allows automatic recovery of sharing for multiple application of a function to the same argument.
@align[
  [ «@(γ + (x \== d))», «= @γ @text« with » @(γa ← (x \== y))», «@(iff $ (y \== d) ∈ γd)» ],
  [ «»                , «= @γ @text« with » @(γd ← (x \== d))», «@text«otherwise»»       ]
]

The rule for conclusions is straightforward, since we do not handle automatic sharing for conclusions as we do for destructions. Rediscovering sharing automatically for constructions is more costly than for destructions, since there are at most two components in a destruction whereas there can be far more in constructions. This additional cost should be evaluated but this is left for future work.
@align[
  [«@γ + @(concl x \== c)», «= @γ @text« with » @(γc ← (concl x \== c))»]
]

When checking or evaluating a case, we keep track of constraints on the variable decomposed by the case, Allowing us to know inside the body of a case which branch we took. Of course, if two incompatible branches are taken, we abort the typechecking, since that means the context is inconsistent.
@align[
  [ «@γ + @(l \== x)», «= @γ»            , «@(iff $ l \== x ∈ γc)»                         ],
  [ «»               , «= @bot»          , «@(iff $ l2 \== x ∈ γc) @text" for " @(l ≠ l2)» ],
  [ «»               , «= @γ @text« with » @(γc ← (l \== x))», «@text«otherwise»»                             ]
]
@todo«not sure if it is @γc, it seems so in the code.»

@eqrules<-subsection«Equality rules»

Equality rules, presented in @fig_eqrules, can only be applied to normalized terms (a term without cuts). The equality relation, noted @(γ ⊢ t \= t') is commutative for @t and @t', hence the rules are given only in one way. We define two operators that are used in equality rules:

@itemize«
@item @(x ≡ y) is the definitional equality between variables. It means @x and @y are the same symbol.
@item @(x ≅ y) is the symbol equality with respect to aliases. It is defined as @(x ≡ y ∧ app γa x ≅ y ∧ x ≅ app γa y). Since the alias environment is only for hypotheses, this operator is not usable for conclusions.
»
Those two operators are used to test equality between conclusions and hypotheses respectively.

The first rule, which can be summarized as ``If the context is inconsistent, everything is true'', is necessary to handle uninteresting branches for @texttt«case». It fulfills the same purpose as the rule for environment extensions on labels presented @envext.

The last two rules are interesting in that they are asymmetric: a construction on the left and a variable on the right. To test the equality in this case, we need to introduce new variables and apply destructions on the left-hand side of the equality. This allows to have η-equality in the type theory, therefore we can prove that @(lambda_ x (mparen (text«f» </> x)) .=. text«f»), even if @text«f» is abstract.

@fig_eqrules<-figure«Equality rules»«
@align[
  [ «@(bot ⊢ text "_")», «@lra true»],
  [],
  [ «@(γ ⊢ let_ x d t \= t')», «@lra @(γ + x \== d ⊢ t \= t')»],
  [ «@(γ ⊢ let_ (concl x) c t \= t')», «@lra @(γ + (concl x) \== c ⊢ t \= t')»],
  [ «@(γ ⊢ case_ x [«@((l @- i) |-> (t @- i))»] \= t)»,
    «@lra @fa @i @quad @(γ + x \== (l @- i) ⊢ (t @- i) \= t)»],
  [ «@(γ ⊢ concl x \= concl y)»,
    «@lra @(concl x ≡ concl y ∧ γ ⊢ app γc (concl x) \= app γc (concl y))»],
  [],
  [],
  [ «@(γ ⊢ (l \= l))», «@lra true»],
  [ «@(γ ⊢ (kind i \= kind j))», «@lra @(i \= j)»],
  [ «@(γ ⊢ x \= y)», «@lra @(x ≅ y)»],
  [ «@(γ ⊢ lambda_ x t \= lambda_ y t')», «@lra @(γ + (x \== y) ⊢ t \= t')»],
  [ «@(γ ⊢ pair_ (concl x) (concl x') \= pair_ (concl y) (concl y'))»,
    «@lra @(γ ⊢ concl x \= concl y ∧ γ ⊢ concl x' \= concl y') »],
  [ «@(γ ⊢ pi_ x (concl y) t \= pi_ x' (concl y') t')»,
    «@lra @(γ ⊢ concl y \= concl y' ∧ γ + (x \== x') ⊢ t \= t') »],
  [ «@(γ ⊢ sigma_ x (concl y) t \= sigma_ x' (concl y') t')»,
    «@lra @(γ ⊢ concl y \= concl y' ∧ γ + (x \== x') ⊢ t \= t') »],
  [ «@(γ ⊢ (fin_ (l @- i) \= fin_ (l2 @- i)))»,
    «@lra @fa @i @quad @((l @- i) \= (l2 @- i))»],
  [ «@(γ ⊢ lambda_ x t \= y)»,
    «@lra @(γ + (concl x \== x) + (z \== (y </> concl x)) ⊢ t \= z)»],
  [ «@(γ ⊢ pair_ (concl x) (concl x') \= y)»,
    «@lra @(γ + (z \== proj1 y) ⊢ concl x \= z ∧ γ + (z \== proj2 y) ⊢ concl x' \= z) »]]»

@typerule<-subsection«Typing rules»

The typing rules can be divided in three relations. Two relations are typechecking relations for respectively terms and constructions, we note typechecking @(Con $ cmd0 "leftleftarrows"). The relation for destruction is an inference, noted @(Con $ cmd0 "rightrightarrows").

We note typechecking for terms @(γ ⊢ t <@ tty), the rules are presented @tr_term. The type here is always a complete term and must have been checked beforehand.
In the @ruleref«Constr» rules, we do not need to typecheck the construction in detail since any construction added this way is typechecked by either the @ruleref«Concl» rule or the @ruleref«Cut» rule. In the @ruleref«Destr» rule, we use the inference relation on destructions so that every hypothesis has a type in the context.

@tr_term<-figure«Typechecking a term: @(γ ⊢ t <@ tty)»«
@mathpar[[
  «@(rule «Case» [
      «@(fa </> i) @quad @(γ + ((l @- i) \== x) ⊢ (t @- i) <@ tty)»,
      «@γty (x) = @(fin_ $ (l @- i))»
     ]
     «@(γ ⊢ case_ x [«@((l @- i) |-> (t @- i))»] <@ tty)») »,
  «@(rule «Destr» [
      «@(γ + (x \== d) + cut_ x tty'  ⊢ t <@ tty)»,
      «@(γ ⊢ d @> tty')»
     ]
     «@(γ ⊢ let_ x d t <@ tty)») »,
  «@(rule «Constr» [
      «@(γ + (concl x \== c) ⊢ t <@ tty)»
     ]
     «@(γ ⊢ let_ (concl x) c t <@ tty)») »,
  «@(rule «Concl» [
      «@γc (@concl(x)) = @c»,
      «@(γ ⊢ c <@ tty)»
     ]
     «@(γ ⊢ concl x <@ tty)») »
]]»

The inference relation for destructions, presented @tr_destr, is noted @(γ ⊢ d @> tty). Most rules rely on the fact that every hypothesis has its type in the context. Once we know the type of the hypothesis part of the destruction, we check that the destruction is consistent and reconstruct the complete type. The @ruleref«Cut» destructions, on the other hand, is verified by typechecking a trivial term composed only of a conclusion.

@tr_destr<-figure«Typechecking a destruction: @(γ ⊢ d @> tty).»«
@mathpar[[
  «@(rule «App» [
      «@(app γty y \= pi_ z (concl xty) tty)»,
      «@(γ ⊢ concl z <@ concl xty)»
     ]
     «@(γ ⊢ y </> concl z @> tty)») »,
  «@(rule «Proj@(indice 1)» [
      «@(app γty y \= sigma_ z (concl xty) tty)»
     ]
    «@(γ ⊢ proj1 y @> concl xty)») »,
  «@(rule «Proj@(indice 2)» [
      «@(app γty y \= sigma_ z (concl xty) tty)»
     ]
    «@(γ ⊢ proj2 y @> tty)») »,
  «@(rule «Cut» [
      «@(γ ⊢ concl x <@ concl xty)»
     ]
     «@(γ ⊢ cut_ (concl x) (concl xty) @> concl xty)») »
]]»

A construction is checked against a term or a construction, it is noted respectively @(γ ⊢ c <@ tty) and @(γ ⊢ c <@ cty). Typechecking a construction against a term is merly a matter of traversing the type to access the final conclusion, as shown by rules @tr_constr_term. When we reach the conclusion of the term, we can look up the definition of this conclusion, which is a construction, and continue typechecking. The @ruleref«Infer» rule is a bit different in that it uses the context for hypotheses and typecheck by unifying the two types.

@tr_constr_term<-figure«Typechecking a construction against a term: @(γ ⊢ c <@ tty).»«
@mathpar[[
  «@(rule «TyDestr» [
      «@(γ + (x \== d) ⊢ c <@ tty )»
     ]
     «@(γ ⊢ c <@ (let_ x d tty) )») »,
  «@(rule «TyConstr» [
      «@(γ + (concl x \== c) ⊢ c <@ tty )»
     ]
     «@(γ ⊢ c <@ (let_ (concl x) c tty) )») »,
  «@(rule «TyCase» [
      «@(fa </> i) @quad @(γ + ((l @- i) \== x) ⊢ c <@ (tty @- i))»,
      «@(γ ⊢ x @> fin_ (l @- i))»
     ]
     «@(γ ⊢ c <@ case_ x [«@((l @- i) |-> (tty @- i))»] )») »,
  «@(rule «TyConcl» [
      «@γc (@(concl x)) = @cty»,
      «@(γ ⊢ c <@ cty)»
     ]
     «@(γ ⊢ c <@ concl x)») »,
  «@(rule «Infer» [
      «@(app γty x \= concl xty)»,
      «@(γ ⊢ concl xty \= tty)»
     ]
     «@(γ ⊢ x <@ tty)») »
]]»

The typechecking rules for constructions is very similar to the typechecking for a language in natural deduction style, except that instead of subterms, we have conclusions. The definition of those conclusions play the role of subterms. @ruleref«Lazy»s rules can only happen if the language is lazily evaluated. If the evaluation need to be strict, the redex would already have been reduced. @eval give more details about the evaluation strategy.

@tr_constr_concl<-figure«Typechecking a construction against a construction: @(γ ⊢ c <@ cty).»«
@mathpar[[
  «@(rule «Pair» [
      «@(γ ⊢ concl y <@ concl xty)»,
      «@(γ +  x \== cut_ (concl y) (concl xty) ⊢ concl z <@ tty)»
     ]
     «@(γ ⊢ pair_ (concl y) (concl z) <@ sigma_ x (concl xty) tty)») »,
  «@(rule «Lambda» [
      «@(γ + cut_ y (concl xty) + (x \== y) ⊢ t <@ tty)»
     ]
     «@(γ ⊢ (lambda_ y t) <@ pi_ x (concl xty) tty)») »,
  «@(rule «Label» [
      «@l ∈ @(fin_ (l @- i))»
     ]
     «@(γ ⊢ l <@ fin_ (l @- i))») »,
  «@(rule «Sigma» [
      «@(γ ⊢ (concl y) <@ kind i)»,
      «@(γ + cut_ x (concl y) ⊢ t <@ kind i)»
     ]
     «@(γ ⊢ (sigma_ x (concl y) t) <@ kind i)») »,
  «@(rule «Pi» [
      «@(γ ⊢ (concl y) <@ kind i)»,
      «@(γ + cut_ x (concl y) ⊢ t <@ kind i)»
     ]
     «@(γ ⊢ (pi_ x (concl y) t) <@ kind i)») »,
  «@(rule «Fin» [
      « »
     ]
     «@(γ ⊢ (fin_ (l @- i)) <@ kind i)») »,
  «@(rule «Universe» [
      «@(binop 1 «<» i j)»
     ]
     «@(γ ⊢ kind i <@ kind j)») »
],[
  «@(rule «LazyEvalApp» [
      «@γd (@x) = @(y </> concl z)»,
      «@γd (@y) = @(lambda_ w t)»,
      «@(γ ⊢ c <@ t <-> mbrac ( concl z // w ))»
     ]
     «@(γ ⊢ c <@ x)») »,
  «@(rule «LazyEvalProj@(indice 1)» [
      «@γd (@x) = @(proj1 y)»,
      «@γd (@y) = @(pair_ (concl z) (concl w))»,
      «@(γ ⊢ c <@ concl z)»
     ]
     «@(γ ⊢ c <@ x)») »,
  «@(rule «LazyEvalProj@(indice 2)» [
      «@γd (@x) = @(proj2 y)»,
      «@γd (@y) = @(pair_ (concl z) (concl w))»,
      «@(γ ⊢ c <@ concl w)»
     ]
     «@(γ ⊢ c <@ x)») »
]]»

@sec_typecheck<-section«Typechecking and evaluation strategy»

@subsection«A generic approach»

@todo«Talk about the continuation passing style thingy. Actually, should I ? On second though, it looks like implementation details...»

@subsection«Reduction rules»

@eval<-subsection«Evaluation: lazy or strict ?»

@todo«talk a bit about the two approaches»

@subsection«Subject reduction and strong normalization»

@todo«Express the theorems»

@section«Results and Examples»

In @envext, we explaine that sharing can be recovered by checking if a variable is already present in a destruction and recording the alias in this case. Here we show an example where this feature is useful. The function in this example takes as argument a pair @agdai«p» and a binary predicate @agdai«P». We then force the typechecker to unify two versions of the same destructions, once at the term level and the other at the type level. In Agda, this is done by unfolding both term completely in order to compare them. This is quite costly in term of efficiency. In @na, we rediscover the sharing between the two versions of @agdai«u1» and @agdai«u2», hence the structure to compare is smaller.

@figure«Recovering sharing in Agda and @na.»«
@minipage"c"«0.5»«
@agdacode«
sharing : (A : Set) -> (B : Set) -> (P : A -> B -> Set) -> (p : A * B) ->
  let (u1 , u2) = p
      v = P u1 u2
  in v -> v
sharing A B P (u1' , u2') =
  let v' = P u1' u2' in \(x : v') -> x
»»
@minipage"c"«0.45»«@nacode"../examples/032-Nisse.ma"»
@centering
»

@figure«Triple boolean functions»«
  @nacode"../examples/031-TripleF.ma"
@todo«Show the agda version (which will not typecheck) and explain it a bit. Is there a ref ?»»

For the next example, we need to define a notion of equality that we can use in type signature. @agdai«Eq» and @agdai«refl» are defined @example_eq in Agda and @na. The idea is to make the unification engine compute the equality. For example, if @nai«Bool» and @nai«not» are defined, @nai«refl Bool 'true : Eq Bool 'true (not 'false)» will make the unification engine compute the fact that @nai«'true» = @nai«not 'false».
@example_eq<-figure«Encoding equality at the type level»«
@minipage"c"«0.5»«
@agdacode«
data _==_ {A : Set} (x : A) : A -> Set where
  refl : x == x
»»
@minipage"c"«0.45»«@listing["language=nanoAgda"]«
Eq = (\A -> \x -> \y -> (P : A -> *0) -> P x -> P y)
   : (A : *0) -> A -> A -> *1;
refl = (\A -> \x -> \P -> \p -> p)
     : (A : *0) -> (x:A) -> Eq A x x;
»»
@centering
»

One of the long standing issue in Agda is that the typechecker has no knowledge of which branch was taken while it typechecks the body of a branch. In the example @example_ulf, we try to make the typechecker verify that @nai«h (f x0)  x0» = @nai«f x» in the branch were @nai«f x0 = 'true» (the equality is true only in this branch). In @na, @nai«f x0» is bound to the intermediate variable @nai«y» and the typechecker can express constraint on it (the fact that @nai«'true = y»).
On the contrary, the Agda typechecker unfold each term completly but do not reconstruct the constraint on @agdai«f x». Hence the Agda piece of code do not typecheck. The fact that this example typecheck in @na and not in Agda is a direct consequence of the sequent calculus presentation. The fact that each subterm is bound to a variable allows to express constraints on a much more precise level.

@example_ulf<-figure«Smart case»«
@minipage"c"«0.5»«
@agdacode«
SmartCase :
  (A : Set) -> (A -> Bool) -> (A -> Bool) -> A -> Bool
SmartCase A f g x = h' y
  where h : Bool -> A -> Bool
        h true = f
        h false = g

        x0 = x
        y = f x0

        h' : Bool -> Bool
        h' true = let z : (h y x0) == y
                      z = refl
                  in true
        h' false = false
»»@minipage"c"«0.5»«@listing["language=nanoAgda"]«
Bool = { 'true, 'false } : *0;
A  = *0 : *1;
SmartCase =
  (\f -> \g -> \x ->
    (h = \b -> case b of {
                'true  -> f.
                'false -> g. }
       : (b : Bool) -> A -> Bool;
    x0 := x;
    y = f x0;
    case y of {
      'true  ->
        z = (refl Bool y)
          : Eq Bool (h y x0) y;
        'true.
      'false -> 'false.}
  ))
  : (f : A -> Bool) -> (g : A -> Bool) -> A -> Bool
»»
@centering
»


@section«Conclusion»

@todo«Conclude.»

@bibliographyAll

»
