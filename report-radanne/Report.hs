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

todo s = emph $ color "red" $ "TODO : " <> s

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

quad = cmd0 "quad"

app f x = f <-> mparen x
(\=) = binop 1 "="
(≡) = binop 1 (cmd0 "equiv")
(≅) = binop 1 (cmd0 "cong")
(</>) = binop 1 space
(<->) = binop 1 nil
(<.>) = binop 1 "."
(<:>) = binop 1 ":"
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

c = text "c"
d = text "d"

xty = text "X"
yty = text "Y"
zty = text "Z"

i = text "i"
j = text "j"

l = text "`l"
l2 = text "`m"
t = text "t"
t' = text "t'"
tty = text "T"

lra = cmd0 "longrightarrow"
star = Con $ cmd0 "star"

pair_ x y = mparen $ binop 1 "," x y
lambda_ x t = λ <-> x <.> t
let_ x a t = texttt«let» </> x \= a </> texttt«in» </> t
case_ x l =
    let l' = text $ mconcat $ intersperse ", " l in
    texttt«case» </> x </> texttt«of» </> mbracket l'
pi_ x y t = mparen ( x <:> y ) → t
sigma_ x y t = mparen ( x <:> y ) × t
fin_ l = mbracket l

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

agda = texttt
agdacode :: Listing () -> TeX
agdacode (Listing s _) =
    env' "lstlisting" ["language=Agda"] (tex s)

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

@deptype<-subsection«Dependent types»

In a regular programming language, terms and types live in two different worlds : you can't talk about terms in types and you can't manipulate types as you can manipulate terms. In a dependently typed programming language, types can depends on terms. This addition sounds quite small at first, but it makes the language significantly more powerful ... and significantly harder to typecheck.



@subsection«An example in Agda»

Numerous examples have been presented to motivate the use of dependent types in mainstream programming @citet"oury_power_2008" @todo«add more». We will try here to give a short and simple example to outline the specificity of dependent type languages from the user point of view but also from the typechecking point of view.

For this example, we will use Agda. The syntax should be familiar enough if you know any statically-typed functional language (like OCaml or Haskell).

Let's first define the @agda«Nat» datatype.
@agdacode«
data Nat : Set where
  Zero : Nat
  Succ : Nat -> Nat
»
This definition is very similar to a GADT one for OCaml or Haskell. @agda«Set» show that @agda«Nat» is a base type, as @agda«Int» or @agda«Char» would be in OCaml or Haskell.

Let's now move on to a more interesting datatype : vectors with fixed length.
@agdacode«
data Vec (A : Set) : Nat -> Set where
  Nil : Vec A 0
  Cons : {n : Nat} -> A -> Vec A n -> Vec A (Succ n)
»
You can see in the signature of the type that @agda«Vec» take a type @agda«A», the type of the elements, and a natural number. Dependent types allow us to encode the length of the vector in the type. The declaration of @agda«Cons» exhibit a very useful feature of Agda : the argument @agda«{n : Nat}» is implicit : the compiler will try to infer this argument whenever possible. In this case, we will not have to provide the length of the vector we are consing to, which would have been quite cumbersome.

We can use those type information to implement a type-safe @agda«head» function:
@agdacode«
head : {A : Set} { n : Nat } -> Vec A (Succ n) -> A
head (Cons x xs) = x
»
The compiler knows that the @agda«Nil» case can't happen since the length of the provided vector is at least one. Any call of head to a empty vector will not typecheck.

We can also implement the append function, which requires us to manipulate the natural number embedded in the type:
@agdacode«
append : forall { n m A } -> Vec A n -> Vec A m -> Vec A (n + m)
append Nil ys = ys
append (Cons x xs) ys = Cons x (append xs ys)
»
In the type, we assert that the length of the results is the sum of the lengths of the operands. We use the @agda«forall» quantifier to declare the implicit arguments without specifying their types.

For now, we have seen that dependent types can be useful to assert properties on some datatype. Those simple examples could be encoded with GADTs even if it would need additional burden and be far less easy to manipulate. We could go on and declare some other functions on vectors, however, we will rather look at something difficult or impossible to do using GADTs.

We will present an embedding of relational algebra that was first discussed by @citep"oury_power_2008". A typed embedded DSL for relational databases present interesting difficulties: relation algebra operators are hard to type, especially join and cartesian product, and type safety usually rely on the static declaration of a schema. We will use dependent types to overcome those two issues.

Let's first considerate the definition of a table schema:
@agdacode«
data U : Set where
  BOOL : U
  CHAR : U
  NAT : U
  VEC : U -> Nat -> U

Schema : Set
Schema = List (String xx U)
»
Here, @agda«×» is simply the type of pairs. The @agda«U» type is the universe type for the value inside our database. Databases are restricted in what type of value they can handle, so this is a perfectly valid restriction. A Schema here is simply a list of columns with a name and a type.

We need to link the constructors of @agda«U» to the representation of each types in Agda:
@agdacode«
el : U -> Set
el BOOL = Bool
el CHAR = Char
el NAT = Nat
el (VEC x n) = Vec (el x) n
»

A table is composed of rows which follows a schema.
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
The first two constructors are quite straightforward, @agda«Read» will read a given table and @agda«Union» will merge two tables following the same schema. The @agda«Product» constructor, however, is much more interesting. To be able to compute the cartesian product of two table, they must have disjoint columns. We can quite easily provide a function checking that two schema are disjoint, of the type:
@agdacode«
disjoint : Schema -> Schema -> Bool
»
We now want to ensure that this property is checked at the type level. In order to do so, we define a bridge from bool to types :
@agdacode«
So : Bool -> Set
So false = Empty
So true = Unit
»
@agda«So» takes a @agda«Bool» and returns a type. The @agda«Empty» types is, as his names indicate, a type with no elements. @agda«Unit» being the type with only one element. Hence, in order to typecheck, @agda«So x» must be @agda«Unit» and @agda«x» must be @agda«true».

The @agda«Product» constructor takes @agda«So (disjoint s s')» as argument: this is a proof that @agda«s» and @agda«s'»  are indeed disjoint.

Finally we define expressions used by selects:
@agdacode«
data Expr : Schema -> U -> Set where
  _!_ : (s : Schema) -> (column : String) -> {p : So (occurs column s)} -> Expr s (lookup column s p)
  equal : forall { u s } -> Expr s u -> Expr s u -> Expr s BOOL
  literal : forall { u s } -> el u -> Expr s u
  ...
»
Constructors @agda«equal» and @agda«literal» are quite simple and could be encoded easily with GADTs. However, the @agda«_!_» constructor, which allows to get the value of a column, take as argument @agda«So (occurs column s)». This is a proof that the column appears in the schema. The @agda«occurs» function would have the type:
@agdacode«
occurs : String -> Schema -> Bool
»
We want the @agda«_!_» constructor to return an expression of the type of the return column, hence we could be tempted to simply use a lookup operator:
@agdacode«
lookup : (col : String) -> (s : Schema) -> U
»
However, Agda only accept terminating function to be executed at the type level. The @agda«lookup» function, as defined here, is not garantee to terminate. Hopefully, we know that, in the context of selects, this lookup will always terminate thanks to the proof object @agda«{p :So (occurs column s)}». We can defined the lookup function with this type instead:
@agdacode«
lookup : (col : String) -> (s : Schema) -> So (occurs col s) -> U
»

We can see in this example multiple caracteristics of dependently typed programming languages.
First, types and terms evolve in the same word and there is little to no distinction between them.
Secondly, terms inhabiting a type are proofs of the proposition expressed by this type. It is a very literal translation of the curry-howard isomorphism. This is quite different than in a theorem proover, like Coq, where the proof part and the programming part are usually separated.

Finally, the typechecker must evaluate terms in order to typecheck.
This make the typechecking more complicated and is the source of some limitation in curent typecheckers.

@subsection«Limitations of current implementations»

The Agda typechecker contains some well known issues that the dependent type theory community has been trying to solve :
@itemize«
  @item The ``case decomposition'' issue @todo«Show the incriminated piece of code».
  @item Since the Agda type checker is using a natural deduction style, the evaluation make terms grow in size very fast which implies important efficiency issues.
»

@todo«Some various attempts.»

A particular language, PiSigma @citep"AltenkirchDLO10" is especially interesting since it tackle those problems by putting some constructions of the language in sequent calculus style, as explained in the next section. Unfortunately, even if this solve some issues, it creates some new ones, in particular the lack of subject reduction. We believe that those issues are present because part of the language is still in natural deduction style.


@subsection«Sequent calculus presentation»

There is various presentation of what is Sequent calculus. In this article, we mean that every intermediate results or sub-terms is bind to a variable.
Sequent calculus is a well known presentation for classical logic but as not been evaluated as a presentation of a type theory.
According to @todo«REF», the translation from natural deduction to sequent calculus is mechanical, but it does seems interesting to actually look at the result, since it present interesting properties:
@itemize«
  @item It's low-level, which makes it suitable as back-end for dependently-typed languages.
  @item Sharing is expressible (J. Launchbury - A Natural Semantics for Lazy Evaluation) @todo«REF». This would help solve some efficiency issues encountered in Agda, for example.
»

@todo«More details ?»

@subsection«Goals»

We aim to construct a type-theory which can be used as a back-end for dependently-typed languages such as Agda or Coq. Such a language should be:
@itemize«
  @item A type-theory: correctness should be expressible via types.
  @item Low-level: one should be able to translate various high-level languages into this language while retaining properties such as run-time behaviour, etc.
  @item Minimal: the type-checking program should be amenable to verification.
»

@sec_lang<-section«Description of the language»

Before describing the language itself, we will define some common notion in type theory that we will manipulate in the rest of this article.

@subsection«Preliminary vocabulary»

@paragraph«Constructor and destructors@newline»
A language is often separated into destructor and constructors. For example in the lambda calculus, lambda expressions are constructors and applications are destructors. A destruction of construction can be reduced through β-reduction. In a more complicated language, like @na, we will have pairs and projections. The projection of a pair can be similarly β-reduced.

@paragraph«Universes@newline»
In regular programming languages, you have types and the set of types. You can't manipulate this set itself but since you can't merge terms and types, this is not an issue. However, in a dependently typed programming language, terms and types live together, and you can theoretically manipulate the set of types. Is this set of types a type itself ? For technical reasons @todo«REF» and in order to preserve the consistency of the type system, the answer must be no.

We classify types in universes (also called ``sorts'' or ``kinds'') indexed by natural numbers.
We note those univers @(star @- i) with @i ∈ @nat.
Base types, like @agda«Int», are in @(star @- 0). @(star @- i) is in @(star @- (i + 1)).
Types composed of other types live in the highest univers of their components. For example @agda«(Char, Int)» live in @(star @- 0) but @agda«(Int, @(star @- 0))» is in @(star @- 1).  Finally, for ease of manipulation, any element in @(star @- i) is in @(star @- j) when @i ≤ @j.

@subsection«@na»

As explained @intro, every variable is binded. We can separate element of the langages, presented figure @grammar_na, into various categories :
@todo«Say something about polarisation ? not sure if it's necessary.»

@description«

@item'«Variables» are separated in two categories : conclusions and hypotheses.

@item'«Hypotheses» are available in the beginning of the program or are the result of an abstraction. It is not possible to construct an hypothesis.

@item'«Conclusions» are either an hypothesis or the result of a construction of conclusions. We mark conclusions by a bar on the top: @(concl x) .

@item'«Destructions», marked by the letter @d in @grammar_na, can be either a @texttt«case» (a pattern match) or of the form @d as shown in @grammar_na (@todo«Can't do ref to internal labels»): an application, a projection or a cut. We don't need to bind the result of a @texttt«case», as opposed to other destructions.

@item'«Dependant functions and products» are both of the same form : @(pi_ x (concl y) t) and @(sigma_ x (concl y) t) . The type on the left hand side can be a conclusion, since it doesn't depend on the type witness @x (@todo«right term ?»), hence it's possible to bind it before. However, the right hand side must be a term, since it will depend on @x. @x is an hypothesis since it is abstract here.

@item'«Enumerations» are a set of scopeless and non-unique labels. Labels are plain strings starting with an apostrophe. We will note them @l, @l2.

@item'«Universes» are arangered in a tower of universes, starting at 0. We will use the usual notation @star = @star @indice(0).

@item'«Constructions», marked by the letter @c and detailed @grammar_na (@todo«Can't do ref to internal labels»), are either a conclusion, a universe, a type or a construction of pair, enum or function. The result must be bound to a conclusion.
»
@grammar_na<-figure«Grammar for @na»«
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

Conclusions are the result of constructions of conclusion or hypotheses. An hypothesis is the result of destructions of hypotheses. This means that we can only produce constructions of destructions, hence there is no reduction possible and the program is in normal form.

 Obviously we don't want to write programs already in normal form, so we need a way to construct hypotheses from conclusions. That is what the cut construction, in red in @grammar_na, is for. It allows to declare a new hypothesis, given a conclusion and its type. The type is needed for type checking purposes.

@subsection«A bit of sugar»

Of course, it's impossible to write reasonable programs with this syntax, it's far too verbose and tedious for humans. We introduced another simpler syntax that you can see below. It's possible to translate this new syntax to the low-level one. The translation is purely syntactic.

@fig_syntaxes<-figure«Regular and low-level syntax.»«
  @todo«Two columns comparison of the two syntax.»
»

@fig_syntaxes is an example of a program in regular syntax and the translation to the low-level syntax. As you can see, the low-level version is very verbose, which shows the need for the regular one.

@sec_type<-section«Type system»

The type rules for @na are quite usual, most of the cleverness is contained in the way the heap is updated. Hence we will start by presenting environment and environment extensions.

We will use the same notation as in @sec_heap : @x for hypotheses, @(concl x) for conclusions, @c for constructions and @d for destructions. For clarity, elements used as types will be capitalized.

@sec_heap<-subsection«The Heap»

Since the language is based on variables and bindings, we need a notion of environment. This notion is captured in a heap composed of several mapping :

@itemize«
  @item @γty   @(x |-> concl y ) : The context heap, containing the type of hypotheses.
  @item @γc  @(concl x |-> c)  : The heap for constructions.
  @item @γa  @(x |-> y) : The heap for aliases.
  @item @γd  @(x |-> d) : The heap for cuts and destructions.
  @item @γd' @(d |-> x) : The reverse map from destruction to hypotheses. @todo«do we really talk about this one ?»
»

We have @γ = (@γty, @γc, @γa, @γd, @γd').

@subsection«Environment extensions»

Here are details of how to update the heap when registering new information. We will use the @(math $ cmd0 "gets")operator to symbolize an update.

When typechecking abstractions, like lambda or dependent functions and products, we need to introduce new hypotheses in the context without any value.
@align[
  [ «@(γ + mparen (x <:> concl yty))», «= @γ @text« with » @(γty ← mparen (x <:> concl yty))» ]
]

When adding a destruction definition, we check if a similar destruction definition exist using @γd. This allows sharing for multiple application of a function on the same argument.
@align[
  [ «@(γ + (x \== d))», «= @γ @text« with » @(γa ← (x \== y))», «@(iff $ (y \== d) ∈ γd)» ],
  [ «»                , «= @γ @text« with » @(γd ← (x \== d))», «@text«otherwise»»       ]
]

The rule for conclusions is straightforward, since we don't handle sharing for conclusions as we do for destructions. @todo«Explain why»
@align[
  [«@γ + @(concl x \== c)», «= @γ @text« with » @(γc ← (concl x \== c)) @todo«not sure if it's @γc, it seems so in the code.»»]
]

During a case, we keep track of constraints on the variable decomposed by the case, Allowing us to know inside the body of a case which branch we took. Of course, if two incompatible branches are taken, we stop the typechecking immediately, since the context is inconsistent.
@align[
  [ «@γ + @(l \== x)», «= @γ»            , «@(iff $ l \== x ∈ γc)»                         ],
  [ «»               , «= @bot»          , «@(iff $ l2 \== x ∈ γc) @text" for " @(l ≠ l2)» ],
  [ «»               , «= @γ, @text« with » @(γc ← (l \== x))», «@text«otherwise»»                             ]
]

@eqrules<-subsection«Equality rules»

Rules to test equality between two expressions are given @fig_eqrules.

@todo«stuff»

@fig_eqrules<-figure«Equality rules»«
@align[
  [ «@(bot ⊢ text "rhs")», «@lra true»],
  [ «@(γ ⊢ let_ x d t \= t')», «@lra @(γ + x \== d ⊢ t \= t')»],
  [ «@(γ ⊢ case_ x [«@((l @- i) |-> (t @- i))»] \= t)»,
    «@lra @fa @i @quad @(γ + x \== (l @- i) ⊢ (t @- i) \= t)»],
  [ «@(γ ⊢ concl x \= concl y)», «@lra @(x ≡ y)»],
  [ «@(γ ⊢ concl x \= c)», «@lra @(γ ⊢ app γc (concl x) \= c)»],
  [ «@(γ ⊢ x \= y)», «@lra @(x ≅ y)»],
  [ «@(γ ⊢ lambda_ x t \= lambda_ y t')», «@lra @(γ + (x \== y) ⊢ t \= t')»],
  [ «@(γ ⊢ lambda_ x t \= y)»,
    «@lra @(γ + (concl x \== x) + (z \== (y </> concl x)) ⊢ t \= z)»],
  [ «@(γ ⊢ pair_ (concl x) (concl x') \= pair_ (concl y) (concl y'))»,
    «@lra @(γ ⊢ concl x \= concl y ∧ γ ⊢ concl x' \= concl y') »],
  [ «@(γ ⊢ pair_ (concl x) (concl x') \= y)»,
    «@lra @(γ + (z \== proj1 y) ⊢ concl x \= z ∧ γ + (z \== proj2 y) ⊢ concl x' \= z) »],
  [ «@(γ ⊢ l \= l)», «@lra true»]
]»

@typerule<-subsection«Typing rules»

The typing rules can be divided in four relations. The first two relations are typechecking relations for respectively terms and constructions. The second one is just a checking relation for destruction. The last relation is the inference for hypotheses.

We will note typechecking for terms and normal forms as @(γ ⊢ t <@ tty), the rules are presentend @tr_term. The type here is always a complete term. The type must have been checked before hand.

The @ruleref«Constr» rules might seems surprising but any construction added this way will be typechecked in the end using either the @ruleref«Concl» rule or the @ruleref«Cut» rule.

@tr_term<-figure«Typechecking a term : @(γ ⊢ t <@ tty)»«
@mathpar[[
  «@(rule «Case» [
      «@(fa </> i) @quad @(γ + ((l @- i) \== x) ⊢ (t @- i) <@ tty)»,
      «@γty (x) = @(fin_ $ (l @- i))»
     ]
     «@(γ ⊢ case_ x [«@((l @- i) |-> (t @- i))»] <@ tty)») »,
  «@(rule «Destr» [
      «@(γ + (x \== d) ⊢ t <@ tty)»,
      «@(γ ⊢ d)»
     ]
     «@(γ ⊢ let_ x d t <@ tty)») »,
  «@(rule «Constr» [
      «@(γ + (x \== c) ⊢ t <@ tty)»
     ]
     «@(γ ⊢ let_ x c t <@ tty)») »,
  «@(rule «Concl» [
      «@γc (@concl(x)) = @c»,
      «@(γ ⊢ c <@ tty)»
     ]
     «@(γ ⊢ concl x <@ tty)») »
]]»

For destructions, only the fact that it is well formed need to be checked, hence we don't need a type parameter. The rules, presented @tr_destr, are quite straightforward. This typing relation is noted @(γ ⊢ d).

@tr_destr<-figure«Typechecking a destruction : @(γ ⊢ d)»«
@mathpar[[
  «@(rule «App» [
      «@(γ ⊢ y @> (pi_ z xty tty))»,
      «@(γ ⊢ concl z <@ xty)»
     ]
     «@(γ ⊢ y </> concl z)») »,
  «@(rule «Proj@(indice 1)» [
      «@(γ ⊢ y @> (sigma_ z xty tty))»
     ]
    «@(γ ⊢ proj1 y)») »,
  «@(rule «Proj@(indice 2)» [
      «@(γ ⊢ y @> (sigma_ z xty tty))»
     ]
    «@(γ ⊢ proj2 y)») »,
  «@(rule «Cut» [
      «@(γ ⊢ concl x <@ concl xty)»
     ]
     «@(γ ⊢ concl x <:> concl xty)») »
]]»

A construction is checked again a term, it's noted @(γ ⊢ c <@ tty).

@todo«stuff»

@tr_constr<-figure«Typechecking a construction : @(γ ⊢ c <@ tty)»«
@mathpar[[
  «@(rule «» [
      «@(γ + (x \== d) ⊢ c <@ tty )»
     ]
     «@(γ ⊢ c <@ (let_ x d tty) )») »,
  «@(rule «» [
      «@(fa </> i) @quad @(γ + ((l @- i) \== x) ⊢ c <@ (tty @- i))»,
      «@γty (x) = @(fin_ $ (l @- i))»
     ]
     «@(γ ⊢ c <@ case_ x [«@((l @- i) |-> (tty @- i))»] )») »,
  «@(rule «» [
      «@γc (@(concl x)) = @tty»,
      «@(γ ⊢ c <@ tty)»
     ]
     «@(γ ⊢ c <@ concl x)») »,
  «@(rule «» [
      «@(γ ⊢ concl y <@ concl xty)»,
      «@(γ +  x \== (concl y <:> concl xty) ⊢ concl z <@ tty)»
     ]
     «@(γ ⊢ pair_ (concl y) (concl z) <@ sigma_ x (concl xty) tty)») »,
  «@(rule «» [
      «@(γ + mparen (y <:> concl xty) ⊢ t <@ let_ x y tty)»
     ]
     «@(γ ⊢ (lambda_ y t) <@ pi_ x (concl xty) tty)») »,
  «@(rule «» [
      «@γa (@z) = @x»,
      «@(γ ⊢ x @> xty)»,
      «@(γ ⊢ xty \= tty)»
     ]
     «@(γ ⊢ z <@ tty)») »
]]»


@(γ ⊢ x @> xty) : infer the type of an hypothesis

@todo«stuff»

@tr_hyp<-figure«Inference for the type of an hypothesis : @(γ ⊢ x @> xty)»«
@mathpar[[
  «@(rule «» [
      «@γty (@x) = @(concl xty)»
     ]
     «@(γ ⊢ x @> concl xty)») »,
  «@(rule «» [
      «@γd (@x) = @(y </> concl z)»,
      «@(γ ⊢ y @> (pi_ z xty tty))»
     ]
     «@(γ ⊢ x @> let_ z (concl z) tty)») »,
  «@(rule «» [
      «@γd (@x) = @(proj1 y)»,
      «@(γ ⊢ y @> (sigma_ z xty tty))»
     ]
     «@(γ ⊢ x @> concl xty)») »,
  «@(rule «» [
      «@γd (@x) = @(proj2 y)»,
      «@(γ ⊢ y @> (pi_ z xty tty))»
     ]
     «@(γ ⊢ x @> let_ z (proj1 y) tty)») »,
  «@(rule «» [
      «@γd (@(x)) = @(mparen (concl y <:> concl xty))»
     ]
     «@(γ ⊢ x @> concl xty)») »
]]»

@sec_typecheck<-section«Typechecking and evaluation strategy»

@subsection«A generic approach»

@todo«Talk about the continuation passing style thingy.»


@subsection«Evaluation : lazy or strict ?»

@todo«talk a bit about the two approaches»

@section«Results»

@subsection«Examples»

@todo«show examples that works with @na.»

@subsection«Subject reduction and strong normalisation»

@todo«Express the theorems»

@section«Conclusion»

@todo«Conclude.»

@bibliographyAll

»
