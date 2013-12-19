% LLTT: A Sequent-Calculus Presentation of Type-Theory.

A. The problem:

- Type-Theory is Great!
- Two problems:

 1. It’s a bit slow. Type inference generates big terms (recall the
 canonical ML program).  The intermediate representation does not
 support sharing. Side note: it’s not good for humans to read normal
 forms like this either!

 2. It’s a bit annoying to use. The “case” function does not quite
 work. McBride invented “the view from the left”, but this departs
 significantly from the tradition of “terms” as text. In practice,
 it makes the system awkward to use, as “with” is translated to an
 extra abstraction. (This means that normal forms using with become
 big!) The types of functions using with can’t even be expressed by
 the user. More quirks of “with”: needs for extra constructs on top
 of it (inspect idiom); and some programs still do not typecheck.
 Here, we instead propose to properly implement the “case” construction.

THE ROOT OF THE PROBLEM: naming intermediate results is essential both
for humans and computers to manipulate typed terms.

Our solution: Make a implementation of a core type-theory based on
sequent-calulus rather than natural deduction.

Technical contributions. (List)

B. The case of Case.

- desired rule for case

   Γ[tt/x] ⊢ e1 : C[tt/x]
   Γ[ff/x] ⊢ e2 : C[ff/x]
 -----------------------------------------
  Γ |- case x of {tt -> e1; ff -> e2} : C

- remarks that it works only if the scrutinee is a variable
- solution: name every intermediate result
- hence technically: we want a sequent calculus.

C. Interlude: sequent calculi vs. natural deduction.
- what is s.c.? what is n.d.?
- It is conjectured that every natural deduction system can be
  presented in s.c. form. (paper)
- corresponds to CPS (see eg. stg machine; Appel’s book: compiling
  with continuations) or even SSA
- Most existing functional compilers either use a s.c.-based
  intermediate language, or the equivalent CPS presentation. In sum,
  we apply “old” functional language compiler technology to dependent
  types.

D. Our calculus
- normal forms (Case done. discuss now Sigma and Pi; show full set of rules)
- example programs and their normal forms

E. Implementation

F. Analysis
- Model back to natural deduction? 

  Sound: Γ;h ⊢ t:A  ⇒  ⟦Γ⟧h ⊢ ⟦t⟧h : ⟦A⟧h
  
  (the heap h gives rise to a substitution which is applied everywhere)
  Maybe it is enough to show that the model preserves substitution (in
  normal forms.)
 
  Complete:  Γ ⊢ t:A  ⇒  Γ;empty ⊢ t:A
  
  (using a trivial embedding which names the intermediate results.)
   
  ⟦t[s/x]⟧ = ⟦t⟧[⟦s⟧/x]
- Alt:
   - subject reduction (adding a binding to an env. does not destroy its
     structure)
   - normalisation (substitution takes a finite amount of time)

G. Related work

F. Related work


http://syntaxexclamation.wordpress.com/2013/06/17/new-draft-proofs-upside-down/

Une autre reference reliee a Hugo Herbelin

https://www.google.se/url?sa=t&rct=j&q=&esrc=s&source=web&cd=1&ved=0CC0QFjAA&url=http%3A%2F%2Fw3.math.uminho.pt%2F~jes%2FHerbelinProgramme(camera-ready).pdf&ei=xO06Uum5OKmg4gT2o4GgBg&usg=AFQjCNGbouAhWtjVNzmJ5I9F96bama8B8Q&sig2=q23cVW14I14t5En5ZdlVdA&bvm=bv.52288139,d.bGE

H. Discussion and Conclusion


