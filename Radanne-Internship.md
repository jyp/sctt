An ongoing quest in the mathematical logic community is to find
suitable logic foundation for mathematics. One of the strong
candidates is the intuitionistic type-theory of Per Martin-Löf (MLTT).
A natural question then is: on what foundations does MLTT rest?  On of
the answers is that it corresponds to an intuitive notion of
computation. A related, but different type of answer is to produce a
system which checks proofs written in MLTT. (By the Curry-Howard
isomorphism, MLTT corresponds to a programming language with dependent
types, and the proof checker corresponds to a type-checker). It is
then important that the type checker is as simple as possible, in
order to be sure of its correctness.

This works falls into a line of research which attempts to design the
smallest type-theory equivalent to MLTT, together with type-checkers
for them. Achievements include Agda Light (Norell), Mini TT (Coquand
et al.), or PiSigma (Altenkirch et al.) In our view, PiSigma is
especially attractive because it rests upon only three simple
primitive constructions: finite types (Fin), dependent products (Pi)
and dependent sums (Sigma). Another interesting aspect of PiSigma is
that the eliminators for Sigma and Fin are to be written in sequent
calculus style. However, because Pi is treated differently, the
languages suffers serious problems (lack of subject reduction).

Traditionally, implementations of minimalistic type-theories are based
on natural deduction.  Using a sequent-calculus style is interesting,
because it corresponds to naming every intermediate result (as it is
usual in intermediate representations of traditional programming
languages). Naming intermediate results means that they can be shared
in subsequent parts of the term, which potentially solves two
problems:

1. The size of certain terms becomes so large that type-checking them
becomes prohibitively expensive.  
    
2. Even for moderately-sized programs, the normalized output given by
the type-checker is to big to be verified by users.

The goal of this project is to solve the above issues by developing a
minimalistic type-theory in sequent calculus style, and implement a
type-checker for it.

With this goal in mind, we will:

- Develop a number of examples to test our theory.
- Design and document fragments of a type-theory in sequent calculus style.
- Implement a type-checker in the Haskell programming language.
- Verify that the examples we have designed work with our implementation.
- If time allows, assess if the theory is suitable as a core, by
  extending it with experimental features.
  
  
