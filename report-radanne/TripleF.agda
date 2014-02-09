module TripleF where

open import Data.Bool

data _==_ {A : Set} (x : A) : A -> Set where
  refl : x == x

tripleF : (f : Bool -> Bool) -> (x : Bool) ->
                (f x) == (f (f (f x)))
tripleF f x with x | f x
... | true  | true  = refl
... | true  | false = refl
... | false | true  = refl
... | false | false = refl
