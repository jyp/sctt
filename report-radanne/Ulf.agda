module Ulf where

open import Data.Bool

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

Ulf : (A : Set) -> (A -> Bool) -> (A -> Bool) -> A -> Bool
Ulf A f g x = h' y
  where h : Bool -> A -> Bool
        h true = f
        h false = g

        x0 = x
        y = f x0

        h' : Bool -> Bool
        h' true = let z : (h y x0) ≡ y
                      z = refl
                  in true
        h' false = false
