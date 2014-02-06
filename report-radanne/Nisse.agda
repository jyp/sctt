module Nisse where

open import Data.Product

nisse : (A : Set) -> (B : Set) -> (P : A → B → Set) -> (p : A × B) ->
  let (u1 , u2) = p
      v = P u1 u2
  in v -> v
nisse A B P (u1' , u2') =
  let v' = P u1' u2' in \(x : v') -> x
