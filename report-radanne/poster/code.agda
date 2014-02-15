data Nat : Set where
  Zero : Nat
  Succ : Nat -> Nat

_+_ : Nat -> Nat -> Nat
Zero + n = n
(Succ n) + m = Succ (n + m)

data Vec (A : Set) : Nat -> Set where
  Nil : Vec A Zero
  Cons : {n : Nat} -> A -> Vec A n -> Vec A (Succ n)

append : forall { n m A } -> Vec A n -> Vec A m -> Vec A (n + m)
append Nil ys = ys
append (Cons x xs) ys = Cons x (append xs ys)
