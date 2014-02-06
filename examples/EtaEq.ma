TERM
  Eq = (\A -> \x -> \y -> (P : A -> *0) -> P x -> P y)
     : (A : *0) -> A -> A -> *1;
  refl = (\A -> \x -> \P -> \p -> p)
       : (A : *0) -> (x:A) -> Eq A x x;

  EtaEq = (\A -> \B -> \f -> (refl (A -> B) f))
  	: (A : *0) -> (B : *0) -> (f : A -> B) -> (Eq (A -> B) f (\x -> f x))
  ;
*0
TYPE
*1