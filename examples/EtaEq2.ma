TERM
  Eq = (\A -> \x -> \y -> (P : A -> *0) -> P x -> P y)
     : (A : *0) -> A -> A -> *1;
  refl = (\A -> \x -> \P -> \p -> p)
       : (A : *0) -> (x:A) -> Eq A x x;

  EtaEq = (\A -> \B -> \p ->
  	    (refl ((a : A) * B) p))
  	: (A : *0) -> (B : *0) -> (p : (a : A) * B) ->
	    ((x,y) = split p ;
	     Eq ((a : A) * B) p (x,y))
  ;
*0
TYPE
*1