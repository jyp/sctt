TERM

  Eq = (\A -> \x -> \y -> (P : A -> *0) -> P x -> P y)
     : (A : *0) -> A -> A -> *1;
  refl = (\A -> \x -> \P -> \p -> p)
       : (A : *0) -> (x:A) -> Eq A x x;

  Bool := { 'true, 'false } ;
  If = (\ x -> \ A -> \ B -> case x of
       { 'true -> A.
         'false -> B.
       })
     : (x : Bool) -> (A : *0) -> (B : *0) -> *0 ;

  PBool = ((x : Bool) -> *0)
     : *1 ;
  if = (\ P -> \ x -> \ y -> \ z -> case x of
       { 'true -> y.
         'false -> z.
       })
     : (P : PBool) -> (x : Bool) -> (y : P 'true) -> (z : P 'false) -> P x ;
  not = (\ x -> if (\ x -> Bool) x 'false 'true)
      : (x : Bool) -> Bool ;
  
  thm = (\ P -> \ x -> \ y -> \ z -> case z of
        { 'true  -> refl (P 'true)  y.
          'false -> refl (P 'false) z.
        })
      : (P : PBool) -> (x : Bool) -> (y : P 'true) -> (z : P 'false) -> 
        Eq (If x (P x) (P (not x))) (if P x y z) (if P (not x) z y) ;

  *0
TYPE
  *1
