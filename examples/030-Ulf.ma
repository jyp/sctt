TERM
  Eq = (\A -> \x -> \y -> (P : A -> *0) -> P x -> P y)
     : (A : *0) -> A -> A -> *1;
  refl = (\A -> \x -> \P -> \p -> p)
       : (A : *0) -> (x:A) -> Eq A x x;
  Bool = { 'true, 'false } : *0;
  A  = *0 : *1;
  Ulf = (\f -> \g -> \x ->
           ( h = \b -> case b of {
                        'true  -> f.
                        'false -> g. }
               : (b : Bool) -> A -> Bool;
             y = f x;
             case y of {
               'true  -> z = (refl Bool y) : Eq Bool (h y x) y;
                         'true.
               'false -> 'false.}
           ))
      : (f : A -> Bool) -> (g : A -> Bool) -> A -> Bool;
  *0
TYPE
  *1
