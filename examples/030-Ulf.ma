TERM
  Eq = (\A -> \x -> \y -> (P : A -> *0) -> P x -> P y)
     : (A : *0) -> A -> A -> *1;
  refl = (\A -> \x -> \P -> \p -> p)
       : (A : *0) -> (x:A) -> Eq A x x;
  Bool = { 'true, 'false } : *0;
  Bla  = *0 : *1;
  BlaFun = (Bla -> Bool) : *1;
  Ulf = (\ f -> \ g -> \ x ->
           ( h = (\ b -> case b of {
                'true  -> f.
                'false -> g.})
               : (b : Bool) -> BlaFun;
             x0 := x;
             y = f x0;
             case y of {
               'true  -> z = (refl Bool y) : Eq Bool (h y x0) y;
                         'true.
               'false -> 'false.}
           ))
      : (f : BlaFun) -> (g : BlaFun) -> BlaFun;
  *0
TYPE
  *1
