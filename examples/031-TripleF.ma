TERM
  Eq = (\A -> \x -> \y -> (P : A -> *0) -> P x -> P y)
     : (A : *0) -> A -> A -> *1;
  refl = (\A -> \x -> \P -> \p -> p)
       : (A : *0) -> (x:A) -> Eq A x x;
  Bool = { 'true, 'false } : *0;
  tripleF = (\f -> \x -> 
                case x of {
                   'true  -> case f x of {
                        'true  -> refl Bool 'true.
                        'false -> refl Bool 'false.
                   }.
                   'false -> case f x of {
                        'true  -> refl Bool 'true.
                        'false -> refl Bool 'false.
                   }.
                })
          : (f: Bool -> Bool) -> (x : Bool) ->
                Eq Bool (f x) (f (f (f x)));
  *0
TYPE
  *1
