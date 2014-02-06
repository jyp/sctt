TERM
  A = *0 : *1; B = *0 : *1;
  Sharing =
    (\P -> \p -> (u1,u2) = split p;
               v = P u1 u2;
               \x -> (y = x : v ; y) )
    : (P : A -> B -> *0) -> (p : (a : A) * B) ->
               (u1,u2) = split p;
               v = P u1 u2 ;
               v -> v ;
  *0
TYPE
  *1
