TERM
  Three = {'t0, 't1, 't2} : *0;
  inc = (\x -> case x of {
                 't0 -> 't1.
                 't1 -> 't2.
                 't2 -> 't0.
                 })
      : (u_ : Three) -> Three;
  Three_elim = (\P -> \a -> \b -> \c -> \x -> case x of {
                 't0 -> a.
                 't1 -> b.
                 't2 -> c.
                 })
             : (P : ((y : Three) -> *0)) -> (a : P 't0) -> (b : P 't1) -> (c : P 't2) -> (x : Three) -> P (x);
  Three
TYPE
  *0