TERM
  Three = {'t0, 't1, 't2} : *0;
  Three_elim = (\P -> \a -> \b -> \c -> \x -> case x of {
                 't0 -> a.
                 't1 -> b.
                 't2 -> c.
                 })
             : (P : ((Three) -> *0)) -> (a : P 't0) -> (b : P 't1) -> (c : P 't2) -> (x : Three) -> P (x);
  inc0 = \x -> x : (Three) -> Three;
  inc1 = (Three_elim (\x -> Three) 't1 't2 't0) : (Three) -> Three;
  inc2 = (Three_elim (\x -> Three) 't2 't0 't1) : (Three) -> Three;
  plus = (Three_elim (\y -> (Three) -> Three) (inc0) (inc1) (inc2))
       : (Three) -> (Three) -> Three;
  Three
TYPE
  *0