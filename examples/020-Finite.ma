TERM
  Three = {'t0, 't1, 't2} : *0;
  inc = (\x -> case x of {
                 't0 -> 't1.
                 't1 -> 't2.
                 't2 -> 't0.
                 })
      : (u_ : Three) -> Three;
  Three
TYPE
  *0