TERM
Top := {'nil};
Tag := {'zer, 'suc};
nat = (rec n -> (t : Tag) * (case t of {'zer -> Top. 'suc -> n}))
    : *0;
zero = ('zer, 'nil) : nat;
succ = (\n -> ('suc, n)) : nat -> nat;
natElim = (rec el -> \P -> \z -> \s -> \m ->
                     (m1,m2) = split m;
            case m1 of
             {'zer -> case m2 of {'nil -> z.}.
              'suc -> s m2 (el P z s m2).})
        : (P : nat -> *0) -> P zero -> ((n : nat) -> P n -> P (succ n)) -> (m : nat) -> P m;
nat
TYPE
*0