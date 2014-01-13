TERM
Top := {'nil};
Tag := {'zer, 'suc};
nat = (rec n -> (t : Tag) * (case t of {'zer -> Top. 'suc -> n}))
    : *0;
zero = ('zer, 'nil) : nat;
suc = (\n -> ('suc, n)) : nat -> nat;
nat
TYPE
*0