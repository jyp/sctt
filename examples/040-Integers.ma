TERM

Bool := { 'true , 'false } ;

Eq = (\A -> \x -> \y -> (P : A -> *0) -> P x -> P y)
   : (A : *0) -> A -> A -> *1;

refl = (\A -> \x -> \P -> \p -> p)
     : (A : *0) -> (x:A) -> Eq A x x;

T = Eq Bool 'true
  : Bool -> *1 ;

t = refl Bool 'true
  : T 'true ;

Bit := { 'zero , 'one } ;
incr =
  \n -> case n of {
     'zero -> ('one, 'zero).
     'one -> ('zero, 'one)
     }
  : Bit -> (b : Bit) * Bit ;

-- return (number, carry)
add = (\n1 -> \n2 -> case n1 of {
     'zero -> (n2, 'zero).
     'one -> incr n2
    })
  : Bit -> Bit -> (b : Bit) * Bit ;

add_carry =
  (\n1 -> \n2 -> \n3 -> (
    n' = add n1 n2 ;
    n'' = add n'.1 n3 ;
    carry = add n'.2 n''.2 ;
    (n''.1 , carry.1)
  )) : Bit -> Bit -> Bit -> (b:Bit) * Bit ;


mult = (\n1 -> \n2 -> case n1 of {
      'zero -> 'zero.
      'one -> case n2 of {
        'zero -> 'zero.
        'one -> 'one
      }})
     : Bit -> Bit -> Bit ;

stuff = add 'zero 'one : (b:Bit) * Bit ;

equal =
  (\n1 -> \n2 -> case n1 of {
    'zero -> case n2 of {
      'zero -> 'true.
      'one -> 'false
     }.
     'one -> case n2 of {
       'zero -> 'false.
       'one -> 'true
     }
  })
  : (n1 : Bit) -> (n2 : Bit) -> Bool ;

stuff = t :
  T (equal 'zero (add 'one 'one).1 ) ;

-- low bits on the left.
Bit5 := (b:Bit) * ((b:Bit) * ((b:Bit) * ((b:Bit) * Bit))) ;

bit5 = (\n4 -> \n3 -> \n2 -> \n1 -> \n0 ->
        (n0,(n1,(n2,(n3,n4)))) )
     : Bit -> Bit -> Bit -> Bit -> Bit -> Bit5 ;

add5 =
  (\n1 -> \n2 -> (
    b0 = (add       n1.1       n2.1            );
    b1 = (add_carry n1.2.1     n2.2.1     b0.2 );
    b2 = (add_carry n1.2.2.1   n2.2.2.1   b1.2 );
    b3 = (add_carry n1.2.2.2.1 n2.2.2.2.1 b2.2 );
    b4 = (add_carry n1.2.2.2.2 n2.2.2.2.2 b3.2 );

    (b0.1, (b1.1, (b2.1, (b3.1, b4.1))))

  )) : Bit5 -> Bit5 -> Bit5 ;


{-
  01101
+ 00111
= 10100
-}

int1 =   (bit5 'zero  'one  'one 'zero  'one) : Bit5 ;
int2 =   (bit5 'zero 'zero  'one  'one  'one) : Bit5 ;
result = (bit5  'one 'zero  'one 'zero 'zero) : Bit5 ;

stuff =
  refl Bit5 result :
  (Eq Bit5 (add5 int1 int2) result) ;

*0
TYPE
*1