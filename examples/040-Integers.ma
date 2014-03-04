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
     'zero -> x := (n2 , 'zero ) ; x .
     'one -> incr n2
    })
  : Bit -> Bit -> (b : Bit) * Bit ;

add_carry =
  (\n1 -> \n2 -> \n3 -> (
    (n', carry1) = split (add n1 n2) ;
    (n'', carry2) = split (add n' n3) ;
    (carry, foo ) = split (add carry1 carry2) ;
    x := ( n'' , carry ) ; x))
  : Bit -> Bit -> Bit -> (b:Bit) * Bit ;


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


( n , c ) = split (add 'one 'one) ;
stuff = t : T (equal 'zero n ) ;

-- low bits on the left.
Bit5 := (b:Bit) * ((b:Bit) * ((b:Bit) * ((b:Bit) * Bit))) ;

bit5 = (\n4 -> \n3 -> \n2 -> \n1 -> \n0 ->
        (x := (n0,(n1,(n2,(n3,n4)))) ; x) )
     : Bit -> Bit -> Bit -> Bit -> Bit -> Bit5 ;

-- add5 =
--   (\n1 -> \n2 -> (
--     (b0, carry0) = split (add       n1.1       n2.1            );
--     (b1, carry1) = split (add_carry n1.2.1     n2.2.1     carry0 );
--     (b2, carry2) = split (add_carry n1.2.2.1   n2.2.2.1   carry1 );
--     (b3, carry3) = split (add_carry n1.2.2.2.1 n2.2.2.2.1 carry2 );
--     (b4, carry4) = split (add_carry n1.2.2.2.2 n2.2.2.2.2 carry3 );

--     (b0, (b1, (b2, (b3, b4))))

--   )) : Bit5 -> Bit5 -> Bit5 ;


-- {-
--   01101
-- + 00111
-- = 10100
-- -}

-- int1 =   (bit5 'zero  'one  'one 'zero  'one) : Bit5 ;
-- int2 =   (bit5 'zero 'zero  'one  'one  'one) : Bit5 ;
-- result = (bit5  'one 'zero  'one 'zero 'zero) : Bit5 ;

-- stuff =
--   refl Bit5 result :
--   (Eq Bit5 (add5 int1 int2) result) ;

*0
TYPE
*1