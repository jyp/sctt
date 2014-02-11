TERM
  Unit = { 'unit } : *0 ;
  \s -> ( c : { 'Foo , 'Bar } ) *
       ( case c of {
           'Foo -> s.
           'Bar -> Unit.
       } )
TYPE
  *0 -> *1