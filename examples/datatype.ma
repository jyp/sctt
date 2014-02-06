TERM
  \s ->
    ( ty : { 'Foo , 'Bar } ) *
    ( case ty of {
        'Foo -> s -> *0.
        'Bar -> *0
    } )
TYPE
  *0 -> *1