! 185.310 Stackbasierte Sprachen
! Alexander Stromberger
USING: kernel lexer sequences strings combinators assocs accessors 
    quotations random locals math prettyprint io dlists deques vectors hashtables ;
IN: stacksat

SYMBOL: sand
SYMBOL: sor 
SYMBOL: snot
SYMBOL: sl
SYMBOL: sr
SYMBOL: sequiv

TUPLE: svar name ;

: <svar> ( name -- svar )
    svar boa ;

! svar helper
: uniquevars ( seq -- u )
    [ f ] H{ } map>assoc ;

: variables ( formula -- vars )
    [ tuple? ] filter uniquevars ;

: rbit? ( n x -- ? )
    swap bit? ;

: forwardvarstate ( i vars -- vars )
    keys 
    dup length <iota>
    rot
    [ rbit? ] curry
    map
    zip
    >hashtable ;    
! [ drop { t f } random ] assoc-map ;

! shunting yard
:: push-operator ( operator output x -- operator output )
    [ operator deque-empty? [ f ] [ operator pop-front dup sl = [ operator push-front f ] [ output push-front t ] if ] if ] loop
    x operator push-front
    operator output ;

:: handle-sl ( operator output x -- operator output )
    x operator push-front
    operator output ;

:: handle-sr  ( operator output x -- operator output )
    [ operator deque-empty? [ f ] [ operator pop-front dup sl = [ drop f ] [ output push-front t ] if ] if ] loop
    ! pop to output queue if function is available
    operator deque-empty? [ ] [ operator pop-front dup snot = [ output push-front ] [ operator push-front ] if ] if
    operator output ;

: handle-function ( operator output x -- operator output )
    rot swap over push-front swap ;

:: cleanup ( operator output -- operator output )
    [ operator deque-empty? [ f ] [ operator pop-front dup svar? [ output push-front f ] [ output push-front t ] if ] if ] loop
    operator output ;

: queue>vec ( queue -- vec )
    0 <vector>
    swap
    [ suffix ] slurp-deque ;

! shunting yard
: torpn ( infix -- postfix )
    <dlist> ! operator
    <dlist> ! output
    rot ! operator output infix
    [ 
        {
            { [ dup tuple? ] [ over push-front ] }
            { [ dup snot = ] [ handle-function ] } ! not is our only "function"
            { [ dup sl = ] [ handle-sl ] }
            { [ dup sr = ] [ handle-sr ] }
            [ push-operator ] ! operators
        } 
        cond 
    ]
    each
    ! pop operators onto output
    cleanup
    ! drop
    nip 
    queue>vec ;


! tokens to symbols
: token>s ( token -- s ) {
        { "and" [ sand ] }
        { "or" [ sor ] }
        { "not" [ snot ] }
        { "<=>" [ sequiv ] }
        ! unicode counterparts
        { "∧" [ sand ] }
        { "∨" [ sor ] }
        { "¬" [ snot ] }
        ! parens
        { "(" [ sl ] }
        { ")" [ sr ] }
        [ <svar> ]
    } case ;

! helper
: equiv ( a b -- bool )
    2dup and -rot not swap not and or ;

! symbol & var to factor counterpart
: s>quot ( vars clause -- token ) {
        { sand [ drop [ and ] ] }
        { sor [ drop [ or ] ] }
        { snot [ drop [ not ] ] }
        { sequiv [ drop [ equiv ] ] }
        [ swap at 1quotation ]
    } case ;

! piece togehther valid factor quotation from symbols & vars
: replace ( vars formula -- r )
    [ dupd s>quot ] map nip 
    [ ] [ append ] reduce 
    >quotation ;

! print results that statisfy
: printresult ( vars -- )
    [ [ "true" ] [ "false" ] if 
    swap name>> swap
    ": " glue print ] assoc-each ;

: max-iterations ( formula -- n )
    variables keys length 2^ ;

! pretty bad "solver"
:: solve ( formula -- )
    formula variables 
    0 f [ not swap dup formula max-iterations < rot and ] [
        ! variables i
        1 + swap ! i+1 variables
        over 1 - swap ! get i to call forwardvarstate
        forwardvarstate dup ! i+1 rvars rvars
        formula replace call( -- x ) ! i+1 rvars t/f
        rot
        swap
    ] while 
    formula max-iterations < [ "satisfiable" print printresult ] [ "not satisfiable" print drop ] if
    ;

! DSL for formulas
SYNTAX: SAT{ "}" parse-tokens [ token>s ] { } map-as suffix! ;
SYNTAX: ISAT{ "}" parse-tokens [ token>s ] { } map-as torpn suffix! ;

! Erfüllbarkeitsproblem der Aussagenlogik
! dh. können wir eine Belegung von Variablen finden, sodass bspw. ( A ∨ B ) ∧ ¬ ( C ) wahr ist

! Fokus von diesem Projekt liegt darin eine DSL für die Formel zu bauen.

! Beispiele

! 100 SAT{ a b not or c and } solve
! 100 ISAT{ ( A ∨ B ) ∧ ¬ ( C ) } solve

! 100 ISAT{ A <=> not ( A ) } solve

