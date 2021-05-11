Require Import String.

Definition did_manager_michelson_string : string := "
parameter (or (address %owner) (or (address %auth) (pair %service string string))) ;
storage
  (pair (pair (big_map %metadata string bytes) address)
        (pair (pair string string) address)) ;
code { UNPAIR ;
       SWAP ;
       UNPAIR ;
       UNPAIR ;
       SWAP ;
       DUP ;
       SENDER ;
       COMPARE ;
       EQ ;
       IF { DIG 3 ;
            IF_LEFT
              { SWAP ; DROP ; SWAP }
              { DIG 3 ;
                SWAP ;
                IF_LEFT { SWAP ; CAR } { SWAP ; CDR ; SWAP } ;
                PAIR ;
                DUG 2 ;
                SWAP } ;
            PUSH mutez 0 ;
            AMOUNT ;
            COMPARE ;
            GT ;
            IF { SWAP ; FAILWITH } { PAIR ; PAIR ; NIL operation ; PAIR } }
          { FAILWITH } }
".

