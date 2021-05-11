Require Import String.

Definition did_manager_string : string := "
{ parameter
    (or (address %owner)
        (or (address %auth) (pair %service (string %endpoint) (string %type_)))) ;
  storage
    (pair (pair (big_map %metadata string bytes) (address %owner))
          (pair (pair %service (string %endpoint) (string %type_))
                (address %verification_method))) ;
  code { UNPAIR ;
         SWAP ;
         DUP ;
         DUG 2 ;
         CAR ;
         CDR ;
         SENDER ;
         COMPARE ;
         NEQ ;
         IF { PUSH string ""Unauthorised sender."" ; FAILWITH } {} ;
         PUSH mutez 0 ;
         AMOUNT ;
         COMPARE ;
         GT ;
         IF { PUSH string ""Tez not accepted."" ; FAILWITH } {} ;
         IF_LEFT
           { SWAP ;
             DUP ;
             DUG 2 ;
             CDR ;
             CDR ;
             DIG 2 ;
             DUP ;
             DUG 3 ;
             CDR ;
             CAR ;
             PAIR ;
             SWAP ;
             DIG 2 ;
             CAR ;
             CAR ;
             PAIR ;
             PAIR ;
             NIL operation ;
             PAIR }
           { IF_LEFT
               { SWAP ;
                 DUP ;
                 DUG 2 ;
                 CDR ;
                 CAR ;
                 PAIR ;
                 SWAP ;
                 DUP ;
                 DUG 2 ;
                 CAR ;
                 CDR ;
                 DIG 2 ;
                 CAR ;
                 CAR ;
                 PAIR ;
                 PAIR ;
                 NIL operation ;
                 PAIR }
               { SWAP ;
                 DUP ;
                 DUG 2 ;
                 CDR ;
                 CDR ;
                 SWAP ;
                 PAIR ;
                 SWAP ;
                 DUP ;
                 DUG 2 ;
                 CAR ;
                 CDR ;
                 DIG 2 ;
                 CAR ;
                 CAR ;
                 PAIR ;
                 PAIR ;
                 NIL operation ;
                 PAIR } } } }
".

