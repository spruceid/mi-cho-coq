Require Import String.

Definition did_manager_string : string := "
{ parameter
    (or (pair %rotateAuthentication
           (pair address
                 (pair (pair (pair (bytes %current_chain) (bytes %current_value_digest))
                             (pair (bytes %next_value_digest) (key %public_key)))
                       (nat %rotation_count)))
           signature)
        (pair %rotateService
           (pair (pair (string %endpoint) (string %type_))
                 (pair (pair (pair (bytes %current_chain) (bytes %current_value_digest))
                             (pair (bytes %next_value_digest) (key %public_key)))
                       (nat %rotation_count)))
           signature)) ;
  storage
    (pair (pair (pair (key %active_key) (big_map %metadata string bytes))
                (pair (nat %rotation_count) (pair %service (string %endpoint) (string %type_))))
          (address %verification_method)) ;
  code { UNPAIR ;
         IF_LEFT
           { DUP ;
             DUG 2 ;
             CDR ;
             PAIR ;
             SWAP ;
             DUP ;
             DUG 2 ;
             CAR ;
             CDR ;
             DIG 2 ;
             CAR ;
             CAR ;
             DIG 2 ;
             UNPAIR ;
             DIG 3 ;
             DUP ;
             DUG 4 ;
             PACK ;
             SWAP ;
             DIG 2 ;
             DUP ;
             DUG 3 ;
             CAR ;
             CAR ;
             CAR ;
             CHECK_SIGNATURE ;
             NOT ;
             IF { PUSH string ""Failed signature check."" ; FAILWITH } {} ;
             CHAIN_ID ;
             PACK ;
             DIG 3 ;
             DUP ;
             DUG 4 ;
             CAR ;
             CAR ;
             CAR ;
             COMPARE ;
             NEQ ;
             IF { PUSH string ""Invalid chain ID."" ; FAILWITH } {} ;
             PUSH nat 1 ;
             SWAP ;
             DUP ;
             DUG 2 ;
             CAR ;
             CDR ;
             CAR ;
             ADD ;
             DIG 3 ;
             DUP ;
             DUG 4 ;
             CDR ;
             COMPARE ;
             NEQ ;
             IF { PUSH string ""Invalid rotation count."" ; FAILWITH } {} ;
             DUP ;
             DUG 2 ;
             CAR ;
             CDR ;
             CDR ;
             DIG 3 ;
             DUP ;
             DUG 4 ;
             CDR ;
             PAIR ;
             DIG 2 ;
             CAR ;
             CAR ;
             CDR ;
             DIG 3 ;
             CAR ;
             CDR ;
             CDR ;
             PAIR ;
             PAIR ;
             PAIR ;
             NIL operation ;
             PAIR }
           { DUP ;
             DUG 2 ;
             CDR ;
             PAIR ;
             SWAP ;
             DUP ;
             DUG 2 ;
             CAR ;
             CDR ;
             DIG 2 ;
             CAR ;
             CAR ;
             DIG 2 ;
             UNPAIR ;
             DIG 3 ;
             DUP ;
             DUG 4 ;
             PACK ;
             SWAP ;
             DIG 2 ;
             DUP ;
             DUG 3 ;
             CAR ;
             CAR ;
             CAR ;
             CHECK_SIGNATURE ;
             NOT ;
             IF { PUSH string ""Failed signature check."" ; FAILWITH } {} ;
             CHAIN_ID ;
             PACK ;
             DIG 3 ;
             DUP ;
             DUG 4 ;
             CAR ;
             CAR ;
             CAR ;
             COMPARE ;
             NEQ ;
             IF { PUSH string ""Invalid chain ID."" ; FAILWITH } {} ;
             PUSH nat 1 ;
             SWAP ;
             DUP ;
             DUG 2 ;
             CAR ;
             CDR ;
             CAR ;
             ADD ;
             DIG 3 ;
             DUP ;
             DUG 4 ;
             CDR ;
             COMPARE ;
             NEQ ;
             IF { PUSH string ""Invalid rotation count."" ; FAILWITH } {} ;
             DUP ;
             CDR ;
             DIG 2 ;
             DIG 3 ;
             CDR ;
             PAIR ;
             DIG 2 ;
             DUP ;
             DUG 3 ;
             CAR ;
             CAR ;
             CDR ;
             DIG 3 ;
             CAR ;
             CAR ;
             CAR ;
             PAIR ;
             PAIR ;
             PAIR ;
             NIL operation ;
             PAIR } } }
".
