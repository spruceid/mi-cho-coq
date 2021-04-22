From Michocoq Require Import macros syntax.
Require Import ZArith String.

Definition payload_ty :=
  or
    (pair
       (pair
          (* %journaliere) *)
          key_hash
          (pair
             (pair
                (*
                 * %fonds_restant
                 *)
                mutez
                (*
                 * %duree_de_blocage
                 *)
                int)
             (* %file *)
             (pair
                (list (pair timestamp mutez))
                (list (pair timestamp mutez)))))
       (*  %nouvelle_clef_maitresse *)
       key_hash)
    None
    (pair
       (lambda unit (list operation))
       (*  %nouvelle_clef_publique *)
       key_hash)
    None.

Definition parameter_master_ty :=
  (pair
     (pair
        (* %clef_publique) *)
        key signature)
     payload_ty).

Definition parameter_transfer_ty :=
  (pair (*  %transfer *)
     (pair
        (list (*  %beneficiaires *)
           (pair
              (* %montant *)
              mutez
              (*  %beneficiaire *)
              (contract unit)))
        (* %novelle_clef_journaliere *)
        key_hash)
     (pair
        (* %clef_publique *)
        key
        signature)).

Definition parameter_ty : type :=
  (or
      (*
       * %send
       *)
     unit
     (Some "%send"%string)
     (or
        parameter_master_ty (Some "%appel_clef_maitresse"%string)
        parameter_transfer_ty (Some "%transfer"%string)) None).

Definition storage_context_ty :=
  (pair
     (* journaliere *)
     key_hash
     (pair
        (pair
           (*
            * %fonds_restant
            *)
           mutez
           (* %duree_de_blocage *)
           int)
        (* %file *)
        (pair
           (list (pair timestamp mutez))
           (list (pair timestamp mutez))))).

Definition storage_auth_ty :=
  (pair
     (* %maitresse *)
     key_hash
     (* %sel *)
     (pair nat nat)).

Definition storage_ty := (pair storage_context_ty storage_auth_ty).

Definition slc_ep_master_lambda :
  instruction_seq (Some (parameter_ty, None))
                  false
                  ((pair
                      (lambda unit (list operation))
                      (*  %nouvelle_clef_publique *)
                      key_hash) ::: (pair nat nat)::: storage_context_ty ::: nil)
                  (list operation ::: storage_context_ty ::: storage_auth_ty ::: nil)
  :=
    (* execute lambda *)
    { UNPAIR (* @function *) (* @new_master_key *) ;
      DIP1 { PAIR; SWAP };
      UNIT ;
      EXEC }%michelson.

Definition slc_ep_master :
  instruction_seq (Some (parameter_ty, None))
                  false
                  (parameter_master_ty ::: storage_context_ty ::: storage_auth_ty ::: nil)
                  (list operation ::: storage_context_ty ::: storage_auth_ty ::: nil) :=
  { (* retrieve master_key and salt from storage *)
    DIP1 {SWAP};
    SWAP ;
    UNPAIR ;
    (* pack the payload with the header (contract, chain_id, salt) *)
    DIP1 {SWAP;
          UNPAIR;
          DIP1 { DUP;
                 (* pack the received payload (new storage or lambda) *)
                 PACK (a := or (pair storage_context_ty key_hash)
                               _ (pair (lambda unit (list operation)) key_hash)
                               _) I (* @packedpayload *) ;
                 (* pack the header *)
                 DIP1 { DIP1 { UNPAIR;
                               DUP ;
                               DIP1 {
                                   PUSH nat (comparable_constant nat 2%N) ;
                                   (* increment salt *)
                                   ADD (s := add_nat_nat) (* @salt_inc *) ;
                                   PAIR };
                               PACK (a := nat) I (* @packed_salt *) ;
                               (* packed(salt) *)
                               CHAIN_ID ;
                               SELF (self_type := parameter_ty) (self_annot := None) None I ;
                               PAIR ;
                               PACK (a := pair (contract parameter_ty) chain_id) I (* @packed_self_chain_id *) ;
                               (* packed(self, chain_id) : packed(salt) : ... *)
                               CONCAT (i := stringlike_bytes) (* @packedheader *)
                                      (* (packed(self, chain_id) ++ packed(salt)) : ... *)
                             } ;
                        SWAP} ;
                 CONCAT (i := stringlike_bytes) (* @packedpayload *) ;
                 (* (packed(storage) *)
                 (*    ++ packed(self, chain_id) *)
                 (*    ++ packed(salt)) : ... *)
                 DUP (* @packedpayloadDup *) } ;
          UNPAIR ;
          DUP ;
          HASH_KEY (* @sender_public_key_hash *)
         } ;

    (* verify that the public key hash of the sender equal the public key has of the master *)
    ASSERT_CMPEQ ;
    (* verify that the that the signature is a signature of the payload with from master *)
    CHECK_SIGNATURE ;
    (* if not, fail. *)
    IF_TRUE {DROP1} {FAILWITH (a := bytes) I} ;

    IF_LEFT { (* set new storage *)
        UNPAIR (* @new_storage *) (* @new_master_key *) ;
        (* pair up the incremented salt with the new master key *)
        DIP1{ PAIR ;
                SWAP ;
                DROP1} ;
        (* no operations will be executed *)
        NIL operation}
            ((* execute lambda *)
              slc_ep_master_lambda
  )}%michelson.


Definition slc_ep_transfer2_transaction_iter_body {A}:
  instruction_seq (Some (parameter_ty, None)) false
              (pair mutez (contract unit) ::: list operation ::: mutez ::: A)
              (list operation ::: mutez ::: A) :=
  { UNPAIR ; (* production des transactions *)
    DUP ;
    DIP1 {
        UNIT ;
        TRANSFER_TOKENS (p := unit) I ;
        CONS
      } ;
    SWAP ;
    (* #calcul du temps de blocage *)
    DIP1 { SWAP ; ADD (s := add_tez_tez) }}%michelson.


Definition slc_ep_transfer2_transaction_iter {A} :
  instruction
    (Some (parameter_ty, None))
    false
    (list (pair mutez (contract unit)) ::: list operation ::: mutez ::: A)
    _
  :=
  ITER (i := iter_list _) (slc_ep_transfer2_transaction_iter_body).


Definition slc_ep_transfer_loop_body :
  instruction (Some (parameter_ty, None)) _
  (list (pair timestamp mutez) ::: list (pair timestamp mutez) ::: mutez ::: storage_auth_ty ::: nil)
  (bool ::: list (pair timestamp mutez) ::: list (pair timestamp mutez) ::: mutez ::: storage_auth_ty::: nil)
  := (IF_CONS { DUP ;
                CAR ;
                NOW ;
                IFCMPGE { CDR ;
                          SWAP ;
                          DIP1 { SWAP ;
                                 DIP1 { ADD (s := add_tez_tez)}} ;
                          PUSH bool True }
                        { CONS ;
                          PUSH bool False}}
              { IF_CONS { NIL (pair timestamp mutez) ;
                          SWAP ;
                          CONS ;
                          SWAP ;
                          ITER (i := iter_list _) { CONS } ;
                          NIL (pair timestamp mutez) ;
                          SWAP ;
                          PUSH bool True}
                        { NIL (pair timestamp mutez) ;
                          DUP ;
                          PUSH bool False}
     })%michelson.

Definition slc_ep_transfer_loop : instruction _ _ _ _ :=
  (LOOP { slc_ep_transfer_loop_body })%michelson.

Definition slc_ep_transfer1_check_signature :
  instruction_seq (Some (parameter_ty, None)) Datatypes.false
                  (parameter_transfer_ty ::: storage_context_ty ::: storage_auth_ty ::: nil)
                  (list (pair mutez (contract unit)) :::
                        list operation ::: mutez ::: key_hash ::: int ::: mutez ::: list (pair timestamp mutez) :::
                        list (pair timestamp mutez) ::: storage_auth_ty ::: nil)
  (*
   * (list operation ::: mutez ::: key_hash ::: int ::: mutez :::
   *       (list (pair timestamp mutez)) :::
   *       (list (pair timestamp mutez)) :::
   *       (pair key_hash nat) ::: nil)
   *)
  :=
    {
      DIP1 { UNPAPAIR } ; (* cas d'un appel simple *)
      UNPAIR ;
      DUP ;
      PACK (a := (pair (list (pair mutez (contract unit))) key_hash)) I ;
      DIP1 {
          UNPAIR (a := list (pair mutez (contract unit)))
                 (b := key_hash) ;
          DIP1 {SWAP}} ;
      SWAP ;
      DIP1 { DIP1 { DIP1 {SWAP} ;
                    SWAP ;
                    DIP1 { UNPAIR ;
                            DUP ;
                            HASH_KEY } ;
                    ASSERT_CMPEQ ; (* verification de compatibilite des clefs *)
                    DIG 5 (S1 := (_ ::: _ ::: _ ::: _ ::: _ ::: nil)) (@eq_refl _ 5) ;
                    UNPAIR ;
                    DIP1 { UNPAIR;
                           DIP1 { DUP ;
                                  PUSH nat (Comparable_constant nat 2%N) ;
                                  ADD (s:= add_nat_nat) } ;
                           PAIR };
                    PAIR ;
                    DUG 6 (S1 := (_ ::: _ ::: _ ::: _ ::: _ ::: _ ::: nil)) (@eq_refl _ 6) ;
                    PACK (a := nat) I ;
                    CHAIN_ID ;
                    SELF (self_type := parameter_ty) (self_annot := None) None I ;
                    PAIR ;
                    PACK (a := pair (contract parameter_ty) chain_id) I  ;
                    CONCAT (i := stringlike_bytes)
                } ;
              CONCAT (i := stringlike_bytes) ;
              SWAP ;
              DIP1 { SWAP ;
                      DIP1 {DUP}} ;
              CHECK_SIGNATURE ; (* #verification de signature *)
              IF_TRUE {DROP1} {FAILWITH (a := bytes) I} ;
              DIP1 { UNPAIR (b := int) ;
                     SWAP ;
                     DIP1 { SWAP ;
                            UNPAIR ;
                            PUSH bool True ;
                            (* recherche de fonds à liberer *)
                            slc_ep_transfer_loop ;
                            DIP1 {SWAP} ;
                            SWAP
                          }
                  } ;
              PUSH mutez (0 ~mutez) ;
              NIL operation
    }}%michelson.

Definition slc_ep_transfer3_register :
  instruction (Some (parameter_ty, None)) false
              (list operation ::: mutez ::: key_hash ::: int ::: mutez :::
                    list (pair timestamp mutez) :::
                    list (pair timestamp mutez) :::
                    storage_auth_ty ::: nil)
              (list operation ::: storage_context_ty ::: storage_auth_ty ::: nil)
  :=
    DIP1 { SWAP ; (* blocage des fonds depensés *)
           DIP1 { SWAP ;
                  DUP ;
                  NOW ;
                  ADD (s := add_timestamp_int);
                  SWAP ;
                  DIP1 { DIP1 { SWAP } ;
                         SWAP ;
                         DIP1 { SWAP ;
                                DUP ;
                                DIP1 { SWAP ;
                                       PAIR ;
                                       SWAP ;
                                       DIP1 { CONS } ; (* ajout dans la file *)
                                       PAIR}} ;
                         SUB (s := sub_tez_tez)} ; (* calcul du reste non bloqué *)
                  SWAP ;
                  PAIR ;
                  PAIR
                } ;
           PAIR}%michelson.


Definition slc_ep_transfer :
  instruction_seq (Some (parameter_ty, None)) false
                  (parameter_transfer_ty ::: storage_context_ty ::: storage_auth_ty ::: nil)
                  (list operation ::: storage_context_ty ::: storage_auth_ty ::: nil)
  := slc_ep_transfer1_check_signature ;;;
     { slc_ep_transfer2_transaction_iter ;
       slc_ep_transfer3_register }.

Definition slc_ep_receive :
  instruction_seq (Some (parameter_ty, None)) false
              (unit ::: storage_context_ty ::: storage_auth_ty ::: nil)
              (list operation ::: storage_context_ty ::: storage_auth_ty ::: nil)
  := { DROP1 ; (* cas d'un simple ajout de fonds (parameter : (Left Unit)) *)
       NIL operation }%michelson.

Definition dsl :
  full_contract _ parameter_ty None storage_ty
  :=
    { UNPAPAIR ;
      IF_RIGHT { (* cas d'un appel par la clef maîtresse *)
          IF_LEFT
            slc_ep_master
            slc_ep_transfer
        }
               slc_ep_receive ;
      PAPAIR}%michelson.

Definition slc_contract_file : contract_file :=
  Mk_contract_file parameter_ty I None storage_ty I Datatypes.false dsl.
