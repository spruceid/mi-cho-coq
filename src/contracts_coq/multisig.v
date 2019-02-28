Add LoadPath "../".
Require Import macros.
Import syntax.
Import comparable.
Require Import NArith.

Definition ADD_nat {S} : instruction (nat ::: nat ::: S) (nat ::: S) := ADD.

Definition storage_ty := pair nat (pair nat (list_ key)).
Definition action_ty := or (pair mutez (contract unit)) (or (option_ key_hash) (pair nat (list_ key))).

Definition parameter_ty := (pair
             (pair
                nat
                action_ty)
             (list_ (option_ signature))).


Definition multisig : full_contract parameter_ty storage_ty :=
  (
    UNPAIR ;; SWAP ;; DUP ;; DIP SWAP ;; (* ; < storage_ty ::: parameter_ty ::: storage_ty ::: nil > *)
    DIP
      (
        UNPAIR ;;
        DUP ;; @SELF parameter_ty _ ;; ADDRESS ;; PAIR ;;
        PACK ;;
        DIP ( UNPAIR ;; DIP SWAP ) ;; SWAP
      ) ;;

    UNPAIR ;; DIP SWAP ;;
    ASSERT_CMPEQ ;;

    DIP SWAP ;; UNPAIR ;;
    DIP
      (
        PUSH nat 0%N ;; SWAP ;;
        ITER_list
          (
            DIP SWAP ;; SWAP ;;
            IF_CONS
              (
                IF_SOME
                  ( SWAP ;;
                    DIP
                      (
                        SWAP ;; DIIP ( DIP DUP ;; SWAP ) ;;
                        CHECK_SIGNATURE ;; ASSERT ;;
                        PUSH nat 1%N ;; ADD_nat))
                  ( SWAP ;; DROP )
              )
              (
                FAIL
              ) ;;
            SWAP
          )
      ) ;;
    ASSERT_CMPLE ;;
    DROP ;; DROP ;;

    DIP ( UNPAIR ;; PUSH nat 1%N ;; ADD ;; PAIR ) ;;

    NIL operation ;; SWAP ;;
    IF_LEFT
      ( UNPAIR ;; UNIT ;; TRANSFER_TOKENS ;; CONS )
      ( IF_LEFT (SET_DELEGATE ;; CONS )
                ( DIP ( SWAP ;; CAR ) ;; SWAP ;; PAIR ;; SWAP )) ;;
    PAIR ).
