Require Import michelson.

Require Import ZArith.
Require Import List.
Import ListNotations.

Hint Constructors BigStep.

(* Notation for sequence of instructinos *)
Notation "x ;; y" :=  (i_SEQ x y) (at level 100)  : list_scope .

(* Shortcuts for instructions *)
Definition PUSH t x := (i_Fun (i_Non_failing (i_nff_nullary (i_PUSH t x)))).
Definition ADD := (i_Fun i_ADD).
Definition SUB := (i_Fun i_SUB).
Definition DUP := (i_Fun (i_Non_failing (i_DUP))).
Definition DIP c := i_DIP c.
Definition SWAP := (i_Fun (i_Non_failing (i_SWAP))).
Definition NEQ := (i_Fun (i_Non_failing (i_nff_unary (i_unary_comparison NEQ)))).
Definition LOOP body := (i_LOOP body).
Definition DROP := (i_Fun (i_Non_failing i_DROP)).
Definition NIL ty := (i_Fun (i_Non_failing (i_nff_nullary (i_NIL ty)))). 
Definition CONS := (i_Fun (i_Non_failing (i_nff_binary i_CONS))).

Fact can_push94 :
  (BigStep (PUSH (ty_Comparable_type cty_nat) (d_Num (num_NatConstant 4)) ;;
            PUSH (ty_Comparable_type cty_nat) (d_Num (num_NatConstant 9)))
           (SE_Stack [])
           (SE_Stack [ (d_Num (num_NatConstant 9)) ; (d_Num (num_NatConstant 4)) ]) ).
Proof. repeat econstructor. Qed.


Fact test_add :
  (BigStep (PUSH (ty_Comparable_type cty_nat) (d_Num (num_NatConstant 4)) ;;
            PUSH (ty_Comparable_type cty_nat) (d_Num (num_NatConstant 9)) ;;
            ADD)
           (SE_Stack [])
           (SE_Stack [ (d_Num (num_NatConstant 13)) ]) ).
Proof. repeat econstructor. Qed.

(* a less trivial example *)
Definition fib (n : Z) :=
  (* push 1 1 on stack *)
  PUSH (ty_Comparable_type cty_nat) (d_Num (num_NatConstant 1)) ;;
  DUP ;;
  (* push n on stack *)
  PUSH (ty_Comparable_type cty_int) (d_Num (num_IntConstant n)) ;;
  (* push True *)
  PUSH (ty_Comparable_type cty_nat) (d_Bool true) ;;
  (* stack := True ; n ; 1 1 *)
  LOOP (
      (* stack := n ; a ; b *)
      DIP (
          DIP ( DUP )  ;;
          (* stack := n ; a ; b ; b *)
          DUP ;;
          (* stack := n ; a ; a ; b ; b *)
          DIP ( SWAP ) ;;
          (* stack := n ; a ; b ; a ; b *)
          ADD
          (* stack := n ; a + b ; a ; b *)
      ) ;;
      PUSH (ty_Comparable_type cty_nat) (d_Num (num_NatConstant 1)) ;;
      (* stack := 1 ; (n) ; a + b ; a ; b *)
      SWAP ;;
      SUB ;;
      (* stack := (n-1) ; a + b ; a ; b *)

      DUP ;; NEQ
      (* stack := (n<>0) ; n ; a + b ; a ; b *)
  ) ;;
  (* stack := 0 ; fib n ; fib (n-1) ; ... *)
  DROP.
  (* stack := (fib (n+2)) ; fib (n+1) ; ... *)



Definition fib5 := [ (d_Num (num_NatConstant 5)) ;
                       (d_Num (num_NatConstant 3)) ;
                       (d_Num (num_NatConstant 2)) ;
                       (d_Num (num_NatConstant 1)) ;
                       (d_Num (num_NatConstant 1)) ].
Definition fib3 := [ (d_Num (num_NatConstant 2)) ;
                       (d_Num (num_NatConstant 1)) ;
                       (d_Num (num_NatConstant 1)) ].

Fact test_fib3 :
  (BigStep (fib 1) (SE_Stack []) (SE_Stack fib3)).
Proof. repeat econstructor. Qed.

Fact test_fib5 :
  (BigStep (fib 3) (SE_Stack []) (SE_Stack fib5)).
Proof.
  repeat econstructor. simpl. omega.
  repeat econstructor. simpl. omega.
Qed.

(* Demonstrates how a ill typed program can be executed *)
Definition c_ill_typed :=
  NIL (ty_Comparable_type cty_int) ;;
  PUSH (ty_Comparable_type cty_int) (d_Num (num_IntConstant 4)) ;;
  CONS ;;
  PUSH (ty_Comparable_type cty_bool) (d_Bool true) ;;
  CONS.

Fact ill_typed :
  (BigStep c_ill_typed
           (SE_Stack [])
           (SE_Stack [ d_SetList [ d_Bool true ; d_Num (num_IntConstant 4) ] ]) ).
Proof. repeat econstructor. Qed.


(* Demonstrates how a ill typed program without semantics *)
Definition c_ill_typed2 :=
  PUSH (ty_Comparable_type cty_int) (d_Num (num_IntConstant 4)) ;;
  PUSH (ty_Comparable_type cty_bool) (d_Bool true) ;;
  ADD.

Fact ill_typed2 :
  ~ exists s, (BigStep c_ill_typed2
                       (SE_Stack [])
                       s ).
Proof.
  intros [se H].
  inversion H. 
  inversion H; subst.
  inversion H3; subst.
  inversion H4; subst.
  inversion H7; subst.
  inversion H5.
Qed.

(* Aborted: To show that the semantics are deterministic.  *)
Theorem deterministic :
  (forall i d d1 d2,
      BigStep i d d1 ->
      BigStep i d d2 ->
      d1 = d2).
Proof.
  intros i d d1 d2 H H0.
  (* induction H; inversion H0; eauto. subst. *)
Abort.
