Require Import michelson.

Require Import ZArith.
Require Import List.
Import ListNotations.

Hint Constructors BigStep.

(* Notation for sequence of instructinos *)
Notation "x ;; y" :=  (i_Seq x y) (at level 100)  : list_scope .

Fact can_push94 :
  (BigStep (i_Push (t_Ct ct_Nat) (d_Num (N_NatConstant 4)) ;;
            i_Push (t_Ct ct_Nat) (d_Num (N_NatConstant 9)))
           (SE_Stack [])
           (SE_Stack [ (d_Num (N_NatConstant 9)) ; (d_Num (N_NatConstant 4)) ]) ).
Proof. repeat econstructor. Qed.


Fact test_add :
  (BigStep (i_Push (t_Ct ct_Nat) (d_Num (N_NatConstant 4)) ;;
            i_Push (t_Ct ct_Nat) (d_Num (N_NatConstant 9)) ;;
            i_Add)
           (SE_Stack [])
           (SE_Stack [ (d_Num (N_NatConstant 13)) ]) ).
Proof. repeat econstructor. Qed.

(* a less trivial example *)
Definition fib (n : Z) :=
  (* push 1 1 on stack *)
  i_Push (t_Ct ct_Nat) (d_Num (N_NatConstant 1)) ;;
  i_Dup ;;
  (* push n on stack *)
  i_Push (t_Ct ct_Int) (d_Num (N_IntConstant n)) ;;
  (* push True *)
  i_Push (t_Ct ct_Nat) (d_BoolConstant true) ;;
  (* stack := True ; n ; 1 1 *)
  i_Loop (
      (* stack := n ; a ; b *)
      i_Dip (
          i_Dip ( i_Dup )  ;;
          (* stack := n ; a ; b ; b *)
          i_Dup ;;
          (* stack := n ; a ; a ; b ; b *)
          i_Dip ( i_Swap ) ;;
          (* stack := n ; a ; b ; a ; b *)
          i_Add
          (* stack := n ; a + b ; a ; b *)
      ) ;;
      i_Push (t_Ct ct_Nat) (d_Num (N_NatConstant 1)) ;;
      (* stack := 1 ; (n) ; a + b ; a ; b *)
      i_Swap ;;
      i_Sub ;;
      (* stack := (n-1) ; a + b ; a ; b *)

      i_Dup ;; i_Neq
      (* stack := (n<>0) ; n ; a + b ; a ; b *)
  ) ;;
  (* stack := 0 ; fib n ; fib (n-1) ; ... *)
  i_Drop.
  (* stack := (fib (n+2)) ; fib (n+1) ; ... *)



Definition fib5 := [ (d_Num (N_NatConstant 5)) ;
                       (d_Num (N_NatConstant 3)) ;
                       (d_Num (N_NatConstant 2)) ;
                       (d_Num (N_NatConstant 1)) ;
                       (d_Num (N_NatConstant 1)) ].
Definition fib3 := [ (d_Num (N_NatConstant 2)) ;
                       (d_Num (N_NatConstant 1)) ;
                       (d_Num (N_NatConstant 1)) ].

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
  i_Nil (t_Ct ct_Int) ;;
  i_Push (t_Ct ct_Int) (d_Num (N_IntConstant 4)) ;;
  i_Cons ;;
  i_Push (t_Ct ct_Bool) (d_BoolConstant true) ;;
  i_Cons.

Fact ill_typed :
  (BigStep c_ill_typed
           (SE_Stack [])
           (SE_Stack [ d_DataList [ d_BoolConstant true ; d_Num (N_IntConstant 4) ] ]) ).
Proof. repeat econstructor. Qed.


(* Demonstrates how a ill typed program without semantics *)
Definition c_ill_typed2 :=
  i_Push (t_Ct ct_Int) (d_Num (N_IntConstant 4)) ;;
  i_Push (t_Ct ct_Bool) (d_BoolConstant true) ;;
  i_Add.

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
