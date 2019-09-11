Require Import michelson.

Require Import List.
Import ListNotations.

Hint Constructors BigStep.


Inductive AExp : Set :=
  | AEConst (n  : nat) : AExp
  | AEAdd (e1 e2  : AExp) : AExp
  | AEMul (e1 e2  : AExp) : AExp.

Fixpoint AExp_denot (e : AExp) : nat:=
  match e with
  | AEConst n => n
  | AEAdd e1 e2 => AExp_denot e1 + AExp_denot e2
  | AEMul e1 e2 => AExp_denot e1 * AExp_denot e2
  end.

Goal (AExp_denot (AEAdd (AEConst 1) (AEConst 5)) = 6). repeat econstructor. Qed.

(* Notation for sequence of instructinos *)
Notation "x ;; y" :=  (i_SEQ x y) (at level 100)  : list_scope .

Fixpoint AExp_compile (e : AExp) : code :=
  match e with
  | AEConst n => i_Fun (i_PUSH (ty_Comparable_type cty_nat) (d_Num (num_NatConstant n)))
  | AEAdd e1 e2 => AExp_compile e2 ;;
                   AExp_compile e1 ;;
                   i_Fun i_ADD
  | AEMul e1 e2 => AExp_compile e2 ;;
                   AExp_compile e1 ;;
                   i_Fun i_MUL
  (* | _ => i_Failwith *)
  end.


Definition aexp_denot_compil_corr (e : AExp) (s_init  : list data): Prop :=
  (BigStep (AExp_compile e)
           (SE_Stack s_init)
           (SE_Stack ((d_Num (num_NatConstant (AExp_denot e))) :: s_init))).

Fact test1 : aexp_denot_compil_corr (AEAdd (AEConst 1) (AEConst 5)) [].
  unfold aexp_denot_compil_corr. simpl.
  repeat econstructor.
Qed.

Lemma aexp_denot_compil_corr_all' :
  forall e s, aexp_denot_compil_corr e s.
Proof.
  unfold aexp_denot_compil_corr.
  induction e; intro s; repeat (eauto; econstructor).
Qed.

Theorem aexp_denot_compil_corr_all :
  forall e, (BigStep (AExp_compile e)
                     (SE_Stack [])
                     (SE_Stack ([(d_Num (num_NatConstant (AExp_denot e)))]))).
Proof. intro e. apply (aexp_denot_compil_corr_all' e []). Qed.
