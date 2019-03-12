Require Import michelson.

Require Import List.
Import ListNotations.

Hint Constructors BigStep.


(* Quick math *)
Fact failed_fails : (forall i, (BigStep i (SE_Failed) (SE_Failed))).
Proof. induction i; eauto. Qed.


(* The semantics is not actually total (example: addition with empty stack is not defined).
 * Hence, we wrap the semantics in an inductive giving a "escape hatch value".
 * *)
Inductive BigStep_total :
  instruction -> stackerr -> option stackerr -> Prop :=
| BigStep_cont :
    forall (i : instruction) (d d' : stackerr),
      BigStep i d d' ->
      BigStep_total i d (Some d')
| BigStep_stuck :
    forall  (i : instruction) (d : stackerr),
      BigStep_total i d None.

(* Clearly if we have Some value with wrapped semantics, it is also in underlying *)
Fact BigStep_total_to_BigStep :
  forall i d d',
    BigStep_total i d (Some d') ->
    BigStep i d d'.
Proof. intros i d d' H. now inversion H. Qed.

(* Some convenient tactics *)

(* called when the interpreter is stuck *)
Ltac stuck := exists None; constructor.

(* destruct a as num, if it is not none the interpreter is stuck *)                     
Ltac as_num v1 :=
  destruct v1 eqn:Hd0;
  match goal with
  | [ Hd0 : v1 = d_Num _ |- _ ] => clear Hd0
  | _ => stuck
  end.

(* To show that the semantics can be executed. This proof of theorem
will then be extracted as an ocaml program *)
Theorem total :
  forall i d,
      { md : _ & BigStep_total i d md }.
Proof.
  intros i.

  intro d. destruct d as [|d].
  eexists. constructor. apply failed_fails.

  Hint Constructors BigStep.
  Hint Resolve BigStep_cont failed_fails BigStep_total_to_BigStep.

  generalize dependent d.
  generalize dependent i.
  induction i; intros d0; eauto.

  (* I here prove for the rules of sequence, addition, subtraction *)

  (* Sequence *)
  1: {
  destruct (IHi1 d0) as [ [[|d'']|] Hi1 ]; [ | | stuck].
  (* Case i1 fails *)
    + eauto.
  (* case it doesn't *)
    + destruct (IHi2 d'') as [ [d'|] Hi2 ]; [ | stuck].
      eauto 10.
  }

  (* Add *)
  30: {
    (* execution can only continue if there two values on the stack *)
    destruct d0 as [ | v1 [| v2 d0] ]; [ stuck | stuck | ].
    as_num v1. as_num v2. eauto.
  }

  (* Sub *)
  30: {
    destruct d0 as [ | v1 [| v2 d0] ]; [ stuck | stuck | ].
    as_num v1. as_num v2. eauto.
  }

  (* TODO: deal with remaining cases *)
  all : stuck.
Defined.

(* extract the function total to michelson.ml *)
Require Extraction.
Extraction Language OCaml.
Extraction "michelson.ml" total.

