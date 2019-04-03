(* Open Source License *)
(* Copyright (c) 2019 Nomadic Labs. <contact@nomadic-labs.com> *)

(* Permission is hereby granted, free of charge, to any person obtaining a *)
(* copy of this software and associated documentation files (the "Software"), *)
(* to deal in the Software without restriction, including without limitation *)
(* the rights to use, copy, modify, merge, publish, distribute, sublicense, *)
(* and/or sell copies of the Software, and to permit persons to whom the *)
(* Software is furnished to do so, subject to the following conditions: *)

(* The above copyright notice and this permission notice shall be included *)
(* in all copies or substantial portions of the Software. *)

(* THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR *)
(* IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, *)
(* FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL *)
(* THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER *)
(* LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING *)
(* FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER *)
(* DEALINGS IN THE SOFTWARE. *)


(* Finite sets implemented by sorted lists *)

Require Sorted.
Require Import error.

Section definition.

  Variable A : Set.
  Variable compare : A -> A -> comparison.
  Hypothesis compare_eq_iff : forall a b : A, compare a b = Eq <-> a = b.
  Definition lt (a b : A) : Prop :=
    compare a b = Lt.
  Hypothesis lt_trans : Relations_1.Transitive lt.
  Definition gt (a b : A) : Prop :=
    compare a b = Gt.
  Hypothesis gt_trans : Relations_1.Transitive gt.

  Lemma compare_gt_lt a b : compare a b = Lt <-> compare b a = Gt.
  Proof.
    split.
    - intro Hlt.
      case_eq (compare b a).
      + rewrite compare_eq_iff.
        intros He.
        symmetry in He.
        rewrite <- compare_eq_iff in He.
        congruence.
      + intro Hba.
        assert (compare a a = Lt) by (exact (lt_trans _ _ _ Hlt Hba)).
        assert (compare a a = Eq) by (rewrite compare_eq_iff; reflexivity).
        congruence.
      + intro; reflexivity.
    - intro Hgt.
      case_eq (compare a b).
      + rewrite compare_eq_iff.
        intros He.
        symmetry in He.
        rewrite <- compare_eq_iff in He.
        congruence.
      + intro; reflexivity.
      + intro Hab.
        assert (compare a a = Gt) by (exact (gt_trans _ _ _ Hab Hgt)).
        assert (compare a a = Eq) by (rewrite compare_eq_iff; reflexivity).
        congruence.
  Qed.

  Lemma decide_eq (a b : A) : {a = b} + {a <> b}.
  Proof.
    case_eq (compare a b).
    - intro H.
      left.
      apply compare_eq_iff.
      assumption.
    - intro H.
      right.
      intro ne.
      rewrite <- compare_eq_iff in ne.
      congruence.
    - intro H.
      right.
      intro ne.
      rewrite <- compare_eq_iff in ne.
      congruence.
  Qed.


  Definition set : Set :=
    { l : list A | Sorted.StronglySorted lt l }.

  Program Definition empty : set :=
    exist _ nil _.
  Next Obligation.
    apply Sorted.SSorted_nil.
  Defined.

  Definition mem (x : A) (s : set) :=
    let (l, _) := s in
    if List.in_dec decide_eq x l then true else false.

  Fixpoint list_insert (x : A) (l : list A) : list A :=
    match l with
    | nil => cons x nil
    | cons y l =>
      match compare x y with
      | Lt => cons x (cons y l)
      | Eq => cons y l
      | Gt => cons y (list_insert x l)
      end
    end.

  Lemma in_cons_iff (elt : Type) (x y : elt) (l : list elt) :
    List.In x (y :: l) <-> (y = x \/ List.In x l).
  Proof.
    split.
    - apply List.in_inv.
    - intros [He|Hin].
      + destruct He.
        apply List.in_eq.
      + apply List.in_cons; assumption.
  Qed.

  Lemma list_insert_in (x y : A) (l : list A) :
    List.In x (list_insert y l) <-> (x = y \/ List.In x l).
  Proof.
    induction l as [| z l]; simpl.
    - intuition.
    - case_eq (compare y z).
      + intro H.
        apply compare_eq_iff in H.
        destruct H.
        rewrite in_cons_iff.
        intuition.
      + intros _.
        rewrite in_cons_iff.
        rewrite in_cons_iff.
        intuition.
      + intros _.
        rewrite in_cons_iff.
        rewrite IHl.
        intuition.
  Qed.

  Lemma list_insert_sorted (x : A) (l : list A) :
    Sorted.StronglySorted lt l ->
    Sorted.StronglySorted lt (list_insert x l).
  Proof.
    induction l as [|y l]; intro Hs; simpl.
    - constructor.
      + assumption.
      + apply List.Forall_nil.
    - case_eq (compare x y).
      + auto.
      + intro Hlt.
        apply Sorted.StronglySorted_Sorted in Hs.
        apply (Sorted.Sorted_StronglySorted lt_trans).
        constructor.
        * assumption.
        * constructor; assumption.
      + intro Hgt.
        constructor.
        * apply IHl.
          inversion Hs.
          assumption.
        * rewrite List.Forall_forall.
          intro z.
          rewrite list_insert_in.
          rewrite <- compare_gt_lt in Hgt.
          fold (lt y x) in Hgt.
          apply Sorted.StronglySorted_inv in Hs.
          destruct Hs as (Hl, Hf).
          rewrite List.Forall_forall in Hf.
          specialize (Hf z).
          intros [He|H]; [destruct He|]; intuition.
  Qed.

  Program Definition insert (x : A) (s : set) : set :=
    let (l, _) := s in
    exist _ (list_insert x l) _.
  Next Obligation.
    apply list_insert_sorted.
    assumption.
  Defined.

  Lemma list_remove_in {elt : Type} (x y : elt) (l : list elt) de :
    List.In x (List.remove de y l) <-> (List.In x l /\ x <> y).
  Proof.
    induction l as [| z l] ; simpl.
    - intuition.
    - case (de y z).
      + intro He.
        destruct He.
        rewrite IHl.
        intuition congruence.
      + intro Hn.
        rewrite in_cons_iff.
        rewrite IHl.
        intuition congruence.
  Qed.

  Lemma list_remove_sorted (x : A) (l : list A) :
    Sorted.StronglySorted lt l ->
    Sorted.StronglySorted lt (List.remove decide_eq x l).
  Proof.
    induction l as [| y l]; simpl.
    - auto.
    - case (decide_eq x y).
      + intros He H.
        apply IHl.
        inversion H.
        assumption.
      + intro Hn.
        intro Hyl.
        constructor.
        * apply IHl.
          inversion Hyl.
          assumption.
        * apply List.Forall_forall.
          intro z.
          intro Hin.
          apply Sorted.StronglySorted_inv in Hyl.
          destruct Hyl as (_, Hf).
          rewrite List.Forall_forall in Hf.
          specialize (Hf z).
          apply Hf.
          apply list_remove_in in Hin.
          intuition.
  Qed.

  Program Definition remove (x : A) (s : set) : set :=
    let (l, _) := s in
    exist _ (List.remove decide_eq x l) _.
  Next Obligation.
    apply list_remove_sorted.
    assumption.
  Qed.

  Definition update (x : A) (b : bool) (s : set) : set :=
    if b then insert x s else remove x s.

  Fixpoint list_reduce (B : Set) (f : (A * B) -> M B) (b : B) (l : list A) : M B :=
    match l with
    | nil => Return _ b
    | cons x l => bind (fun b => list_reduce B f b l) (f (x, b))
    end.

  Definition reduce B f b (s : set) :=
    let (l, _) := s in list_reduce B f b l.

  Program Definition destruct (s : set) : option (A * set) :=
    let (l, _) := s in
    match l with
    | nil => None
    | cons x s' => Some (x, exist _ s' _)
    end.
  Next Obligation.
    inversion H; assumption.
  Defined.

  Definition size (s : set) : nat :=
    let (l, _) := s in List.length l.

End definition.
