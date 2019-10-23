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

Require Sorted Eqdep_dec.
Require Import error.
Import error.Notations.

Section definition.

  Variable A : Set.
  Variable compare : A -> A -> comparison.
  Hypothesis compare_eq_iff : forall a b : A, compare a b = Eq <-> a = b.
  Lemma compare_refl a : compare a a = Eq.
  Proof.
    apply (compare_eq_iff a a).
    reflexivity.
  Qed.
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

  Fixpoint list_in_sorted x l :=
    match l with
    | nil => false
    | cons y l =>
      match compare x y with
      | Gt => list_in_sorted x l
      | Eq => true
      | Lt => false
      end
    end.

  Lemma list_in_sorted_correct x l :
    Sorted.StronglySorted lt l ->
    list_in_sorted x l <-> List.In x l.
  Proof.
    induction l as [|y l]; intro Hs; simpl.
    - split; intro H; inversion H.
    - case_eq (compare x y); intro Hxy.
      + split; [|constructor].
        intros _.
        rewrite compare_eq_iff in Hxy.
        intuition congruence.
      + split; [intro H; inversion H|].
        intros [He|Hin].
        * symmetry in He; rewrite <- compare_eq_iff in He.
          congruence.
        * assert (List.Forall (lt y) l) as Hf by (inversion Hs; assumption).
          rewrite List.Forall_forall in Hf.
          specialize (Hf x Hin).
          exfalso.
          generalize (lt_trans _ _ _ Hxy Hf).
          generalize compare_refl.
          congruence.
      + assert (Sorted.StronglySorted lt l) as Hsl by (inversion Hs; assumption).
        specialize (IHl Hsl).
        rewrite IHl.
        split; [intuition|].
        intros [He|H]; [|auto].
        generalize compare_refl.
        congruence.
  Qed.

  Definition mem (x : A) (s : set) :=
    let (l, _) := s in
    list_in_sorted x l.

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

  Lemma list_insert_in (x y : A) (l : list A) :
    List.In x (list_insert y l) <-> (x = y \/ List.In x l).
  Proof.
    induction l as [| z l]; simpl.
    - intuition.
    - case_eq (compare y z).
      + intro H.
        rewrite compare_eq_iff in H.
        destruct H.
        simpl.
        intuition.
      + intros _.
        simpl.
        intuition.
      + intros _.
        simpl.
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
        simpl.
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
    | cons x l =>
      let! b := f (x, b) in
      list_reduce B f b l
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

  Lemma decide_eq_refl (a : A) : decide_eq a a = left eq_refl.
  Proof.
    case (decide_eq a a).
    - intro e.
      f_equal.
      apply (Eqdep_dec.UIP_dec decide_eq).
    - congruence.
  Qed.

  Lemma in_sorted x a l :
    Sorted.StronglySorted lt (a :: l) ->
    List.In x (a :: l) <-> (x = a \/ (lt a x /\ List.In x l)).
  Proof.
    intro Hs.
    simpl.
    split.
    - intros [H|H].
      + intuition.
      + right.
        assert (List.Forall (lt a) l) as Hf by (inversion Hs; assumption).
        rewrite List.Forall_forall in Hf.
        specialize (Hf x).
        intuition.
    - intuition.
  Qed.

  Lemma not_in_sorted a l :
    Sorted.StronglySorted lt (a :: l) -> ~ List.In a l.
  Proof.
    intros Hs Hin.
    assert (List.Forall (lt a) l) as Hf by (inversion Hs; assumption).
    rewrite List.Forall_forall in Hf.
    specialize (Hf a Hin).
    unfold lt in Hf.
    generalize compare_refl.
    congruence.
  Qed.

  Lemma in_dec_in x l : is_true (if List.in_dec decide_eq x l then true else false) <-> List.In x l.
  Proof.
    case (List.in_dec decide_eq x l).
    - intuition constructor.
    - intro n.
      split.
      + intro H; inversion H.
      + intuition.
  Qed.

  Lemma sorted_inv (X : Type) (R : X -> X -> Prop)
        l (H : Sorted.StronglySorted R l) :
    match l, H with
    | nil, H => H = Sorted.SSorted_nil R
    | cons a l, H => exists Hl Hf, H = Sorted.SSorted_cons _ Hl Hf
    end.
  Proof.
    destruct H.
    - reflexivity.
    - eexists. eexists. reflexivity.
  Qed.

  Lemma Forall_inv (X : Type) (P : X -> Prop) l (H : List.Forall P l) :
    match l, H with
    | nil, H => H = List.Forall_nil _
    | cons a l, H => exists Hp Hl, H = List.Forall_cons _ Hp Hl
    end.
  Proof.
    destruct H.
    - reflexivity.
    - eexists. eexists. reflexivity.
  Qed.

  Lemma Forall_irrel (X : Type) (P : X -> Prop) l  :
    (forall a (Hp1 Hp2 : P a), Hp1 = Hp2) ->
    forall (H1 H2 : List.Forall P l), H1 = H2.
  Proof.
    intros Hp_irrel H1 H2.
    induction l.
    - rewrite (Forall_inv _ _ _ H1).
      rewrite (Forall_inv _ _ _ H2).
      reflexivity.
    - destruct (Forall_inv _ _ _ H1) as (Hp1, (Hl1, He1)).
      rewrite He1.
      destruct (Forall_inv _ _ _ H2) as (Hp2, (Hl2, He2)).
      rewrite He2.
      rewrite (IHl Hl1 Hl2).
      f_equal.
      apply Hp_irrel.
  Qed.

  Lemma sorted_irrel l (H1 H2 : Sorted.StronglySorted lt l) : H1 = H2.
  Proof.
    induction l.
    - rewrite (sorted_inv _ _ _ H1).
      rewrite (sorted_inv _ _ _ H2).
      reflexivity.
    - destruct (sorted_inv _ _ _ H1) as (Hl1, (Hf1, He1)).
      rewrite He1.
      destruct (sorted_inv _ _ _ H2) as (Hl2, (Hf2, He2)).
      rewrite He2.
      rewrite (IHl Hl1 Hl2).
      f_equal.
      apply Forall_irrel.
      unfold lt.
      intro b.
      apply Eqdep_dec.UIP_dec.
      decide equality.
  Qed.

  Lemma extensionality (s1 s2 : set) : (forall x, mem x s1 <-> mem x s2) -> s1 = s2.
  Proof.
    intro H.
    destruct s1 as (l1, Hl1).
    destruct s2 as (l2, Hl2).
    simpl in H.
    assert (l1 = l2) as Hl.
    - generalize l2 Hl2 H; clear l2 Hl2 H; induction l1 as [|a1 l1]; intros [|a2 l2] Hl2 H.
      + reflexivity.
      + specialize (H a2).
        simpl in H.
        rewrite compare_refl in H.
        destruct H as (_, H).
        specialize (H ltac:(constructor)).
        inversion H.
      + specialize (H a1).
        simpl in H.
        rewrite compare_refl in H.
        destruct H as (H, _).
        specialize (H ltac:(constructor)).
        inversion H.
      + assert (a1 = a2) as Ha12.
        * generalize (H a1).
          generalize (H a2).
          simpl.
          do 2 rewrite compare_refl.
          intros (_, Ha2l1) (Ha1l2, _).
          specialize (Ha2l1 ltac:(constructor)).
          specialize (Ha1l2 ltac:(constructor)).
          rewrite <- compare_eq_iff.
          case_eq (compare a1 a2); intro Ha12.
          -- reflexivity.
          -- rewrite Ha12 in Ha1l2.
             inversion Ha1l2.
          -- rewrite <- compare_gt_lt in Ha12.
             rewrite Ha12 in Ha2l1.
             inversion Ha2l1.
        * destruct Ha12.
          f_equal.
          apply IHl1.
          -- inversion Hl1; assumption.
          -- inversion Hl2; assumption.
          -- intro a3.
             rewrite list_in_sorted_correct; [|inversion Hl1; assumption].
             rewrite list_in_sorted_correct; [|inversion Hl2; assumption].
             generalize (H a3).
             simpl.
             intros (He1, He2).
             case_eq (compare a3 a1).
             ++ intro He.
                rewrite compare_eq_iff in He.
                subst a3.
                apply not_in_sorted in Hl1.
                apply not_in_sorted in Hl2.
                intuition.
             ++ clear He1 He2.
                specialize (H a3).
                assert (List.Forall (lt a1) l1) as Ha1l1 by (inversion Hl1; assumption).
                assert (List.Forall (lt a1) l2) as Ha1l2 by (inversion Hl2; assumption).
                intro Hlt.
                split.
                ** intro Ha3l1.
                   rewrite List.Forall_forall in Ha1l1.
                   specialize (Ha1l1 a3 Ha3l1).
                   specialize (lt_trans _ _ _ Ha1l1 Hlt).
                   generalize compare_refl.
                   congruence.
                ** intro Ha3l2.
                   rewrite List.Forall_forall in Ha1l2.
                   specialize (Ha1l2 a3 Ha3l2).
                   specialize (lt_trans _ _ _ Ha1l2 Hlt).
                   generalize compare_refl.
                   congruence.
             ++ intro Hgt.
                rewrite Hgt in He1.
                rewrite Hgt in He2.
                rewrite <- list_in_sorted_correct; [|inversion Hl1; assumption].
                rewrite <- list_in_sorted_correct; [|inversion Hl2; assumption].
                intuition.
    - destruct Hl.
      f_equal.
      apply sorted_irrel.
  Qed.

End definition.
