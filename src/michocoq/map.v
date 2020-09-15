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


(* Finite maps implemented as finite sets of pairs. *)

Require set.
Require Import error.
Require Eqdep_dec.
Import error.Notations.

Section map.

  Variable A : Set.
  Variable B : Set.
  Variable compare : A -> A -> comparison.

  Hypothesis compare_eq_iff : forall a b, compare a b = Eq <-> a = b.
  Hypothesis lt_trans : Relations_1.Transitive (fun a b => compare a b = Lt).
  Hypothesis gt_trans : Relations_1.Transitive (fun a b => compare a b = Gt).

  Lemma compare_refl a : compare a a = Eq.
  Proof.
    apply (compare_eq_iff a a).
    reflexivity.
  Qed.

  Lemma compare_diff : forall a b, compare a b = Lt \/ compare a b = Gt <-> a <> b.
  Proof.
    intros. split.
    - (* -> *)
      intros [Hdiff|Hdiff] contra;
      rewrite <- compare_eq_iff in contra; rewrite Hdiff in contra; discriminate contra.
    - (* <- *)
      intro Hdiff. destruct (compare a b) eqn:Hab.
      + apply compare_eq_iff in Hab. contradiction.
      + left. reflexivity.
      + right. reflexivity.
  Qed.

  Lemma gt_irrefl a : compare a a <> Gt.
  Proof.
    rewrite compare_refl.
    congruence.
  Qed.

  Lemma lt_irrefl a : compare a a <> Lt.
  Proof.
    rewrite compare_refl.
    congruence.
  Qed.

  Lemma lt_antisym a b : compare a b = Lt -> compare b a <> Lt.
  Proof.
    intros H1 H2.
    apply (lt_irrefl a).
    apply (lt_trans a b a); assumption.
  Qed.

  Lemma gt_rev a b : compare a b = Gt -> compare b a = Lt.
  Proof.
    case_eq (compare b a).
    - intro He.
      apply compare_eq_iff in He.
      subst b.
      rewrite compare_refl.
      congruence.
    - intuition.
    - intros H1 H2.
      exfalso.
      apply (gt_irrefl a).
      apply (gt_trans a b a); assumption.
  Qed.

  Lemma lt_rev a b : compare a b = Lt -> compare b a = Gt.
  Proof.
    case_eq (compare b a).
    - intro He.
      apply compare_eq_iff in He.
      subst b.
      rewrite compare_refl.
      congruence.
    - intros H1 H2.
      exfalso.
      apply (lt_irrefl a).
      apply (lt_trans a b a); assumption.
    - intuition.
  Qed.

  Lemma trans_lt_le k1 k2 k3 : compare k1 k2 = Lt -> compare k3 k2 <> Lt -> compare k1 k3 = Lt.
  Proof.
    case_eq (compare k3 k2).
    - intros H23 H12 _.
      apply compare_eq_iff in H23.
      congruence.
    - congruence.
    - intros H23 H12 _.
      apply gt_rev in H23.
      apply (lt_trans k1 k2 k3); assumption.
  Qed.

  Lemma eq_not_lt a b : compare a b = Eq -> compare a b <> Lt.
  Proof.
    congruence.
  Qed.

  Lemma gt_not_lt a b : compare a b = Gt -> compare a b <> Lt.
  Proof.
    congruence.
  Qed.

  Lemma eq_dec (a b : A) : {a = b} + {a <> b}.
  Proof.
    case_eq (compare a b).
    - intro H.
      left.
      apply compare_eq_iff.
      assumption.
    - intro Hlt. right. intro He.
      apply compare_eq_iff in He.
      congruence.
    - intro Hgt. right. intro He.
      apply compare_eq_iff in He.
      congruence.
  Defined.

  Definition map_compare (x_ y_ : A * B) :=
    match x_, y_ with (x, _), (y, _) => compare x y end.

  (* a [sorted_map_above k] represents a non-empty map whose smallest key is [k] *)
  Inductive sorted_map_above : A -> Set :=
  | sorted_map_sing k : sorted_map_above k
  | sorted_map_cons k1 k2 (v2 : B)
                    (H : compare k1 k2 = Lt) :
      sorted_map_above k2 -> sorted_map_above k1.
  Inductive sorted_map : Set :=
  | sorted_map_nil : sorted_map
  | sorted_map_nonnil k (v : B) : sorted_map_above k -> sorted_map.

  Definition map := sorted_map.

  Fixpoint mem_above (k : A) (x : A) (m : sorted_map_above k) : bool :=
    match compare x k with
    | Lt => false
    | Eq => true
    | Gt =>
      match m with
      | sorted_map_sing _ => false
      | sorted_map_cons _ k _ _ m =>
        mem_above k x m
      end
    end.

  Definition mem (x : A) (m : map) : bool :=
    match m with
    | sorted_map_nil => false
    | sorted_map_nonnil k _ m =>
      mem_above k x m
    end.

  Fixpoint get_above (k : A) (v : B) (x : A) (m : sorted_map_above k) : option B :=
    match compare x k with
    | Lt => None
    | Eq => Some v
    | Gt =>
      match m with
      | sorted_map_sing _ => None
      | sorted_map_cons _ k2 v2 _ m =>
        get_above k2 v2 x m
      end
    end.

  Definition get (x : A) (m : map) : option B :=
    match m with
    | sorted_map_nil => None
    | sorted_map_nonnil k v m =>
      get_above k v x m
    end.

  Lemma get_mem_false x m : mem x m = false <-> get x m = None.
  Proof.
    unfold mem, get.
    destruct m.
    - split; reflexivity.
    - generalize dependent v.
      induction s; intro v; simpl.
      + destruct (compare x k); split; congruence.
      + destruct (compare x k1); try (split; congruence).
        apply IHs.
  Qed.

  Lemma get_mem_absurd : false = true <-> (exists b : B, None = Some b).
  Proof.
    split; intro H; [|destruct H]; discriminate.
  Qed.

  Lemma get_mem_base v : true = true <-> (exists b : B, Some v = Some b).
  Proof.
    split; [| reflexivity].
    intros _.
    eexists; reflexivity.
  Qed.

  Lemma get_mem_true x m : mem x m = true <-> exists b, get x m = Some b.
  Proof.
    unfold mem, get.
    destruct m.
    - apply get_mem_absurd.
    - generalize dependent v.
      induction s; intro v; simpl.
      + destruct (compare x k).
        * apply get_mem_base.
        * apply get_mem_absurd.
        * apply get_mem_absurd.
      + destruct (compare x k1).
        * apply get_mem_base.
        * apply get_mem_absurd.
        * apply IHs.
  Qed.

  (* a return value of None means that the map is empty after removal *)
  Fixpoint remove_above (k : A) (v : B) (x : A) (m : sorted_map_above k) :
    option {k' & {v' : B & {m : sorted_map_above k' | compare k' k <> Lt}}} :=
    match compare x k with
    | Lt => Some (existT _ k (existT _ v (exist _ m (lt_irrefl k))))
    | Eq =>
      match m in (sorted_map_above k)
            return (option {k' : A & {_ : B & {_ : sorted_map_above k' | compare k' k <> Lt}}}) with
      | sorted_map_sing _ => None
      | sorted_map_cons k1 k2 v2 H m =>
        Some (existT _ k2 (existT _ v2 (exist _ m (lt_antisym k1 k2 H))))
      end
    | Gt =>
      match m in (sorted_map_above k)
            return (option {k' : A & {_ : B & {_ : sorted_map_above k' | compare k' k <> Lt}}}) with
      | sorted_map_sing k => Some (existT _ k (existT _ v (exist _ (sorted_map_sing k) (lt_irrefl k))))
      | sorted_map_cons k1 k2 v2 H m =>
        match remove_above k2 v2 x m with
        | Some (existT _ k3 (existT _ v3 (exist _ m' H'))) =>
          let m'' := sorted_map_cons k1 k3 v3 (trans_lt_le _ _ _ H H') m' in
          Some (existT _ k1 (existT _ v (exist _ m'' (lt_irrefl k1))))
        | None =>
          Some (existT _ k1 (existT _ v (exist _ (sorted_map_sing k1) (lt_irrefl k1))))
        end
      end
    end.

  Definition remove (x : A) (m : map) : map :=
    match m with
    | sorted_map_nil => sorted_map_nil
    | sorted_map_nonnil k v m =>
      match remove_above k v x m with
      | None => sorted_map_nil
      | Some (existT _ k' (existT _ v' (exist _ m' _))) =>
        sorted_map_nonnil k' v' m'
      end
    end.

  Lemma remove_above_absent k v x m :
    get_above k v x m = None ->
    exists H, remove_above k v x m = Some (existT _ k (existT _ v (exist _ m H))).
  Proof.
    generalize dependent v.
    induction m; intro v; simpl.
    - destruct (compare x k).
      + discriminate.
      + intros _.
        eexists.
        reflexivity.
      + intros _.
        eexists.
        reflexivity.
    - destruct (compare x k1).
      + discriminate.
      + intros _.
        eexists.
        reflexivity.
      + intro Habsent.
        specialize (IHm v2 Habsent).
        destruct IHm as (Hlt, IHm).
        eexists.
        rewrite IHm.
        repeat f_equal.
        apply Eqdep_dec.UIP_dec.
        decide equality.
  Qed.

  Lemma remove_absent x m : get x m = None -> remove x m = m.
  Proof.
    destruct m.
    - reflexivity.
    - intro Habsent.
      specialize (remove_above_absent k v x s Habsent).
      intros (H, He).
      simpl.
      rewrite He.
      reflexivity.
  Qed.

  Lemma get_above_small x k v m : compare x k = Lt -> get_above k v x m = None.
  Proof.
    destruct m; simpl; intro H'; rewrite H'; reflexivity.
  Qed.

  Lemma get_above_eq x k v m : compare x k = Eq -> get_above k v x m = Some v.
  Proof.
    destruct m; simpl; intro H'; rewrite H'; reflexivity.
  Qed.

  Lemma remove_present_same x m :
    get x (remove x m) = None.
  Proof.
    destruct m; simpl.
    - reflexivity.
    - generalize dependent v.
      induction s; intro v; simpl.
      + case_eq (compare x k); simpl.
        * reflexivity.
        * intro H; rewrite H; reflexivity.
        * intro H; rewrite H; reflexivity.
      + case_eq (compare x k1); simpl.
        * intro He; apply compare_eq_iff in He; subst x.
          apply get_above_small.
          assumption.
        * intro H'; rewrite H'; reflexivity.
        * specialize (IHs v2).
          destruct (remove_above k2 v2 x s) as [(k', (v', (m', H')))|]; simpl.
          -- intro Hgt.
             rewrite Hgt.
             exact IHs.
          -- intro Hgt; rewrite Hgt; reflexivity.
  Qed.

  Lemma unsome {X : Set} {x y : X} : Some x = Some y -> x = y.
  Proof.
    congruence.
  Qed.

  Ltac mytac :=
    match goal with
    | H : Some ?x = Some ?y |- _ => apply unsome in H
    | H : existT _ ?x ?Hx = existT _ ?y ?Hy |- _ =>
      apply error.existT_eq_3 in H; destruct H; subst; simpl
    | H : exist _ ?x ?Hx = exist _ ?y ?Hy |- _ =>
      apply error.exist_eq_3 in H; destruct H; subst; simpl
    | H : eq_rec _ _ _ _ eq_refl = _ |- _ => simpl in H
    end.

  Lemma remove_above_none k v x m :
    remove_above k v x m = None ->
    m = sorted_map_sing k.
  Proof.
    destruct m; simpl.
    - intro; reflexivity.
    - destruct (compare x k1); try discriminate.
      destruct (remove_above k2 v2 x m) as [(k3, (v3, (m3, H3)))|]; discriminate.
  Qed.

  Lemma remove_above_present_other k m : forall v x1 y1 x2 k' v' m' H,
    get_above k v x1 m = Some y1 ->
    remove_above k v x2 m = Some (existT _ k' (existT _ v' (exist _ m' H))) ->
    get_above k' v' x1 m' = None ->
    x1 = x2.
  Proof.
    induction m; intros v x1 y1 x2 k' v' m' H'; simpl.
    - case_eq (compare x1 k); [|discriminate|discriminate].
      intro He; apply compare_eq_iff in He; subst x1.
      intros _.
      case_eq (compare x2 k).
      + discriminate.
      + intros Hx2k He.
        repeat mytac.
        rewrite compare_refl.
        discriminate.
      + intros Hx2k He.
        repeat mytac.
        rewrite compare_refl.
        discriminate.
    - case_eq (compare x1 k1).
      + intro He; apply compare_eq_iff in He; subst x1.
        intros _.
        case_eq (compare x2 k1).
        * intros Hx2k1 _ _.
          symmetry.
          apply compare_eq_iff.
          assumption.
        * intros Hx2k1 He.
          repeat mytac.
          rewrite compare_refl.
          discriminate.
        * intros Hx2k1.
          case_eq (remove_above k2 v2 x2 m).
          -- intros (k'', (v'', (m'', H''))) Hm.
             intro He.
             repeat mytac.
             rewrite compare_refl.
             discriminate.
          -- intros Hn He.
             repeat mytac.
             rewrite compare_refl.
             discriminate.
      + discriminate.
      + case_eq (compare x2 k1).
        * intro He; apply compare_eq_iff in He; subst x2.
          intros.
          repeat mytac.
          congruence.
        * intros.
          repeat mytac.
          simpl in H4.
          rewrite H1 in H4.
          congruence.
        * intros Hx2 Hx1 Hmem.
          case_eq (remove_above k2 v2 x2 m).
          -- intros (k'', (v'', (m'', H''))) He Hm Hn.
             specialize (IHm v2 x1 y1 x2 k'' v'' m'' H'' Hmem He).
             repeat mytac.
             simpl in Hn.
             rewrite Hx1 in Hn.
             apply IHm; assumption.
          -- intros Hn _ _.
             generalize (remove_above_none _ _ _ _ Hn).
             intro; subst m.
             simpl in Hn.
             case_eq (compare x2 k2); intro Hx2k2; rewrite Hx2k2 in Hn;
               try discriminate; clear Hn.
             simpl in Hmem.
             case_eq (compare x1 k2); intro Hx1k2; rewrite Hx1k2 in Hmem;
               try discriminate; clear Hmem.
             apply compare_eq_iff in Hx1k2.
             apply compare_eq_iff in Hx2k2.
             congruence.
  Qed.

  Lemma remove_above_present_untouched k m : forall v x1 y1 x2 k' v' m' H,
      get_above k v x1 m = Some y1 ->
      x1 <> x2 ->
      remove_above k v x2 m = Some (existT _ k' (existT _ v' (exist _ m' H))) ->
      get_above k' v' x1 m' = Some y1.
  Proof.
    induction m; intros v x1 y1 x2 k' v' m' H'; simpl.
    - case_eq (compare x1 k); [|discriminate|discriminate].
      intro He; apply compare_eq_iff in He; subst x1.
      intro Hv.
      case_eq (compare x2 k).
      + discriminate.
      + intros Hx2k Hneq He.
        repeat mytac.
        rewrite compare_refl.
        reflexivity.
      + intros Hx2k Hneq He.
        repeat mytac.
        rewrite compare_refl.
        reflexivity.
    - case_eq (compare x1 k1).
      + intro He; apply compare_eq_iff in He; subst x1.
        intro Hv.
        case_eq (compare x2 k1).
        * intros Hx2k1 Hk1x2 _.
          apply compare_eq_iff in Hx2k1.
          congruence.
        * intros Hx2k1 Hneq He.
          repeat mytac.
          rewrite compare_refl.
          reflexivity.
        * intros Hx2k1 Hneq.
          case_eq (remove_above k2 v2 x2 m).
          -- intros (k'', (v'', (m'', H''))) Hm.
             intro He.
             repeat mytac.
             rewrite compare_refl.
             reflexivity.
          -- intros Hn He.
             repeat mytac.
             rewrite compare_refl.
             reflexivity.
      + discriminate.
      + case_eq (compare x2 k1).
        * intro He; apply compare_eq_iff in He; subst x2.
          intros.
          repeat mytac.
          assumption.
        * intros.
          repeat mytac.
          rewrite H1.
          assumption.
        * intros Hx2 Hx1 Hmem.
          case_eq (remove_above k2 v2 x2 m).
          -- intros (k'', (v'', (m'', H''))) He Hm Hn.
             specialize (IHm v2 x1 y1 x2 k'' v'' m'' H'' Hmem Hm He).
             repeat mytac.
             rewrite Hx1.
             apply IHm; assumption.
          -- intros Hn Hneq _.
             generalize (remove_above_none _ _ _ _ Hn).
             intro; subst m.
             simpl in Hn.
             case_eq (compare x2 k2); intro Hx2k2; rewrite Hx2k2 in Hn;
               try discriminate; clear Hn.
             simpl in Hmem.
             case_eq (compare x1 k2); intro Hx1k2; rewrite Hx1k2 in Hmem;
               try discriminate; clear Hmem.
             apply compare_eq_iff in Hx1k2.
             apply compare_eq_iff in Hx2k2.
             congruence.
  Qed.

  Lemma remove_present_other x1 y1 x2 m :
    get x1 m = Some y1 ->
    get x1 (remove x2 m) = None ->
    x1 = x2.
  Proof.
    destruct m; simpl.
    - discriminate.
    - case_eq (remove_above k v x2 s); simpl.
      + intros (k', (v', (m', H'))) Hsome Hmemt Hmemf.
        eapply remove_above_present_other; eassumption.
      + intro Hnone.
        generalize (remove_above_none _ _ _ _ Hnone).
        intro; subst s.
        simpl.
        case_eq (compare x1 k); try discriminate.
        simpl in Hnone.
        case_eq (compare x2 k); intro Hx2; rewrite Hx2 in Hnone;
          try discriminate; clear Hnone.
        intro Hx1.
        apply compare_eq_iff in Hx1.
        apply compare_eq_iff in Hx2.
        congruence.
  Qed.

  Lemma remove_present_untouched x1 y1 x2 m :
    get x1 m = Some y1 ->
    x1 <> x2 ->
    get x1 (remove x2 m) = Some y1.
  Proof.
    destruct m; simpl.
    - discriminate.
    - case_eq (remove_above k v x2 s); simpl.
      + intros (k', (v', (m', H'))) Hsome Hmemt Hmemf.
        eapply remove_above_present_untouched; eassumption.
      + intro Hnone.
        generalize (remove_above_none _ _ _ _ Hnone).
        intro; subst s.
        simpl.
        case_eq (compare x1 k); try discriminate.
        simpl in Hnone.
        case_eq (compare x2 k); intro Hx2; rewrite Hx2 in Hnone;
          try discriminate; clear Hnone.
        intro Hx1.
        apply compare_eq_iff in Hx1.
        apply compare_eq_iff in Hx2.
        congruence.
  Qed.


  Definition min (k1 k2 : A) :=
    match compare k1 k2 with
    | Lt => k1
    | Eq => k2
    | Gt => k2
    end.

  Lemma min_not_lt_1 k1 k2 : compare k1 (min k1 k2) <> Lt.
  Proof.
    unfold min.
    case_eq (compare k1 k2); intro H12.
    - apply compare_eq_iff in H12.
      subst k2.
      apply lt_irrefl.
    - apply lt_irrefl.
    - congruence.
  Qed.

  Lemma min_not_lt_2 k1 k2 : compare k2 (min k1 k2) <> Lt.
  Proof.
    unfold min.
    case_eq (compare k1 k2); intro H12.
    - apply lt_irrefl.
    - intro H21.
      apply (lt_irrefl k1).
      apply (lt_trans k1 k2 k1); assumption.
    - apply lt_irrefl.
  Qed.

  Lemma min_lt k1 k2 k3 : compare k1 k2 = Lt -> compare k1 k3 = Lt -> compare k1 (min k2 k3) = Lt.
  Proof.
    unfold min.
    destruct (compare k2 k3); intros; assumption.
  Qed.

  Fixpoint insert_above (k : A) (v : B) (x : A) (y : B) (m : sorted_map_above k) :
    B * sorted_map_above (min x k) :=
    match compare x k as c
          return (compare x k = c ->
                  B * sorted_map_above match c with
                                       | Lt => x
                                       | _ => k
                                       end) with
    | Eq => fun _  => (y, m)
    | Lt => fun Hxk => (y, sorted_map_cons x k v Hxk m)
    | Gt =>
      fun Hxk =>
        match m with
        | sorted_map_sing k =>
          fun Hxk =>
            (v, sorted_map_cons k x y (gt_rev x k Hxk) (sorted_map_sing x))
        | sorted_map_cons k1 k2 v2 H m =>
          fun Hxk =>
            let (v', m') := insert_above k2 v2 x y m in
            (v, sorted_map_cons k1 (min x k2) v' (min_lt k1 x k2 (gt_rev x k1 Hxk) H) m')
        end Hxk
    end eq_refl.

  Definition insert (x : A) (y : B) (m : map) : map :=
    match m with
    | sorted_map_nil => sorted_map_nonnil x y (sorted_map_sing x)
    | sorted_map_nonnil k v m =>
      let (v', m') := insert_above k v x y m in
      sorted_map_nonnil (min x k) v' m'
    end.

  Definition insert_above_aux k v x y m c : compare x k = c -> B * sorted_map_above (match c with Lt => x | _ => k end) :=
    match c return (compare x k = c -> B * sorted_map_above match c with Lt => x | _ => k end) with
    | Eq => fun _ => (y, m)
    | Lt => fun H => (y, sorted_map_cons x k v H m)
    | Gt => match m with
            | sorted_map_sing k =>
              fun H => (v, sorted_map_cons k x y (gt_rev x k H) (sorted_map_sing x))
            | sorted_map_cons k1 k2 v2 H' m =>
              fun H =>
                let (v', m') := insert_above k2 v2 x y m in
                (v, sorted_map_cons k1 (min x k2) v' (min_lt k1 x k2 (gt_rev x k1 H) H') m')
            end
    end.

  Lemma insert_above_aux_correct k v x y m :
    insert_above k v x y m = insert_above_aux k v x y m (compare x k) eq_refl.
  Proof.
    destruct m; reflexivity.
  Qed.

  Lemma get_insert_above_aux x y v k m c He v' m' :
    insert_above_aux k v x y m c He = (v', m') ->
    get_above (match c with Lt => x | _ => k end) v' x m' = Some y.
  Proof.
    simpl in m.
    generalize dependent v'.
    induction m; intro v'; destruct c; simpl;
      try (intro H'; injection H'; intros; subst; clear H'; simpl; rewrite He);
      try rewrite compare_refl; try reflexivity.
    case_eq (insert_above k2 v2 x y m); intros v'' m'' H''.
    intro H'; injection H'; intros; subst; clear H'.
    simpl.
    rewrite He.
    rewrite insert_above_aux_correct in H''.
    generalize dependent m''.
    unfold min.
    case_eq (compare x k2); simpl.
    - intros Hxk2 m'' Heq.
      injection Heq; intros; subst; clear Heq.
      apply get_above_eq.
      assumption.
    - intros Hxk2 m'' Heq.
      injection Heq; intros; subst; clear Heq.
      simpl.
      rewrite compare_refl.
      reflexivity.
    - intros Hxk2 m''.
      destruct m; simpl.
      + intro Heq; injection Heq; intros; subst; clear Heq.
        simpl.
        rewrite Hxk2.
        rewrite compare_refl.
        reflexivity.
      + case_eq (insert_above k2 v0 x y m).
        intros v''' m''' Hi Heq.
        injection Heq; intros; subst; clear Heq.
        simpl.
        rewrite Hxk2.
        simpl in IHm.
        rewrite Hi in IHm.
        specialize (IHm Hxk2 _ v' eq_refl).
        simpl in IHm.
        rewrite Hxk2 in IHm.
        exact IHm.
  Qed.

  Lemma get_insert x y m : get x (insert x y m) = Some y.
  Proof.
    destruct m; simpl.
    - rewrite compare_refl.
      reflexivity.
    - case_eq (insert_above k v x y s); simpl.
      intros v' m' H'.
      rewrite insert_above_aux_correct in H'.
      apply get_insert_above_aux in H'.
      exact H'.
  Qed.

  Lemma get_insert_other_above_aux x y x' v k m c He v' m' :
    x <> x' ->
    insert_above_aux k v x y m c He = (v', m') ->
    get_above (match c with Lt => x | _ => k end) v' x' m' =
    get_above k v x' m.
  Proof.
    simpl in m.
    intro Hneq.
    assert (compare x' x = Lt \/ compare x' x = Gt) as Hneq2
        by (apply compare_diff; congruence).
    generalize dependent v'.
    induction m; intro v'; destruct c; simpl;
      try (intro H'; injection H'; intros; subst; clear H'; simpl).
    - case_eq (compare x' k); try reflexivity.
      intro Hx'.
      apply compare_eq_iff in He.
      apply compare_eq_iff in Hx'.
      congruence.
    - destruct Hneq2 as [Hneq2|Hneq2]; rewrite Hneq2; [|reflexivity].
      rewrite (lt_trans _ _ _ Hneq2 He).
      reflexivity.
    - case_eq (compare x' k); try reflexivity.
      destruct Hneq2 as [Hneq2|Hneq2]; rewrite Hneq2; reflexivity.
    - case_eq (compare x' k1); try reflexivity.
      apply compare_eq_iff in He.
      intro Hx'.
      apply compare_eq_iff in Hx'.
      congruence.
    - destruct Hneq2 as [Hneq2|Hneq2]; rewrite Hneq2; [|reflexivity].
      rewrite (lt_trans _ _ _ Hneq2 He).
      reflexivity.
    - case_eq (insert_above k2 v2 x y m).
      intros v'' m'' H''.
      intro Heq; injection Heq; intros; subst; clear Heq.
      simpl.
      case_eq (compare x' k1); try reflexivity.
      intro Hx'.
      rewrite insert_above_aux_correct in H''.
      generalize dependent m''.
      unfold min.
      case_eq (compare x k2); intros Hxk2 m'' Hi.
      + simpl in Hi.
        injection Hi; intros; subst; clear Hi.
        apply compare_eq_iff in Hxk2; subst x.
        destruct Hneq2 as [Hneq2|Hneq2].
        * rewrite get_above_small; [|assumption].
          rewrite get_above_small; [|assumption].
          reflexivity.
        * destruct m''; simpl; rewrite Hneq2; reflexivity.
      + simpl in Hi.
        injection Hi; intros; subst; clear Hi.
        simpl.
        destruct Hneq2 as [Hneq2|Hneq2]; rewrite Hneq2.
        * rewrite get_above_small; [reflexivity|].
          apply (lt_trans _ x _); assumption.
        * reflexivity.
      + simpl in Hi.
        destruct m.
        * injection Hi; intros; subst; clear Hi.
          simpl.
          destruct (compare x' k); try reflexivity.
          destruct Hneq2 as [Hneq2|Hneq2]; rewrite Hneq2; reflexivity.
        * case_eq (insert_above k2 v0 x y m).
          intros v''' m''' H'''.
          simpl.
          rewrite H''' in Hi.
          injection Hi; intros; subst; clear Hi.
          simpl.
          case_eq (compare x' k0); try reflexivity.
          simpl in IHm.
          intro Hx'k0.
          rewrite Hx'k0 in IHm.
          rewrite H''' in IHm.
          specialize (IHm Hxk2 _ _ eq_refl).
          simpl in IHm.
          rewrite Hx'k0 in IHm.
          assumption.
  Qed.

  Lemma get_insert_other x y x' m : x <> x' -> get x' (insert x y m) = get x' m.
  Proof.
    intro Hneq.
    assert (compare x' x = Lt \/ compare x' x = Gt) as Hneq2
        by (apply compare_diff; congruence).
    destruct m; simpl.
    - destruct Hneq2 as [Hneq2|Hneq2]; rewrite Hneq2; reflexivity.
    - case_eq (insert_above k v x y s); simpl.
      intros v' m' H'.
      rewrite insert_above_aux_correct in H'.
      eapply get_insert_other_above_aux in H'; eassumption.
  Qed.

  Definition update (x : A) (vo : option B) (m : map) : map :=
    match vo with
    | None => remove x m
    | Some y => insert x y m
    end.

  Definition empty : map := sorted_map_nil.

  Fixpoint size_above k (m : sorted_map_above k) : nat :=
    match m with
    | sorted_map_sing _ => 1
    | sorted_map_cons _ _ _ _ m =>
      S (size_above _ m)
    end.

  Definition size (m : map) : nat :=
    match m with
    | sorted_map_nil => 0
    | sorted_map_nonnil _ _ m => S (size_above _ m)
    end.

  Lemma extensionality (m1 m2 : map) :
    (forall x, get x m1 = get x m2) -> m1 = m2.
  Proof.
    destruct m1 as [|k1 v1 m1]; destruct m2 as [|k2 v2 m2].
    - reflexivity.
    - intro H; exfalso.
      specialize (H k2).
      simpl in H.
      rewrite get_above_eq in H.
      + discriminate.
      + apply compare_refl.
    - intro H; exfalso.
      specialize (H k1).
      simpl in H.
      rewrite get_above_eq in H.
      + discriminate.
      + apply compare_refl.
    - intro H.
      simpl in H.
      case_eq (compare k1 k2).
      + intro Hk1k2.
        apply compare_eq_iff in Hk1k2.
        subst k2.
        generalize (H k1); intro H2.
        rewrite get_above_eq in H2; [|apply compare_refl].
        rewrite get_above_eq in H2; [|apply compare_refl].
        apply unsome in H2.
        subst v2.
        f_equal.
        generalize dependent m2.
        generalize dependent v1.
        induction m1 as [k1|k1 k1' v1' H1]; simpl; intros v1 m2 H.
        * destruct m2 as [k|k1 k2 v2 H2]; [reflexivity|].
          specialize (H k2).
          simpl in H.
          rewrite (lt_rev _ _ H2) in H.
          rewrite get_above_eq in H; [|apply compare_refl].
          discriminate.
        * destruct m2 as [k|k1 k2 v2 H2].
          -- simpl in H.
             specialize (H k1').
             rewrite (lt_rev _ _ H1) in H.
             rewrite get_above_eq in H; [|apply compare_refl].
             discriminate.
          -- simpl in H.
             generalize (H k1'); intro H3.
             rewrite (lt_rev _ _ H1) in H3.
             rewrite get_above_eq in H3; [|apply compare_refl].
             generalize (H k2); intro H4.
             rewrite (lt_rev _ _ H2) in H4.
             rewrite (get_above_eq k2 k2) in H4; [|apply compare_refl].
             case_eq (compare k1' k2).
             ++ intro Hk1k2.
                apply compare_eq_iff in Hk1k2.
                subst k2.
                rewrite get_above_eq in H4; [|apply compare_refl].
                apply unsome in H4.
                subst v2.
                f_equal.
                ** apply Eqdep_dec.UIP_dec.
                   decide equality.
                ** apply (IHm1 v1').
                   intro x.
                   case_eq (compare x k1); intro Hx.
                   --- apply compare_eq_iff in Hx.
                       subst x.
                       rewrite get_above_small; [|assumption].
                       rewrite get_above_small; [|assumption].
                       reflexivity.
                   --- assert (compare x k1' = Lt) as Hx' by (eapply lt_trans; eassumption).
                       rewrite get_above_small; [|assumption].
                       rewrite get_above_small; [|assumption].
                       reflexivity.
                   --- specialize (H x).
                       rewrite Hx in H.
                       exact H.
             ++ intro H5; rewrite get_above_small in H3; [discriminate|assumption].
             ++ intro H5; apply gt_rev in H5; rewrite get_above_small in H4; [discriminate|assumption].
      + intro Hk1k2.
        specialize (H k1).
        rewrite get_above_eq in H; [|apply compare_refl].
        rewrite get_above_small in H; [|assumption].
        discriminate.
      + intro Hk1k2.
        apply gt_rev in Hk1k2.
        specialize (H k2).
        rewrite get_above_small in H; [|assumption].
        rewrite get_above_eq in H; [|apply compare_refl].
        discriminate.
  Qed.

  (* Interesting lemmas to use when working with maps *)

  Lemma map_getmem k m v :
      get k m = Some v -> mem k m.
  Proof.
    intro H.
    apply Bool.Is_true_eq_left.
    rewrite get_mem_true.
    exists v.
    assumption.
  Qed.

  Lemma map_memget k m :
      mem k m -> exists v, get k m = Some v.
  Proof.
    intro H.
    apply get_mem_true.
    apply Bool.Is_true_eq_true.
    exact H.
  Qed.

  Lemma map_updateeq k m v :
      get k (update k (Some v) m) = (Some v).
  Proof.
    apply get_insert.
  Qed.

  Lemma map_updateneq k k' m v :
      k <> k' ->
      get k' (update k (Some v) m) =
      get k' m.
  Proof.
    apply get_insert_other.
  Qed.

  Lemma map_updateSome_spec k v m nm :
      nm = update k (Some v) m <->
      (get k nm = (Some v) /\
       (forall k', k <> k' -> map.get k' nm = map.get k' m)).
  Proof.
    simpl.
    split.
    - (* -> *)
      intros Hnm. subst. split.
      apply map_updateeq. intros k' Hdiff. apply map_updateneq. assumption.
    - (* <- *)
      intros [HSame HDiff].
      apply map.extensionality; try assumption.
      intro k'.
      specialize (compare_diff k k') as HKeyDiff.
      destruct (compare k k') eqn:Hkk'.
      + (* Eq *)
        apply compare_eq_iff in Hkk'; subst.
        rewrite HSame. symmetry. apply map_updateeq.
      + (* Lt *)
        assert (k <> k') by (apply HKeyDiff; left; reflexivity).
        assert (k <> k') as H2 by assumption.
        apply HDiff in H. rewrite H. symmetry.
        apply map_updateneq. assumption.
      + (* Gt *)
        assert (k <> k') by (apply HKeyDiff; right; reflexivity).
        assert (k <> k') as H2 by assumption.
        apply HDiff in H. rewrite H. symmetry.
        apply map_updateneq. assumption.
  Qed.

  Lemma map_updatemem k m v :
      mem k m ->
      forall k', mem k (map.update k' (Some v) m).
  Proof.
    intros Hmem k'.
    simpl.
    destruct (eq_dec k k').
    - subst k'.
      apply (map_getmem _ _ v).
      apply get_insert.
    - apply map_memget in Hmem.
      destruct Hmem as (v', Hget).
      apply (map_getmem _ _ v').
      rewrite <- Hget.
      apply get_insert_other.
      congruence.
  Qed.

  Lemma map_updatemem_rev k k' m v :
      k <> k' ->
      mem k (map.update k' (Some v) m) ->
      mem k m.
  Proof.
    intros Hkk' Hmem.
    apply map_memget in Hmem.
    destruct Hmem as (v', Hget).
    apply (map_getmem _ _ v').
    rewrite <- Hget.
    symmetry.
    apply get_insert_other.
    congruence.
  Qed.

  Definition destruct (m : map) : option (A * B * map) :=
    match m with
    | sorted_map_nil => None
    | sorted_map_nonnil k v m =>
      Some (k, v,
            match m with
            | sorted_map_sing k => sorted_map_nil
            | sorted_map_cons k1 k2 v2 _ m =>
              sorted_map_nonnil k2 v2 m
            end)
    end.

  (* Conversions from and to lists *)
  Fixpoint to_list_above {k} (m : sorted_map_above k) : list (A * B) :=
    match m with
    | sorted_map_sing x => nil
    | sorted_map_cons k1 k2 v2 H m => cons (k2, v2) (to_list_above m)
    end.

  Definition to_list (m : map) : list (A * B) :=
    match m with
    | sorted_map_nil => nil
    | sorted_map_nonnil k v m => cons (k, v) (to_list_above m)
    end.

  Definition map_lt : (A * B) -> (A * B) -> Prop :=
    fun '(k1, _) '(k2, _) => compare k1 k2 = Lt.

  Lemma to_list_above_is_locally_sorted k v (m : sorted_map_above k) :
    Sorted.LocallySorted map_lt (cons (k, v) (to_list_above m)).
  Proof.
    generalize dependent v.
    induction m.
    - constructor.
    - simpl.
      constructor.
      + apply IHm.
      + assumption.
  Defined.

  Lemma to_list_is_locally_sorted (m : map) :
    Sorted.LocallySorted map_lt (to_list m).
  Proof.
    destruct m.
    - constructor.
    - apply to_list_above_is_locally_sorted.
  Defined.

  Definition locally_sorted_proj1 {X lt x y} {l : list X} :
    Sorted.LocallySorted lt (cons x (cons y l)) ->
    Sorted.LocallySorted lt (cons y l).
  Proof.
    intro H; inversion H; assumption.
  Defined.

  Definition locally_sorted_proj2 {X lt x y} {l : list X} :
    Sorted.LocallySorted lt (cons x (cons y l)) ->
    lt x y.
  Proof.
    intro H; inversion H; assumption.
  Defined.

  Fixpoint of_list_above k v (l : list (A * B)) {struct l} :
    Sorted.LocallySorted map_lt (cons (k, v) l) -> sorted_map_above k :=
    match l with
    | nil => fun _ => sorted_map_sing k
    | cons (k2, v2) l =>
      fun H =>
        sorted_map_cons
          k k2 v2
          (locally_sorted_proj2 H)
          (of_list_above k2 v2 l (locally_sorted_proj1 H))
    end.

  Definition of_list (l : list (A * B)) :
    Sorted.LocallySorted map_lt l -> map :=
    match l with
    | nil => fun _ => sorted_map_nil
    | cons (k, v) l =>
      fun H =>
        sorted_map_nonnil k v (of_list_above k v l H)
    end.

  Lemma of_to_list_above k v (l : list (A * B)) H :
    to_list_above (of_list_above k v l H) = l.
  Proof.
    generalize dependent v.
    generalize dependent k.
    induction l as [|(k2, v2) l].
    - reflexivity.
    - simpl.
      intros k1 v1 H.
      f_equal.
      apply IHl.
  Qed.

  Lemma of_to_list (l : list (A * B)) H :
    to_list (of_list l H) = l.
  Proof.
    destruct l as [|(k, v) l].
    - reflexivity.
    - simpl.
      f_equal.
      apply of_to_list_above.
  Qed.

  Lemma to_of_list_above k v (m : sorted_map_above k) :
    of_list_above k v (to_list_above m) (to_list_above_is_locally_sorted k v m) = m.
  Proof.
    generalize dependent v.
    induction m.
    - reflexivity.
    - intro v1.
      simpl.
      f_equal.
      apply IHm.
  Qed.

  Lemma to_of_list (m : sorted_map) :
    of_list (to_list m) (to_list_is_locally_sorted m) = m.
  Proof.
    destruct m.
    - reflexivity.
    - simpl.
      f_equal.
      apply to_of_list_above.
  Qed.

  Lemma sorted_dec l : {Sorted.LocallySorted map_lt l} + {~ Sorted.LocallySorted map_lt l}.
  Proof.
    induction l as [|(k1, v1) l].
    - left.
      constructor.
    - destruct l as [|(k2, v2) l].
      + left.
        constructor.
      + case_eq (compare k1 k2).
        * intro Hk.
          right.
          intro H.
          apply locally_sorted_proj2 in H.
          simpl in H.
          congruence.
        * intro Hk.
          destruct IHl.
          -- left.
             constructor; assumption.
          -- right.
             intro H.
             apply locally_sorted_proj1 in H.
             contradiction.
        * intro Hk.
          right.
          intro H.
          apply locally_sorted_proj2 in H.
          simpl in H.
          congruence.
  Defined.

  Lemma sorted_inversion l (H : Sorted.LocallySorted map_lt l) :
    match l, H with
    | nil, H => H = Sorted.LSorted_nil _
    | cons (k, v) nil, H => H = Sorted.LSorted_cons1 _ _
    | cons (k1, v1) (cons (k2, v2) l), H =>
      H = Sorted.LSorted_consn _
            (locally_sorted_proj1 H) (locally_sorted_proj2 H)
    end.
  Proof.
    destruct H.
    - reflexivity.
    - destruct a as (k, v).
      reflexivity.
    - destruct a as (k1, v1).
      destruct b as (k2, v2).
      reflexivity.
  Qed.

  Lemma lt_irrel k1 k2 : forall H1 H2 : compare k1 k2 = Lt, H1 = H2.
  Proof.
    apply Eqdep_dec.UIP_dec.
    decide equality.
  Qed.

  Lemma sorted_irrel l (H1 H2 : Sorted.LocallySorted map_lt l) : H1 = H2.
  Proof.
    induction l as [|(k1, v1) l].
    - rewrite (sorted_inversion _ H1).
      rewrite (sorted_inversion _ H2).
      reflexivity.
    - destruct l as [|(k2, v2) l].
      + rewrite (sorted_inversion _ H1).
        rewrite (sorted_inversion _ H2).
        reflexivity.
      + rewrite (sorted_inversion _ H1).
        rewrite (sorted_inversion _ H2).
        f_equal.
        * apply IHl.
        * apply lt_irrel.
  Qed.

  Lemma sorted_tail k v l :
    Sorted.LocallySorted map_lt (cons (k, v) l) ->
    Sorted.LocallySorted map_lt l.
  Proof.
    destruct l as [|(k2, v2) l].
    - intros _.
      constructor.
    - apply locally_sorted_proj1.
  Qed.

End map.

Fixpoint map_fun_above (A B B' : Set) compare (f : B -> M B') k (m : sorted_map_above A B compare k)
  : M (sorted_map_above A B' compare k) :=
  match m with
  | sorted_map_sing _ _ _ k =>
    Return (sorted_map_sing _ _ _ k)
  | sorted_map_cons _ _ _ k1 k2 v2 H m =>
    let! v2' := f v2 in
    let! m' := map_fun_above A B B' compare f k2 m in
    Return (sorted_map_cons _ _ _ k1 k2 v2' H m')
  end.

Definition map_fun (A B B' : Set) compare (f : B -> M B') (m : map A B compare)
  : M (map A B' compare) :=
  match m with
  | sorted_map_nil _ _ _ =>
    Return (sorted_map_nil _ _ _)
  | sorted_map_nonnil _ _ _ k v m =>
    let! v' := f v in
    let! m' := map_fun_above A B B' compare f k m in
    Return (sorted_map_nonnil _ _ _ k v' m')
  end.

Fixpoint map_fun_above_pure (A B B' : Set) compare (f : B -> B') k (m : sorted_map_above A B compare k)
  : sorted_map_above A B' compare k :=
  match m with
  | sorted_map_sing _ _ _ k =>
    sorted_map_sing _ _ _ k
  | sorted_map_cons _ _ _ k1 k2 v2 H m =>
    let v2' := f v2 in
    let m' := map_fun_above_pure A B B' compare f k2 m in
    sorted_map_cons _ _ _ k1 k2 v2' H m'
  end.

Definition map_fun_pure (A B B' : Set) compare (f : B -> B') (m : map A B compare)
  : map A B' compare :=
  match m with
  | sorted_map_nil _ _ _ =>
    sorted_map_nil _ _ _
  | sorted_map_nonnil _ _ _ k v m =>
    let v' := f v in
    let m' := map_fun_above_pure A B B' compare f k m in
    sorted_map_nonnil _ _ _ k v' m'
  end.
