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

  Definition map_compare (x_ y_ : A * B) :=
    match x_, y_ with (x, _), (y, _) => compare x y end.

  Definition map := set.set (A * B) map_compare.

  Fixpoint list_mem (x : A) (l : list (A * B)) : bool :=
    match l with
    | nil => false
    | cons y l =>
      let (k, v) := y in
      match compare x k with
      | Lt => false
      | Eq => true
      | Gt => list_mem x l
      end
    end.

  Definition mem (x : A) (m : map) : bool :=
    let (l, _) := m in list_mem x l.

  Fixpoint list_remove (x : A) (l : list (A * B)) : list (A * B) :=
    match l with
    | nil => nil
    | cons y l =>
      let (k, v) := y in
      match compare x k with
      | Lt => cons y l
      | Eq => l
      | Gt => cons y (list_remove x l)
      end
    end.

  Lemma remove_in x v y l : List.In (x, v) (list_remove y l) -> List.In (x, v) l.
  Proof.
    induction l as [|(z, v') l]; simpl.
    - auto.
    - case_eq (compare y z).
      + intuition.
      + intros Hlt Hin.
        simpl in Hin.
        assumption.
      + intros Hgt Hin.
        simpl in Hin.
        intuition.
  Qed.

  Fixpoint list_replace (x : A) (v : B) (l : list (A * B)) : list (A * B) :=
    match l with
    | nil => cons (x, v) nil
    | cons y l =>
      let (k, _) := y in
      match compare x k with
      | Lt => cons (x, v) (cons y l)
      | Eq => cons (x, v) l
      | Gt => cons y (list_replace x v l)
      end
    end.

  Lemma list_replace_same x v v' l :
    Sorted.StronglySorted (set.lt _ map_compare) l ->
    List.In (x, v) (list_replace x v' l) <-> v = v'.
  Proof.
    induction l as [|(y, v'') l].
    - simpl.
      intuition congruence.
    - simpl.
      case_eq (compare x y).
      + intros He Hs.
        apply Sorted.StronglySorted_inv in Hs.
        destruct Hs as (Hs, Hf).
        rewrite compare_eq_iff in He.
        simpl.
        split.
        * intros [He2|Hin].
          {
            congruence.
          }
          {
            rewrite List.Forall_forall in Hf.
            specialize (Hf (x, v) Hin).
            unfold set.lt, map_compare in Hf.
            symmetry in He.
            rewrite <- compare_eq_iff in He.
            congruence.
          }
        * intro; left; congruence.
      + intros Hlt Hs.
        apply Sorted.StronglySorted_inv in Hs.
        destruct Hs as (Hs, Hf).
        simpl.
        split.
        * intros [He2|Hin].
          {
            congruence.
          }
          {
            rewrite List.Forall_forall in Hf.
            specialize (Hf (x, v)).
            unfold set.lt, map_compare in Hf.
            simpl in Hin.
            destruct Hin as [He|Hin].
            - injection He.
              intros _ He2.
              symmetry in He2.
              rewrite <- compare_eq_iff in He2.
              congruence.
            - specialize (Hf Hin).
              assert (compare x x = Lt) by (apply (lt_trans x y x); assumption).
              assert (compare x x = Eq) by (apply (compare_eq_iff x x); reflexivity).
              congruence.
          }
        * intro He.
          destruct He.
          left; reflexivity.
      + simpl.
        intros Hgt Hs.
        rewrite IHl.
        * split; [|intuition].
          intros [He|He]; [|auto].
          injection He.
          intros _ He2.
          symmetry in He2.
          rewrite <- compare_eq_iff in He2.
          congruence.
        * inversion Hs.
          assumption.
  Qed.

  Lemma list_replace_diff x v y v' l :
    Sorted.StronglySorted (set.lt _ map_compare) l ->
    x <> y ->
    List.In (x, v) (list_replace y v' l) <-> List.In (x, v) l.
  Proof.
    induction l as [|(z, v'') l]; simpl.
    - intuition congruence.
    - intros Hs Hd.
      case_eq (compare y z).
      + intro He.
        simpl.
        rewrite compare_eq_iff in He.
        destruct He.
        intuition congruence.
      + intro Hlt.
        simpl.
        intuition congruence.
      + intro Hgt.
        simpl.
        rewrite IHl.
        * intuition congruence.
        * inversion Hs.
          assumption.
        * assumption.
  Qed.

  Lemma list_replace_in x v y v' l :
    Sorted.StronglySorted (set.lt _ map_compare) l ->
    List.In (x, v) (list_replace y v' l) <->
      (match compare x y with Eq => v = v' | _ => List.In (x, v) l end).
  Proof.
    case_eq (compare x y).
    - intro He.
      apply compare_eq_iff in He.
      destruct He.
      apply list_replace_same.
    - intros Hlt Hs.
      apply list_replace_diff.
      + assumption.
      + intro He.
        rewrite <- compare_eq_iff in He.
        congruence.
    - intros Hgt Hs.
      apply list_replace_diff.
      + assumption.
      + intro He.
        rewrite <- compare_eq_iff in He.
        congruence.
  Qed.

  Definition list_update (x : A) (vo : option B) (l : list (A * B)) : list (A * B) :=
    match vo with
    | None => list_remove x l
    | Some v => list_replace x v l
    end.

  Program Definition update (x : A) (vo : option B) (m : map) : map :=
    let (l, _) := m in
    exist _ (list_update x vo l) _.
  Next Obligation.
    destruct vo as [v|]; simpl.
    - induction l as [|(k, v') l]; simpl.
      + constructor.
        * assumption.
        * constructor.
      + apply Sorted.StronglySorted_inv in H.
        destruct H as (Hl, Hf).
        specialize (IHl Hl).
        case_eq (compare x k).
        * intro He.
          apply compare_eq_iff in He.
          destruct He.
          constructor.
          {
            assumption.
          }
          {
            rewrite List.Forall_forall.
            intros (z, v'') Hin.
            rewrite List.Forall_forall in Hf.
            specialize (Hf (z, v'') Hin).
            generalize Hf.
            unfold set.lt, map_compare.
            auto.
          }
        * intro Hxk.
          constructor.
          {
            constructor; assumption.
          }
          {
            apply List.Forall_forall.
            intros (z, v'') Hin.
            rewrite List.Forall_forall in Hf.
            specialize (Hf (z, v'')).
            simpl in Hin.
            destruct Hin as [He | Hin].
            - injection He.
              intros _ He2.
              destruct He2.
              exact Hxk.
            - apply (lt_trans _ k).
              + assumption.
              + apply Hf.
                assumption.
          }
        * intro Hgt.
          constructor; try assumption.
          apply List.Forall_forall.
          intros (y,  v'').
          rewrite list_replace_in; try assumption.
          case_eq (compare y x).
          {
            intro He.
            rewrite compare_eq_iff in He.
            destruct He.
            intros _.
            unfold set.lt, map_compare.
            apply set.compare_gt_lt; assumption.
          }
          {
            intro Hlt.
            rewrite List.Forall_forall in Hf.
            exact (Hf (y, v'')).
          }
          {
            intros Hgt2 _.
            unfold set.lt, map_compare.
            apply set.compare_gt_lt; try assumption.
            apply (gt_trans _ x); assumption.
          }
    - induction l as [|(k, v') l]; simpl.
      + assumption.
      + case_eq (compare x k).
        * intros _.
          inversion H.
          assumption.
        * intros _.
          assumption.
        * apply Sorted.StronglySorted_inv in H.
          destruct H as (Hs, Hf).
          intro Hgt.
          constructor.
          {
            auto.
          }
          {
            apply List.Forall_forall.
            intros (y, v'').
            intro Hy.
            apply remove_in in Hy.
            rewrite List.Forall_forall in Hf.
            exact (Hf _ Hy).
          }
  Qed.

  Program Definition empty : map :=
    exist _ nil _.
  Next Obligation.
    constructor.
  Defined.

  Fixpoint list_get (x : A) (l : list (A * B)) : option B :=
    match l with
    | nil => None
    | cons y l =>
      let (k, v) := y in
      match compare x k with
      | Lt => None
      | Eq => Some v
      | Gt => list_get x l
      end
    end.

  Definition get (x : A) (m : map) : option B :=
    let (l, _) := m in list_get x l.

  Lemma StronglySorted_inv_iff (A' : Type) (R : A' -> A' -> Prop) (a : A')
        (l : list A') :
       Sorted.StronglySorted R (a :: l) <->
       Sorted.StronglySorted R l /\ List.Forall (R a) l.
  Proof.
    split.
    - apply Sorted.StronglySorted_inv.
    - generalize Sorted.SSorted_cons.
      intuition.
  Qed.

  Lemma forall_cons (A' : Type) (P : A' -> Prop) (a : A') (l : list A') :
    List.Forall P (cons a l) <-> (P a /\ List.Forall P l).
  Proof.
    split.
    - intro H.
      inversion H.
      split; assumption.
    - intros (HPa, Hf).
      constructor; assumption.
  Qed.

  Lemma list_sorted_map_fst (l : list (A * B)) :
    Sorted.StronglySorted (fun x y => map_compare x y = Lt) l <->
    Sorted.StronglySorted (fun x y => compare x y = Lt) (List.map fst l).
  Proof.
    induction l as [|(x, v) l]; simpl.
    - split; constructor.
    - rewrite StronglySorted_inv_iff.
      rewrite StronglySorted_inv_iff.
      rewrite IHl.
      clear IHl.
      assert (List.Forall (fun y : A * B => map_compare (x, v) y = Lt) l <->
              List.Forall (fun y : A => compare x y = Lt) (List.map fst l)) as H.
      + induction l as [|(y, v') l]; simpl.
        * split; constructor.
        * rewrite forall_cons.
          rewrite forall_cons.
          rewrite IHl.
          intuition.
      + rewrite H.
        intuition.
  Qed.

  Definition size (m : map) : nat :=
    let (l, _) := m in List.length l.

  Lemma list_get_lt a b l :
    List.Forall (fun y => map_compare (a, b) y = Lt) l ->
    Sorted.StronglySorted (fun x y => map_compare x y = Lt) l ->
    list_get a l = None.
  Proof.
    intros Hf Hl.
    destruct l as [|(a2, b2) l].
    - reflexivity.
    - simpl.
      rewrite List.Forall_forall in Hf.
      specialize (Hf (a2, b2) (or_introl eq_refl)).
      simpl in Hf.
      rewrite Hf.
      reflexivity.
  Qed.

  Lemma extensionality (m1 m2 : map) :
    (forall x, get x m1 = get x m2) -> m1 = m2.
  Proof.
    destruct m1 as (l1, H1).
    destruct m2 as (l2, H2).
    simpl.
    intro Hf.
    assert (l1 = l2).
    - generalize l2 H2 Hf; clear l2 H2 Hf; induction l1 as [|(a1, b1) l1]; intros [|(a2, b2) l2] H2 Hf.
      + reflexivity.
      + exfalso.
        specialize (Hf a2).
        simpl in Hf.
        rewrite compare_refl in Hf.
        discriminate.
      + exfalso.
        specialize (Hf a1).
        simpl in Hf.
        rewrite compare_refl in Hf.
        discriminate.
      + assert (a1 = a2 /\ b1 = b2).
        * generalize (Hf a1); intro Ha1.
          simpl in Ha1.
          rewrite compare_refl in Ha1.
          generalize (Hf a2); intro Ha2.
          simpl in Ha2.
          rewrite compare_refl in Ha2.
          case_eq (compare a1 a2).
          -- intro He.
             rewrite compare_eq_iff in He.
             split; [assumption|].
             subst a2.
             rewrite compare_refl in Ha1.
             injection Ha1.
             auto.
          -- intro Hlt.
             rewrite Hlt in Ha1.
             discriminate.
          -- intro Hgt.
             rewrite Hgt in Ha1.
             rewrite <- set.compare_gt_lt in Hgt;
               [|assumption|assumption|assumption].
             rewrite Hgt in Ha2.
             discriminate.
        * destruct H; subst a2; subst b2.
          f_equal.
          apply IHl1.
          -- inversion H1.
             assumption.
          -- inversion H2.
             assumption.
          -- intro a3.
             specialize (Hf a3).
             simpl in Hf.
             case_eq (compare a3 a1).
             ** intro Heq.
                rewrite compare_eq_iff in Heq.
                subst a3.
                rewrite (list_get_lt a1 b1 l1); [|inversion H1; assumption|inversion H1; assumption].
                rewrite (list_get_lt a1 b1 l2); [|inversion H2; assumption|inversion H2; assumption].
                reflexivity.
             ** intro Hlt.
                rewrite (list_get_lt a3 b1 l1);
                  [rewrite (list_get_lt a3 b1 l2)| |].
                --- reflexivity.
                --- apply (@List.Forall_impl _ (fun y => map_compare (a1, b1) y = Lt)); [|inversion H2; assumption].
                    intros (a4, b4).
                    simpl.
                    apply lt_trans.
                    assumption.
                --- inversion H2; assumption.
                --- apply (@List.Forall_impl _ (fun y => map_compare (a1, b1) y = Lt)); [|inversion H1; assumption].
                    intros (a4, b4).
                    simpl.
                    apply lt_trans.
                    assumption.
                --- inversion H1; assumption.
             ** intro Hgt.
                rewrite Hgt in Hf.
                exact Hf.
    - destruct H.
      f_equal.
      apply set.sorted_irrel.
  Qed.

  (* Interesting lemmas to use when working with maps *)

  Lemma map_getmem : forall k m v, 
      get k m = Some v -> mem k m.
  Proof.
    intros.
    destruct m as [l]. simpl. simpl in H.
    induction l.
    - (* nil *)
      simpl in H. inversion H.
    - (* h::t *)
      simpl. simpl in H.
      destruct a as [k' v']. destruct (compare k k').
      + (* Eq *) constructor.
      + (* Lt *) inversion H.
      + (* Gt *) apply IHl. inversion s. assumption. assumption.
  Qed.

  Lemma map_memget : forall k m,
      mem k m -> exists v, get k m = Some v.
  Proof.
    intros.
    destruct m as [l]. simpl. simpl in H.
    induction l.
    - (* nil *)
      exfalso. simpl in H. inversion H.
    - (* h::t *)
      inversion s; subst.
      specialize (IHl H2).
      simpl in H. simpl.
      destruct a as [k' v']. destruct (compare k k').
      + (* Eq *) exists v'. reflexivity.
      + (* Lt *) inversion H.
      + (* Gt *)
        specialize (IHl H). destruct IHl as [v'' IHl].
        exists v''. assumption.
  Qed.

  Lemma map_updateeq: forall k m v,
      get k (update k (Some v) m) = (Some v).
  Proof.
    intros.
    destruct m as [l]. unfold get, update.
    assert ((compare k k) = Eq) as Hkk by (apply compare_eq_iff; reflexivity).
    induction l.
    - (* nil *)
      simpl. rewrite Hkk. reflexivity.
    - (* h::t *)
      simpl. inversion s; subst.
      specialize (IHl H1). simpl in IHl.
      destruct a as [k' v'].
      destruct (compare k k') eqn:Hkk'; simpl.
      + (* Eq *) simpl. rewrite Hkk. reflexivity.
      + (* Lt *) simpl. rewrite Hkk. reflexivity.
      + (* Gt *) rewrite Hkk'. assumption.
  Qed.

  Lemma map_updateneq: forall k k' m v,
      k <> k' ->
      get k' (update k (Some v) m) =
      get k' m.
  Proof.
    intros.
    destruct m as [l]. unfold get, update; simpl.
    induction l; simpl.
    - (* nil *)
      destruct (compare k' k) eqn:Hcp; try reflexivity.
      apply compare_eq_iff in Hcp. symmetry in Hcp. contradiction.
    - (* h::t *)
      inversion s; subst.
      specialize (IHl H2). simpl in IHl.
      destruct a as [k'' v''].
      destruct (compare k k'') eqn:Hkk''; destruct (compare k' k'') eqn:Hk'k''; simpl;
        try apply compare_eq_iff in Hkk''; try apply compare_eq_iff in Hk'k''; subst;
          assert (compare k'' k'' = Eq) as Hk'' by (apply compare_eq_iff; reflexivity);
          try (rewrite Hk'k''; auto).
      + contradiction.
      + rewrite Hk''. apply set.compare_gt_lt in Hkk''; try assumption.
        rewrite Hkk''. reflexivity.
      + destruct (compare k' k) eqn:Hk'k; try reflexivity.
        apply compare_eq_iff in Hk'k. symmetry in Hk'k. contradiction.
      + apply set.compare_gt_lt in Hkk''; try assumption.
        unfold Relations_1.Transitive in gt_trans.
        assert (compare k' k = Gt) as Hk'k by (eapply gt_trans; eassumption).
        rewrite Hk'k. reflexivity.
      + rewrite Hk''. reflexivity.
  Qed.

  Lemma map_updateSome_spec : forall k v m nm,
      nm = update k (Some v) m <->
      (get k nm = (Some v) /\
       (forall k', k <> k' -> map.get k' nm = map.get k' m)).
  Proof.
    intros. split.
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

  Lemma map_updatemem : forall k m v,
      mem k m ->
      forall k', mem k (map.update k' (Some v) m).
  Proof.
    intros.
    destruct m as [l]. unfold get, update. simpl. simpl in H.
    induction l; simpl; simpl in H.
    - (* nil *) inversion H.
    - (* h::t *)
      inversion s; subst. specialize (IHl H2).
      destruct a as [k'' v''].
      destruct (compare k k'') eqn:Hkk''; destruct (compare k' k'') eqn:Hk'k'';
        simpl in H; simpl;
          try rewrite compare_eq_iff in Hkk''; try rewrite compare_eq_iff in Hk'k''; subst;
            assert (compare k'' k'' = Eq) as Hk'' by (apply compare_eq_iff; reflexivity);
            try inversion H;
            try rewrite Hk''; try rewrite Hkk''; try exact ITT.
      + constructor.
      + apply set.compare_gt_lt in Hk'k''; try assumption.
        rewrite Hk'k''.
        constructor.
      + constructor.
      + assumption.
      + apply set.compare_gt_lt in Hk'k''; try assumption.
        rewrite (gt_trans _ _ _ Hkk'' Hk'k'').
        assumption.
      + apply IHl; assumption.
  Qed.

  Ltac comparison_case k1 k2 H Hmem :=
    case_eq (compare k1 k2); intro H; simpl in Hmem; try rewrite H in Hmem;
    [ rewrite compare_eq_iff in H; try assumption | | ].

  Lemma map_updatemem_rev : forall k k' m v,
      k <> k' ->
      mem k (map.update k' (Some v) m) ->
      mem k m.
  Proof.
    intros k k' m v Hkk' Hmem.
    destruct m as [l].
    simpl in *.
    induction l as [|(k'', v'') l]; simpl in *.
    - (* nil *)
      comparison_case k k' H Hmem.
      + congruence.
      + inversion Hmem.
      + inversion Hmem.
    - (* h::t *)
      comparison_case k' k'' Hk'k'' Hmem;
        [ subst k'' | comparison_case k k'' Hkk'' Hmem | comparison_case k k'' Hkk'' Hmem ]; simpl in Hmem; comparison_case k k' Hckk' Hmem;
          try constructor; simpl in *; try (exact Hmem); try (destruct Hmem);
            try congruence;
            inversion s; apply IHl; assumption.
  Qed.

End map.

Fixpoint list_map (B B' : Set) (f : B -> M B') (l : list B) : M (list B') :=
  match l with
  | nil => Return nil
  | cons x l =>
    let! b' := f x in
    let! l' := list_map _ _ f l in
    Return (cons b' l')
  end.

Definition list_map_pair (A B B' : Set) (f : (A * B) -> M B') :
  list (A * B) -> M (list (A * B')) :=
  list_map (A * B) (A * B')
           (fun ab => let! b' := f ab in Return (fst ab, b')).

Lemma list_map_fst A B B' f l l' :
  list_map_pair A B B' f l = Return l' ->
  List.map fst l = List.map fst l'.
Proof.
  generalize l'. clear l'.
  induction l as [|(x, v) l].
  - simpl.
    intros l' H.
    injection H.
    intro He.
    destruct He.
    reflexivity.
  - simpl.
    intro l'.
    unfold list_map_pair.
    simpl.
    case_eq (f (x, v)); simpl; try congruence.
    intros b' He.
    case_eq (list_map (A * B) (A * B') (fun ab : A * B =>
        let! b'0 : B' := f ab in Return (fst ab, b'0)) l); simpl; try congruence.
    intros l'' He2.
    specialize (IHl l'').
    intro H3.
    injection H3.
    intro Hl'.
    destruct Hl'.
    simpl.
    f_equal.
    apply IHl.
    assumption.
Qed.

Program Definition map_fun_aux (A B B' : Set) compare (f : A * B -> M B') (l : list (A * B))
        (H : Sorted.StronglySorted (fun x y => map_compare _ _ compare x y = Lt) l): M (map A B' compare) :=
  match (list_map_pair _ _ _ f l) with
  | Return l' => Return (exist _ l' _)
  | Failed _ e => Failed _ e
  end.
Next Obligation.
  unfold set.lt.
  rewrite list_sorted_map_fst.
  rewrite <- (list_map_fst _ _ _ f l).
  + apply list_sorted_map_fst.
    assumption.
  + symmetry.
    assumption.
Defined.

Definition map_fun (A B B' : Set) comp
  (f : A * B -> M B')
  (m : map A B comp) : M (map A B' comp) :=
  let (l, H) := m in
  map_fun_aux _ _ _ comp f l H.
