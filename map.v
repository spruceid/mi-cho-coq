(* Finite maps implemented as finite sets of pairs. *)

Require set.
Require Import error.

Section map.

  Variable A : Set.
  Variable B : Set.
  Variable compare : A -> A -> comparison.

  Hypothesis compare_eq_iff : forall a b, compare a b = Eq <-> a = b.
  Hypothesis lt_trans : Relations_1.Transitive (fun a b => compare a b = Lt).
  Hypothesis gt_trans : Relations_1.Transitive (fun a b => compare a b = Gt).
  
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
        rewrite set.in_cons_iff in Hin.
        assumption.
      + intros Hgt Hin.
        rewrite set.in_cons_iff in Hin.
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
        rewrite set.in_cons_iff.
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
        rewrite set.in_cons_iff.
        split.
        * intros [He2|Hin].
          {
            congruence.
          }
          {
            rewrite List.Forall_forall in Hf.
            specialize (Hf (x, v)).
            unfold set.lt, map_compare in Hf.
            rewrite set.in_cons_iff in Hin.
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
      + rewrite set.in_cons_iff.
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
        rewrite set.in_cons_iff.
        rewrite compare_eq_iff in He.
        destruct He.
        intuition congruence.
      + intro Hlt.
        rewrite set.in_cons_iff.
        rewrite set.in_cons_iff.
        intuition congruence.
      + intro Hgt.
        rewrite set.in_cons_iff.
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
            rewrite set.in_cons_iff in Hin.
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

End map.

Fixpoint list_map (B B' : Set) (f : B -> M B') (l : list B) : M (list B') :=
  match l with
  | nil => Return _ nil
  | cons x l =>
    error.bind (fun b' =>
    error.bind (fun l' =>
    Return _ (cons b' l')) (list_map _ _ f l)) (f x)
  end.

Definition list_map_pair (A B B' : Set) (f : (A * B) -> M B') :
  list (A * B) -> M (list (A * B')) :=
  list_map (A * B) (A * B')
           (fun ab => error.bind (fun b' => Return _ (fst ab, b')) (f ab)).

Lemma list_map_fst A B B' f l l' :
  list_map_pair A B B' f l = Return _ l' ->
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
        error.bind (fun b'0 : B' => Return (A * B') (fst ab, b'0)) (f ab)) l); simpl; try congruence.
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
  | Return _ l' => Return _ (exist _ l' _)
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
  