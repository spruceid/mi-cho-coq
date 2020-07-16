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

(* Same as the untyped optimizer but at the level of Michocoq.syntax *)

From Michocoq Require untyped_syntax typer untyper.
From Michocoq Require Import syntax.
Import error.Notations.
Import Notations.
Require optimizer.
Require Import ZArith.
Require JMeq.
Require Import String.

Definition hide_tf {st A B} (i : instruction st true A B) :
           sigT (fun tff => instruction st tff A B) :=
  existT _ true i.

Definition hide_ntf {st A B} (i : instruction st false A B) :
           sigT (fun tff => instruction st tff A B) :=
  existT _ false i.

Definition hide_ntf_seq {st A B} (i : instruction_seq st false A B) :
           sigT (fun tff => instruction_seq st tff A B) :=
  existT _ false i.


(* Manipulations of options *)

Definition option_bind {A B}
           (o : Datatypes.option A) (f : A -> Datatypes.option B) :
  Datatypes.option B :=
  match o with
  | None => None
  | Some a => f a
  end.

Notation "'let?' x ':=' X 'in' Y" :=
  (option_bind X (fun x => Y))
    (at level 200, x pattern, X at level 100, Y at level 200).

Definition opt_get {A} (o : Datatypes.option A) (default : A) : A :=
  match o with Some x => x | None => default end.

Lemma unsome {A} (x y : A) : Some x = Some y -> x = y.
Proof.
  congruence.
Qed.

Lemma bind_some {A B} (y : Datatypes.option A) (w : B) z : (let? x := y in z x) = Some w <-> (exists x, y = Some x /\ z x = Some w).
Proof.
  destruct y; simpl; split.
  - intro H; exists a; split; congruence.
  - intros (x, (Hx, Hz)); congruence.
  - discriminate.
  - intros (x, (Hx, Hz)); discriminate.
Qed.

Fixpoint visit_instruction
         (F : forall st tff A B,
             instruction_seq st tff A B -> instruction_seq st tff A B)
         {st tff A B}
         (i : instruction st tff A B) {struct i} : instruction st tff A B :=
  match i with
  | Instruction_seq i => Instruction_seq (visit_instruction_seq F i)
  | DIP n H i => DIP n H (visit_instruction_seq F i)
  | IF_ f i1 i2 =>
    IF_ f (visit_instruction_seq F i1) (visit_instruction_seq F i2)
  | LOOP_ f i =>
    LOOP_ f (visit_instruction_seq F i)
  | ITER i => ITER (visit_instruction_seq F i)
  | MAP i => MAP (visit_instruction_seq F i)

  (* Note that LAMBDA a b i => LAMBDA a b (visit_instruction_seq F i)
     would be incorrect because we can use PACK to distinguish
     semantically equivalent lambdas in Michelson *)
  | LAMBDA a b i => LAMBDA a b i
  | CREATE_CONTRACT a b an i => CREATE_CONTRACT a b an i
  | PUSH ty x => PUSH ty x
  | FAILWITH => FAILWITH
  | SELF an H => SELF an H
  | EXEC => EXEC
  | Instruction_opcode op => Instruction_opcode op
  end
with
visit_instruction_seq f {st tff A B} (i : instruction_seq st tff A B) {struct i}
: instruction_seq st tff A B :=
  match i with
  | NOOP => f _ _ _ _ NOOP
  | Tail_fail i =>
    let i' := visit_instruction f i in
    f _ _ _ _ (Tail_fail i')
  | SEQ i1 i2 =>
    let i1' := visit_instruction f i1 in
    let i2' := visit_instruction_seq f i2 in
    f _ _ _ _ (SEQ i1' i2')
  end.

Definition untype_fun_seq
           (F1 : forall st tff A B, instruction_seq st tff A B ->
                                    instruction_seq st tff A B)
           (F2 : untyped_syntax.instruction_seq -> untyped_syntax.instruction_seq) :=
  forall st tff A B i,
    untyper.untype_instruction_seq untyper.untype_Optimized (F1 st tff A B i) = F2 (untyper.untype_instruction_seq untyper.untype_Optimized i).

Fixpoint untype_visit_instruction F1 F2
         (H : untype_fun_seq F1 F2)
         (HNOOP : F2 untyped_syntax.NOOP = untyped_syntax.NOOP)
         st tff A B
         (i : instruction st tff A B) :
  untyper.untype_instruction untyper.untype_Optimized (visit_instruction F1 i) =
  optimizer.visit_instruction F2 (untyper.untype_instruction untyper.untype_Optimized i)
with
untype_visit_instruction_seq F1 F2
                             (H : untype_fun_seq F1 F2)
                             (HNOOP : F2 untyped_syntax.NOOP = untyped_syntax.NOOP)
                             st tff A B
                             (i : instruction_seq st tff A B) :
  untyper.untype_instruction_seq untyper.untype_Optimized (visit_instruction_seq F1 i) =
  optimizer.visit_instruction_seq F2 (untyper.untype_instruction_seq  untyper.untype_Optimized i).
Proof.
  - destruct i; simpl; try reflexivity; try (repeat f_equal; apply untype_visit_instruction_seq; assumption).
  - destruct i.
    + apply H.
    + simpl.
      rewrite H.
      simpl.
      repeat f_equal.
      * apply (untype_visit_instruction F1 F2); assumption.
      * symmetry; assumption.
    + simpl.
      rewrite H.
      simpl.
      repeat f_equal.
      * apply (untype_visit_instruction F1 F2); assumption.
      * apply (untype_visit_instruction_seq F1 F2); assumption.
Qed.

Lemma stype_refl (A : Datatypes.list type) (H : A = A) : H = eq_refl.
Proof.
  apply Eqdep_dec.UIP_dec.
  apply stype_dec.
Qed.

Lemma st_dec (st1 st2 : self_info) : sumbool (st1 = st2) (st1 <> st2).
Proof.
  repeat decide equality.
Qed.

Lemma st_refl (st : self_info) (H : st = st) : H = eq_refl.
Proof.
  apply Eqdep_dec.UIP_dec.
  apply st_dec.
Qed.

Definition cast_instruction_seq_opt {st tff A B st' tff' A' B'}
           (i : instruction_seq st tff A B)
  : Datatypes.option (instruction_seq st' tff' A' B').
Proof.
  case (st_dec st st'); [| intros; exact None].
  case (error.bool_dec tff tff'); [| intros; exact None].
  case (stype_dec A A'); [| intros; exact None].
  case (stype_dec B B'); [| intros; exact None].
  intros; subst; exact (Some i).
Defined.

Lemma cast_instruction_seq_same {st tff A B} (i : instruction_seq st tff A B) :
  cast_instruction_seq_opt i = Some i.
Proof.
  unfold cast_instruction_seq_opt.
  destruct (st_dec st st) as [Hst | n]; [|destruct (n eq_refl)].
  destruct (error.bool_dec tff tff) as [Htff | n]; [|destruct (n eq_refl)].
  destruct (stype_dec A A) as [HA | n]; [|destruct (n eq_refl)].
  destruct (stype_dec B B) as [HB | n]; [|destruct (n eq_refl)].
  assert (HA = eq_refl) by apply stype_refl; subst.
  assert (HB = eq_refl) by apply stype_refl; subst.
  assert (Htff = eq_refl) by (apply Eqdep_dec.UIP_dec; apply error.bool_dec); subst.
  assert (Hst = eq_refl) by apply st_refl; subst.
  reflexivity.
Qed.

Definition dig0dug0_opt {st tff A C} (i : instruction_seq st tff A C) :
  Datatypes.option (instruction_seq st tff A C)
  :=
  match i with
  | Tail_fail i =>
    let 'existT _ _ i := hide_tf i in
    match i with
    | Instruction_seq i => cast_instruction_seq_opt i
    | _ => None
    end
  | @SEQ st' A' B _ _ i1 i2 =>
    let 'existT _ _ i1 := hide_ntf i1 in
    let? i1' :=
       match i1 return Datatypes.option (instruction_seq st' false A' B) with
       | DIP 0 _ i => cast_instruction_seq_opt i
       | @DIP _ _ A _ _ _ i =>
         let 'existT _ _ i := hide_ntf_seq i in
         match i with @NOOP _ B => cast_instruction_seq_opt (@NOOP st' (A +++ B))
                 | _ => None
         end
       | Instruction_seq i => cast_instruction_seq_opt i
       | Instruction_opcode op =>
         match op with
         | @DIG _ 0 nil S2 a _ =>
           cast_instruction_seq_opt (@NOOP st' (a ::: S2))
         | @DUG _ 0 nil S2 a _ =>
           cast_instruction_seq_opt (@NOOP st' (a ::: S2))
         | @DIG _ 1 (cons a nil) S2 b _ =>
           cast_instruction_seq_opt (SEQ (@SWAP st' a b S2) NOOP)
         | @DUG _ 1 (cons a nil) S2 b _ =>
           cast_instruction_seq_opt (SEQ (@SWAP st' b a S2) NOOP)
         | @DROP _ 0 nil B' _ =>
           cast_instruction_seq_opt (@NOOP st' B')
         | _ => None
         end
       | _ => None
       end in
    cast_instruction_seq_opt (instruction_app i1' i2)
  | _ => None
  end.


Inductive dig0dug0_opt_rel {st} :
  forall {tff A B} (i i' : instruction_seq st tff A B), Prop :=
| D0D0_tf A B (i : instruction_seq st true A B) :
    dig0dug0_opt_rel (Tail_fail (Instruction_seq i)) i
| D0D0_seq_is {tff A B C}
              (i1 : instruction_seq st false A B)
              (i2 : instruction_seq st tff B C) :
    dig0dug0_opt_rel (SEQ (Instruction_seq i1) i2) (instruction_app i1 i2)
| D0D0_DIP0 {tff A B C}
            (i1 : instruction_seq st false A B)
            (i2 : instruction_seq st tff B C) :
    dig0dug0_opt_rel (SEQ (DIP (A := nil) 0 eq_refl i1) i2) (instruction_app i1 i2)
| D0D0_DIP_NOOP {tff A B C n Hn}
            (i : instruction_seq st tff (A ++ B) C) :
    dig0dug0_opt_rel (SEQ (DIP (A := A) n Hn NOOP) i) i
| D0D0_DROP0 {tff A B}
             (i : instruction_seq st tff A B) :
    dig0dug0_opt_rel (SEQ (DROP (A := nil) 0 eq_refl) i) i
| D0D0_DIG0 {tff t A B}
            (i : instruction_seq st tff (t ::: A) B) :
    dig0dug0_opt_rel (SEQ (DIG 0 (S1 := nil) eq_refl) i) i
| D0D0_DUG0 {tff t A B}
            (i : instruction_seq st tff (t ::: A) B) :
    dig0dug0_opt_rel (SEQ (DUG 0 (S1 := nil) eq_refl) i) i
| D0D0_DIG1 {tff a b A B}
            (i : instruction_seq st tff (b ::: a ::: A) B) :
    dig0dug0_opt_rel (SEQ (DIG 1 (S1 := _ ::: nil) eq_refl) i) (SEQ SWAP i)
| D0D0_DUG1 {tff a b A B}
            (i : instruction_seq st tff (b ::: a ::: A) B) :
    dig0dug0_opt_rel (SEQ (DUG 1 (S1 := _ ::: nil) eq_refl) i) (SEQ SWAP i).

Lemma uncons {A} (a1 a2 : A) l1 l2 :
  cons a1 l1 = cons a2 l2 -> a1 = a2 /\ l1 = l2.
Proof.
  intro H; injection H; auto.
Qed.

Ltac destructable_list l :=
  is_var l +
  match l with
  | nil => idtac
  | cons _ _ => idtac
  end.

Ltac mytac :=
  match goal with
  | H : ?A |- _ =>
    match A with
    | existT _ _ _ = existT _ _ _ =>
      apply error.existT_eq_3 in H
    | exist _ _ _ = exist _ _ _ =>
      apply error.exist_eq_3 in H
    | hide_tf _ = existT _ _ _ =>
      apply error.existT_eq_3 in H
    | hide_ntf _ = existT _ _ _ =>
      apply error.existT_eq_3 in H
    | hide_ntf_seq _ = existT _ _ _ =>
      apply error.existT_eq_3 in H
    | sig _ =>
      destruct H
    | sigT _ =>
      destruct H
    | exists _, _ =>
      destruct H
    | _ /\ _ =>
      destruct H
    | Datatypes.unit =>
      destruct H
    | eq_rec _ _ _ _ eq_refl = _ =>
      simpl in H
    | ?x = ?y =>
      is_var x; subst x
    | ?x = ?y =>
      is_var y; subst y
    | ?x = ?y =>
      assert (H = eq_refl)
        by (match type of x with
            | Datatypes.bool => apply Eqdep_dec.UIP_refl_bool
            | Datatypes.list type => apply Eqdep_dec.UIP_dec;
                                     apply stype_dec
            | type => apply Eqdep_dec.UIP_dec;
                      apply type_dec
            | Datatypes.nat => apply Eqdep_dec.UIP_dec;
                               decide equality
            end);
      subst H
    | cons ?a1 ?l1 = cons ?a2 ?l2 =>
      (destructable_list l1 + destructable_list l2);
      assert (a1 = a2 /\ l1 = l2) by (apply uncons; exact H)
    | Some _ = Some _ =>
      apply unsome in H
    | Some _ = None => discriminate
    | cast_instruction_seq_opt _ = _ =>
      rewrite cast_instruction_seq_same in H
    | option_bind (Some _) _ = _ =>
      simpl in H
    | option_bind None _ = _ =>
      simpl in H
    | option_bind _ _ = Some _ =>
      apply bind_some in H
    | option_bind (cast_instruction_seq_opt _) _ = _ =>
      rewrite cast_instruction_seq_same in H
    end
  end.

Lemma dig0dug0_opt_dig0dug0 {st tff A C} (i i' : instruction_seq st tff A C) :
  dig0dug0_opt i = Some i' <-> dig0dug0_opt_rel i i'.
Proof.
  split.
  - destruct i; try discriminate; unfold dig0dug0_opt.
    + case_eq (hide_tf i).
      intros tff i0 He Hi0.
      destruct i0; try discriminate.
      repeat mytac.
      constructor.
    + case_eq (hide_ntf i).
      intros tff1 i1 He Hi1.
      destruct i1; try discriminate.
      * repeat mytac.
        constructor.
      * destruct n; try discriminate.
        -- destruct A; try discriminate.
           repeat mytac.
           constructor.
        -- destruct (hide_ntf_seq i1) eqn:Hi1eq.
           destruct i2; try discriminate.
           repeat mytac.
           constructor.
      * destruct o; try discriminate; destruct n as [|[|n]]; try discriminate.
        -- destruct S1; try discriminate.
           repeat mytac.
           constructor.
        -- destruct S1 as [|b [|]]; try discriminate.
           repeat mytac.
           constructor.
        -- destruct S1; try discriminate.
           repeat mytac.
           constructor.
        -- destruct S1 as [|b [|]]; try discriminate.
           repeat mytac.
           constructor.
        -- destruct A; try discriminate.
           repeat mytac.
           constructor.
  - intro Hi; destruct Hi; unfold dig0dug0_opt, hide_tf, hide_ntf, hide_ntf_seq;
      repeat (rewrite cast_instruction_seq_same; simpl); try reflexivity.
    destruct n.
    + destruct A; try discriminate.
      rewrite cast_instruction_seq_same.
      simpl.
      rewrite cast_instruction_seq_same.
      reflexivity.
    + simpl.
      rewrite cast_instruction_seq_same.
      reflexivity.
Qed.

Definition dig0dug0_aux {st tff A B} (i : instruction_seq st tff A B) : instruction_seq st tff A B :=
  opt_get (dig0dug0_opt i) i.

Definition dig0dug0 {st tff A B} (i : instruction_seq st tff A B) : instruction_seq st tff A B :=
  visit_instruction_seq (@dig0dug0_aux) i.

Lemma untyped_instruction_app_NOOP :
  forall i, untyped_syntax.instruction_app i untyped_syntax.NOOP = i.
Proof.
  induction i.
  - reflexivity.
  - simpl; f_equal; assumption.
Qed.

Lemma untype_instruction_seq_app_aux {st tff1 tff2 A B C}
         (i1 : instruction_seq st tff1 A B)
         (i2 : instruction_seq st tff2 B C) H :
  untyper.untype_instruction_seq untyper.untype_Optimized (instruction_app_aux i1 H  i2) =
  untyped_syntax.instruction_app
    (untyper.untype_instruction_seq untyper.untype_Optimized i1)
    (untyper.untype_instruction_seq untyper.untype_Optimized i2).
Proof.
  induction i1; simpl.
  - reflexivity.
  - discriminate.
  - f_equal.
    apply IHi1.
Qed.

Lemma untype_instruction_seq_app {st tff A B C}
         (i1 : instruction_seq st false A B)
         (i2 : instruction_seq st tff B C) :
  untyper.untype_instruction_seq untyper.untype_Optimized (i1;;; i2) =
  untyped_syntax.instruction_app
    (untyper.untype_instruction_seq untyper.untype_Optimized i1)
    (untyper.untype_instruction_seq untyper.untype_Optimized i2).
Proof.
  apply untype_instruction_seq_app_aux.
Qed.

Lemma untype_dig0dug0 : untype_fun_seq (@dig0dug0) (optimizer.dig0dug0).
Proof.
  unfold untype_fun_seq, dig0dug0, optimizer.dig0dug0.
  apply untype_visit_instruction_seq; [| reflexivity].
  intros st tff A B i; simpl.
  unfold dig0dug0_aux.
  case_eq (dig0dug0_opt i).
  - intros i' Hi.
    apply dig0dug0_opt_dig0dug0 in Hi.
    destruct Hi; simpl; try reflexivity;
      try (symmetry; apply untyped_instruction_app_NOOP);
      try apply untype_instruction_seq_app.
    destruct n; reflexivity.
  - intro HN.
    simpl.
    destruct i; try reflexivity.
    + unfold dig0dug0_opt in HN.
      case_eq (hide_tf i).
      intros tff i' He.
      rewrite He in HN.
      destruct i'; try discriminate; repeat mytac; try reflexivity.
      destruct tffa; try discriminate.
      repeat mytac; simpl in *; repeat mytac; reflexivity.
    + unfold dig0dug0_opt in HN.
      case_eq (hide_ntf i).
      intros tff1 i' He.
      rewrite He in HN.
      apply error.existT_eq_3 in He.
      destruct He as (Htff', Hi).
      destruct i'; try discriminate;
        try (assert (Htff' = eq_refl) by apply Eqdep_dec.UIP_refl_bool;
             subst Htff'; simpl in Hi; subst; reflexivity).
      * repeat mytac.
      * repeat mytac.
        destruct tffa; simpl in *; repeat mytac; reflexivity.
      * destruct n; destruct A as [|a A]; try discriminate; repeat mytac.
        destruct (hide_ntf_seq i1) eqn:Heqi1.
        destruct i; simpl in *; repeat mytac.
        -- discriminate.
        -- reflexivity.
      * repeat mytac.
        destruct o; try reflexivity.
        -- destruct n as [|[|n]]; destruct S1 as [|a [|b S1]];
             try discriminate; repeat mytac; reflexivity.
        -- destruct n as [|[|n]]; destruct S1 as [|a [|b S1]];
             try discriminate; repeat mytac; reflexivity.
        -- destruct n as [|n]; destruct A as [|a A];
             try discriminate; repeat mytac; reflexivity.
Qed.

(* Destructors for types instruction_seq, instruction, and opcode *)

Definition unseq {st tff A C} (i : instruction_seq st tff A C):
  Datatypes.option (sigT (fun B1 =>
                            (sigT (fun B2 =>
                                     instruction st false A B1 *
                                     instruction_seq st tff B2 C))))%type :=
  match i with
  | NOOP => None
  | Tail_fail _ => None
  | SEQ i1 i2 =>
    Some (existT _ _ (existT _ _ (i1, i2)))
  end.

Definition unseq_fst {st tff A C} (i : instruction_seq st tff A C):
  Datatypes.option (sigT (fun A =>
                            (sigT (fun B =>
                                     instruction st false A B))))%type :=
  match i with
  | SEQ i1 i2 =>
    Some (existT _ _ (existT _ _ i1))
  | _ => None
  end.

Definition unseq_snd {st tff A C} (i : instruction_seq st tff A C):
  Datatypes.option (sigT (fun B =>
                            (sigT (fun C =>
                                     instruction_seq st tff B C))))%type :=
  match i with
  | SEQ i1 i2 =>
    Some (existT _ _ (existT _ _ i2))
  | _ => None
  end.

Lemma unseq_seq {st tff A B C} (i : instruction_seq st tff A C) i1 i2 :
  unseq i = Some (existT _ B (existT _ B (i1, i2))) <-> i = SEQ i1 i2.
Proof.
  split.
  - destruct i; simpl; intro; try discriminate.
    apply unsome in H.
    apply error.existT_eq_3 in H.
    destruct H as (He, H).
    subst B0.
    simpl in H.
    apply error.existT_eq_3 in H.
    destruct H as (He, H).
    assert (He = eq_refl) by (apply Eqdep_dec.UIP_dec; apply stype_dec).
    subst He.
    simpl in H.
    congruence.
  - intro; subst i.
    simpl.
    reflexivity.
Qed.

Definition unopcode {st tff A B} (i : instruction st tff A B) :
  Datatypes.option (@opcode st A B) :=
  match i with
  | Instruction_opcode op => Some op
  | _ => None
  end.

Lemma unopcode_opcode {st tff A B} (i : instruction st tff A B) o (H : false = tff) :
  unopcode i = Some o <->
  i = eq_rec false (fun tff => instruction st tff A B) o tff H.
Proof.
  split.
  - destruct i; simpl; intro; try discriminate.
    apply unsome in H0.
    subst o0.
    assert (H = eq_refl) by apply Eqdep_dec.UIP_refl_bool.
    subst H.
    reflexivity.
  - subst tff.
    simpl.
    intro; subst i.
    reflexivity.
Qed.

Definition unswap_opcode {st A B} (op : @opcode st A B) : Datatypes.option Datatypes.unit :=
  match op with
  | SWAP => Some tt
  | _ => None
  end.

Definition unswap {st tff A B} (i : instruction st tff A B) : Datatypes.option Datatypes.unit :=
  let? op := unopcode i in unswap_opcode op.

(* SWAP-SWAP *)

Definition swapswap_opt {st tff A D} (i : instruction_seq st tff A D) :
  Datatypes.option (instruction_seq st tff A D) :=
  let? existT _ _ (existT _ _ i1) := unseq_fst i in
  let? existT _ _ (existT _ _ i23) := unseq_snd i in
  let '(existT _ _ i1) := hide_ntf i1 in
  let? existT _ _ (existT _ _ i2) := unseq_fst i23 in
  let '(existT _ _ i2) := hide_ntf i2 in
  let? existT _ _ (existT _ _ i3) := unseq_snd i23 in
  let? tt := unswap i1 in
  let? tt := unswap i2 in
  cast_instruction_seq_opt i3.

Inductive swapswap_rel {st tff} :
  forall {A B} (i i' : instruction_seq st tff A B), Prop :=
| Swapswap_intro {a b A B} (i : instruction_seq st tff (a ::: b ::: A) B) :
    swapswap_rel (SEQ SWAP (SEQ SWAP i)) i.

Lemma swapswap_opt_swapswap {st tff A D} (i i' : instruction_seq st tff A D) :
  swapswap_opt i = Some i' <-> swapswap_rel i i'.
Proof.
  split.
  - unfold swapswap_opt.
    intro H.
    apply bind_some in H; destruct H as ((A1, (B1, i1)), (He1, H)).
    apply bind_some in H; destruct H as ((A23, (B23, i23)), (He23, H)).
    case_eq (hide_ntf i1); intros tff1 i1' Hi1'; rewrite Hi1' in H.
    apply bind_some in H; destruct H as ((A2, (B2, i2)), (He2, H)).
    case_eq (hide_ntf i2); intros tff2 i2' Hi2'; rewrite Hi2' in H.
    apply bind_some in H; destruct H as ((A3, (B3, i3)), (He3, H)).

    destruct i1'; try discriminate.
    destruct o; try discriminate.
    simpl in H.

    destruct i2'; try discriminate.
    destruct o; try discriminate.
    simpl in H.

    destruct i; try discriminate.
    destruct i23; try discriminate.
    simpl in *.
    repeat mytac.
    constructor.
  - intro H.
    destruct H.
    simpl.
    unfold swapswap_opt; simpl.
    apply cast_instruction_seq_same.
Qed.

Definition swapswap_aux {st tff A D} (i : instruction_seq st tff A D) :
  instruction_seq st tff A D :=
  opt_get (swapswap_opt i) i.

Definition swapswap {st tff A B} (i : instruction_seq st tff A B) : instruction_seq st tff A B :=
  visit_instruction_seq (@swapswap_aux) i.

Lemma untype_inversion_seq {st tff A C um} {i : instruction_seq st tff A C} {ui1 ui2} :
  untyper.untype_instruction_seq um i = untyped_syntax.SEQ ui1 ui2 ->
  (exists (H : tff = true) i',
      eq_rec _ (fun tff => instruction_seq st tff A C) i _ H = Tail_fail i')
  \/
  (exists B (i1 : instruction st false A B) i2, i = SEQ i1 i2).
Proof.
  destruct i.
  - discriminate.
  - intro H; left.
    exists eq_refl.
    exists i.
    reflexivity.
  - intro H; right.
    repeat eexists.
Qed.

Lemma untype_inversion_swap {st tff A B um} (i : instruction st tff A B) :
  untyper.untype_instruction um i =
  untyped_syntax.instruction_opcode untyped_syntax.SWAP ->
  exists a b SA
         (H : tff = false)
         (HA : A = a ::: b ::: SA)
         (HB : B = b ::: a ::: SA),
    eq_rec
      _
      (fun A => instruction st false A (b ::: a ::: SA))
      (eq_rec
         _
         (fun B => instruction st false A B)
         (eq_rec _ (fun tff => instruction st tff A B) i _ H) _ HB) _ HA
    = Instruction_opcode SWAP.
Proof.
  destruct i; try discriminate.
  destruct o; try discriminate.
  simpl.
  intros _.
  do 3 eexists.
  do 3 (exists eq_refl).
  reflexivity.
Qed.

Lemma untype_inversion_dig {st tff A B um} (i : instruction st tff A B) n :
  untyper.untype_instruction um i =
  untyped_syntax.instruction_opcode (untyped_syntax.DIG n) ->
  exists S1 S2 t
         (H : tff = false)
         (HA : A = S1 +++ t ::: S2)
         (HB : B = t ::: S1 +++ S2)
         (Hn : n = List.length S1),
    eq_rec
      _
      (fun A => instruction st false A (t ::: S1 +++ S2))
      (eq_rec
         _
         (fun B => instruction st false A B)
         (eq_rec _ (fun tff => instruction st tff A B) i _ H) _ HB) _ HA
    = Instruction_opcode (@DIG _ (List.length S1) S1 S2 t eq_refl).
Proof.
  destruct i; try discriminate.
  destruct o; try discriminate.
  simpl.
  intro H.
  injection H.
  intro; subst; clear H.
  do 3 eexists.
  do 4 (exists eq_refl).
  reflexivity.
Qed.

Lemma untype_inversion_dug {st tff A B um} (i : instruction st tff A B) n :
  untyper.untype_instruction um i =
  untyped_syntax.instruction_opcode (untyped_syntax.DUG n) ->
  exists S1 S2 t
         (H : tff = false)
         (HA : A = t ::: S1 +++ S2)
         (HB : B = S1 +++ t ::: S2)
         (Hn : n = List.length S1),
    eq_rec
      _
      (fun A => instruction st false A (S1 +++ t ::: S2))
      (eq_rec
         _
         (fun B => instruction st false A B)
         (eq_rec _ (fun tff => instruction st tff A B) i _ H) _ HB) _ HA
    = Instruction_opcode (@DUG _ (List.length S1) S1 S2 t eq_refl).
Proof.
  destruct i; try discriminate.
  destruct o; try discriminate.
  simpl.
  intro H.
  injection H.
  intro; subst; clear H.
  do 3 eexists.
  do 4 (exists eq_refl).
  reflexivity.
Qed.

Lemma untype_swapswap : untype_fun_seq (@swapswap) (optimizer.swapswap).
Proof.
  unfold untype_fun_seq, swapswap, optimizer.swapswap.
  apply untype_visit_instruction_seq; [| reflexivity].
  intros st tff A D i; simpl.
  unfold swapswap_aux.
  unfold opt_get.
  case_eq (swapswap_opt i).
  - intros i' H.
    rewrite swapswap_opt_swapswap in H.
    destruct H.
    reflexivity.
  - intro H.
    unfold swapswap_opt in H.
    case_eq (untyper.untype_instruction_seq untyper.untype_Optimized i);
      try reflexivity.
    intros ui1 ui23 Hi.
    destruct ui1; try reflexivity.
    destruct o; try reflexivity.
    destruct ui23; try reflexivity.
    destruct i0; try reflexivity.
    destruct o; try reflexivity.
    exfalso.
    generalize (untype_inversion_seq Hi).
    intro Hiinv.
    destruct Hiinv as [(Htff, (i', Hi')) | (B, (i1, (i23, Hi123)))].
    * repeat mytac.
      discriminate.
    * subst i.
      simpl in Hi.
      injection Hi.
      intros Hi23 Hi1.
      generalize (untype_inversion_seq Hi23).
      intros Hiinv.
      destruct Hiinv as [(Htff, (i', Hi')) | (C, (i2, (i3, Hi23')))].
      -- repeat mytac.
         injection Hi23.
         intros Hui23 Hi'.
         apply untype_inversion_swap in Hi'.
         repeat mytac.
         discriminate.
      -- repeat mytac.
         injection Hi23.
         intros Hi3 Hi2.
         apply untype_inversion_swap in Hi1.
         apply untype_inversion_swap in Hi2.
         repeat mytac.
         simpl in H.
         repeat mytac.
Qed.

(* DIG n - DUG n *)


Definition undig_opcode {st A B} (op : @opcode st A B) : Datatypes.option Datatypes.nat :=
  match op with
  | DIG n _ => Some n
  | _ => None
  end.

Definition undug_opcode {st A B} (op : @opcode st A B) : Datatypes.option Datatypes.nat :=
  match op with
  | DUG n _ => Some n
  | _ => None
  end.

Definition undig {st tff A B} (i : instruction st tff A B) : Datatypes.option Datatypes.nat :=
  let? o := unopcode i in undig_opcode o.

Definition undug {st tff A B} (i : instruction st tff A B) : Datatypes.option Datatypes.nat :=
  let? o := unopcode i in undug_opcode o.

Lemma untype_inversion_undig {st tff A B um} (i : instruction st tff A B) n :
  untyper.untype_instruction um i =
  untyped_syntax.instruction_opcode (untyped_syntax.DIG n) ->
  undig i = Some n.
Proof.
  intro H.
  apply untype_inversion_dig in H.
  repeat mytac.
  reflexivity.
Qed.

Lemma untype_inversion_undug {st tff A B um} (i : instruction st tff A B) n :
  untyper.untype_instruction um i =
  untyped_syntax.instruction_opcode (untyped_syntax.DUG n) ->
  undug i = Some n.
Proof.
  intro H.
  apply untype_inversion_dug in H.
  repeat mytac.
  reflexivity.
Qed.

Definition digndugn_opt {st tff A D} (i : instruction_seq st tff A D) :
  Datatypes.option (instruction_seq st tff A D) :=
  let? existT _ _ (existT _ _ i1) := unseq_fst i in
  let? existT _ _ (existT _ _ i23) := unseq_snd i in
  let '(existT _ _ i1) := hide_ntf i1 in
  let? existT _ _ (existT _ _ i2) := unseq_fst i23 in
  let '(existT _ _ i2) := hide_ntf i2 in
  let? existT _ _ (existT _ _ i3) := unseq_snd i23 in
  let? n1 := undig i1 in
  let? n2 := undug i2 in
  if (n1 =? n2) then cast_instruction_seq_opt i3 else None.

Inductive digndugn_rel {st tff} :
  forall {A B} (i i' : instruction_seq st tff A B), Prop :=
| DignDugn_intro {S1 S2 t B} (i : instruction_seq st tff (S1 +++ t ::: S2) B) :
    digndugn_rel
      (SEQ (@DIG st (List.length S1) S1 S2 t eq_refl)
            (SEQ (@DUG st (List.length S1) S1 S2 t eq_refl) i)) i.

Lemma digndugn_opt_digndugn {st tff A D} (i i' : instruction_seq st tff A D) :
  digndugn_opt i = Some i' <->
  digndugn_rel i i'.
Proof.
  split.
  - unfold digndugn_opt.
    intro H.
    apply bind_some in H; destruct H as ((A1, (B1, i1)), (He1, H)).
    apply bind_some in H; destruct H as ((A23, (B23, i23)), (He23, H)).
    case_eq (hide_ntf i1); intros tff1 i1' Hi1'; rewrite Hi1' in H.
    apply bind_some in H; destruct H as ((A2, (B2, i2)), (He2, H)).
    case_eq (hide_ntf i2); intros tff2 i2' Hi2'; rewrite Hi2' in H.
    apply bind_some in H; destruct H as ((A3, (B3, i3)), (He3, H)).

    destruct i1'; try discriminate.
    destruct o; try discriminate.
    simpl in H.

    destruct i2'; try discriminate.
    destruct o; try discriminate.
    simpl in H.

    case_eq (n =? n0); intro Hn; rewrite Hn in H; [|discriminate].

    destruct i; try discriminate.
    destruct i23; try discriminate.
    simpl in *.

    repeat mytac.
    match goal with | H : _ ::: _ +++ _ = _ ::: _ +++ _ |- _ => injection H end.
    intros Happ Ht.
    apply beq_nat_true in Hn.
    symmetry in Hn.
    apply untyper.app_length_inv in Happ; [|assumption].
    repeat mytac.
    constructor.
  - intro H.
    destruct H.
    simpl.
    unfold digndugn_opt; simpl.
    rewrite Nat.eqb_refl.
    apply cast_instruction_seq_same.
Qed.

Definition digndugn_aux {st tff A D} (i : instruction_seq st tff A D) :
  instruction_seq st tff A D :=
  opt_get (digndugn_opt i) i.

Definition digndugn {st tff A B} (i : instruction_seq st tff A B) : instruction_seq st tff A B :=
  visit_instruction_seq (@digndugn_aux) i.

Lemma untype_digndugn : untype_fun_seq (@digndugn) (optimizer.digndugn).
Proof.
  unfold untype_fun_seq, digndugn, optimizer.digndugn.
  apply untype_visit_instruction_seq; [| reflexivity].
  intros st tff A D i; simpl.
  unfold digndugn_aux.
  unfold opt_get.
  case_eq (digndugn_opt i).
  - intros i' H.
    rewrite digndugn_opt_digndugn in H.
    destruct H.
    simpl.
    rewrite Nat.eqb_refl.
    reflexivity.
  - intro H.
    unfold digndugn_opt in H.
    case_eq (untyper.untype_instruction_seq untyper.untype_Optimized i);
      try reflexivity.
    intros ui1 ui23 Hi.
    destruct ui1; try reflexivity.
    destruct o; try reflexivity.
    destruct ui23; try reflexivity.
    destruct i0; try reflexivity.
    destruct o; try reflexivity.
    case_eq (n =? n0); intro Hn; try reflexivity.
    exfalso.
    generalize (untype_inversion_seq Hi).
    intro Hiinv.
    destruct Hiinv as [(Htff, (i', Hi')) | (B, (i1, (i23, Hi123)))].
    * repeat mytac.
      discriminate.
    * subst i.
      simpl in Hi.
      injection Hi.
      intros Hi23 Hi1.
      generalize (untype_inversion_seq Hi23).
      intros Hiinv.
      destruct Hiinv as [(Htff, (i', Hi')) | (C, (i2, (i3, Hi23')))].
      -- repeat mytac.
         injection Hi23.
         intros Hui23 Hi'.
         apply untype_inversion_dug in Hi'.
         repeat mytac.
         discriminate.
      -- repeat mytac.
         injection Hi23.
         intros Hi3 Hi2.
         assert (undig i1 = Some n) as Hni1
             by (eapply untype_inversion_undig; eassumption).
         assert (undug i2 = Some n0) as Hni2
             by (eapply untype_inversion_undug; eassumption).
         simpl in H.
         rewrite Hni1 in H.
         rewrite Hni2 in H.
         simpl in H.
         rewrite Hn in H.
         apply untype_inversion_dig in Hi1.
         apply untype_inversion_dug in Hi2.
         repeat mytac.
         match goal with | H : _ ::: ?S1 +++ _ = _ ::: ?S2 +++ _ |- _ =>
                           rename H into Hl end.
         injection Hl; intros Happ Ht.
         apply beq_nat_true in Hn.
         symmetry in Hn.
         apply untyper.app_length_inv in Happ; [|assumption].
         repeat mytac.
Qed.

(* PUSH - DROP *)

Definition unpush {st tff A B} (i : instruction st tff A B) : Datatypes.option Datatypes.unit :=
  match i with
  | PUSH _ _ => Some tt
  | _ => None
  end.

Lemma untype_inversion_push {st tff A B um} (i : instruction st tff A B) a x :
  untyper.untype_instruction um i =
  untyped_syntax.PUSH a x ->
  exists y (H : tff = false) (HB : B = a ::: A),
    untyper.untype_data um y = x /\
    eq_rec
      _
      (fun B => instruction st false A B)
      (eq_rec _ (fun tff => instruction st tff A B) i _ H) _ HB
    = PUSH a y.
Proof.
  destruct i; try discriminate.
  simpl.
  intro H.
  injection H.
  intros; subst; clear H.
  eexists.
  do 2 (exists eq_refl).
  split; reflexivity.
Qed.

Definition undrop_opcode {st A B} (i : @opcode st A B) : Datatypes.option Datatypes.nat :=
  match i with
  | DROP n _ => Some n
  | _ => None
  end.

Definition undrop {st tff A B} (i : instruction st tff A B) : Datatypes.option Datatypes.nat :=
  let? o := unopcode i in undrop_opcode o.


Lemma untype_inversion_drop {st tff A B um} (i : instruction st tff A B) n :
  untyper.untype_instruction um i =
  untyped_syntax.instruction_opcode (untyped_syntax.DROP n) ->
  exists S1
         (H : tff = false)
         (HA : A = S1 +++ B)
         (Hn : n = List.length S1),
    eq_rec
      _
      (fun A => instruction st false A B)
      (eq_rec _ (fun tff => instruction st tff A B) i _ H) _ HA
    = Instruction_opcode (@DROP _ (List.length S1) S1 B eq_refl).
Proof.
  destruct i; try discriminate.
  destruct o; try discriminate.
  simpl.
  intro H.
  injection H.
  intro; subst; clear H.
  eexists.
  do 3 (exists eq_refl).
  reflexivity.
Qed.

Definition take_one_opt (A : stack_type) :
  Datatypes.option (sigT (fun a : type =>
                          sig (fun B : stack_type => A = a ::: B))) :=
  match A with
  | nil => None
  | cons a A => Some (existT _ a (exist _ A eq_refl))
  end.

Fixpoint take_n_opt (A : stack_type) n :
  Datatypes.option (sig (fun S1 : stack_type => List.length S1 = n)) :=
  match n with
  | 0 => Some (exist _ nil eq_refl)
  | S n =>
    let? existT _ a (exist _ B H) := take_one_opt A in
    let? exist _ S1 H := take_n_opt B n in
    Some (exist _ (a ::: S1) (f_equal S H))
  end.

Lemma take_n_opt_length S1 S2 : take_n_opt (S1 +++ S2) (Datatypes.length S1) =
                                Some (exist _ S1 eq_refl).
Proof.
  induction S1; simpl.
  - reflexivity.
  - rewrite IHS1; reflexivity.
Qed.

Definition pushdrop_opt {st tff A D} (i : instruction_seq st tff A D) :
  Datatypes.option (instruction_seq st tff A D) :=
  let? existT _ _ (existT _ _ i1) := unseq_fst i in
  let? existT _ _ (existT _ _ i23) := unseq_snd i in
  let '(existT _ _ i1) := hide_ntf i1 in
  let? existT _ _ (existT _ _ i2) := unseq_fst i23 in
  let '(existT _ _ i2) := hide_ntf i2 in
  let? existT _ B (existT _ _ i3) := unseq_snd i23 in
  let? tt := unpush i1 in
  let? n := undrop i2 in
  match n with
  | 0 => None
  | 1 => cast_instruction_seq_opt i3
  | S n =>
    let? exist _ S1 H1 := take_n_opt A n in
    cast_instruction_seq_opt (SEQ (@DROP st n S1 B H1) i3)
  end.

Inductive pushdrop_rel {st tff} :
  forall {A B} (i i' : instruction_seq st tff A B), Prop :=
| PushDrop_1 {A B t x} (i : instruction_seq st tff A B) :
    pushdrop_rel
      (SEQ (PUSH t x) (SEQ (@DROP _ 1 (cons t nil) A eq_refl) i)) i
| PushDrop_S {t2 S1 S2 B t1 x} (i : instruction_seq st tff S2 B) :
    pushdrop_rel
      (SEQ (PUSH t1 x) (SEQ (@DROP _ (S (S (List.length S1))) (cons t1 (cons t2 S1)) S2 eq_refl) i))
      (SEQ (@DROP _ (S (List.length S1)) (cons t2 S1) S2 eq_refl) i).

Lemma pushdrop_opt_pushdrop {st tff A D} (i i' : instruction_seq st tff A D) :
  pushdrop_opt i = Some i' <-> pushdrop_rel i i'.
Proof.
  split.
  - unfold pushdrop_opt.
    intro H.
    apply bind_some in H; destruct H as ((A1, (B1, i1)), (He1, H)).
    apply bind_some in H; destruct H as ((A23, (B23, i23)), (He23, H)).
    case_eq (hide_ntf i1); intros tff1 i1' Hi1'; rewrite Hi1' in H.
    apply bind_some in H; destruct H as ((A2, (B2, i2)), (He2, H)).
    case_eq (hide_ntf i2); intros tff2 i2' Hi2'; rewrite Hi2' in H.
    apply bind_some in H; destruct H as ((A3, (B3, i3)), (He3, H)).

    destruct i1'; try discriminate.
    simpl in H.

    destruct i2'; try discriminate.
    destruct o; try discriminate.
    simpl in H.

    destruct n as [|[|n]]; destruct A1 as [|t1[|t2 A1]]; try discriminate.
    + destruct i; try discriminate.
      destruct i23; try discriminate.
      simpl in *.
      repeat mytac.
      constructor.
    + destruct i; try discriminate.
      destruct i23; try discriminate.
      simpl in *.
      injection e; intro.
      repeat mytac.
      rewrite take_n_opt_length in H1.
      simpl in *.
      repeat mytac.
      simpl.
      constructor.
  - intro H.
    destruct H.
    + simpl.
      unfold pushdrop_opt; simpl.
      apply cast_instruction_seq_same.
    + simpl.
      unfold pushdrop_opt; simpl.
      rewrite take_n_opt_length.
      simpl.
      apply cast_instruction_seq_same.
Qed.

Definition pushdrop_aux {st tff A B} (i : instruction_seq st tff A B)
  : instruction_seq st tff A B :=
  opt_get (pushdrop_opt i) i.

Definition pushdrop {st tff A B} (i : instruction_seq st tff A B) :=
  visit_instruction_seq (@pushdrop_aux) i.

Lemma untype_pushdrop : untype_fun_seq (@pushdrop) (optimizer.push_drop).
Proof.
  unfold untype_fun_seq, pushdrop, optimizer.push_drop.
  apply untype_visit_instruction_seq; [| reflexivity].
  intros st tff A D i; simpl.
  unfold pushdrop_aux.
  unfold opt_get.
  case_eq (pushdrop_opt i).
  - intros i' H.
    rewrite pushdrop_opt_pushdrop in H.
    destruct H; reflexivity.
  - intro H.
    unfold pushdrop_opt in H.
    case_eq (untyper.untype_instruction_seq untyper.untype_Optimized i);
      try reflexivity.
    intros ui1 ui23 Hi.
    destruct ui1; try reflexivity.
    destruct ui23; try reflexivity.
    destruct i0; try reflexivity.
    destruct o; try reflexivity.
    destruct n as [|n]; try reflexivity.
    exfalso.
    generalize (untype_inversion_seq Hi).
    intro Hiinv.
    destruct Hiinv as [(Htff, (i', Hi')) | (B, (i1, (i23, Hi123)))].
    * repeat mytac.
      discriminate.
    * subst i.
      simpl in Hi.
      injection Hi.
      intros Hi23 Hi1.
      generalize (untype_inversion_seq Hi23).
      intros Hiinv.
      destruct Hiinv as [(Htff, (i', Hi')) | (C, (i2, (i3, Hi23')))].
      -- repeat mytac.
         injection Hi23.
         intros Hui23 Hi'.
         apply untype_inversion_drop in Hi'.
         repeat mytac.
         discriminate.
      -- repeat mytac.
         injection Hi23.
         intros Hi3 Hi2.
         apply untype_inversion_push in Hi1.
         apply untype_inversion_drop in Hi2.
         repeat mytac.
         match goal with H : S _ = Datatypes.length ?l |- _ =>
                         rename l into B; rename H into HB end.
         destruct B as [| a [| b B]]; [discriminate| |].
         ++ simpl in *.
            injection HB; intro.
            repeat mytac.
            simpl in H.
            repeat mytac.
         ++ simpl in *.
            injection HB; intro.
            repeat mytac.
            simpl in H.
            rewrite take_n_opt_length in H.
            simpl in H.
            repeat mytac.
Qed.

Definition cleanup {st tff A B} (i : instruction_seq st tff A B)
  : instruction_seq st tff A B :=
  pushdrop
    (swapswap
       (digndugn
          (dig0dug0 i))).

Lemma untype_cleanup : untype_fun_seq (@cleanup) (optimizer.cleanup).
Proof.
  intros st tff A B i.
  unfold cleanup, optimizer.cleanup.
  rewrite (@untype_pushdrop st tff A B); f_equal.
  rewrite (@untype_swapswap st tff A B); f_equal.
  rewrite (@untype_digndugn st tff A B); f_equal.
  rewrite (@untype_dig0dug0 st tff A B); f_equal.
Qed.


Module Semantics_Preservation (C : semantics.ContractContext).
  Module S := semantics.Semantics C.
  Import S.

  Definition same_semantics
             (F : forall st tff A B, instruction_seq st tff A B ->
                                     instruction_seq st tff A B)
    :=
      forall st tff env A B fuel i stA,
        Bool.Is_true (error.success (eval_seq env i fuel stA)) ->
        eval_seq env (F st tff A B i) fuel stA = eval_seq env i fuel stA.

  Lemma eval_seq_SEQ st tff env A B C
        (i1 : instruction st false A B)
        (i2 : instruction_seq st tff B C) fuel SA :
    eval_seq env (SEQ i1 i2) fuel SA =
    let! SB := eval env i1 fuel SA in
    eval_seq env i2 fuel SB.
  Proof.
    unfold eval_seq.
    destruct fuel; reflexivity.
  Qed.

  Lemma eval_fail_and_seq :
    (forall st A B (i : instruction st true A B)
            fuel env stA, ~ Bool.Is_true (error.success (eval env i fuel stA))) *
    (forall st A B (i : instruction_seq st true A B)
            fuel env stA, ~ Bool.Is_true (error.success (eval_seq env i fuel stA))).
  Proof.
    apply tail_fail_induction_and_seq; intros; (destruct fuel as [|fuel]; [simpl; auto|]); simpl.
    - destruct stA as (x, stA); simpl.
      auto.
    - destruct stA as (x, stA); simpl.
      destruct (if_family_destruct f x); simpl; [apply H | apply H0].
    - rewrite eval_seq_SEQ.
      intro Hs; apply error.success_bind in Hs.
      destruct Hs as (stB, (Hi1, Hs)).
      apply H in Hs.
      assumption.
    - apply H.
    - apply H.
  Qed.

  Lemma eval_fail st A B (i : instruction st true A B) fuel env stA :
    ~ Bool.Is_true (error.success (eval env i fuel stA)).
  Proof.
    apply eval_fail_and_seq.
  Qed.

  Lemma eval_fail_seq st A B (i : instruction_seq st true A B) fuel env stA :
    ~ Bool.Is_true (error.success (eval_seq env i fuel stA)).
  Proof.
    apply eval_fail_and_seq.
  Qed.

  Lemma same_semantics_visit_seq_aux F (HF : same_semantics F)
        (HNOOP : forall st A, F st _ A A NOOP = NOOP) :
    (forall st tff env A B fuel (i : instruction st tff A B) stA,
        Bool.Is_true (error.success (eval env i fuel stA)) ->
        eval env (visit_instruction F i) fuel stA = eval env i fuel stA) ->
    same_semantics (@visit_instruction_seq F).
  Proof.
    intros Heval st tff env A B fuel i stA Hsucc.
    induction i.
    - simpl.
      rewrite HNOOP.
      reflexivity.
    - simpl.
      apply eval_fail in Hsucc.
      contradiction.
    - simpl.
      rewrite eval_seq_SEQ in Hsucc.
      apply error.success_bind in Hsucc.
      destruct Hsucc as (stB, (Hi, Hsucc)).
      transitivity
        (eval_seq env (SEQ
                         (visit_instruction F i)
                         (visit_instruction_seq F i0)) fuel stA).
      + apply HF.
        rewrite eval_seq_SEQ.
        specialize (IHi env stB Hsucc).
        rewrite Heval; rewrite Hi; [|constructor].
        simpl.
        rewrite IHi.
        assumption.
      + do 2 rewrite eval_seq_SEQ.
        rewrite Heval.
        * rewrite Hi.
          simpl.
          apply IHi.
          exact Hsucc.
        * rewrite Hi.
          simpl.
          constructor.
  Defined.

  Fixpoint same_semantics_visit F (HF : same_semantics F) (HNOOP : forall st A, F st false A A NOOP = NOOP)
           st tff env A B fuel (i : instruction st tff A B) stA {struct fuel} :
    Bool.Is_true (error.success (eval env i fuel stA)) ->
    eval env (visit_instruction F i) fuel stA =
    eval env i fuel stA.
  Proof.
    specialize (same_semantics_visit_seq_aux F HF HNOOP (same_semantics_visit F HF HNOOP)).
    unfold same_semantics.
    intros Hseq.
    destruct fuel as [|fuel]; [reflexivity|]; destruct i; try reflexivity.
    + apply Hseq; try assumption.
    + destruct stA as (x, SA);
        simpl; destruct (if_family_destruct i x);
          intro Hsucc; apply Hseq; exact Hsucc.
    + destruct stA as (ab, SA); simpl; destruct (loop_family_destruct i ab) as [a|b];
        intro Hsucc.
      * apply error.success_bind in Hsucc.
        destruct Hsucc as ((x, SA'), (Hret,Hsucc)).
        unfold eval_seq in Hseq.
        rewrite Hseq.
        -- rewrite Hret; simpl.
           unfold stack_type in Hret; rewrite Hret; simpl.
           generalize (same_semantics_visit F HF HNOOP _ _ env _ _ fuel (LOOP_ i i0));
             intro Hv.
           simpl in Hv.
           apply Hv.
           assumption.
        -- unfold stack_type in Hret.
           rewrite Hret.
           constructor.
      * reflexivity.
    + destruct stA as (x, SA); simpl.
      destruct (iter_destruct (iter_elt_type collection i) collection (iter_variant_field collection i)) as [(a, y)|]; intro Hsucc.
      * apply error.success_bind in Hsucc.
        destruct Hsucc as (z, (Hret,Hsucc)).
        unfold stack_type.
        unfold eval_seq in Hseq.
        rewrite Hseq.
        -- generalize (same_semantics_visit F HF HNOOP _ _ env _ _ fuel (ITER i0));
             intro Hv.
           simpl in Hv.
           unfold stack_type in Hret.
           rewrite Hret.
           simpl.
           apply Hv.
           assumption.
        -- unfold stack_type in Hret.
           rewrite Hret.
           constructor.
      * reflexivity.
    + destruct stA as (x, SA); simpl.
      destruct (map_destruct (map_in_type collection b i) b collection (map_out_collection_type collection b i) (map_variant_field collection b i) x) as [(a, y)|]; intro Hsucc.
      * apply error.success_bind in Hsucc.
        destruct Hsucc as ((b0, SB), (Hret,Hsucc)).
        unfold eval_seq in Hseq.
        rewrite Hseq.
        -- generalize (same_semantics_visit F HF HNOOP self_type _ env _ _ fuel (MAP i0));
             intro Hv.
           simpl in Hv.
           rewrite Hret.
           unfold stack_type in Hret.
           simpl.
           simpl in Hret.
           match goal with |- (let! (b1, SB0) := ?lhs in _ ) = _ =>
                           replace lhs with (error.Return (b0, SB))
           end.
           simpl.
           rewrite Hv.
           ++ reflexivity.
           ++ apply error.success_bind_arg in Hsucc.
              assumption.
        -- unfold stack_type in Hret.
           match goal with |- (Bool.Is_true (error.success ?lhs)) =>
                           replace lhs with (error.Return (b0, SB))
           end.
           constructor.
      * reflexivity.
    + simpl.
      intro Hsucc.
      destruct (stack_split stA) as (S1, S2).
      unfold eval_seq in Hseq.
      rewrite Hseq.
      * reflexivity.
      * unfold stack_type in Hsucc.
        apply error.success_bind_arg in Hsucc.
        assumption.
  Qed.

  Lemma same_semantics_visit_seq F (HF : same_semantics F) (HNOOP : forall st A, F st false A A NOOP = NOOP) :
    same_semantics (@visit_instruction_seq F).
  Proof.
    apply same_semantics_visit_seq_aux; try assumption.
    apply same_semantics_visit; assumption.
  Qed.

  Lemma same_semantics_opt F :
    (forall st tff env A B (i i' : instruction_seq st tff A B) SA fuel,
        F st tff A B i = Some i' ->
        Bool.Is_true (error.success (eval_seq env i fuel SA)) ->
        eval_seq env i' fuel SA = eval_seq env i fuel SA) ->
    same_semantics (fun st tff A B (i : instruction_seq st tff A B) => opt_get (F st tff A B i) i).
  Proof.
    intros HF st tff env A B fuel i SA Hsucc.
    case_eq (F st tff A B i).
    - intros i' Hi'.
      apply HF; assumption.
    - intro; reflexivity.
  Qed.

  Lemma eval_Instruction_seq_aux st tff env A B (i : instruction_seq st tff A B) fuel stA :
    Bool.Is_true (error.success (eval env (Instruction_seq i) fuel stA)) ->
    eval env (Instruction_seq i) fuel stA =
    eval_seq env i fuel stA.
  Proof.
    destruct fuel.
    - contradiction.
    - intro Hsucc.
      change (eval_seq env i fuel stA = eval_seq env i (S fuel) stA).
      apply eval_seq_deterministic_le.
      + omega.
      + assumption.
  Qed.

  Lemma eval_seq_instruction_app_aux st tff1 H1 tff2 env A B C
        (i1 : instruction_seq st tff1 A B)
        (i2 : instruction_seq st tff2 B C) fuel SA :
    eval_seq env (instruction_app_aux i1 H1 i2) fuel SA =
    let! SB := eval_seq env i1 fuel SA in
    eval_seq env i2 fuel SB.
  Proof.
    induction i1; simpl.
    - reflexivity.
    - discriminate.
    - unfold eval_seq.
      simpl.
      destruct (eval env i fuel SA); simpl.
      + reflexivity.
      + apply IHi1.
  Qed.

  Lemma eval_seq_instruction_app st tff env A B C
        (i1 : instruction_seq st false A B)
        (i2 : instruction_seq st tff B C) fuel SA :
    eval_seq env (i1;;;i2) fuel SA =
    let! SB := eval_seq env i1 fuel SA in
    eval_seq env i2 fuel SB.
  Proof.
    apply eval_seq_instruction_app_aux.
  Qed.

  Lemma eval_Instruction_seq self_type tff env fuel A B C
        (i1 : instruction_seq self_type false A B)
        (i2 : instruction_seq self_type tff B C)
        stA:
    Bool.Is_true (error.success (eval_seq env (SEQ (Instruction_seq i1) i2) fuel stA)) ->
    eval_seq env (i1;;; i2) fuel stA =
    eval_seq env (SEQ (Instruction_seq i1) i2) fuel stA.
  Proof.
    intro Hsucc.
    rewrite eval_seq_instruction_app.
    rewrite eval_seq_SEQ.
    rewrite eval_Instruction_seq_aux.
    - reflexivity.
    - rewrite eval_seq_SEQ in Hsucc.
      apply error.success_bind_arg in Hsucc.
      assumption.
  Qed.

  Lemma stack_app_split (S1 S2 : Datatypes.list type) (s1 : stack S1) (s2 : stack S2) sA :
    stack_split sA = (s1, s2) <-> sA = stack_app s1 s2.
  Proof.
    generalize s2; clear s2.
    induction S1; intro s2.
    - simpl.
      simpl in s1.
      destruct s1.
      split; congruence.
    - simpl.
      simpl in s1.
      destruct s1 as (x, s1).
      simpl in sA.
      destruct sA as (y, sA).
      case_eq (stack_split sA).
      intros s1' s2' HsA.
      split.
      + rewrite IHS1 in HsA.
        congruence.
      + intro H; injection H; intros.
        subst y.
        rewrite <- IHS1 in H0.
        congruence.
  Qed.

  Lemma same_semantics_dig0dug0 :
    same_semantics (@dig0dug0).
  Proof.
    apply same_semantics_visit_seq.
    - apply same_semantics_opt.
      intros st tff env A B i i' stA fuel HS Hsucc.
      apply dig0dug0_opt_dig0dug0 in HS.
      destruct HS.
      + apply eval_fail_seq in Hsucc.
        contradiction.
      + apply eval_Instruction_seq.
        assumption.
      + rewrite eval_seq_instruction_app.
        rewrite eval_seq_SEQ.
        f_equal.
        unfold eval_seq in Hsucc.
        apply error.success_bind in Hsucc.
        destruct Hsucc as (stB, (HDIP, _)).
        destruct fuel; [simpl in HDIP; discriminate|].
        simpl.
        simpl in HDIP.
        apply error.bind_eq_return in HDIP.
        destruct HDIP as (stB', (Hi1, HstB')).
        apply error.unreturn in HstB'.
        subst stB'.
        rewrite Hi1.
        simpl.
        rewrite <- Hi1.
        symmetry.
        apply eval_seq_deterministic_le; [omega|].
        unfold eval_seq.
        unfold stack_type in Hi1.
        rewrite Hi1.
        constructor.
      + rewrite eval_seq_SEQ.
        unfold eval_seq in Hsucc.
        apply error.success_bind in Hsucc.
        destruct Hsucc as (stAB, (HDIP, _)).
        destruct fuel; [simpl in HDIP; discriminate|].
        simpl.
        simpl in HDIP.
        destruct (stack_split stA) as (stA', stB) eqn:HstA.
        simpl.
        f_equal.
        apply stack_app_split.
        assumption.
      + rewrite eval_seq_SEQ.
        destruct fuel; [simpl in Hsucc; contradiction|].
        reflexivity.
      + rewrite eval_seq_SEQ.
        destruct fuel; [simpl in Hsucc; contradiction|].
        destruct stA; reflexivity.
      + rewrite eval_seq_SEQ.
        destruct fuel; [simpl in Hsucc; contradiction|].
        destruct stA; reflexivity.
      + rewrite eval_seq_SEQ.
        destruct fuel; [simpl in Hsucc; contradiction|].
        destruct stA as (x, (y, stA)); reflexivity.
      + rewrite eval_seq_SEQ.
        destruct fuel; [simpl in Hsucc; contradiction|].
        destruct stA as (x, (y, stA)); reflexivity.
    - reflexivity.
  Qed.


  Lemma same_semantics_swapswap :
    same_semantics (@swapswap).
  Proof.
    apply same_semantics_visit_seq.
    - apply same_semantics_opt.
      intros st tff env A D i i' stA fuel HS Hsucc.
      apply swapswap_opt_swapswap in HS.
      destruct HS.
      destruct fuel as [|fuel]; [contradiction|].
      destruct stA as (x, (y, stA)).
      rewrite eval_seq_SEQ.
      simpl.
      rewrite eval_seq_SEQ.
      simpl.
      reflexivity.
    - reflexivity.
  Qed.

  Lemma same_semantics_digndugn :
    same_semantics (@digndugn).
  Proof.
    apply same_semantics_visit_seq.
    - apply same_semantics_opt.
      intros st tff env A D i i' stA fuel HS Hsucc.
      apply digndugn_opt_digndugn in HS.
      destruct HS.
      + destruct fuel as [|fuel]; [contradiction|].
        rewrite eval_seq_SEQ.
        simpl.
        rewrite eval_seq_SEQ.
        simpl.
        unfold stack_dig, stack_dug.
        case_eq (stack_split stA).
        intros s1 s2 HS12.
        destruct s2 as (x, s2).
        assert (stack_split (stack_app s1 s2) = (s1, s2)) as H.
        * rewrite stack_app_split.
          reflexivity.
        * rewrite H.
          rewrite stack_app_split in HS12.
          congruence.
    - reflexivity.
  Qed.

  Lemma same_semantics_push_drop :
    same_semantics (@pushdrop).
  Proof.
    apply same_semantics_visit_seq.
    - apply same_semantics_opt.
      intros st tff env A D i i' stA fuel HS Hsucc.
      apply pushdrop_opt_pushdrop in HS.
      destruct HS.
      + destruct fuel as [|fuel]; [contradiction|].
        rewrite eval_seq_SEQ.
        simpl.
        rewrite eval_seq_SEQ.
        simpl.
        reflexivity.
      + destruct fuel as [|fuel]; [contradiction|].
        rewrite eval_seq_SEQ.
        simpl.
        rewrite eval_seq_SEQ.
        simpl.
        rewrite eval_seq_SEQ.
        simpl.
        destruct stA as (y, stA).
        case_eq (stack_split stA).
        reflexivity.
    - reflexivity.
  Qed.

  Lemma same_semantics_compose F G :
    same_semantics F ->
    same_semantics G ->
    same_semantics (fun st tff A B i => F st tff A B (G st tff A B i)).
  Proof.
    intros HF HG.
    unfold same_semantics.
    intros.
    rewrite HF.
    - rewrite HG.
      + reflexivity.
      + assumption.
    - rewrite HG; assumption.
  Qed.

  Lemma same_semantics_cleanup :
    same_semantics (@cleanup).
  Proof.
    unfold cleanup.
    apply same_semantics_compose; [exact same_semantics_push_drop|].
    apply same_semantics_compose; [exact same_semantics_swapswap|].
    apply same_semantics_compose; [exact same_semantics_digndugn|].
    exact same_semantics_dig0dug0.
  Qed.

  Definition typecheck_and_eval_seq
             (i : untyped_syntax.instruction_seq)
             A B (sA : stack A)
             self_type env fuel : error.M (stack B) :=
    let! existT _ tff i' :=
       typer.type_check_instruction_seq
         (self_type := self_type)
         (typer.type_instruction_seq typer.Optimized)
         i A B in
    eval_seq env i' fuel sA.

  (* If the untyped instruction sequence i can be typechecked from
     stack type A to stack type B and then run successfully on stack
     sA, then (optimizer.optimize i) can also be typechecked from
     stack type A to stack type B and run successfully on stack sA
     yielding the same result. *)

  Theorem optimize_correct :
    forall i A B sA self_type env fuel,
      let e := typecheck_and_eval_seq i A B sA self_type env fuel in
      Bool.Is_true (error.success e) ->
      typecheck_and_eval_seq (optimizer.optimize i) A B sA self_type env fuel = e.
  Proof.
    intros ui A B sA self_type env fuel.
    unfold typecheck_and_eval_seq.
    intro Hsucc.
    apply error.success_bind in Hsucc.
    destruct Hsucc as ((tff, i), (Hret, Hsucc)).
    rewrite Hret.
    simpl.
    unfold typer.type_check_instruction_seq in Hret.
    apply error.bind_eq_return in Hret.
    destruct Hret as (t, (Ht, Hret)).
    apply untyper.type_untype_seq in Ht.
    destruct t.
    - subst ui.
      unfold typer.instruction_seq_cast_range, typer.instruction_seq_cast in Hret.
      rewrite untyper.stype_dec_same in Hret.
      destruct (stype_dec B0 B); [|discriminate].
      simpl in Hret.
      apply error.unreturn in Hret.
      repeat mytac.
      rewrite <- (untype_cleanup).
      unfold typer.type_check_instruction_seq.
      simpl in *.
      rewrite untyper.untype_type_instruction_seq.
      simpl.
      unfold typer.instruction_seq_cast_range.
      rewrite untyper.instruction_seq_cast_same.
      simpl.
      apply same_semantics_cleanup.
      assumption.
    - apply error.unreturn in Hret.
      repeat mytac.
      simpl in Hsucc.
      apply eval_fail_seq in Hsucc.
      contradiction.
  Qed.

End Semantics_Preservation.
