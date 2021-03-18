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


(* The error monad, and various basic stuff *)

Require Bool String.
Require Import location.
Require Import syntax_type.

Inductive exception : Type :=
| Out_of_fuel
| Overflow
| Assertion_Failure (A : Set) (a : A)
| Lexing (_ : location)
| Parsing
| Parsing_Out_of_Fuel
| Expansion (_ _ : location)
| Expansion_prim (_ _ : location) (_ : String.string)
| Typing (A : Set) (a : A).

Inductive M (A : Type) : Type :=
| Failed : exception -> M A
| Return : A -> M A.

Arguments Return {_} _.

Lemma unreturn {A} (a b : A) : Return a = Return b -> a = b.
Proof.
  congruence.
Qed.

Lemma unsome {A} (x y : A) : Some x = Some y -> x = y.
Proof.
  congruence.
Qed.

Definition bind {A B : Type} (m : M A) (f : A -> M B) :=
  match m with
  | Failed _ e => Failed B e
  | Return SB => f SB
  end.

Definition option_bind {A B}
           (o : Datatypes.option A) (f : A -> Datatypes.option B) :
  Datatypes.option B :=
  match o with
  | None => None
  | Some a => f a
  end.

Module Notations.
  (** Notation for the bind with a typed answer. *)
  Notation "'let!' x : A ':=' X 'in' Y" :=
    (bind X (fun (x : A) => Y))
    (at level 200, x pattern, X at level 100, A at level 200, Y at level 200).

  (** Notation for the bind. *)
  Notation "'let!' x ':=' X 'in' Y" :=
    (bind X (fun x => Y))
    (at level 200, x pattern, X at level 100, Y at level 200).


  Notation "'let?' x ':=' X 'in' Y" :=
    (option_bind X (fun x => Y))
      (at level 200, x pattern, X at level 100, Y at level 200).

End Notations.

Import Notations.

Fixpoint list_fold_left {A B : Set} (f : A -> B -> M A) (l : Datatypes.list B) (a : A) : M A :=
  match l with
  | nil => Return a
  | cons x l =>
    let! a := f a x in
    list_fold_left f l a
  end.

Fixpoint list_map {A B : Set} (f : A -> M B) (l : Datatypes.list A) : M (Datatypes.list B) :=
  match l with
  | nil => Return nil
  | cons a l =>
    let! b := f a in
    let! l := list_map f l in
    Return (cons b l)
  end.

Lemma list_map_map {A B C : Set} (f : A -> B) (g : B -> M C) (l : Datatypes.list A) :
  list_map g (List.map f l) =
  list_map (fun x => g (f x)) l.
Proof.
  induction l; simpl.
  - reflexivity.
  - rewrite IHl.
    reflexivity.
Qed.

Lemma list_map_id {A : Set} (f : A -> M A) (l : Datatypes.list A) :
  (forall x : A, f x = Return x) ->
  list_map f l = Return l.
Proof.
  intro Hf.
  induction l; simpl.
  - reflexivity.
  - rewrite Hf.
    simpl.
    rewrite IHl.
    simpl.
    reflexivity.
Qed.

Definition try {A} (m1 m2 : M A) : M A :=
  match m1 with
  | Failed _ _ => m2
  | Return _ => m1
  end.

Definition success {A} (m : M A) :=
  match m with
  | Failed _ _ => false
  | Return _ => true
  end.

Definition isSome {A} (m : Datatypes.option A) :=
  match m with
  | None => false
  | Some _ => true
  end.

Lemma bool_dec (b1 b2 : Datatypes.bool) : { b1 = b2 } + { b1 <> b2 }.
Proof.
  repeat decide equality.
Qed.

Definition Is_true := Bool.Is_true.

Lemma Is_true_UIP b (x y : Is_true b) : x = y.
Proof.
  destruct b; destruct x; destruct y; reflexivity.
Defined.

Coercion is_true := Is_true.

Lemma IT_eq (b : Datatypes.bool) : b -> b = true.
Proof.
  destruct b; auto.
Qed.

Lemma IT_eq_rev (b : Datatypes.bool) : b = true -> b.
Proof.
  intro H; subst b; exact I.
Qed.

Lemma IT_eq_iff (b : Datatypes.bool) : b <-> b = true.
Proof.
  split.
  - apply IT_eq.
  - apply IT_eq_rev.
Qed.

Lemma Is_true_and_left b1 b2 : (b1 && b2)%bool -> b1.
Proof.
  destruct b1; simpl.
  - intro; constructor.
  - auto.
Qed.

Lemma Is_true_and_right b1 b2 : (b1 && b2)%bool -> b2.
Proof.
  destruct b1; simpl.
  - auto.
  - intro H.
    inversion H.
Qed.

Definition extract {A : Type} (m : M A) : success m -> A :=
  match m with
  | Return x => fun _ => x
  | Failed _ _ => fun H => match H with end
  end.

Definition opt_get {A} (o : Datatypes.option A) (default : A) : A :=
  match o with Some x => x | None => default end.

Definition opt_extract {A} (o : Datatypes.option A) : isSome o -> A :=
  match o with
  | Some x => fun _ => x
  | None => fun H => match H with end
  end.

Definition IT_if {A : Type} (b : Datatypes.bool) (th : b -> A) (els : A) : A :=
  (if b as b0 return b = b0 -> A then
     fun H => th (IT_eq_rev _ H)
   else fun _ => els) eq_refl.

Lemma success_bind {A B : Set} (f : A -> M B) m :
  success (let! x := m in f x) ->
  exists x, m = Return x /\ success (f x).
Proof.
  destruct m.
  - contradiction.
  - intro H.
    exists a.
    auto.
Qed.

Lemma isSome_bind {A B : Set} (f : A -> Datatypes.option B) m :
  isSome (let? x := m in f x) ->
  exists x, m = Some x /\ isSome (f x).
Proof.
  destruct m.
  - intro H.
    exists a.
    auto.
  - contradiction.
Qed.

Lemma success_bind_rev {A B : Set} (f : A -> M B) m :
  (exists x, m = Return x /\ success (f x)) ->
  success (let! x := m in f x).
Proof.
  destruct m;
  intro H;
  inversion H as (x & H_eq & H_success);
  inversion H_eq;
  auto.
Qed.

Lemma isSome_bind_rev {A B : Set} (f : A -> Datatypes.option B) m :
  (exists x, m = Some x /\ isSome (f x)) ->
  isSome (let? x := m in f x).
Proof.
  destruct m;
  intro H;
  inversion H as (x & H_eq & H_success);
  inversion H_eq;
  auto.
Qed.

Lemma success_eq_return A (x : A) m :
  m = Return x -> success m.
Proof.
  intro He.
  rewrite He.
  exact I.
Qed.

Lemma isSome_eq_Some A (x : A) m :
  m = Some x -> isSome m.
Proof.
  intro He.
  rewrite He.
  exact I.
Qed.

Lemma success_bind_arg {A B : Set} (f : A -> M B) m :
  success (let! x := m in f x) ->
  success m.
Proof.
  intro H.
  apply success_bind in H.
  destruct H as (x, (H, _)).
  apply success_eq_return in H.
  exact H.
Qed.

Lemma success_eq_return_rev A (m : M A) :
  success m -> exists x, m = Return x.
Proof.
  destruct m.
  - contradiction.
  - exists a.
    reflexivity.
Qed.

Lemma bind_eq_return {A B : Set} f (m : M A) (b : B) :
  (let! x := m in f x) = Return b <->
  exists a : A, m = Return a /\ f a = Return b.
Proof.
  split.
  - destruct m.
    + discriminate.
    + simpl.
      exists a.
      auto.
  - intros (a, (Hm, Hb)).
    subst m; exact Hb.
Qed.

Lemma bind_some {A B} (y : Datatypes.option A) (w : B) z : (let? x := y in z x) = Some w <-> (exists x, y = Some x /\ z x = Some w).
Proof.
  destruct y; simpl; split.
  - intro H; exists a; split; congruence.
  - intros (x, (Hx, Hz)); congruence.
  - discriminate.
  - intros (x, (Hx, Hz)); discriminate.
Qed.


Definition precond {A} (m : M A) p :=
  match m with
  | Failed _ _ => is_true false
  | Return a => p a
  end.

Lemma success_precond {A} (m : M A) : is_true (success m) = precond m (fun _ => is_true true).
Proof.
  destruct m; reflexivity.
Qed.

Definition precond_ex {A} (m : M A) p := exists a, m = Return a /\ p a.

Lemma precond_exists {A} (m : M A) p : precond m p <-> precond_ex m p.
Proof.
  destruct m; simpl; split.
  - contradiction.
  - intros (a, (Hf, _)).
    discriminate.
  - intro H.
    exists a.
    auto.
  - intros (b, (Hb, Hp)).
    injection Hb.
    congruence.
Qed.

Lemma precond_bind {A B : Set} (f : A -> M B) m p :
  precond (let! x := m in f x) p = precond m (fun a => precond (f a) p).
Proof.
  destruct m; reflexivity.
Qed.

Lemma return_precond {A} (m : M A) a :
  m = Return a <-> precond m (fun x => x = a).
Proof.
  destruct m; simpl; split.
  - discriminate.
  - contradiction.
  - intro H; injection H; auto.
  - congruence.
Qed.

Lemma precond_eqv {A} (m : M A) phi psi  :
  (forall x, phi x <-> psi x) -> precond m phi <-> precond m psi.
Proof.
  destruct m; simpl.
  - intuition.
  - intro H.
    apply H.
Qed.

Definition dif {A : Datatypes.bool -> Type} (b : Datatypes.bool) (t : b -> A b) (e : negb b -> A b) : A b.
Proof.
  destruct b; [apply t | apply e]; constructor.
Defined.

Lemma dif_case {A : Datatypes.bool -> Type} {b t e} {P : A b -> Prop} : (forall h, P (t h)) -> (forall h, P (e h)) -> P (dif b t e).
Proof.
  unfold dif.
  destruct b.
  - intros H _; apply H.
  - intros _ H; apply H.
Defined.

Lemma dif_is_true {A : Datatypes.bool -> Type} (b : Datatypes.bool)
  (t : b -> A b) (e : negb b -> A b)
  (H : is_true b) : dif b t e = t H.
Proof.
  destruct b, H; reflexivity.
Qed.

Lemma dif_is_false {A : Datatypes.bool -> Type} (b : Datatypes.bool)
  (t : b -> A b) (e : negb b -> A b)
  (H : is_true (negb b)) : dif b t e = e H.
Proof.
  destruct b, H; reflexivity.
Qed.

(* Lemmas about sigT *)

Definition sigT_eq_1 {A} (P : A -> Set) (xa yb : sigT P) : xa = yb -> projT1 xa = projT1 yb.
Proof.
  apply f_equal.
Defined.

Definition sigT_eq_2 {A} (P : A -> Set) (xa yb : sigT P) (H : xa = yb) :
  eq_rec (projT1 xa) P (projT2 xa) (projT1 yb) (sigT_eq_1 P xa yb H) = projT2 yb.
Proof.
  subst xa.
  reflexivity.
Defined.

Definition existT_eq_1 {A} (P : A -> Set) x y a b : existT P x a = existT P y b -> x = y.
Proof.
  apply (f_equal (@projT1 A P)).
Defined.

Definition existT_eq_2 {A} (P : A -> Set) x y a b (H : existT P x a = existT P y b ) :
  eq_rec x P a y (existT_eq_1 P x y a b H) = b.
Proof.
  apply (sigT_eq_2 P (existT P x a) (existT P y b)).
Defined.

Definition existT_eq_3 {A} (P : A -> Set) x y a b :
  existT P x a = existT P y b ->
  sig (fun H : x = y => eq_rec x P a y H = b).
Proof.
  intro H.
  exists (existT_eq_1 P x y a b H).
  apply existT_eq_2.
Defined.

(* Same about sig *)

Definition sig_eq_1 {A} (P : A -> Prop) (xa yb : sig P) : xa = yb -> proj1_sig xa = proj1_sig yb.
Proof.
  apply f_equal.
Defined.

Definition sig_eq_2 {A} (P : A -> Prop) (xa yb : sig P) (H : xa = yb) :
  eq_rec (proj1_sig xa) P (proj2_sig xa) (proj1_sig yb) (sig_eq_1 P xa yb H) = proj2_sig yb.
Proof.
  subst xa.
  reflexivity.
Defined.

Definition exist_eq_1 {A} (P : A -> Prop) x y a b : exist P x a = exist P y b -> x = y.
Proof.
  apply (f_equal (@proj1_sig A P)).
Defined.

Definition exist_eq_2 {A} (P : A -> Prop) x y a b (H : exist P x a = exist P y b ) :
  eq_rec x P a y (exist_eq_1 P x y a b H) = b.
Proof.
  apply (sig_eq_2 P (exist P x a) (exist P y b)).
Defined.

Definition exist_eq_3 {A} (P : A -> Prop) x y a b :
  exist P x a = exist P y b ->
  sig (fun H : x = y => eq_rec x P a y H = b).
Proof.
  intro H.
  exists (exist_eq_1 P x y a b H).
  apply exist_eq_2.
Defined.
