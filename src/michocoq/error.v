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


(* The error monad *)
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

Definition bind {A B : Type} (m : M A) (f : A -> M B) :=
  match m with
  | Failed _ e => Failed B e
  | Return SB => f SB
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

Definition Is_true := Bool.Is_true.

Lemma Is_true_UIP b : forall x y : Is_true b, x = y.
Proof.
  destruct b.
  - intros [] [].
    reflexivity.
  - contradiction.
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
  | Return x => fun 'I => x
  | Failed _ _ => fun H => match H with end
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

Lemma success_eq_return A (x : A) m :
  m = Return x -> success m.
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
