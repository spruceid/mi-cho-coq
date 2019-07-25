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

Inductive exception : Set :=
| Out_of_fuel
| Overflow
| Assertion_Failure (_ : String.string)
| Lexing (_ : location)
| Parsing
| Parsing_Out_of_Fuel
| Expansion (_ _ : location)
| Typing.

Inductive M (A : Type) : Type :=
| Failed : exception -> M A
| Return : A -> M A.

Lemma exception_dec (x y : exception) : {x = y} + {x <> y}.
Proof.
  generalize String.string_dec location_dec.
  decide equality.
Qed.

Lemma M_dec {A} :
  (forall x y : A, {x = y} + {x <> y}) ->
  forall x y : M A, {x = y} + {x <> y}.
Proof.
  intros H x y.
  generalize exception_dec.
  decide equality.
Qed.

Definition bind {A B} (f : A -> M B) (m : M A) :=
  match m with
  | Failed _ e => Failed B e
  | Return _ SB => f SB
  end.

Definition try {A} (m1 m2 : M A) : M A :=
  match m1 with
  | Failed _ _ => m2
  | Return _ _ => m1
  end.

Definition success {A} (m : M A) :=
  match m with
  | Failed _ _ => false
  | Return _ _ => true
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

Lemma IT_eq (b : bool) : b -> b = true.
Proof.
  destruct b; auto.
Qed.

Lemma IT_eq_rev (b : bool) : b = true -> b.
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
  | Return _ x => fun 'I => x
  | Failed _ _ => fun H => match H with end
  end.

Definition IT_if {A : Type} (b : bool) (th : b -> A) (els : A) : A :=
  (if b as b0 return b = b0 -> A then
     fun H => th (IT_eq_rev _ H)
   else fun _ => els) eq_refl.

Lemma success_bind {A B} (f : A -> M B) m :
  success (bind f m) ->
  exists x, m = Return _ x /\ success (f x).
Proof.
  destruct m.
  - contradiction.
  - intro H.
    exists a.
    auto.
Qed.

Lemma success_eq_return A x m :
  m = Return A x -> success m.
Proof.
  intro He.
  rewrite He.
  exact I.
Qed.

Lemma success_bind_arg {A B} (f : A -> M B) m :
  success (bind f m) ->
  success m.
Proof.
  intro H.
  apply success_bind in H.
  destruct H as (x, (H, _)).
  apply success_eq_return in H.
  exact H.
Qed.

Lemma success_eq_return_rev A m :
  success m -> exists x, m = Return A x.
Proof.
  destruct m.
  - contradiction.
  - exists a.
    reflexivity.
Qed.

Lemma bind_eq_return {A B} f m b :
  bind f m = Return B b ->
  exists a : A, m = Return A a /\ f a = Return B b.
Proof.
  destruct m.
  - discriminate.
  - simpl.
    exists a.
    auto.
Qed.


Definition precond {A} (m : M A) p :=
  match m with
  | Failed _ _ => is_true false
  | Return _ a => p a
  end.

Lemma success_precond {A} (m : M A) : is_true (success m) = precond m (fun _ => is_true true).
Proof.
  destruct m; reflexivity.
Qed.

Definition precond_ex {A} (m : M A) p := exists a, m = Return _ a /\ p a.

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
  precond (bind f m) p = precond m (fun a => precond (f a) p).
Proof.
  destruct m; reflexivity.
Qed.

Lemma return_precond {A} (m : M A) a :
  m = Return A a <-> precond m (fun x => x = a).
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
