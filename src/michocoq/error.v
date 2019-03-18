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

Record location := Mk_loc { line : nat; column : nat }.

Inductive exception : Prop :=
| Out_of_fuel
| Overflow
| Assertion_Failure (A : Set) (a : A)
| Lexing (_ : location)
| Parsing (_ : location)
| Typing (_ : location).

Inductive M (A : Set) : Set :=
| Failed : exception -> M A
| Return : A -> M A.

Definition bind {A B : Set} (f : A -> M B) (m : M A) :=
  match m with
  | Failed _ e => Failed B e
  | Return _ SB => f SB
  end.

Definition success {A} (m : M A) :=
  match m with
  | Failed _ _ => false
  | Return _ _ => true
  end.

Inductive Is_true : bool -> Prop := ITT : Is_true true.

Coercion is_true := Is_true.

Lemma IT_eq (b : bool) : b -> b = true.
Proof.
  intros [].
  reflexivity.
Qed.

Lemma not_false : ~ false.
Proof.
  intro H.
  apply IT_eq in H.
  discriminate.
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
    destruct (not_false H).
Qed.

Lemma success_bind {A B : Set} (f : A -> M B) m :
  success (bind f m) ->
  exists x, m = Return _ x /\ success (f x).
Proof.
  destruct m; simpl.
  - intro H.
    destruct (not_false H).
  - intro H.
    exists a.
    split.
    + reflexivity.
    + exact H.
Qed.

Lemma success_eq_return A x m :
  m = Return A x -> success m.
Proof.
  intro He.
  rewrite He.
  apply ITT.
Qed.

Lemma success_bind_arg {A B : Set} (f : A -> M B) m :
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
  - intro H.
    destruct (not_false H).
  - exists a.
    reflexivity.
Qed.

Lemma bind_eq_return {A B : Set} f m b :
  bind f m = Return B b ->
  exists a : A, m = Return A a /\ f a = Return B b.
Proof.
  destruct m.
  - discriminate.
  - simpl.
    exists a.
    auto.
Qed.


Definition precond {A : Set} (m : M A) p :=
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
  - intro H; destruct (not_false H).
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
  - intro Hf; destruct (not_false Hf).
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
