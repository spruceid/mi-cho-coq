(* Open Source License *)
(* Copyright (c) 2020 Nomadic Labs. <contact@nomadic-labs.com> *)

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


(* Manipulation of sequences of bytes *)
Require Import String Ascii ZArith Lia.
Require error.
Import error.Notations.
Require Import ListString.All.

Definition byte := ascii.
Definition bytes := string.

Open Scope N_scope.
Open Scope char_scope.

Definition is_hexa_char (c : ascii) : bool :=
  match c with
  | "0" | "1" | "2" | "3" | "4" | "5" | "6" | "7" | "8" | "9"
  | "a" | "A" | "b" | "B" | "c" | "C" | "d" | "D" | "e" | "E" | "f" | "F" => true
  | _ => false
  end.

Definition read_hexa (c : ascii) : Bool.Is_true (is_hexa_char c) -> N :=
  match c with
  | "0" => fun _ => 0
  | "1" => fun _ => 1
  | "2" => fun _ => 2
  | "3" => fun _ => 3
  | "4" => fun _ => 4
  | "5" => fun _ => 5
  | "6" => fun _ => 6
  | "7" => fun _ => 7
  | "8" => fun _ => 8
  | "9" => fun _ => 9
  | "a" | "A" => fun _ => 10
  | "b" | "B" => fun _ => 11
  | "c" | "C" => fun _ => 12
  | "d" | "D" => fun _ => 13
  | "e" | "E" => fun _ => 14
  | "f" | "F" => fun _ => 15
  | c => fun H => match H with end
  end.

Definition pp_hexa (n : N) (H : n < 16) : ascii :=
  if (n <? 10) then ascii_of_N (n + 48) else ascii_of_N (n + 87).

Lemma arith_aux m n : m < n + 1 <-> m < n \/ m = n.
Proof.
  lia.
Qed.

Lemma arith_aux2 n : n < 1 <-> n = 0.
Proof.
  lia.
Qed.

Lemma is_hexa_pp_hexa n H : Bool.Is_true (is_hexa_char (pp_hexa n H)).
Proof.
  assert (n < 16) as H' by assumption.
  rewrite (arith_aux n 15) in H'.
  rewrite (arith_aux n 14) in H'.
  rewrite (arith_aux n 13) in H'.
  rewrite (arith_aux n 12) in H'.
  rewrite (arith_aux n 11) in H'.
  rewrite (arith_aux n 10) in H'.
  rewrite (arith_aux n 9) in H'.
  rewrite (arith_aux n 8) in H'.
  rewrite (arith_aux n 7) in H'.
  rewrite (arith_aux n 6) in H'.
  rewrite (arith_aux n 5) in H'.
  rewrite (arith_aux n 4) in H'.
  rewrite (arith_aux n 3) in H'.
  rewrite (arith_aux n 2) in H'.
  rewrite (arith_aux n 1) in H'.
  repeat (destruct H' as [H'|He]; [|subst n; constructor]).
  apply arith_aux2 in H'.
  subst n; constructor.
Qed.

Lemma read_pp_hexa n H : read_hexa (pp_hexa n H) (is_hexa_pp_hexa n H) = n.
Proof.
  assert (n < 16) as H' by assumption.
  rewrite (arith_aux n 15) in H'.
  rewrite (arith_aux n 14) in H'.
  rewrite (arith_aux n 13) in H'.
  rewrite (arith_aux n 12) in H'.
  rewrite (arith_aux n 11) in H'.
  rewrite (arith_aux n 10) in H'.
  rewrite (arith_aux n 9) in H'.
  rewrite (arith_aux n 8) in H'.
  rewrite (arith_aux n 7) in H'.
  rewrite (arith_aux n 6) in H'.
  rewrite (arith_aux n 5) in H'.
  rewrite (arith_aux n 4) in H'.
  rewrite (arith_aux n 3) in H'.
  rewrite (arith_aux n 2) in H'.
  rewrite (arith_aux n 1) in H'.
  repeat (destruct H' as [H'|He]; [|subst n; reflexivity]).
  apply arith_aux2 in H'.
  subst n; reflexivity.
Qed.

Lemma read_hexa_lt_16 c H : read_hexa c H < 16.
Proof.
  destruct c as [[|] [|] [|] [|] [|] [|] [|] [|]];
    simpl in H; try contradiction; simpl; lia.
Qed.

Lemma pp_read_hexa c H : pp_hexa (read_hexa c H) (read_hexa_lt_16 c H) = ListString.Char.down_case c.
Proof.
  destruct c as [[|] [|] [|] [|] [|] [|] [|] [|]];
    simpl in H; try contradiction; reflexivity.
Qed.

Definition read_2_hexa c1 H1 c2 H2 : N :=
  let n1 := read_hexa c1 H1 in
  let n2 := read_hexa c2 H2 in
  16 * n1 + n2.

Lemma read_2_hexa_lt_256 c1 H1 c2 H2 : read_2_hexa c1 H1 c2 H2 < 256.
Proof.
  unfold read_2_hexa.
  specialize (read_hexa_lt_16 c1 H1).
  specialize (read_hexa_lt_16 c2 H2).
  lia.
Qed.

Definition high_half (n : N) (H : n < 256) : N := n / 16.
Definition low_half (n : N) (H : n < 256) : N := n mod 16.

Lemma high_lt_16 n H : high_half n H < 16.
Proof.
  apply (N.div_lt_upper_bound n 16 16).
  - lia.
  - exact H.
Qed.

Lemma low_lt_16 n H : low_half n H < 16.
Proof.
  apply N.mod_upper_bound.
  lia.
Qed.

Definition pp_2_hexa (n : N) (H : n < 256) :=
  let h := high_half n H in
  let l := low_half n H in
  let Hh : h < 16 := high_lt_16 n H in
  let Hl : l < 16 := low_lt_16 n H in
  let c1 := pp_hexa h Hh in
  let c2 := pp_hexa l Hl in
  String c1 (String c2 ""%string).

Definition read_byte c1 H1 c2 H2 : byte :=
  ascii_of_N (read_2_hexa c1 H1 c2 H2).

(* This is proved in stdlib but only from Coq 8.10. *)
Lemma N_ascii_bounded (a : ascii) : N_of_ascii a < 256.
Proof.
  destruct a as [[|] [|] [|] [|] [|] [|] [|] [|]]; simpl; lia.
Qed.

Definition pp_byte (b : byte) : string :=
  pp_2_hexa (N_of_ascii b) (N_ascii_bounded b).

Close Scope N_scope.

Fixpoint forallb {A} (P : A -> bool) (l : list A) : bool :=
  match l with
  | nil => true
  | cons a l => (P a && forallb P l)%bool
  end.

(* Redefinition of stdlib lemmas because we need them to compute *)
Definition andb_prop a b : (a && b)%bool = true -> a = true /\ b = true.
Proof.
  destruct a; destruct b; try discriminate; split; reflexivity.
Defined.

Definition andb_prop_elim a b : Bool.Is_true (a && b) -> Bool.Is_true a /\ Bool.Is_true b.
Proof.
  destruct a; destruct b; try contradiction; split; constructor.
Defined.

Fixpoint of_list_char (s : list ascii) (H : Bool.Is_true (forallb is_hexa_char s)) (Hl : (N.of_nat (List.length s) mod 2 = 0)%N) : bytes.
Proof.
  destruct s as [|c1 [|c2 s]].
  - exact ""%string.
  - simpl in Hl.
    compute in Hl.
    exfalso.
    lia.
  - change (Datatypes.length (c1 :: c2 :: s)%list) with (2 + Datatypes.length s) in Hl.
    rewrite Nnat.Nat2N.inj_add in Hl.
    rewrite <- N.add_mod_idemp_l in Hl; [|lia].
    simpl in Hl.
    simpl in H.
    apply andb_prop_elim in H.
    destruct H as (H1, H).
    apply andb_prop_elim in H.
    destruct H as (H2, H).
    apply (String (read_byte c1 H1 c2 H2)).
    apply (of_list_char s H Hl).
Defined.

Definition of_string (s : string) : option bytes.
Proof.
  pose (l := LString.of_string s).
  case_eq (forallb is_hexa_char l && (N.of_nat (List.length l) mod 2 =? 0)%N)%bool.
  - intro Htrue.
    apply andb_prop in Htrue.
    destruct Htrue as (H, Hl).
    apply error.IT_eq_rev in H.
    apply Neqb_ok in Hl.
    apply Some.
    apply (of_list_char l H Hl).
  - intro; apply None.
Defined.

Fixpoint to_string (bs : bytes) : string :=
  match bs with
  | ""%string => ""%string
  | String b bs =>
    pp_byte b ++ to_string bs
  end.

Eval compute in
    (match of_string "0123456789abcdefABCDEF" with
     | Some bs => Some (to_string bs)
     | None => None
     end).

