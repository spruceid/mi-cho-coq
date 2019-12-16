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

(** Michelson optimizer working on the untyped syntax *)

Require Import Michocoq.untyped_syntax.
Require Import ZArith.

(* Optimizations *)

Fixpoint visit_instruction
         (F : instruction_seq -> instruction_seq)
         (i : instruction) {struct i} : instruction :=
  match i with
  | DIP n i => DIP n (visit_instruction_seq F i)
  | IF_ f i1 i2 =>
    IF_ f (visit_instruction_seq F i1) (visit_instruction_seq F i2)
  | LOOP_ f i =>
    LOOP_ f (visit_instruction_seq F i)
  | ITER i => ITER (visit_instruction_seq F i)
  | MAP i => MAP (visit_instruction_seq F i)
  | LAMBDA a b i => LAMBDA a b i
  | CREATE_CONTRACT a b an i => CREATE_CONTRACT a b an i
  | PUSH ty x => PUSH ty x
  | FAILWITH => FAILWITH
  | SELF an => SELF an
  | EXEC => EXEC
  | instruction_opcode op => op
  | Instruction_seq i =>
    Instruction_seq (visit_instruction_seq F i)
  end
with
visit_instruction_seq f i {struct i} :=
  match i with
  | NOOP => f NOOP
  | SEQ i1 i2 =>
    let i1' := visit_instruction f i1 in
    let i2' := visit_instruction_seq f i2 in
    f (SEQ i1' i2')
  end.

Definition dig0dug0 :=
  visit_instruction_seq
    (fun i =>
       match i with
       | SEQ (DIG 0) i => i
       | SEQ (DUG 0) i => i
       | SEQ (DROP 0) i => i
       | SEQ (DIP 0 i1) i2 => instruction_app i1 i2
       | SEQ (DIG 1) i => SEQ SWAP i
       | SEQ (DUG 1) i => SEQ SWAP i
       | SEQ (Instruction_seq i1) i2 => instruction_app i1 i2
       | i => i
       end).

Definition digndugn :=
  visit_instruction_seq
    (fun i =>
       match i with
       | SEQ (DIG n1) (SEQ (DUG n2) i') =>
         if (n1 =? n2) then i' else i
       | i => i
       end).

Definition swapswap :=
  visit_instruction_seq
    (fun i =>
       match i with
       | SEQ SWAP (SEQ SWAP i) => i
       | i => i
       end).

Definition push_drop :=
  visit_instruction_seq
    (fun i =>
       match i with
       | SEQ (PUSH _ _) (SEQ (DROP 1) i) => i
       | SEQ (PUSH _ _) (SEQ (DROP (S n)) i) => SEQ (DROP n) i
       | i => i
       end).

(** Clean some stuff in the code *)
Definition cleanup (ins : instruction_seq) : instruction_seq :=
  push_drop
    (swapswap
       (digndugn
          (dig0dug0 ins))).

(** Optimize the code (currently only cleanup of useless instructions *)
Definition optimize := cleanup.
