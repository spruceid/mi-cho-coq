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

Require Import syntax.
Require Import comparable.

Module Macros(ST:SelfType)(C:ContractContext).

Module syntax := Syntax ST C.
Export syntax.

Definition CMPEQ {a : comparable_type} {S} :
  instruction (a ::: a ::: S) (bool ::: S) := COMPARE ;; EQ.
Definition CMPNEQ {a : comparable_type} {S} :
  instruction (a ::: a ::: S) (bool ::: S) := COMPARE ;; NEQ.
Definition CMPLT {a : comparable_type} {S} :
  instruction (a ::: a ::: S) (bool ::: S) := COMPARE ;; LT.
Definition CMPGT {a : comparable_type} {S} :
  instruction (a ::: a ::: S) (bool ::: S) := COMPARE ;; GT.
Definition CMPLE {a : comparable_type} {S} :
  instruction (a ::: a ::: S) (bool ::: S) := COMPARE ;; LE.
Definition CMPGE {a : comparable_type} {S} :
  instruction (a ::: a ::: S) (bool ::: S) := COMPARE ;; GE.

Definition IFEQ {SA SB} (bt bf : instruction SA SB) := EQ ;; IF_ bt bf.
Definition IFNEQ {SA SB} (bt bf : instruction SA SB) := NEQ ;; IF_ bt bf.
Definition IFLT {SA SB} (bt bf : instruction SA SB) := LT ;; IF_ bt bf.
Definition IFGT {SA SB} (bt bf : instruction SA SB) := GT ;; IF_ bt bf.
Definition IFLE {SA SB} (bt bf : instruction SA SB) := LE ;; IF_ bt bf.
Definition IFGE {SA SB} (bt bf : instruction SA SB) := GE ;; IF_ bt bf.

Definition IFCMPEQ {a : comparable_type} {SA SB} bt bf :
  instruction (a ::: a ::: SA) SB := COMPARE ;; EQ ;; IF_ bt bf.
Definition IFCMPNEQ {a : comparable_type} {SA SB} bt bf :
  instruction (a ::: a ::: SA) SB := COMPARE ;; NEQ ;; IF_ bt bf.
Definition IFCMPLT {a : comparable_type} {SA SB} bt bf :
  instruction (a ::: a ::: SA) SB := COMPARE ;; LT ;; IF_ bt bf.
Definition IFCMPGT {a : comparable_type} {SA SB} bt bf :
  instruction (a ::: a ::: SA) SB := COMPARE ;; GT ;; IF_ bt bf.
Definition IFCMPLE {a : comparable_type} {SA SB} bt bf :
  instruction (a ::: a ::: SA) SB := COMPARE ;; LE ;; IF_ bt bf.
Definition IFCMPGE {a : comparable_type} {SA SB} bt bf :
  instruction (a ::: a ::: SA) SB := COMPARE ;; GE ;; IF_ bt bf.

Definition FAIL {SA SB} : instruction SA SB := UNIT ;; FAILWITH.

Definition ASSERT {S} : instruction (bool ::: S) S := IF_ NOOP FAIL.

Definition ASSERT_EQ {S} : instruction (int ::: S) S := IFEQ NOOP FAIL.
Definition ASSERT_NEQ {S} : instruction (int ::: S) S := IFNEQ NOOP FAIL.
Definition ASSERT_LT {S} : instruction (int ::: S) S := IFLT NOOP FAIL.
Definition ASSERT_GT {S} : instruction (int ::: S) S := IFGT NOOP FAIL.
Definition ASSERT_LE {S} : instruction (int ::: S) S := IFLE NOOP FAIL.
Definition ASSERT_GE {S} : instruction (int ::: S) S := IFGE NOOP FAIL.

Definition ASSERT_CMPEQ {a : comparable_type} {S} :
  instruction (a ::: a ::: S) S := IFCMPEQ NOOP FAIL.
Definition ASSERT_CMPNEQ {a : comparable_type} {S} :
  instruction (a ::: a ::: S) S := IFCMPNEQ NOOP FAIL.
Definition ASSERT_CMPLT {a : comparable_type} {S} :
  instruction (a ::: a ::: S) S := IFCMPLT NOOP FAIL.
Definition ASSERT_CMPGT {a : comparable_type} {S} :
  instruction (a ::: a ::: S) S := IFCMPGT NOOP FAIL.
Definition ASSERT_CMPLE {a : comparable_type} {S} :
  instruction (a ::: a ::: S) S := IFCMPLE NOOP FAIL.
Definition ASSERT_CMPGE {a : comparable_type} {S} :
  instruction (a ::: a ::: S) S := IFCMPGE NOOP FAIL.

Definition ASSERT_NONE {a S} : instruction (option a ::: S) S :=
  IF_NONE NOOP FAIL.

Definition ASSERT_SOME {a S} : instruction (option a ::: S) (a ::: S) :=
  IF_NONE FAIL NOOP.

Definition ASSERT_LEFT {a b S} : instruction (or a b ::: S) (a ::: S) :=
  IF_LEFT NOOP FAIL.
Definition ASSERT_RIGHT {a b S} : instruction (or a b ::: S) (b ::: S) :=
  IF_LEFT FAIL NOOP.


Definition DIIP {a b SA SB} code : instruction (a ::: b ::: SA) (a ::: b ::: SB) :=
  DIP (DIP code).
Definition DIIIP {a b c SA SB} code :
  instruction (a ::: b ::: c ::: SA) (a ::: b ::: c ::: SB) :=
  DIP (DIIP code).
Definition DIIIIP {a b c d SA SB} code :
  instruction (a ::: b ::: c ::: d ::: SA) (a ::: b ::: c ::: d ::: SB) :=
  DIP (DIIIP code).

Definition DUUP {a b S} : instruction (a ::: b ::: S) (b ::: a ::: b ::: S) :=
  DIP DUP ;; SWAP.
Definition DUUUP {a b c S} : instruction (a ::: b ::: c ::: S) (c ::: a ::: b ::: c ::: S) :=
  DIP DUUP ;; SWAP.
Definition DUUUUP {a b c d S} : instruction (a ::: b ::: c ::: d ::: S) (d ::: a ::: b ::: c ::: d ::: S) :=
  DIP DUUUP ;; SWAP.

(* Missing: PAPPAIIR and such *)

Definition UNPAIR {a b S} : instruction (pair a b ::: S) (a ::: b ::: S) :=
  DUP ;; CAR ;; DIP CDR.

Definition CAAR {a b c S} : instruction (pair (pair a b) c ::: S) (a ::: S) :=
  CAR ;; CAR.

Definition CADR {a b c S} : instruction (pair (pair a b) c ::: S) (b ::: S) :=
  CAR ;; CDR.

Definition CDAR {a b c S} : instruction (pair a (pair b c) ::: S) (b ::: S) :=
  CDR ;; CAR.

Definition CDDR {a b c S} : instruction (pair a (pair b c) ::: S) (c ::: S) :=
  CDR ;; CDR.

Definition IF_SOME {a SA SB} bt bf : instruction (option a ::: SA) SB :=
  IF_NONE bf bt.

Definition SET_CAR {a b S} : instruction (pair a b ::: a ::: S) (pair a b ::: S) :=
  CDR ;; SWAP ;; PAIR.

Definition SET_CDR {a b S} : instruction (pair a b ::: b ::: S) (pair a b ::: S) :=
  CAR ;; PAIR.

Definition MAP_CAR {a1 a2 b S} (code : instruction (a1 ::: S) (a2 ::: S)) :
  instruction (pair a1 b ::: S) (pair a2 b ::: S) :=
  DUP ;; CDR ;; DIP (CAR ;; code) ;; SWAP ;; PAIR.

Definition MAP_CDR {a b1 b2 S} (code : instruction (b1 ::: pair a b1 ::: S) (b2 ::: pair a b1 ::: S)) :
  instruction (pair a b1 ::: S) (pair a b2 ::: S) :=
  DUP ;; CDR ;; code ;; SWAP ;; CAR ;; PAIR.


Definition UNPAPAIR {a b c S} : instruction (pair a (pair b c) :: S) (a ::: b ::: c ::: S) := UNPAIR ;; DIP UNPAIR.
Definition PAPAIR {a b c S} : instruction (a ::: b ::: c ::: S) (pair a (pair b c) :: S) := DIP PAIR;; PAIR.

End Macros.
