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

Require Import syntax syntax_type.
Require Import comparable.

Module Macros(C : ContractContext).

Module syntax := Syntax C.
Export syntax.

Section macros.
  Context {self_type : Datatypes.option type}.

Definition CMPop (a : comparable_type) S (op : instruction self_type Datatypes.false (int ::: S) (bool ::: S))
           : instruction self_type Datatypes.false (a ::: a ::: S) (bool ::: S) := COMPARE ;; op.

Definition CMPEQ {a S} := CMPop a S EQ.
Definition CMPNEQ {a S} := CMPop a S NEQ.
Definition CMPLT {a S} := CMPop a S LT.
Definition CMPGT {a S} := CMPop a S GT.
Definition CMPLE {a S} := CMPop a S LE.
Definition CMPGE {a S} := CMPop a S GE.

Definition IFop SA SB tffa tffb
           (bt : instruction self_type tffa SA SB) (bf : instruction self_type tffb SA SB)
           (op : instruction self_type Datatypes.false (int ::: SA) (bool ::: SA)) :=
  op ;; IF_ bt bf.

Definition IFEQ {SA SB tffa tffb} bt bf := IFop SA SB tffa tffb bt bf EQ.
Definition IFNEQ {SA SB tffa tffb} bt bf := IFop SA SB tffa tffb bt bf NEQ.
Definition IFLT {SA SB tffa tffb} bt bf := IFop SA SB tffa tffb bt bf LT.
Definition IFGT {SA SB tffa tffb} bt bf := IFop SA SB tffa tffb bt bf GT.
Definition IFLE {SA SB tffa tffb} bt bf := IFop SA SB tffa tffb bt bf LE.
Definition IFGE {SA SB tffa tffb} bt bf := IFop SA SB tffa tffb bt bf GE.

Definition IFCMPop (a : comparable_type) SA SB tffa tffb
           (bt : instruction self_type tffa SA SB) (bf : instruction self_type tffb SA SB)
           (op : instruction self_type Datatypes.false (int ::: SA) (bool ::: SA)) :
  instruction self_type (tffa && tffb) (a ::: a ::: SA) SB :=
  COMPARE ;; op ;; IF_ bt bf.

Definition IFCMPEQ {a SA SB tffa tffb} bt bf := IFCMPop a SA SB tffa tffb bt bf EQ.
Definition IFCMPNEQ {a SA SB tffa tffb} bt bf := IFCMPop a SA SB tffa tffb bt bf NEQ.
Definition IFCMPLT {a SA SB tffa tffb} bt bf := IFCMPop a SA SB tffa tffb bt bf LT.
Definition IFCMPGT {a SA SB tffa tffb} bt bf := IFCMPop a SA SB tffa tffb bt bf GT.
Definition IFCMPLE {a SA SB tffa tffb} bt bf := IFCMPop a SA SB tffa tffb bt bf LE.
Definition IFCMPGE {a SA SB tffa tffb} bt bf := IFCMPop a SA SB tffa tffb bt bf GE.

Definition FAIL {SA SB} : instruction self_type Datatypes.true SA SB := UNIT ;; FAILWITH.

Definition ASSERT {S} : instruction self_type Datatypes.false (bool ::: S) S := IF_ NOOP FAIL.

Definition ASSERT_op S (op : instruction self_type Datatypes.false (int ::: S) (bool ::: S)) : instruction self_type Datatypes.false (int ::: S) S :=
  IFop _ _ _ _ NOOP FAIL op.

Definition ASSERT_EQ {S} := ASSERT_op S EQ.
Definition ASSERT_NEQ {S} := ASSERT_op S NEQ.
Definition ASSERT_LT {S} := ASSERT_op S LT.
Definition ASSERT_GT {S} := ASSERT_op S GT.
Definition ASSERT_LE {S} := ASSERT_op S LE.
Definition ASSERT_GE {S} := ASSERT_op S GE.

Definition ASSERT_CMPop (a : comparable_type) S (op : instruction self_type Datatypes.false (int ::: S) (bool ::: S))
  : instruction self_type Datatypes.false (a ::: a ::: S) S := IFCMPop _ _ _ _ _ NOOP FAIL op.

Definition ASSERT_CMPEQ {a S} := ASSERT_CMPop a S EQ.
Definition ASSERT_CMPNEQ {a S} := ASSERT_CMPop a S NEQ.
Definition ASSERT_CMPLT {a S} := ASSERT_CMPop a S LT.
Definition ASSERT_CMPGT {a S} := ASSERT_CMPop a S GT.
Definition ASSERT_CMPLE {a S} := ASSERT_CMPop a S LE.
Definition ASSERT_CMPGE {a S} := ASSERT_CMPop a S GE.

Definition ASSERT_NONE {a S} : instruction self_type Datatypes.false (option a ::: S) S :=
  IF_NONE NOOP FAIL.

Definition ASSERT_SOME {a S} : instruction self_type Datatypes.false (option a ::: S) (a ::: S) :=
  IF_NONE FAIL NOOP.

Definition ASSERT_LEFT {a b S} : instruction self_type Datatypes.false (or a b ::: S) (a ::: S) :=
  IF_LEFT NOOP FAIL.
Definition ASSERT_RIGHT {a b S} : instruction self_type Datatypes.false (or a b ::: S) (b ::: S) :=
  IF_LEFT FAIL NOOP.

Definition DROP1 {a SA} : instruction self_type Datatypes.false (a ::: SA) SA :=
  DROP (A := a ::: nil) 1 eq_refl.

Definition DIP1 {a SA SB} code : instruction self_type _ (a ::: SA) (a ::: SB) :=
  DIP (A := (a ::: nil)) 1 eq_refl code.
Definition DIIP {a b SA SB} code : instruction self_type _ (a ::: b ::: SA) (a ::: b ::: SB) :=
  DIP (A := (a ::: b ::: nil)) 2 eq_refl code.
Definition DIIIP {a b c SA SB} code :
  instruction self_type _ (a ::: b ::: c ::: SA) (a ::: b ::: c ::: SB) :=
  DIP (A := (a ::: b ::: c ::: nil)) 3 eq_refl code.
Definition DIIIIP {a b c d SA SB} code :
  instruction self_type _ (a ::: b ::: c ::: d ::: SA) (a ::: b ::: c ::: d ::: SB) :=
  DIP (A := (a ::: b ::: c ::: d ::: nil)) 4 eq_refl code.

Definition DUUP {a b S} : instruction self_type Datatypes.false (a ::: b ::: S) (b ::: a ::: b ::: S) :=
  DIP1 DUP ;; SWAP.

Definition DUPn {A b C} n (H : length A = n) : instruction self_type Datatypes.false (A +++ b ::: C) (b ::: A +++ b ::: C) :=
  DIG n H ;; DUP ;; DIP1 (DUG n H).

Definition DUUUP {a b c S} : instruction self_type Datatypes.false (a ::: b ::: c ::: S) (c ::: a ::: b ::: c ::: S) :=
  DUPn (A := a ::: b ::: nil) 2 eq_refl.

Definition DUUUUP {a b c d S} : instruction self_type Datatypes.false (a ::: b ::: c ::: d ::: S) (d ::: a ::: b ::: c ::: d ::: S) :=
  DUPn (A := a ::: b ::: c ::: nil) 3 eq_refl.

(* Missing: PAPPAIIR and such *)

Definition UNPAIR {a b S} : instruction self_type Datatypes.false (pair a b ::: S) (a ::: b ::: S) :=
  DUP ;; CAR ;; DIP1 CDR.

Definition CAAR {a b c S} : instruction self_type Datatypes.false (pair (pair a b) c ::: S) (a ::: S) :=
  CAR ;; CAR.

Definition CADR {a b c S} : instruction self_type Datatypes.false (pair (pair a b) c ::: S) (b ::: S) :=
  CAR ;; CDR.

Definition CDAR {a b c S} : instruction self_type Datatypes.false (pair a (pair b c) ::: S) (b ::: S) :=
  CDR ;; CAR.

Definition CDDR {a b c S} : instruction self_type Datatypes.false (pair a (pair b c) ::: S) (c ::: S) :=
  CDR ;; CDR.

Definition IF_SOME {a SA SB tffa tffb} (bt : instruction self_type tffa _ _) (bf : instruction self_type tffb _ _) : instruction self_type _ (option a ::: SA) SB :=
  IF_NONE bf bt.

Definition SET_CAR {a b S} : instruction self_type Datatypes.false (pair a b ::: a ::: S) (pair a b ::: S) :=
  CDR ;; SWAP ;; PAIR.

Definition SET_CDR {a b S} : instruction self_type Datatypes.false (pair a b ::: b ::: S) (pair a b ::: S) :=
  CAR ;; PAIR.

Definition MAP_CAR {a1 a2 b S} (code : instruction self_type Datatypes.false (a1 ::: S) (a2 ::: S)) :
  instruction self_type Datatypes.false (pair a1 b ::: S) (pair a2 b ::: S) :=
  DUP ;; CDR ;; DIP1 (CAR ;; code) ;; SWAP ;; PAIR.

Definition MAP_CDR {a b1 b2 S} (code : instruction self_type Datatypes.false (b1 ::: pair a b1 ::: S) (b2 ::: pair a b1 ::: S)) :
  instruction self_type Datatypes.false (pair a b1 ::: S) (pair a b2 ::: S) :=
  DUP ;; CDR ;; code ;; SWAP ;; CAR ;; PAIR.


Definition UNPAPAIR {a b c S} : instruction self_type Datatypes.false (pair a (pair b c) :: S) (a ::: b ::: c ::: S) := UNPAIR ;; DIP1 UNPAIR.
Definition PAPAIR {a b c S} : instruction self_type Datatypes.false (a ::: b ::: c ::: S) (pair a (pair b c) :: S) := DIP1 PAIR;; PAIR.
End macros.
End Macros.
