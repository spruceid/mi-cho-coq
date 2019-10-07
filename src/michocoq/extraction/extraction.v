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
Require Extraction.
Require ExtrOcamlBasic.
Require ExtrOcamlString.

Extract Constant Ascii.ascii_of_pos => "(fun x -> Char.chr (Zarith.to_int x))".


(* Require Import Michocoq.semantics. *)
(* Recursive Extraction Library semantics. *)
Require Import Michocoq.comparable Michocoq.int64bv Michocoq.typer Michocoq.micheline_lexer Michocoq.micheline_parser
Michocoq.micheline2michelson Michocoq.main.
(* Recursive Extraction Library micheline_lexer. *)
(* Recursive Extraction Library micheline_parser. *)

Extract Inlined Constant ascii_compare => "(fun c1 c2 -> if (c1 < c2) then cl else if (c1 > c2) then Gt else Eq)".

Require Import ZArith NArith.

(* Mapping Z to the OCaml library Zarith. *)
Extract Inductive positive =>
"Zarith.t"
  [ "(fun x -> Zarith.add Zarith.one (Zarith.mul (Zarith.add Zarith.one Zarith.one) x))" "(fun x -> Zarith.mul (Zarith.add Zarith.one Zarith.one) x)" "Zarith.one" ]
  "(fun b1 b2 b3 x -> Zarith.(if x = one then b3 () else let (q, r) = ediv_rem x (of_int 2) in if r = zero then b2 q else b1 q))".

Extract Inductive Z =>
"Zarith.t"
  [ "Zarith.zero" "" "Zarith.neg" ]
  "(fun b1 b2 b3 x -> Zarith.(if x > zero then b2 x else if x < zero then b3 x else b1 ()))".

Extract Inductive N => "Zarith.t"
 [ "Zarith.zero" "" ] "(fun b1 b2 x -> Zarith.(if x > zero then b2 x else b1 ()))".

Extract Constant Pos.add => "Zarith.add".
Extract Constant Pos.succ => "Zarith.succ".
Extract Constant Pos.pred => "fun n -> Zarith.(max one (pred n))".
Extract Constant Pos.sub => "fun n m -> Zarith.(max one (sub n m))".
Extract Constant Pos.mul => "Zarith.mul".
Extract Constant Pos.min => "Zarith.min".
Extract Constant Pos.max => "Zarith.max".
Extract Constant Pos.compare =>
 "fun x y -> Zarith.(if x < y then Lt else if x > y then Gt else Eq)".
Extract Constant Pos.compare_cont =>
 "fun c x y -> Zarith.(if x < y then Lt else if x > y then Gt else c)".

Extract Constant N.add => "Zarith.add".
Extract Constant N.succ => "Zarith.succ".
Extract Constant N.pred => "fun n -> Zarith.(max zero (pred n))".
Extract Constant N.sub => "fun n m -> Zarith.(max zero (sub n m))".
Extract Constant N.mul => "Zarith.mul".
Extract Constant N.min => "Zarith.min".
Extract Constant N.max => "Zarith.max".
Extract Constant N.div =>
 "fun a b -> Zarith.(if b = zero then zero else Zarith.div a b)".
Extract Constant N.modulo =>
 "fun a b -> Zarith.(if b = zero then zero else Zarith.rem a b)".
Extract Constant N.compare =>
 "fun x y -> Zarith.(if x < y then Lt else if x > y then Gt else Eq)".

Extract Constant Z.add => "Zarith.add".
Extract Constant Z.succ => "Zarith.succ".
Extract Constant Z.pred => "Zarith.pred".
Extract Constant Z.sub => "Zarith.sub".
Extract Constant Z.mul => "Zarith.mul".
Extract Constant Z.opp => "Zarith.neg".
Extract Constant Z.abs => "Zarith.abs".
Extract Constant Z.min => "Zarith.min".
Extract Constant Z.max => "Zarith.max".
Extract Constant Z.compare => "fun x y -> Zarith.(if x < y then Lt else if x > y then Gt else Eq)".

Extract Constant Z.of_N => "fun p -> p".
Extract Constant Z.abs_N => "Zarith.abs".

Extract Constant Zdigits.Zmod2 => "fun x -> Zarith.ediv x (Zarith.add Zarith.one Zarith.one)".

Extract Inlined Constant int64 => "int64".
Extract Inlined Constant sign => "(fun x -> Int64.compare x 0L < 0)".
Extract Inlined Constant to_Z => "Zarith.of_int64".
Extract Inlined Constant of_Z => "Zarith.to_int64".

Recursive Extraction Library main.

(* Require Import Michocoq.main. *)
(* Recursive Extraction Library main. *)
