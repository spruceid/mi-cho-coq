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

Require main syntax.
Require spending_limit_contract_string spending_limit_contract_definition.

Definition slc_contract_file_m :=
  main.contract_file_M spending_limit_contract_string.slc_contract 500.

Fact slc_contract_well_parsed : error.is_true (error.success slc_contract_file_m).
Proof. exact I. Defined.

Definition dsl_contract_file :=
  Eval cbv in (error.extract slc_contract_file_m slc_contract_well_parsed).


Definition slc_contract_file : syntax.contract_file :=
  syntax.Mk_contract_file spending_limit_contract_definition.parameter_ty
                          None
                          spending_limit_contract_definition.storage_ty
                          Datatypes.false
                          spending_limit_contract_definition.dsl.

Definition dsl_parameter :=
  Eval cbv in syntax.contract_file_parameter dsl_contract_file.

Goal spending_limit_contract_definition.slc_contract_file = dsl_contract_file.
Proof.
  reflexivity.
Qed.
