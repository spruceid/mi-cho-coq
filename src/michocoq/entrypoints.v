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

Require Import syntax_type.

Inductive entrypoint_tree : Set :=
| ep_leaf (a : type)
| ep_node (a : entrypoint_tree) (_ : annot_o) (b : entrypoint_tree) (_ : annot_o).

Definition opt_bind {A B : Set} (m : Datatypes.option A) (f : A -> Datatypes.option B) : Datatypes.option B :=
  match m with
  | Some a => f a
  | None => None
  end.

Definition opt_merge {A : Set} (m1 m2 : Datatypes.option A) : Datatypes.option A :=
  match m1 with
  | Some a1 => Some a1
  | None => m2
  end.

Fixpoint entrypoint_tree_to_type (ep : entrypoint_tree) : type :=
  match ep with
  | ep_leaf a => a
  | ep_node a _ b _ => or (entrypoint_tree_to_type a) (entrypoint_tree_to_type b)
  end.

Coercion entrypoint_tree_to_type : entrypoint_tree >-> type.

(* Returns [Some a] if the root annotation [an] is exactly [Some e];
   returns [None] otherwise *)
Definition get_entrypoint_root (e : annotation) (a : entrypoint_tree) (an : annot_o) :
  Datatypes.option type :=
  opt_bind an (fun e' => if String.eqb e e' then Some (entrypoint_tree_to_type a) else None).

(* Returns the first entrypoint to match e in the annotated type (a, an).
   The traversal is depth-first *)
Fixpoint get_entrypoint (e : annotation) (a : entrypoint_tree) (an : annot_o) : Datatypes.option type :=
  opt_merge (get_entrypoint_root e a an)
            (match a with
             | ep_node a annot_a b annot_b =>
               opt_merge (get_entrypoint e a annot_a) (get_entrypoint e b annot_b)
             | _ => None
             end).

(* Returns the type of the default entrypoint *)
Definition get_default_entrypoint (a : entrypoint_tree) (an : annot_o) : Datatypes.option type :=
  opt_merge (get_entrypoint default_entrypoint.default a an)
            (Some (entrypoint_tree_to_type a)).

Definition get_entrypoint_opt (e : annot_o) (a : entrypoint_tree) (an : annot_o) : Datatypes.option type :=
  match e with
  | None => get_default_entrypoint a an
  | Some e =>
    if String.eqb e default_entrypoint.default
    then get_default_entrypoint a an
    else get_entrypoint e a an
  end.

