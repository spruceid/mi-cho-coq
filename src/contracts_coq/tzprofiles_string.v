(* Open Source License *)
(* Copyright (c) 2021 Michael J. Klein, TQ Tezos, Spruce Systems, Inc. *)

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

Require Import String.

Definition tzprofiles_string : string := "
parameter (pair (set (pair (pair string bytes) string)) bool) ;
storage
  (pair (pair (set %claims (pair (pair string bytes) string)) (string %contract_type))
        (pair (big_map %metadata string bytes) (address %owner))) ;
code { UNPAIR ;
       SWAP ;
       DUP ;
       DUG 2 ;
       CDR ;
       CDR ;
       SENDER ;
       COMPARE ;
       NEQ ;
       IF { PUSH string ""Unauthorized."" ; FAILWITH } {} ;
       UNPAIR ;
       DUP 3 ;
       CDR ;
       CDR ;
       DUP 4 ;
       CDR ;
       CAR ;
       PAIR ;
       DUP 4 ;
       CAR ;
       CDR ;
       DIG 4 ;
       CAR ;
       CAR ;
       DIG 3 ;
       ITER { SWAP ; DUP 5 ; DIG 2 ; UPDATE } ;
       DIG 3 ;
       DROP ;
       PAIR ;
       PAIR ;
       NIL operation ;
       PAIR }
".

