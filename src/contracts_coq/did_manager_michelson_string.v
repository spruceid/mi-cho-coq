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

Definition did_manager_michelson_string : string := "
parameter (or (address %owner) (or (address %auth) (pair %service string string))) ;
storage
  (pair (pair (big_map %metadata string bytes) address)
        (pair (pair string string) address)) ;
code { UNPAIR ;
       SWAP ;
       UNPAIR ;
       UNPAIR ;
       SWAP ;
       DUP ;
       SENDER ;
       COMPARE ;
       EQ ;
       IF { DIG 3 ;
            IF_LEFT
              { SWAP ; DROP ; SWAP }
              { DIG 3 ;
                SWAP ;
                IF_LEFT { SWAP ; CAR } { SWAP ; CDR ; SWAP } ;
                PAIR ;
                DUG 2 ;
                SWAP } ;
            PUSH mutez 0 ;
            AMOUNT ;
            COMPARE ;
            GT ;
            IF { SWAP ; FAILWITH } { PAIR ; PAIR ; NIL operation ; PAIR } }
          { FAILWITH } }
".

