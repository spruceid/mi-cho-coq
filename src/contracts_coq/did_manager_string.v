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

Definition did_manager_string : string := "
{ parameter
    (or (address %owner)
        (or (address %auth) (pair %service (string %endpoint) (string %type_)))) ;
  storage
    (pair (pair (big_map %metadata string bytes) (address %owner))
          (pair (pair %service (string %endpoint) (string %type_))
                (address %verification_method))) ;
  code { UNPAIR ;
         SWAP ;
         DUP ;
         DUG 2 ;
         CAR ;
         CDR ;
         SENDER ;
         COMPARE ;
         NEQ ;
         IF { PUSH string ""Unauthorised sender."" ; FAILWITH } {} ;
         PUSH mutez 0 ;
         AMOUNT ;
         COMPARE ;
         GT ;
         IF { PUSH string ""Tez not accepted."" ; FAILWITH } {} ;
         IF_LEFT
           { SWAP ;
             DUP ;
             DUG 2 ;
             CDR ;
             CDR ;
             DIG 2 ;
             DUP ;
             DUG 3 ;
             CDR ;
             CAR ;
             PAIR ;
             SWAP ;
             DIG 2 ;
             CAR ;
             CAR ;
             PAIR ;
             PAIR ;
             NIL operation ;
             PAIR }
           { IF_LEFT
               { SWAP ;
                 DUP ;
                 DUG 2 ;
                 CDR ;
                 CAR ;
                 PAIR ;
                 SWAP ;
                 DUP ;
                 DUG 2 ;
                 CAR ;
                 CDR ;
                 DIG 2 ;
                 CAR ;
                 CAR ;
                 PAIR ;
                 PAIR ;
                 NIL operation ;
                 PAIR }
               { SWAP ;
                 DUP ;
                 DUG 2 ;
                 CDR ;
                 CDR ;
                 SWAP ;
                 PAIR ;
                 SWAP ;
                 DUP ;
                 DUG 2 ;
                 CAR ;
                 CDR ;
                 DIG 2 ;
                 CAR ;
                 CAR ;
                 PAIR ;
                 PAIR ;
                 NIL operation ;
                 PAIR } } } }
".

