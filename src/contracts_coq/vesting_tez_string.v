(* Open Source License *)
(* Copyright (c) 2020 Michael J. Klein, TQ Tezos *)

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

Definition vesting_tez_s : string := "
parameter (or (option %setDelegate key_hash)
              (nat %vest));
storage (pair (pair %wrapped (address %target)
                             (address %delegateAdmin))
              (pair (nat %vested)
                    (pair %schedule (timestamp %epoch)
                                    (pair (nat %secondsPerTick)
                                          (nat %tokensPerTick)))));
code { DUP;
       CAR;
       DIP { CDR };
       IF_LEFT { SWAP;
                 DUP;
                 DIP { CAR;
                       CDR;
                       SENDER;
                       COMPARE;
                       EQ;
                       IF { DIP { NIL operation };
                            SET_DELEGATE;
                            CONS }
                          { FAILWITH } };
                 SWAP;
                 PAIR }
               { PAIR;
                 DUP;
                 CAR;
                 DIP { CDR;
                       DUP;
                       DIP { CAR };
                       CDR;
                       DUP;
                       DIP { CDR };
                       DUP;
                       CDR;
                       DIP { CAR } };
                 DUP;
                 DIP { DIP { DIP { DUP };
                             DUP;
                             CAR;
                             NOW;
                             SUB;
                             DIP { CDR;
                                   CAR };
                             EDIV;
                             IF_NONE { FAILWITH }
                                     { CAR };
                             SUB;
                             ISNAT };
                       SWAP;
                       IF_NONE { FAILWITH }
                               { DIP { DUP };
                                 SWAP;
                                 COMPARE;
                                 LE;
                                 IF { ADD }
                                    { FAILWITH } };
                       DIP { DUP };
                       SWAP;
                       DIP { PAIR;
                             SWAP;
                             DUP };
                       CDR;
                       CDR };
                 MUL;
                 SWAP;
                 CAR;
                 CONTRACT unit;
                 IF_NONE { FAILWITH }
                         { SWAP;
                           PUSH mutez 1;
                           MUL;
                           UNIT;
                           TRANSFER_TOKENS;
                           DIP { NIL operation };
                           CONS };
                 DIP { PAIR };
                 PAIR } };
".
