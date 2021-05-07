Require syntax.
Require Import ZArith String.
Require Import syntax_type.
Require Import entrypoints.

Inductive opcode : Set :=
| APPLY : opcode
| DUP : opcode
| SWAP : opcode
| UNIT : opcode
| EQ : opcode
| NEQ : opcode
| LT : opcode
| GT : opcode
| LE : opcode
| GE : opcode
| OR : opcode
| AND : opcode
| XOR : opcode
| NOT : opcode
| NEG : opcode
| ABS : opcode
| INT : opcode
| ISNAT : opcode
| ADD : opcode
| SUB : opcode
| MUL : opcode
| EDIV : opcode
| LSL : opcode
| LSR : opcode
| COMPARE : opcode
| CONCAT : opcode
| SIZE : opcode
| SLICE : opcode
| PAIR : opcode
| CAR : opcode
| CDR : opcode
| EMPTY_SET : comparable_type -> opcode
| MEM : opcode
| UPDATE : opcode
| EMPTY_MAP : comparable_type -> type -> opcode
| EMPTY_BIG_MAP : comparable_type -> type -> opcode
| GET : opcode
| SOME : opcode
| NONE : type -> opcode
| LEFT : type -> opcode
| RIGHT : type -> opcode
| CONS : opcode
| NIL : type -> opcode
| TRANSFER_TOKENS : opcode
| SET_DELEGATE : opcode
| BALANCE : opcode
| ADDRESS : opcode
| CONTRACT : annot_o -> type -> opcode
| SOURCE : opcode
| SENDER : opcode
| AMOUNT : opcode
| IMPLICIT_ACCOUNT : opcode
| NOW : opcode
| PACK : opcode
| UNPACK : type -> opcode
| HASH_KEY : opcode
| BLAKE2B : opcode
| SHA256 : opcode
| SHA512 : opcode
| CHECK_SIGNATURE : opcode
| DIG : Datatypes.nat -> opcode
| DUG : Datatypes.nat -> opcode
| DROP : Datatypes.nat -> opcode
| CHAIN_ID : opcode.

Inductive if_family : Set := IF_bool | IF_or | IF_option | IF_list.

Inductive loop_family : Set := LOOP_bool | LOOP_or.

Inductive instruction : Set :=
| Instruction_seq : instruction_seq -> instruction
| FAILWITH : instruction
| IF_ : if_family -> instruction_seq -> instruction_seq -> instruction
| LOOP_ : loop_family -> instruction_seq -> instruction
| PUSH : type -> concrete_data -> instruction
| LAMBDA : type -> type -> instruction_seq -> instruction
| ITER : instruction_seq -> instruction
| MAP : instruction_seq -> instruction
| CREATE_CONTRACT : type -> entrypoint_tree -> annot_o -> instruction_seq -> instruction
| DIP : Datatypes.nat -> instruction_seq -> instruction
| SELF : annot_o -> instruction
| EXEC : instruction
| instruction_opcode : opcode -> instruction
with instruction_seq : Set :=
| NOOP : instruction_seq
| SEQ : instruction -> instruction_seq -> instruction_seq
with
concrete_data : Set :=
| Int_constant : Z -> concrete_data
| String_constant : String.string -> concrete_data
| Bytes_constant : String.string -> concrete_data
| Unit : concrete_data
| True_ : concrete_data
| False_ : concrete_data
| Pair : concrete_data -> concrete_data -> concrete_data
| Left : concrete_data -> concrete_data
| Right : concrete_data -> concrete_data
| Some_ : concrete_data -> concrete_data
| None_ : concrete_data
| Elt : concrete_data -> concrete_data -> concrete_data
| Concrete_seq : Datatypes.list concrete_data -> concrete_data
| Instruction : instruction_seq -> concrete_data.


Coercion instruction_opcode : opcode >-> instruction.

Fixpoint instruction_app i1 i2 :=
  match i1 with
  | NOOP => i2
  | SEQ i11 i12 => SEQ i11 (instruction_app i12 i2)
  end.

Module notations.

Delimit Scope michelson_untyped_scope with michelson_untyped.
Bind Scope michelson_untyped_scope with instruction.
Bind Scope michelson_untyped_scope with instruction_seq.

Notation "A ;;; B" := (instruction_app A B) (at level 100, right associativity).
Notation "A ;; B" := (SEQ A B) (at level 100, right associativity).

Notation "{ }" := NOOP : michelson_untyped_scope.

Notation "{ A ; .. ; B }" := (SEQ A .. (SEQ B NOOP) ..) : michelson_untyped_scope.

Notation "'IF'" := (IF_ IF_bool).
Notation "'IF_LEFT'" := (IF_ IF_or).
Notation "'IF_NONE'" := (IF_ IF_option).
Notation "'IF_CONS'" := (IF_ IF_list).
Notation "'LOOP'" := (LOOP_ LOOP_bool).
Notation "'LOOP_LEFT'" := (LOOP_ LOOP_or).

End notations.
Import notations.

(* Some macros *)
Definition UNPAIR : instruction :=
  Instruction_seq {DUP; CAR; DIP 1 {CDR}}.
Definition UNPAPAIR : instruction :=
  Instruction_seq {UNPAIR; DIP 1 {UNPAIR}}.
