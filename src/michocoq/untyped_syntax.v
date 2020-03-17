Require syntax.
Require Import ZArith String.
Require Import syntax_type.

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

Inductive instruction : Set :=
| NOOP : instruction
| FAILWITH : instruction
| SEQ : instruction -> instruction -> instruction
| IF_ : instruction -> instruction -> instruction
| LOOP : instruction -> instruction
| LOOP_LEFT : instruction -> instruction
| PUSH : type -> concrete_data -> instruction
| LAMBDA : type -> type -> instruction -> instruction
| ITER : instruction -> instruction
| MAP : instruction -> instruction
| IF_NONE : instruction -> instruction -> instruction
| IF_LEFT : instruction -> instruction -> instruction
| IF_CONS : instruction -> instruction -> instruction
| CREATE_CONTRACT : type -> type -> annot_o -> instruction -> instruction
| DIP : Datatypes.nat -> instruction -> instruction
| SELF : annot_o -> instruction
| EXEC : instruction
| instruction_opcode : opcode -> instruction
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
| Instruction : instruction -> concrete_data.

Coercion instruction_opcode : opcode >-> instruction.

(* Some macros *)
Definition UNPAIR : instruction :=
  SEQ DUP (SEQ CAR (DIP 1 CDR)).
Definition UNPAPAIR : instruction :=
  SEQ UNPAIR (DIP 1 UNPAIR).
