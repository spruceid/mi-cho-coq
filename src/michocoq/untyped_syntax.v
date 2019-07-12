Require syntax.
Require Import ZArith String.

Definition type := syntax.type.
Definition comparable_type := syntax.comparable_type.


Inductive instruction : Set :=
| NOOP : instruction
| FAILWITH : instruction
| SEQ : instruction -> instruction -> instruction
| IF_ : instruction -> instruction -> instruction
| LOOP : instruction -> instruction
| LOOP_LEFT : instruction -> instruction
| EXEC : instruction
| APPLY : instruction
| DUP : instruction
| SWAP : instruction
| PUSH : syntax.type -> concrete_data -> instruction
| UNIT : instruction
| LAMBDA : syntax.type -> syntax.type -> instruction -> instruction
| EQ : instruction
| NEQ : instruction
| LT : instruction
| GT : instruction
| LE : instruction
| GE : instruction
| OR : instruction
| AND : instruction
| XOR : instruction
| NOT : instruction
| NEG : instruction
| ABS : instruction
| INT : instruction
| ISNAT : instruction
| ADD : instruction
| SUB : instruction
| MUL : instruction
| EDIV : instruction
| LSL : instruction
| LSR : instruction
| COMPARE : instruction
| CONCAT : instruction
| SIZE : instruction
| SLICE : instruction
| PAIR : instruction
| CAR : instruction
| CDR : instruction
| EMPTY_SET : comparable_type -> instruction
| MEM : instruction
| UPDATE : instruction
| ITER : instruction -> instruction
| EMPTY_MAP : comparable_type -> type -> instruction
| GET : instruction
| MAP : instruction -> instruction
| SOME : instruction
| NONE : type -> instruction
| IF_NONE : instruction -> instruction -> instruction
| LEFT : type -> instruction
| RIGHT : type -> instruction
| IF_LEFT : instruction -> instruction -> instruction
| IF_RIGHT : instruction -> instruction -> instruction
| CONS : instruction
| NIL : type -> instruction
| IF_CONS : instruction -> instruction -> instruction
| CREATE_CONTRACT : type -> type -> instruction -> instruction
| TRANSFER_TOKENS : instruction
| SET_DELEGATE : instruction
| BALANCE : instruction
| ADDRESS : instruction
| CONTRACT : type -> instruction
| SOURCE : instruction
| SENDER : instruction
| SELF : instruction
| AMOUNT : instruction
| IMPLICIT_ACCOUNT : instruction
| NOW : instruction
| PACK : instruction
| UNPACK : type -> instruction
| HASH_KEY : instruction
| BLAKE2B : instruction
| SHA256 : instruction
| SHA512 : instruction
| CHECK_SIGNATURE : instruction
| DIG : nat -> instruction
| DUG : nat -> instruction
| DIP : nat -> instruction -> instruction
| DROP : nat -> instruction
| CHAIN_ID : instruction
with
concrete_data : Set :=
| Int_constant : Z -> concrete_data
| Nat_constant : N -> concrete_data
| String_constant : String.string -> concrete_data
| Mutez_constant : syntax.mutez_constant -> concrete_data
| Bytes_constant : String.string -> concrete_data
| Timestamp_constant : Z -> concrete_data
| Signature_constant : String.string -> concrete_data
| Key_constant : String.string -> concrete_data
| Key_hash_constant : String.string -> concrete_data
| Contract_constant : syntax.contract_constant -> concrete_data
| Address_constant : syntax.address_constant -> concrete_data
| Unit : concrete_data
| True_ : concrete_data
| False_ : concrete_data
| Pair : concrete_data -> concrete_data -> concrete_data
| Left : concrete_data -> concrete_data
| Right : concrete_data -> concrete_data
| Some_ : concrete_data -> concrete_data
| None_ : concrete_data
| Elt : concrete_data -> concrete_data -> concrete_data
| Concrete_seq : list concrete_data -> concrete_data
| Instruction : instruction -> concrete_data
| Chain_id_constant : syntax.chain_id_constant -> concrete_data.
