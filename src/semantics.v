(* Oprational semantics of the Michelson language *)

Require Import syntax.
Require Import ZArith.
Require Import String.
Require NPeano.

Require Import comparable error.
Import syntax.

Section semantics.

  Parameter nd : node.

  (* The gas argument is used to ensure termination, it is not the
  amount of gas that is actually required to run the contract because
  in the SEQ case, both instructions are run with gas n *)
  Fixpoint eval {A : stack_type} {B : stack_type}
           (i : instruction A B) (fuel : Datatypes.nat) {struct fuel} :
    stack A -> M (stack B) :=
    match fuel with
    | O => fun SA => Failed _ Out_of_fuel
    | S n =>
      match i in instruction A B return stack A -> M (stack B) with
      | @FAILWITH A B a =>
        fun xS =>
          let (x, S) := xS in
          Failed _ (Assertion_Failure (data a) x)

      (* According to the documentation, FAILWITH's argument should
         not be part of the state reached by the instruction but the
         whole point of this instruction (compared to the FAIL macro)
         is to report the argument to the user. *)

      | NOOP => fun SA => Return _ SA
      | SEQ B C =>
        fun SA => bind (eval C n) (eval B n SA)
      | IF_ bt bf =>
        fun SbA =>
          let (b, SA) := SbA in
          if b then eval bt n SA else eval bf n SA
      | LOOP body =>
        fun SbA =>
          let (b, SA) := SbA in
          if b then eval (SEQ body (LOOP body)) n SA else Return _ SA
      | LOOP_LEFT body =>
        fun SabA =>
          let (ab, SA) := SabA in
          match ab return M (stack (_ ::: _)) with
          | inl x => eval (SEQ body (LOOP_LEFT body)) n (x, SA)
          | inr y => Return _ (y, SA)
          end
      | DIP i =>
        fun SbA =>
          let (y, SA) := SbA in
          bind (fun SC => Return _ (y, SC)) (eval i n SA)
      | EXEC =>
        fun SxfA =>
          match SxfA return M (stack (_ ::: _)) with
          | (x, (f, SA)) =>
            bind (fun y =>
                    Return _ (y, SA))
                 (f x)
          end
      | DROP =>
        fun SxA =>
          let (x, SA) := SxA in
          Return _ SA
      | DUP =>
        fun SxA =>
          let (x, SA) := SxA in
          Return _ (x, (x, SA))
      | SWAP =>
        fun SxyA =>
          let (x, SyA) := SxyA in
          let (y, SA) := SyA in
          Return _ (y, (x, SA))
      | PUSH a x => fun SA => Return _ (x, SA)
      | UNIT => fun SA => Return _ (tt, SA)
      | LAMBDA a b code =>
        fun SA =>
          Return _ (fun x : data a =>
                       @bind
                         (stack (b ::: nil))
                         (data b)
                         (fun SB =>
                            let (y, tt) := SB in
                            Return _ y)
                         (eval code n (x, tt)), SA)
      | EQ =>
        fun SxA =>
          let (x, SA) := SxA in
          Return _ ((x =? 0)%Z, SA)
      | NEQ =>
        fun SxA =>
          let (x, SA) := SxA in
          Return _ (negb (x =? 0)%Z, SA)
      | LT =>
        fun SxA =>
          let (x, SA) := SxA in
          Return _ ((x <? 0)%Z, SA)
      | GT =>
        fun SxA =>
          let (x, SA) := SxA in
          Return _ ((x >? 0)%Z, SA)
      | LE =>
        fun SxA =>
          let (x, SA) := SxA in
          Return _ ((x <=? 0)%Z, SA)
      | GE =>
        fun SxA =>
          let (x, SA) := SxA in
          Return _ ((x >=? 0)%Z, SA)
      | @OR b s _ =>
        fun SxyA =>
          let (x, SyA) := SxyA in
          let (y, SA) := SyA in
          bind (fun r => Return _ (r, SA))
               (@bitwise.or b s x y)
      | @AND b s _ =>
        fun SxyA =>
          let (x, SyA) := SxyA in
          let (y, SA) := SyA in
          bind (fun r => Return _ (r, SA))
               (@bitwise.and b s x y)
      | @XOR b s _ =>
        fun SxyA =>
          let (x, SyA) := SxyA in
          let (y, SA) := SyA in
          bind (fun r => Return _ (r, SA))
               (@bitwise.xor b s x y)
      | NOT =>
        fun SxA =>
          let (x, SA) := SxA in
          bind (fun r => Return _ (r, SA))
               (not.not _ x)
      | @NEG b s _ =>
        fun SxA =>
          let (x, SA) := SxA in
          bind (fun r => Return _ (r, SA))
               (@neg.op b s x)
      | ABS =>
        fun SxA =>
          let (x, SA) := SxA in
          Return _ (Z.abs_N x, SA)
      | ADD =>
        fun SxyA =>
          let (x, SyA) := SxyA in
          let (y, SA) := SyA in
          bind (fun r => Return _ (r, SA))
               (add.op _ _ x y)
      | SUB =>
        fun SxyA =>
          let (x, SyA) := SxyA in
          let (y, SA) := SyA in
          bind (fun r => Return _ (r, SA))
               (sub.op _ _ x y)
      | MUL =>
        fun SxyA =>
          let (x, SyA) := SxyA in
          let (y, SA) := SyA in
          bind (fun r => Return _ (r, SA))
               (mul.op _ _ x y)
      | EDIV =>
        fun SxyA =>
          let (x, SyA) := SxyA in
          let (y, SA) := SyA in
          bind (fun r => Return _ (r, SA))
               (ediv.op _ _ x y)
      | LSL =>
        fun SxyA =>
          let (x, SyA) := SxyA in
          let (y, SA) := SyA in
          Return _ (N.shiftl x y, SA)
      | LSR =>
        fun SxyA =>
          let (x, SyA) := SxyA in
          let (y, SA) := SyA in
          Return _ (N.shiftr x y, SA)
      | COMPARE =>
        fun SxyA =>
          let (x, SyA) := SxyA in
          let (y, SA) := SyA in
          Return _ (comparison_to_int (compare _ x y), SA)
      | @CONCAT _ _ i =>
        fun SxyA =>
          let (x, SyA) := SxyA in
          let (y, SA) := SyA in
          bind (fun r => Return _ (r, SA))
               (@string_like.concat _ i x y)
      | @SLICE _ _ i =>
        fun SabcA =>
          match SabcA with
            (a, (b, (c, SA))) =>
            bind (fun r => Return _ (r, SA))
                 (@string_like.slice _ i a b c)
          end
      | PAIR =>
        fun SxyA =>
          let (x, SyA) := SxyA in
          let (y, SA) := SyA in
          Return _ ((x, y), SA)
      | CAR =>
        fun SxyA =>
          let (xy, SA) := SxyA in
          let (x, y) := xy in
          Return _ (x, SA)
      | CDR =>
        fun SxyA =>
          let (xy, SA) := SxyA in
          let (x, y) := xy in
          Return _ (y, SA)
      | EMPTY_SET a =>
        fun SA => Return _ (set.empty _ (compare a), SA)
      | MEM =>
        fun SxyA =>
          let (x, SyA) := SxyA in
          let (y, SA) := SyA in
          bind (fun r => Return _ (r, SA))
               (mem.op _ _ _ x y)
      | UPDATE =>
        fun SxyzA =>
          let (x, SyzA) := SxyzA in
          let (y, SzA) := SyzA in
          let (z, SA) := SzA in
          bind (fun r => Return _ (r, SA))
               (update.op _ _ _ x y z)
      | ITER_set body =>
        fun SxA =>
          let (x, SA) := SxA in
          match set.destruct _ _ x with
          | None => Return _ SA
          | Some (a, y) =>
            bind (fun SB =>
                    eval (ITER_set body) n (y, SB))
                 (eval body n (a, SA))
          end
      | SIZE =>
        fun SxA =>
          let (x, SA) := SxA in
          bind (fun r => Return _ (r, SA))
               (@size.op data _ x)
      | EMPTY_MAP k val =>
        fun SA => Return _ (map.empty (comparable_data k) (data val) _, SA)
      | GET =>
        fun SxyA =>
          let (x, SyA) := SxyA in
          let (y, SA) := SyA in
          bind (fun r => Return _ (r, SA))
               (get.op _ _ _ x y)
      | MAP_map_body body =>
        fun SxA =>
          let (x, SA) := SxA in
          match set.destruct _ _ x with
          | None => Return _ (map.empty _ _ _, SA)
          | Some (a, y) =>
            let (k, _) := a in
            bind (fun SbB : data _ * _ =>
                    let (b, SB) := SbB in
                    bind (fun ScC : data (map _ _) * _ =>
                            let (c, SC) := ScC in
                            Return _ (map.update _ _ _ (compare_eq_iff _) (lt_trans _) (gt_trans _) k (Some b) c, SC))
                         (eval (MAP_map_body body) n (y, SB)))
                 (eval body n (a, SA))
          end
      | ITER_map body =>
        fun SxA =>
          let (x, SA) := SxA in
          match set.destruct _ _ x with
          | None => Return _ SA
          | Some (a, y) =>
            bind (fun SB =>
                    eval (ITER_map body) n (y, SB))
                 (eval body n (a, SA))
          end
      | SOME =>
        fun SxA =>
          let (x, SA) := SxA in
          Return _ (Some x, SA)
      | NONE _ =>
        fun SA =>
          Return _ (None, SA)
      | IF_NONE bt bf =>
        fun SbA =>
          match SbA with
          | (None, SA) => eval bt n SA
          | (Some b, SA) => eval bf n (b, SA)
          end
      | LEFT _ =>
        fun SxA =>
          let (x, SA) := SxA in
          Return _ (inl x, SA)
      | RIGHT _ =>
        fun SxA =>
          let (x, SA) := SxA in
          Return _ (inr x, SA)
      | IF_LEFT bt bf =>
        fun SbA =>
          match SbA with
          | (inl a, SA) => eval bt n (a, SA)
          | (inr b, SA) => eval bf n (b, SA)
          end
      | IF_RIGHT bt bf =>
        fun SbA =>
          match SbA with
          | (inl a, SA) => eval bf n (a, SA)
          | (inr b, SA) => eval bt n (b, SA)
          end
      | CONS =>
        fun SxyA =>
          let (x, SyA) := SxyA in
          let (y, SA) := SyA in
          Return _ (cons x y, SA)
      | NIL _ =>
        fun SA =>
          Return _ (nil, SA)
      | IF_CONS bt bf =>
        fun SbA =>
          match SbA with
          | (cons a b, SA) => eval bt n (a, (b, SA))
          | (nil, SA) => eval bf n SA
          end
      | MAP_list_body body =>
        fun SxA =>
          let (x, SA) := SxA in
          match x with
          | nil => Return _ (nil, SA)
          | cons a y =>
            bind (fun SbB : data _ * _ =>
                    let (b, SB) := SbB in
                    bind (fun ScC : data (list_ _) * _ =>
                            let (c, SC) := ScC in
                            Return _ (cons b c, SC))
                         (eval (MAP_list_body body) n (y, SB)))
                 (eval body n (a, SA))
          end
      | ITER_list body =>
        fun SxA =>
          let (x, SA) := SxA in
          match x with
          | nil => Return _ SA
          | cons a y =>
            bind (fun SB =>
                    eval (ITER_list body) n (y, SB))
                 (eval body n (a, SA))
          end
      | CREATE_CONTRACT =>
        fun SabcdefgA =>
          match SabcdefgA with
          | (a, (b, (c, (d, (e, (f, (g, SA))))))) =>
            bind (fun r : data operation * data address =>
                    let (a, b) := r in Return _ (a, (b, SA)))
                 (create_contract nd _ _ a b c d e f g)
          end
      | CREATE_CONTRACT_literal _ _ f =>
        fun SabcdegA =>
          let ff := fun p =>
                      bind (fun SxA =>
                              match SxA with (x, tt) => Return _ x end)
                           (eval f n (p, tt))
          in
          match SabcdegA with
          | (a, (b, (c, (d, (e, (g, SA)))))) =>
            bind (fun r : data operation * data address =>
                     let (a, b) := r in Return _ (a, (b, SA)))
                 (create_contract nd _ _ a b c d e ff g)
          end
      | CREATE_ACCOUNT =>
        fun SabcdA =>
          match SabcdA with
          | (a, (b, (c, (d, SA)))) =>
            bind (fun r : data _ * data _ =>
                     let (a, b) := r in Return _ (a, (b, SA)))
                 (create_account nd a b c d)
          end
      | TRANSFER_TOKENS =>
        fun SabcdA =>
          match SabcdA with
          | (a, (b, (c, SA))) =>
            bind (fun r => Return _ (r, SA))
                 (transfer_tokens nd _ a b c)
          end
      | SET_DELEGATE =>
        fun SxA =>
          let (x, SA) := SxA in
          bind (fun r => Return _ (r, SA))
               (set_delegate nd x)
      | BALANCE => fun SA => bind (fun r => Return _ (r, SA)) (balance nd)
      | ADDRESS =>
        fun SxA =>
          let (x, SA) := SxA in
          bind (fun r => Return _ (r, SA))
               (address_ nd _ x)
      | CONTRACT _ =>
        fun SxA =>
          let (x, SA) := SxA in
          bind (fun r => Return _ (r, SA))
               (contract_ nd _ x)
      | SOURCE =>
        fun SA =>
          bind (fun r => Return _ (r, SA))
               (source nd)
      | SENDER =>
        fun SA =>
          bind (fun r => Return _ (r, SA))
               (sender nd)
      | SELF =>
        fun SA =>
          bind (fun r => Return _ (r, SA))
               (self nd _)
      | AMOUNT => fun SA => bind (fun r => Return _ (r, SA)) (amount nd)
      | IMPLICIT_ACCOUNT =>
        fun SxA =>
          let (x, SA) := SxA in
          bind (fun r => Return _ (r, SA))
               (implicit_account nd x)
      | STEPS_TO_QUOTA =>
        fun SA =>
          bind (fun r => Return _ (r, SA))
               (steps_to_quota nd)
      | NOW => fun SA => bind (fun r => Return _ (r, SA)) (now nd)
      | PACK => fun SxA => let (x, SA) := SxA in
                           bind (fun r => Return _ (r, SA)) (pack nd _ x)
      | UNPACK => fun SxA => let (x, SA) := SxA in
                             bind (fun r => Return _ (r, SA)) (unpack nd _ x)
      | HASH_KEY =>
        fun SxA =>
          let (x, SA) := SxA in
          bind (fun r => Return _ (r, SA))
               (hash_key nd x)
      | BLAKE2B =>
        fun SxA =>
          let (x, SA) := SxA in
          bind (fun r => Return _ (r, SA))
               (blake2b nd x)
      | SHA256 =>
        fun SxA =>
          let (x, SA) := SxA in
          bind (fun r => Return _ (r, SA))
               (sha256 nd x)
      | SHA512 =>
        fun SxA =>
          let (x, SA) := SxA in
          bind (fun r => Return _ (r, SA))
               (sha512 nd x)
      | CHECK_SIGNATURE =>
        fun SxyzA =>
          let (x, SyzA) := SxyzA in
          let (y, SzA) := SyzA in
          let (z, SA) := SzA in
          bind (fun r => Return _ (r, SA))
               (check_signature nd x y z)
      end
    end.
End semantics.
