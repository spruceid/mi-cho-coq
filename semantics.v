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
           (i : instruction A B) (gas : nat) {struct gas} :
    stack A -> M (stack B) :=
    match gas with
    | O => fun SA => Failed _ Out_of_gas
    | S n =>
      match i in instruction A B return stack A -> M (stack B) with
      | FAIL => fun _ => Failed _ Assertion_Failure
      | SEQ i1 i2 =>
        fun SA => bind (eval i2 n) (eval i1 n SA)
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
      | CONCAT =>
        fun SxyA =>
          let (x, SyA) := SxyA in
          let (y, SA) := SyA in
          Return _ ((x ++ y)%string, SA)
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
      | @REDUCE elt i b _ =>
        fun SxyzA =>
          let (x, SyzA) := SxyzA in
          let (y, SzA) := SyzA in
          let (z, SA) := SzA in
          bind (fun r => Return _ (r, SA))
               (@reduce.op _ i b x y z)
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
      | MAP =>
        fun SxyA =>
          let (x, SyA) := SxyA in
          let (y, SA) := SyA in
          bind (fun r => Return _ (r, SA))
               (MAP.op _ _ _ x y)
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

      | MANAGER =>
        fun SxA =>
          let (x, SA) := SxA in
          bind (fun r => Return _ (r, SA))
               (manager nd _ _ x)
      | CREATE_CONTRACT =>
        fun SabcdefgA =>
          match SabcdefgA with
          | (a, (b, (c, (d, (e, (f, (g, SA))))))) =>
            bind (fun r => Return _ (r, SA))
                 (create_contract nd _ _ _ a b c d e f g)
          end
      | CREATE_CONTRACT_literal _ _ _ f =>
        fun SabcdegA =>
          let ff := fun p =>
                      bind (fun SxA =>
                              match SxA with (x, tt) => Return _ x end)
                           (eval f n (p, tt))
          in
          match SabcdegA with
          | (a, (b, (c, (d, (e, (g, SA)))))) =>
            bind (fun r => Return _ (r, SA))
                 (create_contract nd _ _ _ a b c d e ff g)
          end
      | CREATE_ACCOUNT =>
        fun SabcdA =>
          match SabcdA with
          | (a, (b, (c, (d, SA)))) =>
            bind (fun r => Return _ (r, SA))
                 (create_account nd a b c d)
          end
      | TRANSFER_TOKENS =>
        fun SabcdA =>
          match SabcdA with
          | (a, (b, (c, (d, SA)))) =>
            bind (fun ret : (data _ * data _) => let (s, t) := ret in Return _ (s, (t, SA)))
                 (transfer_tokens nd _ _ _ a b c d)
          end
      | BALANCE => fun SA => bind (fun r => Return _ (r, SA)) (balance nd)
      | SOURCE =>
        fun SA =>
          bind (fun r => Return _ (r, SA))
               (source nd _ _)
      | SELF =>
        fun SA =>
          bind (fun r => Return _ (r, SA))
               (self nd _ _)
      | AMOUNT => fun SA => bind (fun r => Return _ (r, SA)) (amount nd)
      | DEFAULT_ACCOUNT =>
        fun SxA =>
          let (x, SA) := SxA in
          bind (fun r => Return _ (r, SA))
               (default_account nd x)
      | STEPS_TO_QUOTA =>
        fun SA =>
          bind (fun r => Return _ (r, SA))
               (steps_to_quota nd)
      | NOW => fun SA => bind (fun r => Return _ (r, SA)) (now nd)
      | HASH_KEY =>
        fun SxA =>
          let (x, SA) := SxA in
          bind (fun r => Return _ (r, SA))
               (hash_key nd x)
      | H =>
        fun SxA =>
          let (x, SA) := SxA in
          bind (fun r => Return _ (r, SA))
               (h nd _ x)
      | CHECK_SIGNATURE =>
        fun SxyA =>
          let (x, SyA) := SxyA in
          let (y, SA) := SyA in
          bind (fun r => Return _ (r, SA))
               (check_signature nd x y)
      end
    end.
End semantics.
