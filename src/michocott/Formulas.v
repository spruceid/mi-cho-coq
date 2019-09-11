Definition typeof (d : data) : type := ty_key.

Definition num_compat (d d' : num) : Prop :=
  typeof (d_Num d) = typeof (d_Num d').

Definition lift_num (rn : nat -> nat -> Prop) (rz : Z -> Z -> Prop) : num -> num -> Prop :=
  fun N1 N2 =>
    match N1, N2 with
      | num_IntConstant z1, num_IntConstant z2 => rz z1 z2
      | num_NatConstant n1, num_NatConstant n2 => rn n1 n2
      | _, _ => False
    end.

Definition lift_num2 (r : forall (A : Type) (_ _ : A), Prop) : (num -> num -> Prop) := lift_num (@r nat) (@r Z).


(* Definition fun_lift_num (rn : nat -> nat -> nat) (rz : Z -> Z -> Z) : num -> num -> option num := *)
(*   fun N1 N2 => *)
(*     match N1, N2 with *)
(*       | num_IntConstant z1, num_IntConstant z2 => Some (num_IntConstant (rz z1 z2)) *)
(*       | num_NatConstant n1, num_NatConstant n2 => Some (num_NatConstant (rn n1 n2)) *)
(*       | _, _ => None *)
(*     end. *)

(* 
 * Definition zaop (op : aop) : (Z -> Z -> Z) :=
 *   match op with
 *   | aop_Add => Z.add
 *   | aop_Sub => Z.sub
 *   | aop_Mul => Z.mul
 *   | aop_Div => Z.divide
 *   | aop_Mod => Z.mod
 *   (* TODO! *)
 *   | aop_Lsl => fun z z' => 0
 *   | aop_Lsr => fun z z' => 0
 *   end.
 * 
 * Definition nataop (op : aop) : (nat -> nat -> nat) :=
 *   match op with
 *   | aop_Add => Nat.add
 *   | aop_Sub => Nat.sub
 *   | aop_Mul => Nat.mul
 *   | aop_Div => Nat.divide
 *   | aop_Mod => Nat.mod
 *   (* TODO! *)
 *   | aop_Lsl => fun nat nat' => 0
 *   | aop_Lsr => fun nat nat' => 0
 *   end.
 *)

Definition num_apply_aop (op : aop) (N1 N2 : num) :=
  match op with
  | aop_Add =>
    match N1, N2 with
    | num_IntConstant z1, num_IntConstant z2 => num_IntConstant (Z.add z1 z2)
    | num_IntConstant z1, num_NatConstant n2 => num_IntConstant (Z.add z1 (Z.of_nat n2))
    | num_NatConstant n1, num_IntConstant z2 => num_IntConstant (Z.add (Z.of_nat n1) z2)
    | num_NatConstant n1, num_NatConstant n2 => num_NatConstant (Nat.add n1 n2)
    end
  | aop_Mul => match N1, N2 with
    | num_IntConstant z1, num_IntConstant z2 => num_IntConstant (Z.mul z1 z2)
    | num_IntConstant z1, num_NatConstant n2 => num_IntConstant (Z.mul z1 (Z.of_nat n2))
    | num_NatConstant n1, num_IntConstant z2 => num_IntConstant (Z.mul (Z.of_nat n1) z2)
    | num_NatConstant n1, num_NatConstant n2 => num_NatConstant (Nat.mul n1 n2)
    end
  | aop_Sub => match N1, N2 with
    | num_IntConstant z1, num_IntConstant z2 => num_IntConstant (Z.sub z1 z2)
    | num_IntConstant z1, num_NatConstant n2 => num_IntConstant (Z.sub z1 (Z.of_nat n2))
    | num_NatConstant n1, num_IntConstant z2 => num_IntConstant (Z.sub (Z.of_nat n1) z2)
    | num_NatConstant n1, num_NatConstant n2 => num_IntConstant (Z.sub (Z.of_nat n1) (Z.of_nat n2))
    end
  (* TODO! *)
  (* 
   * | aop_Div => fun nat nat' => 0
   * | aop_Mod => fun nat nat' => 0
   * | aop_Lsl => fun nat nat' => 0
   * | aop_Lsr => fun nat nat' => 0
   *)
  | _ => num_NatConstant 0
  end.


Definition num_apply_bitop (op : bitop) (N1 N2 : num) : num :=
  match op with
  (* TODO *)
  | bitop_Or => num_NatConstant 0
  | bitop_And => num_NatConstant 0
  | bitop_Xor => num_NatConstant 0
  end.

(* TODO *)
Definition num_bit_neg (N1 : num) : num := N1.

Definition num_neq_zero (N : num) : Prop :=
  match N with
  | num_IntConstant z1 => z1 <> (0 % Z)
  | num_NatConstant n1 => n1 <> (0 % nat)
  end.

Definition num_neg ( N : num ) : num :=
  match N with
  | num_IntConstant z1 => num_IntConstant (- z1)
  | num_NatConstant n1 => num_IntConstant (- (Z.of_nat n1))
  end.

Definition TODO : Prop := False.

(*
 * Definition apply_bop (b : bop) : bool -> bool -> bool :=
 *   match bop with
 *   | bop_Or => orb
 *   | bop_And => andb
 *   | bop_Xor => xorb
 *   end.
 *)

Definition compare x comp y :=
    match x, y with
    | d_Num (num_NatConstant x), d_Num (num_NatConstant y) =>
         match comp with
         | i_EQ => x = y
         | i_NEQ => x <> y
         | i_LT => x < y
         | i_GT => x > y
         | i_LE => x <= y
         | i_GE => x >= y
         end
    | d_Num (num_IntConstant x), d_Num (num_IntConstant y) =>
         match comp with
         | i_EQ => Z.eq x y
         | i_NEQ => x <> y
         | i_LT => Z.lt x y
         | i_GT => Z.gt x y
         | i_LE => Z.le x y
         | i_GE => Z.ge x y
         end
    | _,_ => False (* TODO *)
    end.
