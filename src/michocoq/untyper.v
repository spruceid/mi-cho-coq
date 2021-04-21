(* Not really needed but eases reading of proof states. *)
Require Import String.
Require Import Ascii.

Require Import ZArith List.
Require Import syntax.
Require Import typer.
Require Import untyped_syntax error.
Require Eqdep_dec.
Import error.Notations.
Require Import Lia.

Inductive untype_mode := untype_Readable | untype_Optimized.

  Definition untype_opcode {self_type A B} (o : @syntax.opcode self_type A B) : opcode :=
    match o with
    | syntax.APPLY => APPLY
    | syntax.DROP n _ => DROP n
    | syntax.DUP => DUP
    | syntax.SWAP => SWAP
    | syntax.UNIT => UNIT
    | syntax.EQ => EQ
    | syntax.NEQ => NEQ
    | syntax.LT => LT
    | syntax.GT => GT
    | syntax.LE => LE
    | syntax.GE => GE
    | syntax.OR => OR
    | syntax.AND => AND
    | syntax.XOR => XOR
    | syntax.NOT => NOT
    | syntax.NEG => NEG
    | syntax.ABS => ABS
    | syntax.INT => INT
    | syntax.ISNAT => ISNAT
    | syntax.ADD => ADD
    | syntax.SUB => SUB
    | syntax.MUL => MUL
    | syntax.EDIV => EDIV
    | syntax.LSL => LSL
    | syntax.LSR => LSR
    | syntax.COMPARE => COMPARE
    | syntax.CONCAT => CONCAT
    | syntax.CONCAT_list => CONCAT
    | syntax.SIZE => SIZE
    | syntax.SLICE => SLICE
    | syntax.PAIR => PAIR
    | syntax.CAR => CAR
    | syntax.CDR => CDR
    | syntax.EMPTY_SET a => EMPTY_SET a
    | syntax.MEM => MEM
    | syntax.UPDATE => UPDATE
    | syntax.EMPTY_MAP kty vty => EMPTY_MAP kty vty
    | syntax.EMPTY_BIG_MAP kty vty => EMPTY_BIG_MAP kty vty
    | syntax.GET => GET
    | syntax.SOME => SOME
    | syntax.NONE a => NONE a
    | syntax.LEFT b => LEFT b
    | syntax.RIGHT a => RIGHT a
    | syntax.CONS => CONS
    | syntax.NIL a => NIL a
    | syntax.TRANSFER_TOKENS => TRANSFER_TOKENS
    | syntax.SET_DELEGATE => SET_DELEGATE
    | syntax.BALANCE => BALANCE
    | syntax.ADDRESS => ADDRESS
    | syntax.CONTRACT an a => CONTRACT an a
    | syntax.SOURCE => SOURCE
    | syntax.SENDER => SENDER
    | syntax.AMOUNT => AMOUNT
    | syntax.IMPLICIT_ACCOUNT => IMPLICIT_ACCOUNT
    | syntax.NOW => NOW
    | syntax.PACK => PACK
    | syntax.UNPACK a => UNPACK a
    | syntax.HASH_KEY => HASH_KEY
    | syntax.BLAKE2B => BLAKE2B
    | syntax.SHA256 => SHA256
    | syntax.SHA512 => SHA512
    | syntax.CHECK_SIGNATURE => CHECK_SIGNATURE
    | syntax.DIG n _ => DIG n
    | syntax.DUG n _ => DUG n
    | syntax.CHAIN_ID => CHAIN_ID
    end.

  Definition untype_if_family {A B t} (f : syntax.if_family A B t) : if_family :=
    match f with
    | syntax.IF_bool => IF_bool
    | syntax.IF_or _ _ _ _ => IF_or
    | syntax.IF_option _ => IF_option
    | syntax.IF_list _ => IF_list
    end.

  Definition untype_loop_family {A B t} (f : syntax.loop_family A B t) : loop_family :=
    match f with
    | syntax.LOOP_bool => LOOP_bool
    | syntax.LOOP_or _ _ _ _ => LOOP_or
    end.

  Definition untype_simple_comparable_data {a : simple_comparable_type} (um : untype_mode) : comparable.comparable_data a -> concrete_data :=
    match a as a return comparable.comparable_data a -> concrete_data with
    | int => Int_constant
    | nat => fun n => Int_constant (Z.of_N n)
    | string => String_constant
    | mutez => fun m => Int_constant (tez.to_Z m)
    | bytes => Bytes_constant
    | timestamp => fun t =>
      match um with
      | untype_Readable =>
        String_constant
          (All.LString.to_string
             (Moment.Print.rfc3339
                (Moment.of_epoch t)))
      | untype_Optimized =>
        Int_constant t
      end
    | key_hash => fun '(comparable.Mk_key_hash s) => String_constant s
    | address => fun c =>
      match c with
      | comparable.Implicit (comparable.Mk_key_hash s) =>
        String_constant (String "t" (String "z" s))
      | comparable.Originated (comparable.Mk_smart_contract_address s) =>
        String_constant (String "K" (String "T" (String "1" s)))
      end
    | bool => fun b => if b then True_ else False_
    end.

  Fixpoint untype_comparable_data {a : comparable_type} (um : untype_mode) (d : comparable.comparable_data a) {struct a} :
    concrete_data :=
    match a return comparable.comparable_data a -> concrete_data with
    | Comparable_type_simple s => untype_simple_comparable_data um
    | Cpair a b => fun '(x, y) =>
      Pair (untype_simple_comparable_data um x) (untype_comparable_data um y)
    end d.

  Fixpoint untype_data {a} (um : untype_mode) (d : syntax.concrete_data a) {struct d}: concrete_data :=
    match d with
    | syntax.Comparable_constant a x => untype_simple_comparable_data um x
    | syntax.Signature_constant s => String_constant s
    | syntax.Key_constant s => String_constant s
    | syntax.Unit => Unit
    | syntax.Pair x y => Pair (untype_data um x) (untype_data um y)
    | syntax.Left x _ _ => Left (untype_data um x)
    | syntax.Right y _ _ => Right (untype_data um y)
    | syntax.Some_ x => Some_ (untype_data um x)
    | syntax.None_ => None_
    | syntax.Concrete_list l => Concrete_seq (List.map (untype_data um) l)
    | syntax.Concrete_set (exist _ l _) =>
      Concrete_seq (List.map (untype_comparable_data um) l)
    | syntax.Concrete_map m =>
      Concrete_seq (
          match m with
          | map.sorted_map_nil _ _ _ => nil
          | map.sorted_map_nonnil _ _ _ k v m =>
            cons
              (Elt (untype_comparable_data um k) (untype_data um v))
              ((fix to_list_above k m :=
                 match m with
                 | map.sorted_map_sing _ _ _ _ => nil
                 | map.sorted_map_cons _ _ _ k1 k2 v2 _ m =>
                   cons
                     (Elt (untype_comparable_data um k2) (untype_data um v2))
                     (to_list_above k2 m)
                 end) k m)
          end)
    | syntax.Concrete_big_map m =>
      Concrete_seq (
          match m with
          | map.sorted_map_nil _ _ _ => nil
          | map.sorted_map_nonnil _ _ _ k v m =>
            cons
              (Elt (untype_comparable_data um k) (untype_data um v))
              ((fix to_list_above k m :=
                 match m with
                 | map.sorted_map_sing _ _ _ _ => nil
                 | map.sorted_map_cons _ _ _ k1 k2 v2 _ m =>
                   cons
                     (Elt (untype_comparable_data um k2) (untype_data um v2))
                     (to_list_above k2 m)
                 end) k m)
          end)
    | syntax.Instruction _ i => Instruction (untype_instruction_seq um i)
    | syntax.Chain_id_constant (comparable.Mk_chain_id c) => Bytes_constant c
    end
  with
  untype_instruction {self_type tff0 A B} (um : untype_mode) (i : syntax.instruction self_type tff0 A B) : instruction :=
    match i with
    | syntax.Instruction_seq i =>
      Instruction_seq (untype_instruction_seq um i)
    | syntax.FAILWITH => FAILWITH
    | syntax.IF_ f i1 i2 => IF_ (untype_if_family f) (untype_instruction_seq um i1) (untype_instruction_seq um i2)
    | syntax.LOOP_ f i => LOOP_ (untype_loop_family f) (untype_instruction_seq um i)
    | syntax.DIP n _ i => DIP n (untype_instruction_seq um i)
    | syntax.EXEC => EXEC
    | syntax.PUSH a x => PUSH a (untype_data um x)
    | syntax.LAMBDA a b i => LAMBDA a b (untype_instruction_seq um i)
    | syntax.ITER i => ITER (untype_instruction_seq um i)
    | syntax.MAP i => MAP (untype_instruction_seq um i)
    | syntax.CREATE_CONTRACT g p an i => CREATE_CONTRACT g p an (untype_instruction_seq um i)
    | syntax.SELF an _ => SELF an
    | syntax.Instruction_opcode o => instruction_opcode (untype_opcode o)
    end
  with untype_instruction_seq {self_type tff0 A B} (um : untype_mode) (i : syntax.instruction_seq self_type tff0 A B) : instruction_seq :=
    match i with
    | syntax.NOOP => NOOP
    | syntax.SEQ i1 i2 => SEQ (untype_instruction um i1) (untype_instruction_seq um i2)
    | syntax.Tail_fail i => SEQ (untype_instruction um i) NOOP
  end.

  Lemma stype_dec_same A : stype_dec A A = left eq_refl.
  Proof.
    destruct (stype_dec A A) as [e | n].
    - f_equal.
      apply Eqdep_dec.UIP_dec.
      apply stype_dec.
    - destruct (n eq_refl).
  Qed.

  Lemma bool_dec_same (a : Datatypes.bool) (H : a = a) : H = eq_refl.
  Proof.
    apply Eqdep_dec.UIP_dec.
    apply Bool.bool_dec.
  Qed.

  Lemma lt_proof_irrelevant : forall (n1 n2 : Datatypes.nat) (p q : (n1 ?= n2) = Lt), p = q.
  Proof.
    intros n1 n2 p q.
    apply Eqdep_dec.UIP_dec.
    destruct x; destruct y; auto;
      try (right; intro contra; discriminate contra).
  Qed.

  Lemma bool_dec_same2 (x y : Datatypes.bool) (H1 H2 : x = y) (HH1 HH2 : H1 = H2) : HH1 = HH2.
  Proof.
    apply Eqdep_dec.UIP_dec.
    intros x2 y2.
    left.
    apply Eqdep_dec.UIP_dec.
    apply Bool.bool_dec.
  Qed.

  Lemma bool_dec_same_same (x : Datatypes.bool) : bool_dec_same x eq_refl = eq_refl.
  Proof.
    apply bool_dec_same2.
  Qed.

  Lemma andb_prop_refl : andb_prop true true eq_refl = conj eq_refl eq_refl.
  Proof.
    destruct (andb_prop true true eq_refl).
    f_equal; apply bool_dec_same.
  Qed.

  Definition tail_fail_change_range_seq {self_type} A B B' (i : syntax.instruction_seq self_type true A B) :
    syntax.instruction_seq self_type true A B'.
  Proof.
    apply (tail_fail_induction_seq self_type A B i (fun self_type A B i => syntax.instruction self_type true A B')
                                   (fun self_type A B i => syntax.instruction_seq self_type true A B')); clear A B i.
    - intros st a A _.
      apply syntax.FAILWITH.
    - intros st A B C1 C2 t f _ _ i1 i2.
      apply (syntax.IF_ f i1 i2).
    - intros st A B C i1 _ i2.
      apply (syntax.SEQ i1 i2).
    - intros st A B _ i.
      apply (syntax.Tail_fail i).
    - intros st A B _ i.
      apply (syntax.Instruction_seq i).
  Defined.

  Lemma tail_fail_change_range_same {self_type} A B (i : syntax.instruction self_type true A B) :
    tail_fail_change_range A B B i = i.
  Proof.
    apply (tail_fail_induction _ A B i
                               (fun st A B i => tail_fail_change_range A B B i = i)
                               (fun st A B i => tail_fail_change_range_seq A B B i = i)); clear A B i;
      intros; unfold tail_fail_change_range, tail_fail_change_range_seq; simpl; f_equal; assumption.
  Qed.

  Lemma tail_fail_change_range_same_seq {self_type} A B (i : syntax.instruction_seq self_type true A B) :
    tail_fail_change_range_seq A B B i = i.
  Proof.
    apply (tail_fail_induction_seq _ A B i
                                   (fun st A B i => tail_fail_change_range A B B i = i)
                                   (fun st A B i => tail_fail_change_range_seq A B B i = i)); clear A B i;
      intros; unfold tail_fail_change_range, tail_fail_change_range_seq; simpl; f_equal; assumption.
  Qed.

  Definition untype_type_spec {self_type} tffi A B (i : syntax.instruction self_type tffi A B) :=
    typer.type_instruction (typer.Optimized) (untype_instruction untype_Optimized i) A =
    Return ((if tffi return syntax.instruction self_type tffi A B -> typer.typer_result A
               then
                 fun i =>
                   typer.Any_type _ (fun B' => tail_fail_change_range A B B' i)
               else
                 typer.Inferred_type _ B) i).

  Definition untype_type_spec_seq {self_type} tffi A B (i : syntax.instruction_seq self_type tffi A B) :=
    typer.type_instruction_seq typer.Optimized (untype_instruction_seq untype_Optimized i) A =
    Return ((if tffi return syntax.instruction_seq self_type tffi A B -> typer.typer_result_seq A
               then
                 fun i =>
                   typer.Any_type_seq _ (fun B' => tail_fail_change_range_seq A B B' i)
               else
                 typer.Inferred_type_seq _ B) i).

  Lemma instruction_cast_same {self_type} tffi A B (i : syntax.instruction self_type tffi A B) :
    typer.instruction_cast A A B B i = Return i.
  Proof.
    unfold typer.instruction_cast.
    rewrite stype_dec_same.
    rewrite stype_dec_same.
    reflexivity.
  Qed.

  Lemma instruction_seq_cast_same {self_type} tffi A B (i : syntax.instruction_seq self_type tffi A B) :
    typer.instruction_seq_cast A A B B i = Return i.
  Proof.
    unfold typer.instruction_seq_cast.
    rewrite stype_dec_same.
    rewrite stype_dec_same.
    reflexivity.
  Qed.

  Lemma opcode_cast_same {self_type} A B
        (o : syntax.opcode (self_type := self_type) A B) :
    typer.opcode_cast A A B B o = Return o.
  Proof.
    unfold typer.opcode_cast.
    rewrite stype_dec_same.
    rewrite stype_dec_same.
    reflexivity.
  Qed.

  Lemma instruction_cast_range_same {self_type} tffi A B (i : syntax.instruction self_type tffi A B) :
    typer.instruction_cast_range A B B i = Return i.
  Proof.
    apply instruction_cast_same.
  Qed.

  Lemma instruction_seq_cast_range_same {self_type} tffi A B (i : syntax.instruction_seq self_type tffi A B) :
    typer.instruction_seq_cast_range A B B i = Return i.
  Proof.
    apply instruction_seq_cast_same.
  Qed.

  Lemma instruction_cast_domain_same {self_type} tffi A B (i : syntax.instruction self_type tffi A B) :
    typer.instruction_cast_domain A A B i = Return i.
  Proof.
    apply instruction_cast_same.
  Qed.

  Lemma opcode_cast_domain_same self_type A B (o : @syntax.opcode self_type A B) :
    typer.opcode_cast_domain self_type A A B o = Return o.
  Proof.
    apply opcode_cast_same.
  Qed.

  Lemma untype_type_check_instruction {self_type} tffi A B (i : syntax.instruction self_type tffi A B) :
    untype_type_spec _ _ _ i ->
    typer.type_check_instruction (typer.type_instruction typer.Optimized) (untype_instruction untype_Optimized i) A B =
    Return (existT _ tffi i).
  Proof.
    intro IH.
    unfold typer.type_check_instruction.
    rewrite IH.
    simpl.
    destruct tffi.
    - rewrite tail_fail_change_range_same.
      reflexivity.
    - rewrite instruction_cast_range_same.
      reflexivity.
  Qed.

  Lemma untype_type_check_instruction_seq {self_type} tffi A B (i : syntax.instruction_seq self_type tffi A B) :
    untype_type_spec_seq _ _ _ i ->
    typer.type_check_instruction_seq (typer.type_instruction_seq typer.Optimized) (untype_instruction_seq untype_Optimized i) A B =
    Return (existT _ tffi i).
  Proof.
    intro IH.
    unfold typer.type_check_instruction_seq.
    rewrite IH.
    simpl.
    destruct tffi.
    - rewrite tail_fail_change_range_same_seq.
      reflexivity.
    - rewrite instruction_seq_cast_range_same.
      reflexivity.
  Qed.

  Lemma untype_type_check_instruction_seq_no_tail_fail {self_type} A B (i : syntax.instruction_seq self_type false A B) :
    untype_type_spec_seq _ _ _ i ->
    typer.type_check_instruction_seq_no_tail_fail (typer.type_instruction_seq typer.Optimized) (untype_instruction_seq untype_Optimized i) A B =
    Return i.
  Proof.
    intro IH.
    unfold typer.type_check_instruction_seq_no_tail_fail.
    rewrite IH.
    simpl.
    apply instruction_seq_cast_range_same.
  Qed.

  Lemma untype_type_instruction_no_tail_fail {self_type} A B (i : syntax.instruction self_type false A B) :
    untype_type_spec _ _ _ i ->
    typer.type_instruction_no_tail_fail (typer.type_instruction typer.Optimized) (untype_instruction untype_Optimized i) A = Return (existT _ _ i).
  Proof.
    intro IH.
    unfold typer.type_instruction_no_tail_fail.
    rewrite IH.
    reflexivity.
  Qed.

  Lemma untype_type_instruction_seq_no_tail_fail {self_type} A B (i : syntax.instruction_seq self_type false A B) :
    untype_type_spec_seq _ _ _ i ->
    typer.type_instruction_seq_no_tail_fail (typer.type_instruction_seq typer.Optimized) (untype_instruction_seq untype_Optimized i) A = Return (existT _ _ i).
  Proof.
    intro IH.
    unfold typer.type_instruction_seq_no_tail_fail.
    rewrite IH.
    reflexivity.
  Qed.

  Ltac trans_refl t := transitivity t; [reflexivity|].

  Lemma app_length_inv {A} : forall (l1 l1' l2 l2' : Datatypes.list A),
      List.length l1 = List.length l1' ->
      l1 ++ l2 = l1' ++ l2' ->
      l1 = l1' /\ l2 = l2'.
  Proof.
    induction l1; intros l1' l2 l2' Hlen Happ.
    - destruct l1'; simpl in *.
      + auto.
      + inversion Hlen.
    - destruct l1'; simpl in *.
      + inversion Hlen.
      + injection Happ. intros Happ2 Ha. subst. 
        specialize (IHl1 l1' l2 l2' (eq_add_S _ _ Hlen) Happ2) as [Hl1 Hl2]. subst. auto.
  Qed.

  Lemma untype_type_opcode self_type A B (o : @syntax.opcode self_type A B) :
    typer.type_opcode (untype_opcode o) A = Return (existT _ B o).
  Proof.
    destruct o; simpl; try reflexivity;
      try (destruct s as [v]; destruct v; reflexivity);
      try (destruct s as [c v]; destruct v; reflexivity);
      try (destruct i as [v]; destruct v; reflexivity);
      try (destruct i as [v]; destruct v; rewrite opcode_cast_domain_same; reflexivity);
      try (rewrite opcode_cast_domain_same; reflexivity).
    - erewrite (assume_ok _ _ _); simpl.
      rewrite opcode_cast_domain_same.
      reflexivity.
    - destruct s as [c d v]; destruct v; reflexivity.
    - simpl.
      rewrite as_comparable_comparable.
        destruct a; simpl.
        * rewrite opcode_cast_domain_same.
          reflexivity.
        * rewrite opcode_cast_domain_same.
          simpl.
          reflexivity.
    - destruct i as [x v]; destruct v; rewrite opcode_cast_domain_same; reflexivity.
    - unfold type_check_dig.
      simpl.
      rewrite (take_n_length n S1 (t ::: S2) e).
      simpl.
      rewrite opcode_cast_domain_same.
      reflexivity.
    - unfold type_check_dug.
      simpl.
      rewrite (take_n_length n S1 S2 e).
      simpl.
      rewrite opcode_cast_domain_same.
      reflexivity.
    - rewrite (take_n_length n A B e).
      simpl.
      rewrite opcode_cast_domain_same.
      reflexivity.
  Qed.

  Lemma untype_type_simple_comparable_data a (d : comparable.simple_comparable_data a) :
    typer.type_comparable_data typer.Optimized (untype_simple_comparable_data untype_Optimized d) a = Return d.
  Proof.
    destruct a; try reflexivity.
    - simpl.
      assert (0 <= Z.of_N d)%Z as H by apply N2Z.is_nonneg.
      rewrite <- Z.geb_le in H.
      rewrite H.
      rewrite N2Z.id.
      reflexivity.
    - destruct d; reflexivity.
    - simpl.
      rewrite tez.of_Z_to_Z.
      reflexivity.
    - destruct d as [c|c]; destruct c; simpl; reflexivity.
    - destruct d; reflexivity.
  Qed.

  Lemma untype_type_comparable_data a (d : comparable.comparable_data a) :
    typer.type_comparable_data typer.Optimized (untype_comparable_data untype_Optimized d) a = Return d.
  Proof.
    induction a.
    - apply untype_type_simple_comparable_data.
    - destruct d.
      simpl.
      rewrite untype_type_simple_comparable_data.
      simpl.
      rewrite IHa.
      reflexivity.
  Qed.

  Lemma untype_type_data_simple_comparable a s :
    type_data Optimized (untype_simple_comparable_data untype_Optimized s)
              (Comparable_type a) = Return (Comparable_constant a s).
  Proof.
    destruct a; try reflexivity.
    - simpl.
      assert (0 <= Z.of_N s)%Z as H by apply N2Z.is_nonneg.
      rewrite <- Z.geb_le in H.
      rewrite H.
      rewrite N2Z.id.
      reflexivity.
    - destruct s; reflexivity.
    - simpl.
      rewrite tez.of_Z_to_Z.
      reflexivity.
    - destruct s as [c|c]; destruct c; simpl; reflexivity.
    - destruct s; reflexivity.
  Qed.

  Lemma untype_map a b m :
    untype_data untype_Optimized (@Concrete_map a b m) =
    Concrete_seq
      (List.map (fun '(x, y) =>
                   Elt
                     (untype_comparable_data untype_Optimized x)
                     (untype_data untype_Optimized y))
                (map.to_list _ _ _ m)).
  Proof.
    destruct m; simpl.
    - reflexivity.
    - repeat f_equal.
      clear v.
      induction s; simpl.
      + reflexivity.
      + repeat f_equal.
        exact IHs.
  Qed.

  Lemma untype_big_map a b m :
    untype_data untype_Optimized (@Concrete_big_map a b m) =
    Concrete_seq
      (List.map (fun '(x, y) =>
                   Elt
                     (untype_comparable_data untype_Optimized x)
                     (untype_data untype_Optimized y))
                (map.to_list _ _ _ m)).
  Proof.
    destruct m; simpl.
    - reflexivity.
    - repeat f_equal.
      clear v.
      induction s; simpl.
      + reflexivity.
      + repeat f_equal.
        exact IHs.
  Qed.

  Lemma type_map a b l :
    type_data typer.Optimized (Concrete_seq l) (map a b) =
    let! l :=
       error.list_map
         (fun xy =>
            match xy with
            | Elt x y =>
            let! x := type_comparable_data typer.Optimized x a in
            let! y := type_data typer.Optimized y b in
            Return (x, y)
            | _ => Failed _ (Typing _ ("map literals are sequences of the form {Elt k1 v1; ...; Elt kn vn}"%string))
            end
         ) l in
    match map.sorted_dec _ _ _ l with
    | left H => Return (syntax.Concrete_map (map.of_list _ _ _ l H))
    | right _ => Failed _ (Typing _ ("map literals have to be sorted by keys"%string))
    end.
  Proof.
    simpl.
    f_equal.
    induction l; simpl.
    - reflexivity.
    - destruct a0; try reflexivity.
      rewrite IHl.
      destruct (type_comparable_data Optimized a0_1 a); simpl; try reflexivity.
      destruct (type_data Optimized a0_2 b); reflexivity.
  Qed.

  Lemma type_big_map a b l :
    type_data typer.Optimized (Concrete_seq l) (big_map a b) =
    let! l :=
       error.list_map
         (fun xy =>
            match xy with
            | Elt x y =>
            let! x := type_comparable_data typer.Optimized x a in
            let! y := type_data typer.Optimized y b in
            Return (x, y)
            | _ => Failed _ (Typing _ ("big map literals are sequences of the form {Elt k1 v1; ...; Elt kn vn}"%string))
            end
         ) l in
    match map.sorted_dec _ _ _ l with
    | left H => Return (syntax.Concrete_big_map (map.of_list _ _ _ l H))
    | right _ => Failed _ (Typing _ ("big map literals have to be sorted by keys"%string))
    end.
  Proof.
    simpl.
    f_equal.
    induction l; simpl.
    - reflexivity.
    - destruct a0; try reflexivity.
      rewrite IHl.
      destruct (type_comparable_data Optimized a0_1 a); simpl; try reflexivity.
      destruct (type_data Optimized a0_2 b); reflexivity.
  Qed.

  Fixpoint untype_type_data a (d : syntax.concrete_data a) :
    typer.type_data typer.Optimized (untype_data untype_Optimized d) a = Return d
  with
  untype_type_instruction {self_type} tffi A B (i : syntax.instruction self_type tffi A B) :
    untype_type_spec _ _ _ i
  with
  untype_type_instruction_seq {self_type} tffi A B (i : syntax.instruction_seq self_type tffi A B) :
    untype_type_spec_seq _ _ _ i.
  Proof.
    - destruct d; try reflexivity; try (simpl; repeat rewrite untype_type_data; reflexivity).
      + simpl.
        apply untype_type_data_simple_comparable.
      + simpl.
        pose (fix type_data_list (l : Datatypes.list concrete_data) :=
                match l with
                | nil => Return nil
                | cons x l =>
                  let! x := typer.type_data typer.Optimized x a in
                  let! l := type_data_list l in
                  Return (cons x l)
                end) as type_data_list.
        assert (forall l, type_data_list (List.map (untype_data untype_Optimized) l) = Return l).
        * clear l.
          intro l; induction l.
          -- reflexivity.
          -- simpl.
             rewrite untype_type_data.
             rewrite IHl.
             reflexivity.
        * simpl.
          rewrite H.
          reflexivity.
      + destruct s as (l, H).
        simpl.
        assert (forall l, type_data_set Optimized (List.map (untype_comparable_data untype_Optimized) l) a = Return l) as H1.
        * clear l H; induction l.
          -- reflexivity.
          -- simpl.
             rewrite untype_type_comparable_data.
             simpl.
             rewrite IHl.
             reflexivity.
        * rewrite H1.
          simpl.
          case (set.sorted_dec _ _ (comparable.compare_eq_iff a) (comparable.lt_trans a) l).
          -- intro s.
             repeat f_equal.
             apply set.sorted_irrel.
          -- intro; contradiction.
      + rewrite untype_map.
        rewrite type_map.
        rewrite list_map_map.
        match goal with
          |- (let! l := list_map ?f ?L in _) = _ =>
          replace (list_map f L) with (Return L)
        end.
        * simpl.
          destruct (map.sorted_dec _ _ _ (map.to_list _ _ _ m)) as [Hs|Hn].
          -- assert (Hs = map.to_list_is_locally_sorted _ _ _ m) as HHs by (apply map.sorted_irrel).
             subst Hs.
             rewrite map.to_of_list.
             reflexivity.
          -- exfalso.
             apply Hn.
             apply map.to_list_is_locally_sorted.
        * (* We cannot use error.list_map_id because we need to apply untype_type_data on syntactic subterms *)
          destruct m; simpl.
          -- reflexivity.
          -- rewrite untype_type_comparable_data; simpl.
             rewrite untype_type_data; simpl.
             match goal with
               |- (_ = let! l := list_map ?f ?L in _) =>
               replace (list_map f L) with (Return L)
             end.
             ++ reflexivity.
             ++ induction s; simpl.
                ** reflexivity.
                ** rewrite untype_type_comparable_data; simpl.
                   rewrite untype_type_data; simpl.
                   rewrite <- IHs.
                   reflexivity.
      + rewrite untype_big_map.
        rewrite type_big_map.
        rewrite list_map_map.
        match goal with
          |- (let! l := list_map ?f ?L in _) = _ =>
          replace (list_map f L) with (Return L)
        end.
        * simpl.
          destruct (map.sorted_dec _ _ _ (map.to_list _ _ _ m)) as [Hs|Hn].
          -- assert (Hs = map.to_list_is_locally_sorted _ _ _ m) as HHs by (apply map.sorted_irrel).
             subst Hs.
             rewrite map.to_of_list.
             reflexivity.
          -- exfalso.
             apply Hn.
             apply map.to_list_is_locally_sorted.
        * (* We cannot use error.list_map_id because we need to apply untype_type_data on syntactic subterms *)
          destruct m; simpl.
          -- reflexivity.
          -- rewrite untype_type_comparable_data; simpl.
             rewrite untype_type_data; simpl.
             match goal with
               |- (_ = let! l := list_map ?f ?L in _) =>
               replace (list_map f L) with (Return L)
             end.
             ++ reflexivity.
             ++ induction s; simpl.
                ** reflexivity.
                ** rewrite untype_type_comparable_data; simpl.
                   rewrite untype_type_data; simpl.
                   rewrite <- IHs.
                   reflexivity.
      + simpl.
        rewrite untype_type_check_instruction_seq; auto.
      + simpl.
        destruct c.
        simpl.
        reflexivity.
    - destruct i; try reflexivity; simpl.
      + unfold untype_type_spec.
        simpl.
        rewrite untype_type_instruction_seq.
        destruct tff; reflexivity.
      + unfold untype_type_spec.
        simpl.
        unfold type_branches.
        assert (type_if_family (untype_if_family i) t = Return (existT _ C1 (existT _ C2 i))) as Hi.
        * destruct i; reflexivity.
        * rewrite Hi.
          simpl.
          rewrite untype_type_instruction_seq; simpl.
          rewrite untype_type_instruction_seq; simpl.
          destruct tffa; destruct tffb;
            try rewrite instruction_seq_cast_range_same; simpl; repeat f_equal; apply tail_fail_change_range_same_seq.
      + unfold untype_type_spec.
        simpl.
        unfold type_loop.
        assert (type_loop_family (untype_loop_family i) t = Return (existT _ C1 (existT _ C2 i))) as Hi.
        * destruct i; reflexivity.
        * rewrite Hi.
          simpl.
          rewrite untype_type_check_instruction_seq.
          -- reflexivity.
          -- apply untype_type_instruction_seq.
      + unfold untype_type_spec.
        simpl.
        rewrite untype_type_data.
        reflexivity.
      + unfold untype_type_spec.
        simpl.
        rewrite untype_type_check_instruction_seq; auto.
      + destruct i as [c v]; destruct v.
        * unfold untype_type_spec; simpl.
          rewrite untype_type_check_instruction_seq; auto.
        * unfold untype_type_spec; simpl.
          rewrite untype_type_check_instruction_seq; auto.
        * unfold untype_type_spec; simpl.
          rewrite untype_type_check_instruction_seq; auto.
      + destruct i as [a c v]; destruct v.
        * unfold untype_type_spec; simpl.
          rewrite untype_type_instruction_seq_no_tail_fail.
          -- simpl.
             rewrite instruction_seq_cast_range_same.
             reflexivity.
          -- auto.
        * unfold untype_type_spec; simpl.
          rewrite untype_type_instruction_seq_no_tail_fail.
          -- simpl.
             rewrite instruction_seq_cast_range_same.
             reflexivity.
          -- auto.
      + unfold untype_type_spec; simpl.
        rewrite untype_type_check_instruction_seq.
        -- simpl.
           rewrite instruction_cast_domain_same.
           reflexivity.
        -- auto.
      + unfold untype_type_spec; simpl.
        assert (isSome_maybe (Typing _ "No such self entrypoint"%string)
                             (get_entrypoint_opt annot_opt self_type self_annot) = Return H).
        * destruct (get_entrypoint_opt annot_opt self_type self_annot) as [x|].
          -- simpl.
             destruct H.
             reflexivity.
          -- inversion H.
        * rewrite H0.
          reflexivity.
      + unfold untype_type_spec; simpl.
        rewrite instruction_cast_domain_same.
        reflexivity.
      + unfold untype_type_spec.
        simpl.
        rewrite (take_n_length n A B e).
        simpl.
        rewrite untype_type_instruction_seq_no_tail_fail.
        * simpl.
          rewrite instruction_cast_domain_same.
          reflexivity.
        * apply untype_type_instruction_seq.
      + unfold untype_type_spec.
        simpl.
        rewrite untype_type_opcode.
        reflexivity.
    - destruct i; try reflexivity; simpl.
      + unfold untype_type_spec_seq.
        simpl.
        rewrite untype_type_instruction.
        simpl.
        reflexivity.
      + unfold untype_type_spec_seq.
        simpl.
        rewrite untype_type_instruction.
        simpl.
        rewrite untype_type_instruction_seq.
        simpl.
        destruct tff; reflexivity.
  Qed.

  Lemma type_untype_simple_comparable_data a x (x' : comparable.simple_comparable_data a) :
    typer.type_comparable_data typer.Optimized x a = error.Return x' ->
    untype_simple_comparable_data untype_Optimized x' = x.
  Proof.
    destruct a; destruct x; simpl; try congruence.
    - intro H.
      case_eq (z >=? 0)%Z; intro He; rewrite He in H; try discriminate.
      rewrite Z.geb_le in He.
      f_equal.
      apply unreturn in H.
      subst x'.
      apply Z2N.id.
      assumption.
    - intro H; apply unreturn in H; subst.
      reflexivity.
    - intro H; apply unreturn in H; subst.
      reflexivity.
    - intro H.
      f_equal.
      apply tez.of_Z_to_Z_eqv.
      assumption.
    - intro H.
      destruct s as [|c1 [|c2 s]]; [discriminate|discriminate|].
      destruct (ascii_dec c1 "t").
      + destruct (ascii_dec c2 "z"); try discriminate.
        injection H; intros; subst.
        reflexivity.
      + destruct s as [|c3 s]; try discriminate.
        destruct (ascii_dec c1 "K"); try discriminate.
        destruct (ascii_dec c2 "T"); try discriminate.
        destruct (ascii_dec c3 "1"); try discriminate.
        injection H; intros; subst.
        reflexivity.
    - intro H; apply unreturn in H; subst.
      reflexivity.
  Qed.

  Lemma type_untype_comparable_data a x (x' : comparable.comparable_data a) :
    typer.type_comparable_data typer.Optimized x a = error.Return x' ->
    untype_comparable_data untype_Optimized x' = x.
  Proof.
    generalize dependent x'.
    generalize dependent x.
    induction a as [s|a b].
    - simpl.
      apply type_untype_simple_comparable_data.
    - simpl.
      destruct x; try discriminate.
      destruct x' as (x1', x2').
      simpl.
      intro H.
      apply bind_eq_return in H.
      destruct H as (d, (Hd, H)).
      apply type_untype_simple_comparable_data in Hd.
      subst x1.
      apply bind_eq_return in H.
      destruct H as (d', (Hd', H)).
      apply IHb in Hd'.
      subst x2.
      congruence.
  Qed.

  Lemma type_untype_cast_seq um self_type A B C D tff i i' :
    instruction_seq_cast (self_type := self_type) (tff := tff) A B C D i = Return i' ->
    untype_instruction_seq um i = untype_instruction_seq um i'.
  Proof.
    unfold instruction_seq_cast.
    destruct (stype_dec A B); [| discriminate].
    destruct (stype_dec C D); [| discriminate].
    destruct e.
    destruct e0.
    simpl.
    intro H; apply unreturn in H.
    congruence.
  Qed.

  Lemma type_untype_cast um self_type A B C D tff i i' :
    instruction_cast (self_type := self_type) (tff := tff) A B C D i = Return i' ->
    untype_instruction um i = untype_instruction um i'.
  Proof.
    unfold instruction_cast.
    destruct (stype_dec A B); [| discriminate].
    destruct (stype_dec C D); [| discriminate].
    destruct e.
    destruct e0.
    simpl.
    intro H; apply unreturn in H.
    congruence.
  Qed.

  Lemma type_untype_cast_opcode self_type A B C D i i' :
    opcode_cast (self_type := self_type) A B C D i = Return i' ->
    untype_opcode i = untype_opcode i'.
  Proof.
    unfold opcode_cast.
    destruct (stype_dec A B); [| discriminate].
    destruct (stype_dec C D); [| discriminate].
    destruct e.
    destruct e0.
    simpl.
    intro H; apply unreturn in H.
    congruence.
  Qed.

  Lemma type_untype_if_family f t A B ff :
    type_if_family f t = Return (existT _ A (existT _ B ff)) ->
    untype_if_family ff = f.
  Proof.
    destruct f; destruct ff; try discriminate; simpl; reflexivity.
  Qed.

  Lemma type_untype_loop_family f t A B ff :
    type_loop_family f t = Return (existT _ A (existT _ B ff)) ->
    untype_loop_family ff = f.
  Proof.
    destruct f; destruct ff; try discriminate; simpl; reflexivity.
  Qed.

  Ltac mytac type_untype type_untype_seq type_untype_data :=
    match goal with
    | |- _ -> _ =>
      intro
    | H : (bind _ _ = Return _) |- _ =>
      rewrite error.bind_eq_return in H
    | H : (exists _, _) |- _ =>
      destruct H
    | H : (_ /\ _) |- _ =>
      destruct H
    | H : (Return _ = Return _) |- _ =>
      apply unreturn in H
    | H : (Failed _ _ = Return _) |- _ =>
      discriminate
    | H : (match ?x with | Any_type_seq _ _ => _ | Inferred_type_seq _ _ _ => _ end = Return _) |- _ =>
      is_var x; destruct x
    | H : (match ?x with | Any_type _ _ => _ | Inferred_type _ _ _ => _ end = Return _) |- _ =>
      is_var x; destruct x
    | H : (match ?x with | existT _ _ _ => _ end = Return _) |- _ =>
      is_var x; destruct x
    | H : (match ?x with | exist _ _ _ => _ end = Return _) |- _ =>
      is_var x; destruct x
    | H : (match ?x with | (_, _) => _ end = Return _) |- _ =>
      is_var x; destruct x
    | H : (match ?x with | nil => _ | cons _ _ => _ end = Return _) |- _ =>
      is_var x; destruct x
    | H : (match ?x with | nil => _ | cons _ _ => _ end _ = Return _) |- _ =>
      is_var x; destruct x
    | H : (match ?x with | None => _ | Some _ => _ end = Return _) |- _ =>
      is_var x; destruct x
    | H : (match ?x with | NOOP => _ | SEQ _ _ => _ end = Return _) |- _ =>
      is_var x; destruct x
    | H : _ = ?x |- _ =>
      is_var x; subst x
    | H : ?x = _ |- _ =>
      is_var x; subst x
    | H : type_instruction_seq _ _ _ = Return _ |- _ =>
      apply type_untype_seq in H
    | H : type_instruction _ _ _ = Return _ |- _ =>
      apply type_untype in H
    | H : type_data _ _ _ = Return _ |- _ =>
      apply type_untype_data in H
    | H : type_if_family _ _ = Return (existT _ _ (existT _ _ _)) |- _ =>
      apply type_untype_if_family in H
    | H : type_loop_family _ _ = Return (existT _ _ (existT _ _ _)) |- _ =>
      apply type_untype_loop_family in H
    | H : instruction_seq_cast_range _ _ _ _ = Return _ |- _ =>
      unfold instruction_seq_cast_range in H
    | H : instruction_seq_cast _ _ _ _ _ = Return _ |- _ =>
      apply (type_untype_cast_seq untype_Optimized) in H
    | H : instruction_cast _ _ _ _ _ = Return _ |- _ =>
      apply (type_untype_cast untype_Optimized) in H
    | H : opcode_cast _ _ _ _ _ = Return _ |- _ =>
      apply type_untype_cast_opcode in H
    | H : instruction_cast_domain _ _ _ _ = Return _ |- _ =>
      unfold instruction_cast_domain in H
    | H : opcode_cast_domain _ _ _ _ _ = Return _ |- _ =>
      unfold opcode_cast_domain in H
    | H : type_check_instruction_seq _ _ _ _ = Return _ |- _ =>
      unfold type_check_instruction_seq in H
    | H : type_check_instruction_seq_no_tail_fail _ _ _ _ = Return _ |- _ =>
      unfold type_check_instruction_seq_no_tail_fail in H
    | H : type_instruction_seq_no_tail_fail _ _ _ = Return _ |- _ =>
      unfold type_instruction_seq_no_tail_fail in H
    | H : assert_not_tail_fail_seq _ _ = Return _ |- _ =>
      unfold assert_not_tail_fail_seq in H
    |  H : match ?x with
           | Comparable_type _ => _
           | key => _
           | unit => _
           | signature => _
           | option _ => _
           | list _ => _
           | set _ => _
           | contract _ => _
           | operation => _
           | pair _ _ => _
           | or _ _ _ _ => _
           | lambda _ _ => _
           | map _ _ => _
           | big_map _ _ => _
           | chain_id => _
           end = Return _ |- _ =>
       destruct x; try discriminate
    | H : match ?x with
            | syntax_type.string => _
            | nat => _
            | int => _
            | bytes => _
            | bool => _
            | mutez => _
            | address => _
            | key_hash => _
            | timestamp => _
          end = Return _ |- _ =>
      destruct x; try discriminate
    | H : (existT _ _ _ = existT _ _ _) |- _ =>
      apply existT_eq_3 in H; destruct H
    | H : (untype_instruction_seq _
             (eq_rec _ _ _ _ eq_refl) = _) |- _ =>
      simpl in H
    | H : (untype_instruction _
             (syntax.CREATE_CONTRACT _ _ _
                 (eq_rec _ _ _ _ eq_refl)) = _) |- _ =>
      simpl in H
    | H : (untype_instruction _
             (syntax.DIP _ _
                 (eq_rec _ _ _ _ eq_refl)) = _) |- _ =>
      simpl in H
    | |- _ = _ =>
      simpl in *; f_equal; congruence
    end.

  Lemma type_untype_opcode self_type A B o (o' : syntax.opcode A B) :
    typer.type_opcode (self_type := self_type) o A =
    error.Return (existT _ B o') ->
    untype_opcode o' = o.
  Proof.
    destruct o; simpl.
    - repeat mytac (eq_refl Z) (eq_refl Z) (eq_refl Z).
    - repeat mytac (eq_refl Z) (eq_refl Z) (eq_refl Z).
    - repeat mytac (eq_refl Z) (eq_refl Z) (eq_refl Z).
    - repeat mytac (eq_refl Z) (eq_refl Z) (eq_refl Z).
    - repeat mytac (eq_refl Z) (eq_refl Z) (eq_refl Z).
    - repeat mytac (eq_refl Z) (eq_refl Z) (eq_refl Z).
    - repeat mytac (eq_refl Z) (eq_refl Z) (eq_refl Z).
    - repeat mytac (eq_refl Z) (eq_refl Z) (eq_refl Z).
    - repeat mytac (eq_refl Z) (eq_refl Z) (eq_refl Z).
    - repeat mytac (eq_refl Z) (eq_refl Z) (eq_refl Z).
    - repeat mytac (eq_refl Z) (eq_refl Z) (eq_refl Z).
    - repeat mytac (eq_refl Z) (eq_refl Z) (eq_refl Z).
    - repeat mytac (eq_refl Z) (eq_refl Z) (eq_refl Z).
    - repeat mytac (eq_refl Z) (eq_refl Z) (eq_refl Z).
    - repeat mytac (eq_refl Z) (eq_refl Z) (eq_refl Z).
    - repeat mytac (eq_refl Z) (eq_refl Z) (eq_refl Z).
    - repeat mytac (eq_refl Z) (eq_refl Z) (eq_refl Z).
    - repeat mytac (eq_refl Z) (eq_refl Z) (eq_refl Z).
    - repeat mytac (eq_refl Z) (eq_refl Z) (eq_refl Z).
    - repeat mytac (eq_refl Z) (eq_refl Z) (eq_refl Z).
    - repeat mytac (eq_refl Z) (eq_refl Z) (eq_refl Z).
    - repeat mytac (eq_refl Z) (eq_refl Z) (eq_refl Z).
    - repeat mytac (eq_refl Z) (eq_refl Z) (eq_refl Z).
    - repeat mytac (eq_refl Z) (eq_refl Z) (eq_refl Z).
    - repeat mytac (eq_refl Z) (eq_refl Z) (eq_refl Z).
    - repeat mytac (eq_refl Z) (eq_refl Z) (eq_refl Z).
    - repeat mytac (eq_refl Z) (eq_refl Z) (eq_refl Z).
    - repeat mytac (eq_refl Z) (eq_refl Z) (eq_refl Z).
    - repeat mytac (eq_refl Z) (eq_refl Z) (eq_refl Z).
    - repeat mytac (eq_refl Z) (eq_refl Z) (eq_refl Z).
    - repeat mytac (eq_refl Z) (eq_refl Z) (eq_refl Z).
    - repeat mytac (eq_refl Z) (eq_refl Z) (eq_refl Z).
    - repeat mytac (eq_refl Z) (eq_refl Z) (eq_refl Z).
    - repeat mytac (eq_refl Z) (eq_refl Z) (eq_refl Z).
    - repeat mytac (eq_refl Z) (eq_refl Z) (eq_refl Z).
    - repeat mytac (eq_refl Z) (eq_refl Z) (eq_refl Z).
    - repeat mytac (eq_refl Z) (eq_refl Z) (eq_refl Z).
    - repeat mytac (eq_refl Z) (eq_refl Z) (eq_refl Z).
    - repeat mytac (eq_refl Z) (eq_refl Z) (eq_refl Z).
    - repeat mytac (eq_refl Z) (eq_refl Z) (eq_refl Z).
    - repeat mytac (eq_refl Z) (eq_refl Z) (eq_refl Z).
    - repeat mytac (eq_refl Z) (eq_refl Z) (eq_refl Z).
    - repeat mytac (eq_refl Z) (eq_refl Z) (eq_refl Z).
    - repeat mytac (eq_refl Z) (eq_refl Z) (eq_refl Z).
    - repeat mytac (eq_refl Z) (eq_refl Z) (eq_refl Z).
    - repeat mytac (eq_refl Z) (eq_refl Z) (eq_refl Z).
    - repeat mytac (eq_refl Z) (eq_refl Z) (eq_refl Z).
    - repeat mytac (eq_refl Z) (eq_refl Z) (eq_refl Z).
    - repeat mytac (eq_refl Z) (eq_refl Z) (eq_refl Z).
    - repeat mytac (eq_refl Z) (eq_refl Z) (eq_refl Z).
    - repeat mytac (eq_refl Z) (eq_refl Z) (eq_refl Z).
    - repeat mytac (eq_refl Z) (eq_refl Z) (eq_refl Z).
    - repeat mytac (eq_refl Z) (eq_refl Z) (eq_refl Z).
    - repeat mytac (eq_refl Z) (eq_refl Z) (eq_refl Z).
    - repeat mytac (eq_refl Z) (eq_refl Z) (eq_refl Z).
    - repeat mytac (eq_refl Z) (eq_refl Z) (eq_refl Z).
    - repeat mytac (eq_refl Z) (eq_refl Z) (eq_refl Z).
    - repeat mytac (eq_refl Z) (eq_refl Z) (eq_refl Z).
    - repeat mytac (eq_refl Z) (eq_refl Z) (eq_refl Z).
    - repeat mytac (eq_refl Z) (eq_refl Z) (eq_refl Z).
    - unfold type_check_dig.
      repeat mytac (eq_refl Z) (eq_refl Z) (eq_refl Z).
    - unfold type_check_dug.
      repeat mytac (eq_refl Z) (eq_refl Z) (eq_refl Z).
    - repeat mytac (eq_refl Z) (eq_refl Z) (eq_refl Z).
    - repeat mytac (eq_refl Z) (eq_refl Z) (eq_refl Z).
  Qed.

  Fixpoint type_untype self_type A i t {struct i} :
    typer.type_instruction typer.Optimized (self_type := self_type) i A = error.Return t ->
    match t with
    | Inferred_type _ B i' => untype_instruction untype_Optimized i' = i
    | Any_type _ i' => forall B, untype_instruction untype_Optimized (i' B) = i
    end
  with type_untype_seq self_type A i t {struct i} :
    typer.type_instruction_seq typer.Optimized (self_type := self_type) i A = error.Return t ->
    match t with
    | Inferred_type_seq _ B i' => untype_instruction_seq untype_Optimized i' = i
    | Any_type_seq _ i' => forall B, untype_instruction_seq untype_Optimized (i' B) = i
    end
  with type_untype_data a x (x' : syntax.concrete_data a) {struct x} :
    typer.type_data typer.Optimized x a = error.Return x' ->
    untype_data untype_Optimized x' = x.
  Proof.
    {
      destruct i; simpl.
      - repeat mytac type_untype type_untype_seq type_untype_data.
      - repeat mytac type_untype type_untype_seq type_untype_data.
      - unfold type_branches.
        repeat mytac type_untype type_untype_seq type_untype_data.
      - unfold type_loop.
        repeat mytac type_untype type_untype_seq type_untype_data.
      - repeat mytac type_untype type_untype_seq type_untype_data.
      - repeat mytac type_untype type_untype_seq type_untype_data.
      - repeat mytac type_untype type_untype_seq type_untype_data.
      - repeat mytac type_untype type_untype_seq type_untype_data.
      - repeat mytac type_untype type_untype_seq type_untype_data.
      - repeat mytac type_untype type_untype_seq type_untype_data.
      - repeat mytac type_untype type_untype_seq type_untype_data.
      - repeat mytac type_untype type_untype_seq type_untype_data.
      - repeat mytac type_untype type_untype_seq type_untype_data.
        apply type_untype_opcode in H.
        simpl.
        f_equal.
        exact H.
    }
    {
      destruct i; simpl.
      - repeat mytac type_untype type_untype_seq type_untype_data.
      - repeat mytac type_untype type_untype_seq type_untype_data.
    }
    {
      destruct x; simpl.
      - repeat mytac type_untype type_untype_seq type_untype_data.
        + case_eq (z >=? 0)%Z; intro He; rewrite He in H; try discriminate.
          repeat mytac type_untype type_untype_seq type_untype_data.
          simpl.
          rewrite Z.geb_le in He.
          f_equal.
          apply Z2N.id.
          assumption.
        + simpl.
          f_equal.
          apply tez.of_Z_to_Z_eqv.
          assumption.
      - repeat mytac type_untype type_untype_seq type_untype_data.
        destruct s as [|c1 [|c2 s]]; [discriminate|discriminate|].
        destruct (ascii_dec c1 "t").
        + destruct (ascii_dec c2 "z"); try discriminate.
          injection H; intros; subst.
          reflexivity.
        + destruct s as [|c3 s]; try discriminate.
          destruct (ascii_dec c1 "K"); try discriminate.
          destruct (ascii_dec c2 "T"); try discriminate.
          destruct (ascii_dec c3 "1"); try discriminate.
          injection H; intros; subst.
          reflexivity.
      - repeat mytac type_untype type_untype_seq type_untype_data.
      - repeat mytac type_untype type_untype_seq type_untype_data.
      - repeat mytac type_untype type_untype_seq type_untype_data.
      - repeat mytac type_untype type_untype_seq type_untype_data.
      - repeat mytac type_untype type_untype_seq type_untype_data.
      - repeat mytac type_untype type_untype_seq type_untype_data.
      - repeat mytac type_untype type_untype_seq type_untype_data.
      - repeat mytac type_untype type_untype_seq type_untype_data.
      - repeat mytac type_untype type_untype_seq type_untype_data.
      - repeat mytac type_untype type_untype_seq type_untype_data.
      - repeat mytac type_untype type_untype_seq type_untype_data.
        + simpl.
          f_equal.
          generalize dependent x.
          generalize dependent l.
          induction l.
          * repeat mytac type_untype type_untype_seq type_untype_data.
          * repeat mytac type_untype type_untype_seq type_untype_data.
            simpl.
            f_equal.
            apply IHl.
            assumption.
        + destruct (set.sorted_dec _ _ (comparable.compare_eq_iff a)
                                   (comparable.lt_trans a) x); [|discriminate].
          do 2 mytac type_untype type_untype_seq type_untype_data.
          simpl.
          f_equal.
          clear s.
          generalize dependent x.
          induction l.
          * simpl.
            repeat mytac type_untype type_untype_seq type_untype_data.
          * simpl.
            repeat mytac type_untype type_untype_seq type_untype_data.
            simpl.
            erewrite type_untype_comparable_data; [|eassumption].
            rewrite IHl; [reflexivity|assumption].
        + destruct (map.sorted_dec _ _ _ x); try discriminate.
          apply unreturn in H0.
          subst x'.
          rewrite untype_map.
          f_equal.
          rewrite map.of_to_list.
          generalize dependent x; induction l; intro x.
          * repeat mytac type_untype type_untype_seq type_untype_data.
          * repeat mytac type_untype type_untype_seq type_untype_data.
            destruct a0; try discriminate.
            repeat mytac type_untype type_untype_seq type_untype_data.
            simpl.
            apply type_untype_comparable_data in H.
            repeat mytac type_untype type_untype_seq type_untype_data.
            f_equal.
            apply IHl.
            -- assumption.
            -- apply map.sorted_tail in l0; assumption.
        + destruct (map.sorted_dec _ _ _ x); try discriminate.
          apply unreturn in H0.
          subst x'.
          rewrite untype_big_map.
          f_equal.
          rewrite map.of_to_list.
          generalize dependent x; induction l; intro x.
          * repeat mytac type_untype type_untype_seq type_untype_data.
          * repeat mytac type_untype type_untype_seq type_untype_data.
            destruct a0; try discriminate.
            repeat mytac type_untype type_untype_seq type_untype_data.
            simpl.
            apply type_untype_comparable_data in H.
            repeat mytac type_untype type_untype_seq type_untype_data.
            f_equal.
            apply IHl.
            -- assumption.
            -- apply map.sorted_tail in l0; assumption.
      - repeat mytac type_untype type_untype_seq type_untype_data.
    }
  Qed.
