Require Import ZArith List.
Require Import syntax.
Require Import typer.
Require Import untyped_syntax error.
Require Eqdep_dec.
Import error.Notations.
Require Import Lia.

(* Not really needed but eases reading of proof states. *)
Require Import String.
Require Import Ascii.

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

  Fixpoint untype_data {a} (um : untype_mode) (d : syntax.concrete_data a) : concrete_data :=
    match d with
    | syntax.Int_constant z => Int_constant z
    | syntax.Nat_constant n => Int_constant (Z.of_N n)
    | syntax.String_constant s => String_constant s
    | syntax.Mutez_constant (Mk_mutez m) => Int_constant (tez.to_Z m)
    | syntax.Bytes_constant s => Bytes_constant s
    | syntax.Timestamp_constant t =>
      match um with
      | untype_Readable =>
        String_constant
          (All.LString.to_string
             (Moment.Print.rfc3339
                (Moment.of_epoch t)))
      | untype_Optimized =>
        Int_constant t
      end
    | syntax.Signature_constant s => String_constant s
    | syntax.Key_constant s => String_constant s
    | syntax.Key_hash_constant s => String_constant s
    | syntax.Address_constant c =>
      match c with
      | syntax.Implicit (syntax.Mk_key_hash s) =>
        String_constant (String "t" (String "z" s))
      | syntax.Originated (syntax.Mk_smart_contract_address s) =>
        String_constant (String "K" (String "T" (String "1" s)))
      end
    | syntax.Unit => Unit
    | syntax.True_ => True_
    | syntax.False_ => False_
    | syntax.Pair x y => Pair (untype_data um x) (untype_data um y)
    | syntax.Left x _ _ => Left (untype_data um x)
    | syntax.Right y _ _ => Right (untype_data um y)
    | syntax.Some_ x => Some_ (untype_data um x)
    | syntax.None_ => None_
    | syntax.Concrete_list l => Concrete_seq (List.map (untype_data um) l)
    | syntax.Concrete_set l => Concrete_seq (List.map (untype_data um) l)
    | syntax.Concrete_map l =>
      Concrete_seq (List.map
                      (fun '(syntax.Elt _ _ x y) => Elt (untype_data um x) (untype_data um y))
                      l)
    | syntax.Concrete_big_map l =>
      Concrete_seq (List.map
                      (fun '(syntax.Elt _ _ x y) => Elt (untype_data um x) (untype_data um y))
                      l)
    | syntax.Instruction _ i => Instruction (untype_instruction_seq um i)
    | syntax.Chain_id_constant (Mk_chain_id c) => Bytes_constant c
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
    - pose (A := a :: lambda (pair a b) c :: D).
      assert (forall (b : Datatypes.bool) i1,
                 (if b return is_packable a = b -> _
                  then fun h =>
                         let! o := opcode_cast_domain self_type A A _ (@syntax.APPLY _ _ _ _ _ (IT_eq_rev _ h)) in
                         Return (existT _ _ o)
                  else fun _ => Failed _ (Typing _ "APPLY"%string)) i1
                 = Return (existT _ _ (@syntax.APPLY _ _ _ _ _ i))).
      * intros b0 i1.
          destruct b0.
          -- rewrite opcode_cast_domain_same.
             simpl.
             repeat f_equal.
             apply Is_true_UIP.
          -- exfalso.
             rewrite i1 in i.
             exact i.
        * apply H.
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
        assert (0 <= Z.of_N n)%Z as H by apply N2Z.is_nonneg.
        rewrite <- Z.geb_le in H.
        rewrite H.
        rewrite N2Z.id.
        reflexivity.
      + simpl.
        destruct m.
        unfold type_data.
        rewrite tez.of_Z_to_Z.
        reflexivity.
      + simpl.
        destruct a as [c|c]; destruct c; simpl; reflexivity.
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
      + pose (fix type_data_set (l : Datatypes.list concrete_data) :=
                match l with
                | nil => Return nil
                | cons x l =>
                  let! x := typer.type_data typer.Optimized x a in
                  let! l := type_data_set l in
                  Return (cons x l)
                end) as type_data_set.
        assert (forall l, type_data_set (List.map (untype_data untype_Optimized) l) = Return l).
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
      + pose (fix type_data_list L :=
                   match L with
                   | nil => Return nil
                   | cons (Elt x y) l =>
                    let! x := type_data typer.Optimized x a in
                    let! y := type_data typer.Optimized y b in
                    let! l := type_data_list l in
                    Return (cons (syntax.Elt _ _ x y) l)
                   | _ => Failed _ (Typing _ (untype_data untype_Optimized (syntax.Concrete_map l), (map a b)))
                   end) as type_data_map.
        assert (forall l, type_data_map (List.map (fun '(syntax.Elt _ _ x y) => Elt (untype_data untype_Optimized x) (untype_data untype_Optimized y)) l) = Return l).
        * intro L; induction L.
          -- reflexivity.
          -- simpl.
             destruct a0.
             rewrite untype_type_data.
             rewrite untype_type_data.
             rewrite IHL.
             reflexivity.
        * simpl.
          rewrite H.
          reflexivity.
      + pose (fix type_data_list L :=
                   match L with
                   | nil => Return nil
                   | cons (Elt x y) l =>
                    let! x := type_data Optimized x a in
                    let! y := type_data Optimized y b in
                    let! l := type_data_list l in
                    Return (cons (syntax.Elt _ _ x y) l)
                   | _ => Failed _ (Typing _ (untype_data untype_Optimized (syntax.Concrete_big_map l), (big_map a b)))
                   end) as type_data_map.
        assert (forall l, type_data_map (List.map (fun '(syntax.Elt _ _ x y) => Elt (untype_data untype_Optimized x) (untype_data untype_Optimized y)) l) = Return l).
        * intro L; induction L.
          -- reflexivity.
          -- simpl.
             destruct a0.
             rewrite untype_type_data.
             rewrite untype_type_data.
             rewrite IHL.
             reflexivity.
        * trans_refl (
            let! l := type_data_map (List.map (fun '(syntax.Elt _ _ x y) => Elt (untype_data untype_Optimized x) (untype_data untype_Optimized y)) l) in
            Return (@syntax.Concrete_big_map a b l)
          ).
          rewrite H.
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
          rewrite untype_type_check_instruction_seq_no_tail_fail.
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
          rewrite untype_type_check_instruction_seq_no_tail_fail; auto.
        * unfold untype_type_spec; simpl.
          rewrite untype_type_check_instruction_seq_no_tail_fail; auto.
        * unfold untype_type_spec; simpl.
          rewrite untype_type_check_instruction_seq_no_tail_fail; auto.
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
        assert (isSome_maybe (Typing string "No such self entrypoint"%string)
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
    - destruct A; [discriminate|].
      destruct A; [discriminate|].
      destruct t0; try discriminate.
      destruct t0_1; try discriminate.
      match goal with
        | |-
          ((match ?b0 as b return _ with | true => ?th | false => ?e end) eq_refl = ?rhs -> _) =>
          intro Ho'; assert (exists b (Hb : is_packable t = b),
                                (if b return is_packable t = b -> _
                                 then th else e) Hb = rhs)
        end.
      + exists (is_packable t); exists eq_refl; exact Ho'.
      + clear Ho'.
        destruct H as ([|], (Hb, H)); try discriminate.
        unfold typer.opcode_cast_domain in H.
        repeat mytac (eq_refl Z) (eq_refl Z) (eq_refl Z).
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

  Definition un_address ty (addr : syntax.concrete_data ty) :
    Datatypes.option (comparable.comparable_data address) :=
    match addr return Datatypes.option (comparable.comparable_data address) with
    | Address_constant x => Some x
    | _ => None
    end.

  Lemma un_address_some ty (addr : syntax.concrete_data ty) (H : ty = address) :
    exists x, un_address ty addr = Some x.
  Proof.
    destruct addr; try discriminate.
    simpl; eexists; reflexivity.
  Qed.

  Lemma un_address_some_rev ty (addr : syntax.concrete_data ty) x :
    un_address ty addr = Some x ->
    exists He, eq_rect ty syntax.concrete_data addr address He = Address_constant x.
  Proof.
    destruct addr; try discriminate.
    simpl.
    intro Hs; injection Hs; intro; subst x.
    exists eq_refl.
    reflexivity.
  Qed.

  Lemma concrete_address_inversion (addr : syntax.concrete_data (Comparable_type address)) :
    exists x : comparable.comparable_data address,
      addr = Address_constant x.
  Proof.
    case_eq (un_address address addr).
    - intros c Hc.
      apply un_address_some_rev in Hc.
      destruct Hc as (Haddr, H).
      assert (Haddr = eq_refl) by (apply Eqdep_dec.UIP_dec; apply type_dec).
      subst Haddr.
      simpl in H.
      eexists; eassumption.
    - intro H.
      destruct (un_address_some address addr eq_refl) as (c, Hc).
      congruence.
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
        destruct (concrete_address_inversion x') as (x, Hx).
        subst x'.
        simpl.
        destruct s as [|c1 [|c2 s]]; try discriminate.
        destruct (ascii_dec c1 "t").
        + destruct (ascii_dec c2 "z"); try discriminate.
          injection H; intros; subst x.
          congruence.
        + destruct s as [|c3 s]; try discriminate.
          destruct (ascii_dec c1 "K"); try discriminate.
          destruct (ascii_dec c2 "T"); try discriminate.
          destruct (ascii_dec c3 "1"); try discriminate.
          injection H; intros; subst x.
          congruence.
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
        + simpl.
          f_equal.
          match goal with | H : ?F l = Return x |- _ => pose F as type_data_list end.
          change (type_data_list l = Return x) in H.
          assert (exists l', l' = l) as Hl' by (exists l; reflexivity).
          rename l into linit.
          destruct Hl' as (l, Hl).
          rewrite <- Hl in H.
          rewrite <- Hl.
          clear Hl.
          generalize dependent x.
          induction l; simpl in *.
          * repeat mytac type_untype type_untype_seq type_untype_data.
          * repeat mytac type_untype type_untype_seq type_untype_data.
            destruct a0; try discriminate.
            repeat mytac type_untype type_untype_seq type_untype_data.
            simpl.
            f_equal.
            apply IHl.
            assumption.
        + simpl.
          f_equal.
          match goal with | H : ?F l = Return x |- _ => pose F as type_data_list end.
          change (type_data_list l = Return x) in H.
          assert (exists l', l' = l) as Hl' by (exists l; reflexivity).
          rename l into linit.
          destruct Hl' as (l, Hl).
          rewrite <- Hl in H.
          rewrite <- Hl.
          clear Hl.
          generalize dependent x.
          induction l; simpl in *.
          * repeat mytac type_untype type_untype_seq type_untype_data.
          * repeat mytac type_untype type_untype_seq type_untype_data.
            destruct a0; try discriminate.
            repeat mytac type_untype type_untype_seq type_untype_data.
            simpl.
            f_equal.
            apply IHl.
            assumption.
      - repeat mytac type_untype type_untype_seq type_untype_data.
    }
  Qed.
