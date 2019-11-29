Require Import ZArith List.
Require Import syntax.
Require Import typer.
Require Import untyped_syntax error.
Require Eqdep_dec.
Import error.Notations.

(* Not really needed but eases reading of proof states. *)
Require Import String.

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

  Fixpoint untype_data {a} (d : syntax.concrete_data a) : concrete_data :=
    match d with
    | syntax.Int_constant z => Int_constant z
    | syntax.Nat_constant n => Int_constant (Z.of_N n)
    | syntax.String_constant s => String_constant s
    | syntax.Mutez_constant (Mk_mutez m) => Int_constant (tez.to_Z m)
    | syntax.Bytes_constant s => Bytes_constant s
    | syntax.Timestamp_constant t => Int_constant t
    | syntax.Signature_constant s => String_constant s
    | syntax.Key_constant s => String_constant s
    | syntax.Key_hash_constant s => String_constant s
    | syntax.Address_constant (Mk_address c) => String_constant c
    | syntax.Unit => Unit
    | syntax.True_ => True_
    | syntax.False_ => False_
    | syntax.Pair x y => Pair (untype_data x) (untype_data y)
    | syntax.Left x _ _ => Left (untype_data x)
    | syntax.Right y _ _ => Right (untype_data y)
    | syntax.Some_ x => Some_ (untype_data x)
    | syntax.None_ => None_
    | syntax.Concrete_list l => Concrete_seq (List.map (fun x => untype_data x) l)
    | syntax.Concrete_set l => Concrete_seq (List.map (fun x => untype_data x) l)
    | syntax.Concrete_map l =>
      Concrete_seq (List.map
                      (fun '(syntax.Elt _ _ x y) => Elt (untype_data x) (untype_data y))
                      l)
    | syntax.Instruction _ i => Instruction (untype_instruction i)
    | syntax.Chain_id_constant (Mk_chain_id c) => String_constant c
    end
  with
  untype_instruction {self_type tff0 A B} (i : syntax.instruction self_type tff0 A B) : instruction :=
    match i with
    | syntax.NOOP => NOOP
    | syntax.FAILWITH => FAILWITH
    | syntax.SEQ i1 i2 => SEQ (untype_instruction i1) (untype_instruction i2)
    | syntax.IF_ f i1 i2 => IF_ (untype_if_family f) (untype_instruction i1) (untype_instruction i2)
    | syntax.LOOP_ f i => LOOP_ (untype_loop_family f) (untype_instruction i)
    | syntax.DIP n _ i => DIP n (untype_instruction i)
    | syntax.EXEC => EXEC
    | syntax.PUSH a x => PUSH a (untype_data x)
    | syntax.LAMBDA a b i => LAMBDA a b (untype_instruction i)
    | syntax.ITER i => ITER (untype_instruction i)
    | syntax.MAP i => MAP (untype_instruction i)
    | syntax.CREATE_CONTRACT g p an i => CREATE_CONTRACT g p an (untype_instruction i)
    | syntax.SELF an _ => SELF an
    | syntax.Instruction_opcode o => instruction_opcode (untype_opcode o)
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

  Fixpoint tail_fail_induction self_type A B (i : syntax.instruction self_type true A B)
        (P : forall self_type A B, syntax.instruction self_type true A B -> Type)
        (HFAILWITH : forall st a A B, P st (a ::: A) B syntax.FAILWITH)
        (HSEQ : forall st A B C i1 i2,
            P st B C i2 ->
            P st A C (i1;; i2))
        (HIF : forall st A B C1 C2 t (f : syntax.if_family C1 C2 t) i1 i2,
            P st (C1 ++ A) B i1 ->
            P st (C2 ++ A) B i2 ->
            P st (t ::: A) B (syntax.IF_ f i1 i2))
    : P self_type A B i :=
    let P' st b A B : syntax.instruction st b A B -> Type :=
        if b return syntax.instruction st b A B -> Type
        then P st A B
        else fun i => True
    in
    match i as i0 in syntax.instruction st b A B return P' st b A B i0
    with
    | syntax.FAILWITH => HFAILWITH _ _ _ _
    | @syntax.SEQ _ A B C tff i1 i2 =>
      (if tff return
          forall i2 : syntax.instruction _ tff B C,
            P' _ tff A C (syntax.SEQ i1 i2)
       then
         fun i2 =>
           HSEQ _ _ _ _ i1 i2
                (tail_fail_induction _ B C i2 P HFAILWITH HSEQ HIF)
       else fun i2 => I)
        i2
    | @syntax.IF_ _ A B tffa tffb _ _ _ f i1 i2 =>
      (if tffa as tffa return
          forall i1, P' _ (tffa && tffb)%bool _ _ (syntax.IF_ f i1 i2)
       then
         fun i1 =>
           (if tffb return
               forall i2,
                 P' _ tffb _ _ (syntax.IF_ f i1 i2)
            then
              fun i2 =>
                HIF _ _ _ _ _ _ f i1 i2
                    (tail_fail_induction _ _ _ i1 P HFAILWITH HSEQ HIF)
                    (tail_fail_induction _ _ _ i2 P HFAILWITH HSEQ HIF)
            else
              fun _ => I) i2
       else
         fun _ => I) i1
    | _ => I
    end.

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

  Definition tail_fail_change_range {self_type} A B B' (i : syntax.instruction self_type true A B) :
    syntax.instruction self_type true A B'.
  Proof.
    apply (tail_fail_induction self_type A B i (fun self_type A B i => syntax.instruction self_type true A B')); clear A B i.
    - intros st a A _.
      apply syntax.FAILWITH.
    - intros st A B C i1 _ i2.
      apply (syntax.SEQ i1 i2).
    - intros st A B C1 C2 t f _ _ i1 i2.
      apply (syntax.IF_ f i1 i2).
  Defined.


  Lemma tail_fail_change_range_same {self_type} A B (i : syntax.instruction self_type true A B) :
    tail_fail_change_range A B B i = i.
  Proof.
    apply (tail_fail_induction _ A B i); clear A B i;
      intros; unfold tail_fail_change_range; simpl; f_equal; assumption.
  Qed.

  Definition untype_type_spec {self_type} tffi A B (i : syntax.instruction self_type tffi A B) :=
    typer.type_instruction (untype_instruction i) A =
    Return ((if tffi return syntax.instruction self_type tffi A B -> typer.typer_result A
               then
                 fun i =>
                   typer.Any_type _ (fun B' => tail_fail_change_range A B B' i)
               else
                 typer.Inferred_type _ B) i).

  Lemma instruction_cast_same {self_type} tffi A B (i : syntax.instruction self_type tffi A B) :
    typer.instruction_cast A A B B i = Return i.
  Proof.
    unfold typer.instruction_cast.
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
    typer.type_check_instruction typer.type_instruction (untype_instruction i) A B =
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

  Lemma untype_type_check_instruction_no_tail_fail {self_type} A B (i : syntax.instruction self_type false A B) :
    untype_type_spec _ _ _ i ->
    typer.type_check_instruction_no_tail_fail typer.type_instruction (untype_instruction i) A B =
    Return i.
  Proof.
    intro IH.
    unfold typer.type_check_instruction_no_tail_fail.
    rewrite IH.
    simpl.
    apply instruction_cast_range_same.
  Qed.

  Lemma untype_type_instruction_no_tail_fail {self_type} A B (i : syntax.instruction self_type false A B) :
    untype_type_spec _ _ _ i ->
    typer.type_instruction_no_tail_fail typer.type_instruction (untype_instruction i) A = Return (existT _ _ i).
  Proof.
    intro IH.
    unfold typer.type_instruction_no_tail_fail.
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
    typer.type_data (untype_data d) a = Return d
  with
  untype_type_instruction {self_type} tffi A B (i : syntax.instruction self_type tffi A B) :
    untype_type_spec _ _ _ i.
  Proof.
    - destruct d; try reflexivity.
      + simpl.
        assert (0 <= Z.of_N n)%Z as H by apply N2Z.is_nonneg.
        rewrite <- Z.geb_le in H.
        rewrite H.
        rewrite N2Z.id.
        reflexivity.
      + simpl.
        destruct m.
        trans_refl (
          let! m := tez.of_Z (tez.to_Z m) in
          Return (syntax.Mutez_constant (Mk_mutez m))
        ).
        rewrite tez.of_Z_to_Z.
        reflexivity.
      + simpl.
        destruct a.
        simpl.
        reflexivity.
      + simpl.
        trans_refl (
          let! x := typer.type_data (untype_data d1) a in
          let! y := typer.type_data (untype_data d2) b in
          Return (@syntax.Pair a b x y)
        ).
        rewrite (untype_type_data _ d1).
        rewrite (untype_type_data _ d2).
        reflexivity.
      + trans_refl (
          let! x := typer.type_data (untype_data d) a in
          Return (@syntax.Left a b x an bn)
        ).
        rewrite (untype_type_data _ d).
        reflexivity.
      + trans_refl (
          let! x := typer.type_data (untype_data d) b in
          Return (@syntax.Right a b x an bn)
        ).
        rewrite (untype_type_data _ d).
        reflexivity.
      + trans_refl (
          let! x := typer.type_data (untype_data d) a in
          Return (@syntax.Some_ a x)
        ).
        rewrite (untype_type_data _ d).
        reflexivity.
      + pose (fix type_data_list (l : Datatypes.list concrete_data) :=
                match l with
                | nil => Return nil
                | cons x l =>
                  let! x := typer.type_data x a in
                  let! l := type_data_list l in
                  Return (cons x l)
                end) as type_data_list.
        assert (forall l, type_data_list (List.map (fun x => untype_data x) l) = Return l).
        * clear l.
          intro l; induction l.
          -- reflexivity.
          -- simpl.
             rewrite untype_type_data.
             rewrite IHl.
             reflexivity.
        * trans_refl (
            let! l := type_data_list (List.map (fun x => untype_data x) l) in
            Return (@syntax.Concrete_list a l)
          ).
          rewrite H.
          reflexivity.
      + pose (fix type_data_set (l : Datatypes.list concrete_data) :=
                match l with
                | nil => Return nil
                | cons x l =>
                  let! x := typer.type_data x a in
                  let! l := type_data_set l in
                  Return (cons x l)
                end) as type_data_set.
        assert (forall l, type_data_set (List.map (fun x => untype_data x) l) = Return l).
        * clear l.
          intro l; induction l.
          -- reflexivity.
          -- simpl.
             rewrite untype_type_data.
             rewrite IHl.
             reflexivity.
        * trans_refl (
            let! l := type_data_set (List.map (fun x => untype_data x) l) in
            Return (@syntax.Concrete_set a l)
          ).
          rewrite H.
          reflexivity.
      + pose (fix type_data_list L :=
                   match L with
                   | nil => Return nil
                   | cons (Elt x y) l =>
                    let! x := type_data x a in
                    let! y := type_data y b in
                    let! l := type_data_list l in
                    Return (cons (syntax.Elt _ _ x y) l)
                   | _ => Failed _ (Typing _ (untype_data (syntax.Concrete_map l), (map a b)))
                   end) as type_data_map.
        assert (forall l, type_data_map (List.map (fun '(syntax.Elt _ _ x y) => Elt (untype_data x) (untype_data y)) l) = Return l).
        * intro L; induction L.
          -- reflexivity.
          -- simpl.
             destruct a0.
             rewrite untype_type_data.
             rewrite untype_type_data.
             rewrite IHL.
             reflexivity.
        * trans_refl (
            let! l := type_data_map (List.map (fun '(syntax.Elt _ _ x y) => Elt (untype_data x) (untype_data y)) l) in
            Return (@syntax.Concrete_map a b l)
          ).
          rewrite H.
          reflexivity.
      + simpl.
        rewrite untype_type_check_instruction; auto.
      + simpl.
        destruct c.
        simpl.
        reflexivity.
    - destruct i; try reflexivity; simpl.
      + trans_refl (
          let! existT _ B i1 :=
            typer.type_instruction_no_tail_fail typer.type_instruction
              (untype_instruction i1) A in
          let! r2 := typer.type_instruction (untype_instruction i2) B in
          match r2 with
          | typer.Inferred_type _ C i2 =>
            Return (typer.Inferred_type _ _ (syntax.SEQ (i1 : syntax.instruction self_type _ _ _) i2))
          | typer.Any_type _ i2 =>
            Return (typer.Any_type _ (fun C => syntax.SEQ i1 (i2 C)))
          end
        ).
        rewrite untype_type_instruction_no_tail_fail.
        * simpl.
          rewrite untype_type_instruction.
          destruct tff; reflexivity.
        * auto.
      + unfold untype_type_spec.
        simpl.
        unfold type_branches.
        assert (type_if_family (untype_if_family i1) t = Return (existT _ C1 (existT _ C2 i1))) as Hi1.
        * destruct i1; reflexivity.
        * rewrite Hi1.
          simpl.
          rewrite untype_type_instruction; simpl.
          rewrite untype_type_instruction; simpl.
          destruct tffa; destruct tffb;
            try rewrite instruction_cast_range_same; simpl; repeat f_equal; apply tail_fail_change_range_same.
      + unfold untype_type_spec.
        simpl.
        unfold type_loop.
        assert (type_loop_family (untype_loop_family i) t = Return (existT _ C1 (existT _ C2 i))) as Hi.
        * destruct i; reflexivity.
        * rewrite Hi.
          simpl.
          rewrite untype_type_check_instruction_no_tail_fail.
          -- reflexivity.
          -- apply untype_type_instruction.
      + trans_refl (
          let! d := typer.type_data (untype_data x) a in
          Return (@typer.Inferred_type self_type A _ (syntax.PUSH a d))
        ).
        rewrite untype_type_data.
        reflexivity.
      + trans_refl (
          let! existT _ tff i :=
            typer.type_check_instruction
              typer.type_instruction (untype_instruction i) (a :: nil) (b :: nil) in
          Return (@typer.Inferred_type self_type _ (lambda a b ::: A) (syntax.LAMBDA a b i))
        ).
        rewrite untype_type_check_instruction; auto.
      + destruct i as [c v]; destruct v.
        * unfold untype_type_spec; simpl.
          rewrite untype_type_check_instruction_no_tail_fail; auto.
        * unfold untype_type_spec; simpl.
          rewrite untype_type_check_instruction_no_tail_fail; auto.
        * unfold untype_type_spec; simpl.
          rewrite untype_type_check_instruction_no_tail_fail; auto.
      + destruct i as [a c v]; destruct v.
        * unfold untype_type_spec; simpl.
          rewrite untype_type_instruction_no_tail_fail.
          -- simpl.
             rewrite instruction_cast_range_same.
             reflexivity.
          -- auto.
        * unfold untype_type_spec; simpl.
          rewrite untype_type_instruction_no_tail_fail.
          -- simpl.
             rewrite instruction_cast_range_same.
             reflexivity.
          -- auto.
      + unfold untype_type_spec; simpl.
        rewrite untype_type_check_instruction.
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
        rewrite untype_type_instruction_no_tail_fail.
        * simpl.
          rewrite instruction_cast_domain_same.
          reflexivity.
        * apply untype_type_instruction.
      + unfold untype_type_spec.
        simpl.
        rewrite untype_type_opcode.
        reflexivity.
  Qed.
