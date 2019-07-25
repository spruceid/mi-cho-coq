Require Import ZArith List.
Require Import syntax.
Require Import untyped_syntax error.
Require typer.
Require Eqdep_dec.

Module Untyper(ST: SelfType)(C:ContractContext).

  Module syntax := Syntax ST C.
  Module typer := typer.Typer ST C.
  Import typer. Import syntax. Import untyped_syntax.


  Fixpoint untype_data {a} (d : syntax.concrete_data a) : concrete_data :=
    match d with
    | syntax.Int_constant z => Int_constant z
    | syntax.Nat_constant n => Nat_constant n
    | syntax.String_constant s => String_constant s
    | syntax.Mutez_constant m => Mutez_constant m
    | syntax.Bytes_constant s => Bytes_constant s
    | syntax.Timestamp_constant t => Timestamp_constant t
    | syntax.Signature_constant s => Signature_constant s
    | syntax.Key_constant s => Key_constant s
    | syntax.Key_hash_constant s => Key_hash_constant s
    | syntax.Contract_constant c _ => Contract_constant c
    | syntax.Address_constant c => Address_constant c
    | syntax.Unit => Unit
    | syntax.True_ => True_
    | syntax.False_ => False_
    | syntax.Pair x y => Pair (untype_data x) (untype_data y)
    | syntax.Left x => Left (untype_data x)
    | syntax.Right y => Right (untype_data y)
    | syntax.Some_ x => Some_ (untype_data x)
    | syntax.None_ => None_
    | syntax.Concrete_list l => Concrete_seq (List.map (fun x => untype_data x) l)
    | syntax.Concrete_set l => Concrete_seq (List.map (fun x => untype_data x) l)
    | syntax.Concrete_map l =>
      Concrete_seq (List.map
                      (fun '(syntax.Elt _ _ x y) => Elt (untype_data x) (untype_data y))
                      l)
    | syntax.Instruction _ i => Instruction (untype_instruction i)
    | syntax.Chain_id_constant c => Chain_id_constant c
    end
  with
  untype_instruction {tff0 A B} (i : syntax.instruction tff0 A B) : instruction :=
    match i with
    | syntax.NOOP => NOOP
    | syntax.FAILWITH => FAILWITH
    | syntax.SEQ i1 i2 => SEQ (untype_instruction i1) (untype_instruction i2)
    | syntax.IF_ i1 i2 => IF_ (untype_instruction i1) (untype_instruction i2)
    | syntax.LOOP i => LOOP (untype_instruction i)
    | syntax.LOOP_LEFT i => LOOP_LEFT (untype_instruction i)
    | syntax.DIP n _ i => DIP n (untype_instruction i)
    | syntax.EXEC => EXEC
    | syntax.APPLY => APPLY
    | syntax.DROP n _ => DROP n
    | syntax.DUP => DUP
    | syntax.SWAP => SWAP
    | syntax.PUSH a x => PUSH a (untype_data x)
    | syntax.UNIT => UNIT
    | syntax.LAMBDA a b i => LAMBDA a b (untype_instruction i)
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
    | syntax.SIZE => SIZE
    | syntax.SLICE => SLICE
    | syntax.PAIR => PAIR
    | syntax.CAR => CAR
    | syntax.CDR => CDR
    | syntax.EMPTY_SET a => EMPTY_SET a
    | syntax.MEM => MEM
    | syntax.UPDATE => UPDATE
    | syntax.ITER i => ITER (untype_instruction i)
    | syntax.EMPTY_MAP kty vty => EMPTY_MAP kty vty
    | syntax.GET => GET
    | syntax.MAP i => MAP (untype_instruction i)
    | syntax.SOME => SOME
    | syntax.NONE a => NONE a
    | syntax.IF_NONE i1 i2 => IF_NONE (untype_instruction i1) (untype_instruction i2)
    | syntax.LEFT b => LEFT b
    | syntax.RIGHT a => RIGHT a
    | syntax.IF_LEFT i1 i2 => IF_LEFT (untype_instruction i1) (untype_instruction i2)
    | syntax.IF_RIGHT i1 i2 => IF_RIGHT (untype_instruction i1) (untype_instruction i2)
    | syntax.CONS => CONS
    | syntax.NIL a => NIL a
    | syntax.IF_CONS i1 i2 => IF_CONS (untype_instruction i1) (untype_instruction i2)
    | syntax.CREATE_CONTRACT g p i => CREATE_CONTRACT g p (untype_instruction i)
    | syntax.TRANSFER_TOKENS => TRANSFER_TOKENS
    | syntax.SET_DELEGATE => SET_DELEGATE
    | syntax.BALANCE => BALANCE
    | syntax.ADDRESS => ADDRESS
    | syntax.CONTRACT a => CONTRACT a
    | syntax.SOURCE => SOURCE
    | syntax.SENDER => SENDER
    | syntax.SELF => SELF
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

  Fixpoint tail_fail_induction A B (i : syntax.instruction true A B)
        (P : forall A B, syntax.instruction true A B -> Type)
        (HFAILWITH : forall a A B, P (a ::: A) B syntax.FAILWITH)
        (HSEQ : forall A B C i1 i2,
            P B C i2 ->
            P A C (i1;; i2))
        (HIF : forall A B i1 i2,
            P A B i1 ->
            P A B i2 ->
            P (bool ::: A) B (syntax.IF_ i1 i2))
        (HIF_NONE : forall a A B i1 i2,
            P A B i1 ->
            P (a ::: A) B i2 ->
            P (option a ::: A) B (syntax.IF_NONE i1 i2))
        (HIF_LEFT : forall a b A B i1 i2,
            P (a ::: A) B i1 ->
            P (b ::: A) B i2 ->
            P (or a b ::: A) B (syntax.IF_LEFT i1 i2))
        (HIF_RIGHT : forall a b A B i1 i2,
            P (b ::: A) B i1 ->
            P (a ::: A) B i2 ->
            P (or a b ::: A) B (syntax.IF_RIGHT i1 i2))
        (HIF_CONS : forall a A B i1 i2,
            P (a ::: list a ::: A) B i1 ->
            P A B i2 ->
            P (list a ::: A) B (syntax.IF_CONS i1 i2))
    : P A B i :=
    let P' b A B : syntax.instruction b A B -> Type :=
        if b return syntax.instruction b A B -> Type
        then P A B
        else fun i => True
    in
    match i as i0 in syntax.instruction b A B return P' b A B i0
    with
    | syntax.FAILWITH => HFAILWITH _ _ _
    | @syntax.SEQ A B C tff i1 i2 =>
      (if tff return
          forall i2 : syntax.instruction tff B C,
            P' tff A C (syntax.SEQ i1 i2)
       then
         fun i2 =>
           HSEQ _ _ _ i1 i2
                (tail_fail_induction B C i2 P HFAILWITH HSEQ HIF HIF_NONE HIF_LEFT HIF_RIGHT HIF_CONS)
       else fun i2 => I)
        i2
    | @syntax.IF_ A B tffa tffb i1 i2 =>
      (if tffa as tffa return
          forall i1, P' (tffa && tffb)%bool _ _ (syntax.IF_ i1 i2)
       then
         fun i1 =>
           (if tffb return
               forall i2,
                 P' tffb _ _ (syntax.IF_ i1 i2)
            then
              fun i2 =>
                HIF _ _ i1 i2
                    (tail_fail_induction _ _ i1 P HFAILWITH HSEQ HIF HIF_NONE HIF_LEFT HIF_RIGHT HIF_CONS)
                    (tail_fail_induction _ _ i2 P HFAILWITH HSEQ HIF HIF_NONE HIF_LEFT HIF_RIGHT HIF_CONS)
            else
              fun _ => I) i2
       else
         fun _ => I) i1
    | @syntax.IF_NONE a A B tffa tffb i1 i2 =>
      (if tffa as tffa return
          forall i1, P' (tffa && tffb)%bool _ _ (syntax.IF_NONE i1 i2)
       then
         fun i1 =>
           (if tffb return
               forall i2,
                 P' tffb _ _ (syntax.IF_NONE i1 i2)
            then
              fun i2 =>
                HIF_NONE _ _ _ i1 i2
                    (tail_fail_induction _ _ i1 P HFAILWITH HSEQ HIF HIF_NONE HIF_LEFT HIF_RIGHT HIF_CONS)
                    (tail_fail_induction _ _ i2 P HFAILWITH HSEQ HIF HIF_NONE HIF_LEFT HIF_RIGHT HIF_CONS)
            else
              fun _ => I) i2
       else
         fun _ => I) i1
    | @syntax.IF_LEFT a b A B tffa tffb i1 i2 =>
      (if tffa as tffa return
          forall i1, P' (tffa && tffb)%bool _ _ (syntax.IF_LEFT i1 i2)
       then
         fun i1 =>
           (if tffb return
               forall i2,
                 P' tffb _ _ (syntax.IF_LEFT i1 i2)
            then
              fun i2 =>
                HIF_LEFT _ _ _ _ i1 i2
                    (tail_fail_induction _ _ i1 P HFAILWITH HSEQ HIF HIF_NONE HIF_LEFT HIF_RIGHT HIF_CONS)
                    (tail_fail_induction _ _ i2 P HFAILWITH HSEQ HIF HIF_NONE HIF_LEFT HIF_RIGHT HIF_CONS)
            else
              fun _ => I) i2
       else
         fun _ => I) i1
    | @syntax.IF_RIGHT a b A B tffa tffb i1 i2 =>
      (if tffa as tffa return
          forall i1, P' (tffa && tffb)%bool _ _ (syntax.IF_RIGHT i1 i2)
       then
         fun i1 =>
           (if tffb return
               forall i2,
                 P' tffb _ _ (syntax.IF_RIGHT i1 i2)
            then
              fun i2 =>
                HIF_RIGHT _ _ _ _ i1 i2
                    (tail_fail_induction _ _ i1 P HFAILWITH HSEQ HIF HIF_NONE HIF_LEFT HIF_RIGHT HIF_CONS)
                    (tail_fail_induction _ _ i2 P HFAILWITH HSEQ HIF HIF_NONE HIF_LEFT HIF_RIGHT HIF_CONS)
            else
              fun _ => I) i2
       else
         fun _ => I) i1
    | @syntax.IF_CONS a A B tffa tffb i1 i2 =>
      (if tffa as tffa return
          forall i1, P' (tffa && tffb)%bool _ _ (syntax.IF_CONS i1 i2)
       then
         fun i1 =>
           (if tffb return
               forall i2,
                 P' tffb _ _ (syntax.IF_CONS i1 i2)
            then
              fun i2 =>
                HIF_CONS _ _ _ i1 i2
                    (tail_fail_induction _ _ i1 P HFAILWITH HSEQ HIF HIF_NONE HIF_LEFT HIF_RIGHT HIF_CONS)
                    (tail_fail_induction _ _ i2 P HFAILWITH HSEQ HIF HIF_NONE HIF_LEFT HIF_RIGHT HIF_CONS)
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

  Definition tail_fail_change_range A B B' (i : syntax.instruction true A B) :
    syntax.instruction true A B'.
  Proof.
    apply (tail_fail_induction A B i (fun A B i => syntax.instruction true A B')); clear A B i.
    - intros a A _.
      apply syntax.FAILWITH.
    - intros A B C i1 _ i2.
      apply (syntax.SEQ i1 i2).
    - intros A B _ _ i1 i2.
      apply (syntax.IF_ i1 i2).
    - intros a A B _ _ i1 i2.
      apply (syntax.IF_NONE i1 i2).
    - intros a b A B _ _ i1 i2.
      apply (syntax.IF_LEFT i1 i2).
    - intros a b A B _ _ i1 i2.
      apply (syntax.IF_RIGHT i1 i2).
    - intros a A B _ _ i1 i2.
      apply (syntax.IF_CONS i1 i2).
  Defined.


  Lemma tail_fail_change_range_same A B (i : syntax.instruction true A B) :
    tail_fail_change_range A B B i = i.
  Proof.
    apply (tail_fail_induction A B i); clear A B i;
      intros; unfold tail_fail_change_range; simpl; f_equal; assumption.
  Qed.

  Definition untype_type_spec tffi A B (i : syntax.instruction tffi A B) :=
    typer.type_instruction (untype_instruction i) A =
    Return _ ((if tffi return syntax.instruction tffi A B -> typer.typer_result A
               then
                 fun i =>
                   typer.Any_type _ (fun B' => tail_fail_change_range A B B' i)
               else
                 typer.Inferred_type _ B) i).

  Lemma instruction_cast_same tffi A B (i : syntax.instruction tffi A B) :
    typer.instruction_cast A A B B i = Return _ i.
  Proof.
    unfold typer.instruction_cast.
    rewrite stype_dec_same.
    rewrite stype_dec_same.
    reflexivity.
  Qed.

  Lemma instruction_cast_range_same tffi A B (i : syntax.instruction tffi A B) :
    typer.instruction_cast_range A B B i = Return _ i.
  Proof.
    apply instruction_cast_same.
  Qed.

  Lemma instruction_cast_domain_same tffi A B (i : syntax.instruction tffi A B) :
    typer.instruction_cast_domain A A B i = Return _ i.
  Proof.
    apply instruction_cast_same.
  Qed.

  Lemma untype_type_check_instruction tffi A B (i : syntax.instruction tffi A B) :
    untype_type_spec _ _ _ i ->
    typer.type_check_instruction typer.type_instruction (untype_instruction i) A B =
    Return _ (existT _ tffi i).
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

  Lemma untype_type_check_instruction_no_tail_fail A B (i : syntax.instruction false A B) :
    untype_type_spec _ _ _ i ->
    typer.type_check_instruction_no_tail_fail typer.type_instruction (untype_instruction i) A B =
    Return _ i.
  Proof.
    intro IH.
    unfold typer.type_check_instruction_no_tail_fail.
    rewrite IH.
    simpl.
    apply instruction_cast_range_same.
  Qed.

  Lemma untype_type_instruction_no_tail_fail A B (i : syntax.instruction false A B) :
    untype_type_spec _ _ _ i ->
    typer.type_instruction_no_tail_fail typer.type_instruction (untype_instruction i) A = Return _ (existT _ _ i).
  Proof.
    intro IH.
    unfold typer.type_instruction_no_tail_fail.
    rewrite IH.
    reflexivity.
  Qed.

  Inductive IF_instruction : forall (A1 A2 A : Datatypes.list type), Set :=
  | IF_i A : IF_instruction A A (bool ::: A)
  | IF_NONE_i a A : IF_instruction A (a ::: A) (option a ::: A)
  | IF_LEFT_i a b A : IF_instruction (a ::: A) (b ::: A) (or a b ::: A)
  | IF_RIGHT_i a b A : IF_instruction (b ::: A) (a ::: A) (or a b ::: A)
  | IF_CONS_i a A : IF_instruction (a ::: list a ::: A) A (list a ::: A).

  Definition IF_instruction_to_instruction A1 A2 A (IFi : IF_instruction A1 A2 A) :
    forall B tffa tffb,
      syntax.instruction tffa A1 B ->
      syntax.instruction tffb A2 B -> syntax.instruction (tffa && tffb) A B :=
    match IFi with
    | IF_i A => fun B ttffa tffb i1 i2 => syntax.IF_ i1 i2
    | IF_NONE_i a A => fun B ttffa tffb i1 i2 => syntax.IF_NONE i1 i2
    | IF_LEFT_i a b A => fun B ttffa tffb i1 i2 => syntax.IF_LEFT i1 i2
    | IF_RIGHT_i a b A => fun B ttffa tffb i1 i2 => syntax.IF_RIGHT i1 i2
    | IF_CONS_i a A => fun B ttffa tffb i1 i2 => syntax.IF_CONS i1 i2
    end.

  Lemma untype_type_branches tff1 tff2 A1 A2 A B
        (i1 : syntax.instruction tff1 A1 B)
        (i2 : syntax.instruction tff2 A2 B) IF_instr :
    untype_type_spec _ _ _ i1 ->
    untype_type_spec _ _ _ i2 ->
    typer.type_branches typer.type_instruction
                        (untype_instruction i1)
                        (untype_instruction i2)
                        A1 A2 A (IF_instruction_to_instruction A1 A2 A IF_instr) =
    Return _ ((if (tff1 && tff2)%bool
                 as b return syntax.instruction b A B -> typer.typer_result A
               then
                 fun i =>
                   typer.Any_type _ (fun B' => tail_fail_change_range A B B' i)
               else
                 typer.Inferred_type _ B) (IF_instruction_to_instruction A1 A2 A IF_instr B tff1 tff2 i1 i2)).
  Proof.
    intros IH1 IH2.
    unfold typer.type_branches.
    rewrite IH1.
    rewrite IH2.
    simpl.
    destruct tff1; destruct tff2; simpl.
    - f_equal.
      f_equal.
      destruct IF_instr; simpl; unfold tail_fail_change_range; reflexivity.
    - rewrite tail_fail_change_range_same.
      reflexivity.
    - rewrite tail_fail_change_range_same.
      reflexivity.
    - rewrite instruction_cast_range_same.
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

  Fixpoint untype_type_data a (d : syntax.concrete_data a) :
    typer.type_data (untype_data d) a = Return _ d
  with
  untype_type_instruction tffi A B (i : syntax.instruction tffi A B) :
    untype_type_spec _ _ _ i.
  Proof.
    - destruct d; try reflexivity.
      + simpl.
        unfold typer.type_data.
        destruct (mtype_dec (C.get_contract_type cst) (Return _ a)).
        * f_equal. f_equal.
          apply Eqdep_dec.UIP_dec.
          apply M_dec.
          apply type_dec.
        * congruence.
      + simpl.
        trans_refl (bind (fun x => bind (fun y => Return _ (@syntax.Pair a b x y)) (typer.type_data (untype_data d2) b)) (typer.type_data (untype_data d1) a)).
        rewrite (untype_type_data _ d1).
        rewrite (untype_type_data _ d2).
        reflexivity.
      + trans_refl (bind (fun x => Return _ (@syntax.Left a b x)) (typer.type_data (untype_data d) a)).
        rewrite (untype_type_data _ d).
        reflexivity.
      + trans_refl (bind (fun x => Return _ (@syntax.Right a b x)) (typer.type_data (untype_data d) b)).
        rewrite (untype_type_data _ d).
        reflexivity.
      + trans_refl (bind (fun x => Return _ (@syntax.Some_ a x)) (typer.type_data (untype_data d) a)).
        rewrite (untype_type_data _ d).
        reflexivity.
      + pose (fix type_data_list (l : Datatypes.list concrete_data) :=
                match l with
                | nil => Return _ nil
                | cons x l =>
                  bind (fun x =>
                          bind (fun l =>
                                  Return (Datatypes.list (@syntax.concrete_data a)) (cons x l))
                               (type_data_list l))
                       (typer.type_data x a)
                end) as type_data_list.
        assert (forall l, type_data_list (List.map (fun x => untype_data x) l) = Return _ l).
        * clear l.
          intro l; induction l.
          -- reflexivity.
          -- simpl.
             rewrite untype_type_data.
             rewrite IHl.
             reflexivity.
        * trans_refl
            (bind
               (fun l => Return _ (@syntax.Concrete_list a l))
               (type_data_list (List.map (fun x => untype_data x) l))).
          rewrite H.
          reflexivity.
      + pose (fix type_data_set (l : Datatypes.list concrete_data) :=
                match l with
                | nil => Return _ nil
                | cons x l =>
                  bind (fun x =>
                          bind (fun l =>
                                  Return (Datatypes.list (@syntax.concrete_data a)) (cons x l))
                               (type_data_set l))
                       (typer.type_data x a)
                end) as type_data_set.
        assert (forall l, type_data_set (List.map (fun x => untype_data x) l) = Return _ l).
        * clear l.
          intro l; induction l.
          -- reflexivity.
          -- simpl.
             rewrite untype_type_data.
             rewrite IHl.
             reflexivity.
        * trans_refl
            (bind
               (fun l => Return _ (@syntax.Concrete_set a l))
               (type_data_set (List.map (fun x => untype_data x) l))).
          rewrite H.
          reflexivity.
      + pose (fix type_data_map (l : Datatypes.list concrete_data) :=
                match l with
                | nil =>
                  Return
                    (Datatypes.list
                       (syntax.elt_pair
                          (@syntax.concrete_data a)
                          (@syntax.concrete_data b)))
                    nil
                | cons (Elt x y) l =>
                  bind (fun x =>
                          bind (fun y =>
                                  bind (fun l =>
                                          Return _ (cons (syntax.Elt _ _ x y) l))
                                       (type_data_map l))
                               (typer.type_data y b))
                       (typer.type_data x a)
                | _ => Failed _ Typing
                end) as type_data_map.
        assert (forall l, type_data_map (List.map (fun '(syntax.Elt _ _ x y) => Elt (untype_data x) (untype_data y)) l) = Return _ l).
        * clear l.
          intro l; induction l.
          -- reflexivity.
          -- simpl.
             destruct a0.
             rewrite untype_type_data.
             rewrite untype_type_data.
             rewrite IHl.
             reflexivity.
        * trans_refl (bind
                          (fun l => Return _ (@syntax.Concrete_map a b l))
                          (type_data_map (List.map (fun '(syntax.Elt _ _ x y) => Elt (untype_data x) (untype_data y)) l))).
          rewrite H.
          reflexivity.
      + trans_refl
          (bind
             (fun '(existT _ tff i) => Return _ (syntax.Instruction _ (i : syntax.instruction _ _ _)))
             (typer.type_check_instruction
                typer.type_instruction
                (untype_instruction i)
                (cons a nil)
                (cons b nil))).
        rewrite untype_type_check_instruction; auto.
    - destruct i; try reflexivity; simpl.
      + trans_refl
          (bind (fun '(existT _ B i1) =>
                   bind (fun r2 =>
                           match r2 with
                           | typer.Inferred_type _ C i2 =>
                             Return _ (typer.Inferred_type _ _ (syntax.SEQ (i1 : syntax.instruction _ _ _) i2))
                           | typer.Any_type _ i2 =>
                             Return _ (typer.Any_type _ (fun C => syntax.SEQ i1 (i2 C)))
                           end)
                        (typer.type_instruction (untype_instruction i2) B))
                (typer.type_instruction_no_tail_fail typer.type_instruction
                                                     (untype_instruction i1) A)).
        rewrite untype_type_instruction_no_tail_fail.
        * simpl.
          rewrite untype_type_instruction.
          destruct tff; reflexivity.
        * auto.
      + trans_refl
          (@typer.type_branches
             typer.type_instruction
             (untype_instruction i1)
             (untype_instruction i2) _ _ _
             (IF_instruction_to_instruction _ _ _ (IF_i A))).
        rewrite untype_type_branches; auto.
      + trans_refl
          (bind (fun i => Return _ (@typer.Inferred_type _ _ (syntax.LOOP i)))
           (typer.type_check_instruction_no_tail_fail
              typer.type_instruction (untype_instruction i) A (bool ::: A))).
        rewrite untype_type_check_instruction_no_tail_fail; auto.
      + trans_refl
          (bind (fun i => Return _ (@typer.Inferred_type _ _ (syntax.LOOP_LEFT i)))
           (typer.type_check_instruction_no_tail_fail
              typer.type_instruction (untype_instruction i) _ (or a b ::: A))).
        rewrite untype_type_check_instruction_no_tail_fail; auto.
      + trans_refl
          (let A := a :: lambda a b :: C in
           bind (fun i => Return _ (@typer.Inferred_type _ _ i))
                (typer.instruction_cast_domain A A _ syntax.EXEC)).
        simpl.
        rewrite instruction_cast_domain_same.
        reflexivity.
      + pose (A := a :: lambda (pair a b) c :: D).
        trans_refl
          ((if is_packable a as b return is_packable a = b -> _
            then fun i =>
                   bind (fun i => Return _ (Inferred_type _ _ i))
                        (instruction_cast_domain A A _ (@syntax.APPLY _ _ _ _ (IT_eq_rev _ i)))
            else fun _ => Failed _ Typing) eq_refl).
        assert (forall (b : Datatypes.bool) i0,
                   (if b return is_packable a = b -> _
                    then fun i =>
                           bind (fun i => Return _ (Inferred_type _ _ i))
                                (instruction_cast_domain A A _ (@syntax.APPLY _ _ _ _ (IT_eq_rev _ i)))
                    else fun _ => Failed _ Typing) i0
                   = Return _ (Inferred_type A _ (@syntax.APPLY _ _ _ _ i))).
        * intros b0 i0.
          destruct b0.
          -- rewrite instruction_cast_domain_same.
             simpl.
             repeat f_equal.
             apply Is_true_UIP.
          -- exfalso.
             rewrite i0 in i.
             exact i.
        * apply H.
      + trans_refl
          (bind (fun d => Return _ (@typer.Inferred_type A _ (syntax.PUSH a d)))
                (typer.type_data (untype_data x) a)).
        rewrite untype_type_data.
        reflexivity.
      + trans_refl
          (bind (fun '(existT _ tff i) =>
                   Return _ (@typer.Inferred_type _ (lambda a b ::: A) (syntax.LAMBDA a b i)))
                (typer.type_check_instruction
                   typer.type_instruction (untype_instruction i) (a :: nil) (b :: nil))).
        rewrite untype_type_check_instruction; auto.
      + destruct s as [v]; destruct v; reflexivity.
      + destruct s as [v]; destruct v; reflexivity.
      + destruct s as [v]; destruct v; reflexivity.
      + destruct s as [a v]; destruct v; reflexivity.
      + destruct s as [v]; destruct v; reflexivity.
      + destruct s as [c v]; destruct v; reflexivity.
      + destruct s as [c v]; destruct v; reflexivity.
      + destruct s as [c v]; destruct v; reflexivity.
      + destruct s as [c d v]; destruct v; reflexivity.
      + trans_refl (type_instruction (untype_instruction (syntax.COMPARE (a := a) (S := S))) (a ::: a ::: S)).
        destruct a.
        * simpl.
          rewrite instruction_cast_domain_same.
          reflexivity.
        * simpl.
          repeat rewrite as_comparable_comparable.
          simpl.
          rewrite instruction_cast_domain_same.
          simpl.
          reflexivity.
      + destruct i as [v]; destruct v; reflexivity.
      + destruct i as [v]; destruct v; reflexivity.
      + destruct i as [v]; destruct v; reflexivity.
      + destruct i as [v]; destruct v.
        * trans_refl
            (let A := a ::: set a ::: S in
             bind (fun i => Return _ (@typer.Inferred_type _ _ i))
                  (typer.instruction_cast_domain
                     A A _ (@syntax.MEM _ _ (mem_set a) _))).
          simpl.
          rewrite instruction_cast_domain_same.
          reflexivity.
        * trans_refl
            (let A := key ::: map key val ::: S in
             bind (fun i => Return _ (@typer.Inferred_type _ _ i))
                  (typer.instruction_cast_domain
                     A A _ (@syntax.MEM _ _ (mem_map key val) _))).
          simpl.
          rewrite instruction_cast_domain_same.
          reflexivity.
        * trans_refl
            (let A := key ::: big_map key val ::: S in
             bind (fun i => Return _ (@typer.Inferred_type _ _ i))
                  (typer.instruction_cast_domain
                     A A _ (@syntax.MEM _ _ (mem_bigmap key val) _))).
          simpl.
          rewrite instruction_cast_domain_same.
          reflexivity.
      + destruct i as [v]; destruct v.
        * trans_refl
          (let A := a ::: bool ::: set a :: S in
           bind (fun i => Return _ (typer.Inferred_type _ _ i))
                (typer.instruction_cast_domain
                   A A _ (@syntax.UPDATE _ _ _ (update_set a) _))).
          simpl.
          rewrite instruction_cast_domain_same.
          reflexivity.
        * trans_refl
            (let A := key ::: option val ::: map key val :: S in
             bind (fun i => Return _ (typer.Inferred_type _ _ i))
                  (typer.instruction_cast_domain
                     A A _ (@syntax.UPDATE _ _ _ (update_map key val) _))).
          simpl.
          rewrite instruction_cast_domain_same.
          reflexivity.
        * trans_refl
            (let A := key ::: option val ::: big_map key val :: S in
             bind (fun i => Return _ (typer.Inferred_type _ _ i))
                  (typer.instruction_cast_domain
                     A A _ (@syntax.UPDATE _ _ _ (update_bigmap key val) _))).
          simpl.
          rewrite instruction_cast_domain_same.
          reflexivity.
      + destruct i as [c v]; destruct v.
        * trans_refl
            (bind (fun i => Return _ (@typer.Inferred_type _ _ (syntax.ITER i)))
                  (typer.type_check_instruction_no_tail_fail typer.type_instruction (untype_instruction i0) (a ::: A) A)).
          rewrite untype_type_check_instruction_no_tail_fail; auto.
        * trans_refl
            (bind (fun i => Return _ (@typer.Inferred_type _ _ (syntax.ITER i)))
                  (typer.type_check_instruction_no_tail_fail typer.type_instruction (untype_instruction i0) (pair key val :: A) A)).
          rewrite untype_type_check_instruction_no_tail_fail; auto.
        * trans_refl
            (bind (fun i => Return _ (@typer.Inferred_type _ _ (syntax.ITER i)))
                  (typer.type_check_instruction_no_tail_fail typer.type_instruction (untype_instruction i0) (a :: A) A)).
          rewrite untype_type_check_instruction_no_tail_fail; auto.
      + destruct i as [c v]; destruct v.
        * trans_refl
            (let A := key ::: map key val :: S in
             bind (fun i => Return _ (typer.Inferred_type _ _ i))
                  (typer.instruction_cast_domain
                     A A _ (@syntax.GET _ _ (get_map key val) _))).
          simpl.
          rewrite instruction_cast_domain_same.
          reflexivity.
        * trans_refl
            (let A := key ::: big_map key val :: S in
             bind (fun i => Return _ (typer.Inferred_type _ _ i))
                  (typer.instruction_cast_domain
                     A A _ (@syntax.GET _ _ (get_bigmap key val) _))).
          simpl.
          rewrite instruction_cast_domain_same.
          reflexivity.
      + destruct i as [a c v]; destruct v.
        * trans_refl
            (bind (fun r =>
                     match r with
                     | existT _ (b :: A') i =>
                       bind (fun i => Return _ (@typer.Inferred_type _ _ (syntax.MAP i)))
                            (typer.instruction_cast_range (pair key val :: A) (b :: A') (b :: A) i)
                     | _ => Failed _ Typing
                     end)
                  (typer.type_instruction_no_tail_fail typer.type_instruction (untype_instruction i0) (pair key val ::: A))).
          rewrite untype_type_instruction_no_tail_fail.
          -- simpl.
             rewrite instruction_cast_range_same.
             reflexivity.
          -- auto.
        * trans_refl
            (bind (fun r =>
              match r with
              | existT _ (b :: A') i =>
                bind (fun i => Return _ (@typer.Inferred_type _ _ (syntax.MAP i)))
                     (typer.instruction_cast_range (a :: A) (b :: A') (b :: A) i)
              | _ => Failed _ Typing
              end)
                  (typer.type_instruction_no_tail_fail typer.type_instruction (untype_instruction i0) (a :: A))).
          rewrite untype_type_instruction_no_tail_fail.
          -- simpl.
             rewrite instruction_cast_range_same.
             reflexivity.
          -- auto.
      + trans_refl
          (@typer.type_branches
             typer.type_instruction
             (untype_instruction i1)
             (untype_instruction i2) _ _ _
             (IF_instruction_to_instruction _ _ _ (IF_NONE_i a A))).
        rewrite untype_type_branches; auto.
      + trans_refl
          (@typer.type_branches
             typer.type_instruction
             (untype_instruction i1)
             (untype_instruction i2) _ _ _
             (IF_instruction_to_instruction _ _ _ (IF_LEFT_i a b A))).
        rewrite untype_type_branches; auto.
      + trans_refl
          (@typer.type_branches
             typer.type_instruction
             (untype_instruction i1)
             (untype_instruction i2) _ _ _
             (IF_instruction_to_instruction _ _ _ (IF_RIGHT_i a b A))).
        rewrite untype_type_branches; auto.
      + trans_refl
          (let A := a :: list a :: S in
           bind (fun i => Return _ (@typer.Inferred_type _ _ i))
                (typer.instruction_cast_domain A A _ (syntax.CONS))).
        simpl.
        rewrite instruction_cast_domain_same.
        reflexivity.
      + trans_refl
          (@typer.type_branches
             typer.type_instruction
             (untype_instruction i1)
             (untype_instruction i2) _ _ _
             (IF_instruction_to_instruction _ _ _ (IF_CONS_i a A))).
        rewrite untype_type_branches; auto.
      + trans_refl
          (let A := option key_hash ::: mutez ::: g ::: S in
           bind (fun '(existT _ tff i) =>
                   bind (fun i => Return _ (@typer.Inferred_type _ _ i))
                        (typer.instruction_cast_domain
                           A A _
                           (syntax.CREATE_CONTRACT g p i)))
                (typer.type_check_instruction typer.type_instruction (untype_instruction i) (pair p g :: nil) (pair (list operation) g :: nil))).
        simpl.
        rewrite untype_type_check_instruction.
        -- simpl.
           rewrite instruction_cast_domain_same.
           reflexivity.
        -- auto.
      + trans_refl
          (let A := p ::: mutez ::: contract p ::: S in
           bind (fun i => Return _ (@typer.Inferred_type _ _ i))
                (typer.instruction_cast_domain A A _ syntax.TRANSFER_TOKENS)).
        simpl.
        rewrite instruction_cast_domain_same.
        reflexivity.
      + unfold untype_type_spec.
        simpl. unfold type_check_dig.
        simpl.
        rewrite (take_n_length n S1 (t ::: S2) e).
        simpl.
        rewrite instruction_cast_domain_same.
        reflexivity.
      + unfold untype_type_spec.
        simpl. unfold type_check_dug.
        simpl.
        rewrite (take_n_length n S1 S2 e).
        simpl.
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
        rewrite (take_n_length n A B e).
        simpl.
        rewrite instruction_cast_domain_same.
        reflexivity.
  Qed.

End Untyper.
