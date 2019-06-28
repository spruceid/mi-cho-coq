Require Import String ZArith.
Require micheline_lexer micheline_parser.
Require untyped_syntax micheline2michelson typer.
Require syntax.
Require Import syntax_type.


Definition wrap_parser_result {A} r : error.M A :=
  match r with
  | micheline_parser.MenhirLibParser.Inter.Fail_pr =>
    error.Failed _ error.Parsing
  | micheline_parser.MenhirLibParser.Inter.Timeout_pr =>
    error.Failed _ error.Parsing_Out_of_Fuel
  | micheline_parser.MenhirLibParser.Inter.Parsed_pr m _ =>
    error.Return _ m
  end.

Definition parse_micheline fuel (s : micheline_parser.MenhirLibParser.Inter.buffer)
  : error.M micheline_syntax.loc_micheline :=
  wrap_parser_result (micheline_parser.file fuel s).

Definition lex_and_parse_micheline fuel input :
  error.M (micheline_syntax.loc_micheline) :=
  error.bind
    (parse_micheline fuel)
    (micheline_lexer.lex_micheline_to_parser input).

Definition lex_and_parse_and_expand_type fuel input
  : error.M type :=
  error.bind
    (fun m => micheline2michelson.micheline2michelson_type m)
    (lex_and_parse_micheline fuel input).

Definition get_file_object_from_string fuel input :=
  error.bind
    micheline2michelson.micheline2michelson_file
    (error.bind
       (fun x => wrap_parser_result (micheline_parser.seq_file fuel x))
       (micheline_lexer.lex_micheline_to_parser input)).

Definition get_parameter_type_from_string fuel input :=
  error.bind
    (fun a => error.Return _ a.(micheline2michelson.parameter))
    (get_file_object_from_string fuel input).

Definition get_storage_type_from_string fuel input :=
  error.bind
    (fun a => error.Return _ a.(micheline2michelson.storage))
    (get_file_object_from_string fuel input).

Module Type PARSEDSELFTYPE.
  Parameter input : String.string.
  Parameter fuel : Datatypes.nat.
  Parameter success_param : error.Is_true (error.success (get_parameter_type_from_string fuel input)).
  Parameter success_storage : error.Is_true (error.success (get_storage_type_from_string fuel input)).
End PARSEDSELFTYPE.

Module Type PARSEDFILE <: semantics.SelfType.
  Parameter file_object : error.M micheline2michelson.untyped_michelson_file.
  Parameter self_type : type.
  Parameter storage_type : type.
End PARSEDFILE.

Module ParsedFile (ParsedSelfType : PARSEDSELFTYPE) <: PARSEDFILE.
  Definition file_object := get_file_object_from_string ParsedSelfType.fuel ParsedSelfType.input.
  Definition self_type :=
    error.extract (error.bind (fun a => error.Return _ a.(micheline2michelson.parameter)) file_object)
                  ParsedSelfType.success_param.
  Definition storage_type :=
    error.extract (error.bind (fun a => error.Return _ a.(micheline2michelson.storage)) file_object)
                  ParsedSelfType.success_storage.
End ParsedFile.

Module Main(ST : PARSEDFILE).

  (* Dummy context: getting the type of a contract always fails. *)
  Module ContractContext.
    Definition get_contract_type (_ : syntax.contract_constant) :
      Datatypes.option type := None.
  End ContractContext.

  Module syntax := syntax.Syntax(ContractContext).
  Module typer := typer.Typer(ContractContext).
  Import typer. Import syntax.

  Definition full_contract := syntax.full_contract.

  Definition code_M : error.M untyped_syntax.instruction :=
    error.bind
      (fun a => error.Return _ a.(micheline2michelson.code))
      ST.file_object.

  Definition lex_and_parse_and_expand_and_type_full_contract
    : error.M (syntax.full_contract ST.self_type ST.storage_type) :=
         error.bind
           (fun i =>
              typer.type_check_instruction_no_tail_fail typer.type_instruction i _ _)
           code_M.

  Definition type_check : Datatypes.bool := error.success lex_and_parse_and_expand_and_type_full_contract.

End Main.

Module MultisigParsedSelfType <: PARSEDSELFTYPE.
  Definition input : String.string :=
    "
parameter (pair
             (pair :payload
                (nat %counter) # counter, used to prevent replay attacks
                (or :action    # payload to sign, represents the requested action
                   (pair :transfer    # transfer tokens
                      (mutez %amount) # amount to transfer
                      (contract %dest unit)) # destination to transfer to
                   (or
                      (option %delegate key_hash) # change the delegate to this address
                      (pair %change_keys          # change the keys controlling the multisig
                         (nat %threshold)         # new threshold
                         (list %keys key)))))     # new list of keys
             (list %sigs (option signature)));    # signatures

storage (pair (nat %stored_counter) (pair (nat %threshold) (list %keys key))) ;

code
  {
    UNPAIR ; SWAP ; DUP ; DIP { SWAP } ;
    DIP
      {
        UNPAIR ;
        # pair the payload with the current contract address, to ensure signatures
        # can't be replayed accross different contracts if a key is reused.
        DUP ; SELF ; ADDRESS ; PAIR ;
        PACK ; # form the binary payload that we expect to be signed
        DIP { UNPAIR @counter ; DIP { SWAP } } ; SWAP
      } ;

    # Check that the counters match
    UNPAIR @stored_counter; DIP { SWAP };
    ASSERT_CMPEQ ;

    # Compute the number of valid signatures
    DIP { SWAP } ; UNPAIR @threshold @keys;
    DIP
      {
        # Running count of valid signatures
        PUSH @valid nat 0; SWAP ;
        ITER
          {
            DIP { SWAP } ; SWAP ;
            IF_CONS
              {
                IF_SOME
                  { SWAP ;
                    DIP
                      {
                        SWAP ; DIIP { DIP { DUP } ; SWAP } ;
                        # Checks signatures, fails if invalid
                        CHECK_SIGNATURE ; ASSERT ;
                        PUSH nat 1 ; ADD @valid } }
                  { SWAP ; DROP }
              }
              {
                # There were fewer signatures in the list
                # than keys. Not all signatures must be present, but
                # they should be marked as absent using the option type.
                FAIL
              } ;
            SWAP
          }
      } ;
    # Assert that the threshold is less than or equal to the
    # number of valid signatures.
    ASSERT_CMPLE ;
    DROP ; DROP ;

    # Increment counter and place in storage
    DIP { UNPAIR ; PUSH nat 1 ; ADD @new_counter ; PAIR} ;

    # We have now handled the signature verification part,
    # produce the operation requested by the signers.
    NIL operation ; SWAP ;
    IF_LEFT
      { # Transfer tokens
        UNPAIR ; UNIT ; TRANSFER_TOKENS ; CONS }
      { IF_LEFT {
                  # Change delegate
                  SET_DELEGATE ; CONS }
                {
                  # Change set of signatures
                  DIP { SWAP ; CAR } ; SWAP ; PAIR ; SWAP }} ;
    PAIR }".

  Definition fuel := 600.

  Definition success_param := I.
  Definition success_storage := I.
End MultisigParsedSelfType.

Module MultisigParsedFile := ParsedFile MultisigParsedSelfType.
Module MultisigMain := Main MultisigParsedFile.

Lemma multisig_type_check : Bool.Is_true MultisigMain.type_check.
Proof. exact I. Qed.
