Require Import String.

(* New lines are not picked up in this string, hence i've converted one-line comments to
 *  /* */-style comments.
 *)

Definition slc_contract : string :=
"storage (pair
           (pair
              (key_hash %journaliere)
              (pair
                 (pair
                    (mutez %fonds_restant)
                    (int %duree_de_blocage))
                 (pair %file
                    (list (pair timestamp mutez))
                    (list (pair timestamp mutez)))))
           (pair
              (key_hash %maitresse)
              (pair %sel nat nat)));
parameter (or
             (unit %send)
             (or
                (pair %appel_clef_maitresse
                   (pair
                      (key %clef_publique)
                      signature)
                   (or
                      (pair
                         (pair
                            (key_hash %journaliere)
                            (pair
                               (pair
                                  (mutez %fonds_restant)
                                  (int %duree_de_blocage))
                               (pair %file
                                  (list (pair timestamp mutez))
                                  (list (pair timestamp mutez)))))
                         (key_hash %nouvelle_clef_maitresse))
                      (pair
                         (lambda unit (list operation))
                         (key_hash %nouvelle_clef_publique)))
                )
                (pair %transfer
                   (pair
                      (list %beneficiaires
                         (pair
                            (mutez %montant)
                            (contract %beneficiaire unit)))
                      (key_hash %novelle_clef_journaliere))
                   (pair
                      (key %clef_publique)
                      signature))));
code { UNPAPAIR;
       IF_RIGHT{ IF_LEFT{ DIP{SWAP}; # cas d'un appel par la clef maîtresse
                          SWAP;
                          UNPAIR;
                          DIP{ SWAP;
                               UNPAIR;
                               DIP{ DUP;
                                    PACK;
                                    DIP{ DIP{ UNPAIR @master_salt @slave_salt;
                                              DUP;
                                              DIP{ PUSH nat 2;
                                                   ADD @master_salt;
                                                   PAIR};
                                              PACK;
                                              CHAIN_ID;
                                              SELF;
                                              PAIR;
                                              PACK;
                                              CONCAT};
                                         SWAP};
                                    CONCAT;
                                    DUP};
                               UNPAIR;
                               DUP;
                               HASH_KEY;
                             };
                          ASSERT_CMPEQ;
                          CHECK_SIGNATURE;
                          IF{DROP}{FAILWITH};
                          IF_LEFT{ UNPAIR;
                                   DIP{ PAIR;
                                        SWAP;
                                        DROP};
                                   NIL operation}
                                 { UNPAIR;
                                   DIP{ PAIR;
                                        SWAP};
                                   UNIT;
                                   EXEC}}
                        { DIP {UNPAPAIR}; # cas d'un appel simple
                          UNPAIR;
                          DUP;
                          PACK;
                          DIP{ UNPAIR;
                               DIP{SWAP}};
                          SWAP;
                          DIP{ DIP{ DIP{SWAP};
                                    SWAP;
                                    DIP{ UNPAIR;
                                         DUP;
                                         HASH_KEY};
                                    ASSERT_CMPEQ; # verification de compatibilite des clefs
                                    DIG 5;
                                    UNPAIR;
                                    DIP{ UNPAIR @master_salt @slave_salt;
                                         DIP{ DUP;
                                              PUSH nat 2;
                                              ADD};
                                         PAIR};
                                    PAIR;
                                    DUG 6;
                                    PACK;
                                    CHAIN_ID;
                                    SELF;
                                    PAIR;
                                    PACK;
                                    CONCAT
                                  };
                               CONCAT;
                               SWAP;
                               DIP{ SWAP;
                                    DIP{DUP}};
                               CHECK_SIGNATURE; #verification de signature
                               IF{DROP}{FAILWITH};
                               DIP{ UNPAIR;
                                    SWAP;
                                    DIP{ SWAP;
                                         UNPAIR;
                                         PUSH bool True;
                                         LOOP{ # recherche de fonds à liberer
                                               IF_CONS{ DUP;
                                                        CAR;
                                                        NOW;
                                                        IFCMPGE{ CDR;
                                                                 SWAP;
                                                                 DIP{ SWAP;
                                                                      DIP{ ADD}};
                                                                 PUSH bool True
                                                               }
                                                               { CONS;
                                                                 PUSH bool False
                                                               };
                                                      }
                                                      { IF_CONS{ NIL (pair timestamp mutez);
                                                                 SWAP;
                                                                 CONS;
                                                                 SWAP;
                                                                 ITER{ CONS};
                                                                 NIL (pair timestamp mutez);
                                                                 SWAP;
                                                                 PUSH bool True}
                                                               { NIL (pair timestamp mutez);
                                                                 DUP;
                                                                 PUSH bool False}
                                                      };
                                             };
                                         DIP{ SWAP};
                                         SWAP;
                                       };
                                  };
                               PUSH mutez 0;
                               NIL operation;
                             };
                          ITER{ UNPAIR; # production des transactions
                                DUP;
                                DIP{
                                     UNIT;
                                     TRANSFER_TOKENS;
                                     CONS;
                                   };
                                SWAP;
                                DIP{ SWAP;
                                     ADD} #calcul du temps de blocage
                              };
                          DIP{ SWAP; # blocage des fonds depensés
                               DIP{ SWAP;
                                    DUP;
                                    NOW;
                                    ADD;
                                    SWAP;
                                    DIP{ DIP{SWAP};
                                         SWAP;
                                         DIP{ SWAP;
                                              DUP;
                                              DIP{ SWAP;
                                                   PAIR;
                                                   SWAP;
                                                   DIP{ CONS}; # ajout dans la file
                                                   PAIR}};
                                         SUB}; # calcul du reste non bloqué
                                    SWAP;
                                    PAIR;
                                    PAIR;
                                  };
                               PAIR};
                        }
               }
               { DROP; # cas d'un simple ajout de fonds (parameter : (Left Unit))
                 NIL  operation};
       PAPAIR}".

Definition dsl_ep_master_lambda_s : string := "UNPAIR;
                                               DIP{ PAIR;
                                                    SWAP};
                                               UNIT;
                                               EXEC".

