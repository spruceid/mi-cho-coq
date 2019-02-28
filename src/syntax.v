(* Syntax and typing of the Michelson language *)

Require Import ZArith.
Require String.
Require Import ListSet.
Require Import comparable.
Require set map.
Require Import error.

(* source: http://doc.tzalpha.net/whitedoc/michelson.html#xii-full-grammar *)

Inductive type : Set :=
| Comparable_type : comparable_type -> type
| key : type
| unit : type
| signature : type
| option_ : type -> type
| list_ : type -> type
| set_ : comparable_type -> type
| contract : type -> type
| address : type
| operation : type
| pair : type -> type -> type
| or : type -> type -> type
| lambda : type -> type -> type
| map : comparable_type -> type -> type
| big_map : comparable_type -> type -> type.

Coercion Comparable_type : comparable_type >-> type.

Definition contract_env : Set := contract_constant -> type.

Module neg.
  Record class (a : comparable_type) :=
    Class { neg : comparable_data a -> M Z }.

  Structure type (a : comparable_type) := Pack { class_of : class a }.

  Definition op (a : comparable_type) {e : type a} : comparable_data a -> M Z :=
    neg _ (class_of a e).

End neg.

Canonical Structure neg_nat : neg.type nat :=
  neg.Pack nat (neg.Class nat (fun x => Return _ (- Z.of_N x)%Z)).

Canonical Structure neg_int : neg.type int :=
  neg.Pack int (neg.Class int (fun x => Return _ (- x)%Z)).

Module add.
  Record class (a b c : comparable_type) :=
    Class
      { add : comparable_data a -> comparable_data b -> M (comparable_data c) }.

  Structure type (a b : comparable_type) :=
    Pack { ret : comparable_type; class_of : class a b ret }.

  Definition op (a b : comparable_type) {e : type a b} :
    comparable_data a -> comparable_data b ->
    M (comparable_data (ret a b e)) :=
    add _ _ _ (class_of a b e).

End add.

Canonical Structure add_nat_nat : add.type nat nat :=
  add.Pack
    nat nat nat
    (add.Class nat nat nat (fun x y => Return _ (x + y)%N)).

Canonical Structure add_nat_int : add.type nat int :=
  add.Pack
    nat int int
    (add.Class nat int int (fun x y => Return _ (Z.of_N x + y)%Z)).

Canonical Structure add_int_nat : add.type int nat :=
  add.Pack
    int nat int
    (add.Class int nat int (fun x y => Return _ (x + Z.of_N y)%Z)).

Canonical Structure add_int_int : add.type int int :=
  add.Pack
    int int int
    (add.Class int int int (fun x y => Return _ (x + y)%Z)).

Canonical Structure add_timestamp_int : add.type timestamp int :=
  add.Pack
    timestamp int timestamp
    (add.Class timestamp int timestamp (fun x y => Return _ (x + y)%Z)).

Canonical Structure add_int_timestamp : add.type int timestamp :=
  add.Pack
    int timestamp timestamp
    (add.Class int timestamp timestamp (fun x y => Return _ (x + y)%Z)).

Canonical Structure add_tez_tez : add.type mutez mutez :=
  add.Pack
    mutez mutez mutez
    (add.Class
       mutez mutez mutez
       (fun x y =>
          match tez.of_Z (tez.to_Z x + tez.to_Z y) with
          | None => Failed _ Overflow
          | Some t => Return _ t
          end)).

Module sub.
  Record class (a b c : comparable_type) :=
    Class
      { sub : comparable_data a -> comparable_data b -> M (comparable_data c) }.

  Structure type (a b : comparable_type) :=
    Pack { ret : comparable_type; class_of : class a b ret }.

  Definition op (a b : comparable_type) {e : type a b} :
    comparable_data a -> comparable_data b ->
    M (comparable_data (ret a b e)) :=
    sub _ _ _ (class_of a b e).

End sub.

Canonical Structure sub_nat_nat : sub.type nat nat :=
  sub.Pack _ _ _ (sub.Class nat nat int (fun x y => Return _ (Z.of_N x - Z.of_N y)%Z)).

Canonical Structure sub_nat_int : sub.type nat int :=
  sub.Pack _ _ _ (sub.Class nat int int (fun x y => Return _ (Z.of_N x - y)%Z)).

Canonical Structure sub_int_nat : sub.type int nat :=
  sub.Pack _ _ _ (sub.Class int nat int (fun x y => Return _ (x - Z.of_N y)%Z)).

Canonical Structure sub_int_int : sub.type int int :=
  sub.Pack _ _ _ (sub.Class int int int (fun x y => Return _ (x - y)%Z)).

Canonical Structure sub_timestamp_int : sub.type timestamp int :=
  sub.Pack _ _ _ (sub.Class timestamp int timestamp (fun x y => Return _ (x - y)%Z)).

Canonical Structure sub_timestamp_timestamp : sub.type timestamp timestamp :=
  sub.Pack _ _ _ (sub.Class timestamp timestamp int (fun x y => Return _ (x - y)%Z)).

Canonical Structure sub_tez_tez : sub.type mutez mutez :=
  sub.Pack
    _ _ _ (sub.Class mutez mutez mutez
    (fun x y =>
       match tez.of_Z (tez.to_Z x - tez.to_Z y) with
       | None => Failed _ Overflow
       | Some t => Return _ t
       end)).

Module mul.
  Record class (a b c : comparable_type) :=
    Class
      { mul : comparable_data a -> comparable_data b -> M (comparable_data c) }.

  Structure type (a b : comparable_type) :=
    Pack { ret : comparable_type; class_of : class a b ret }.

  Definition op (a b : comparable_type) {e : type a b} :
    comparable_data a -> comparable_data b ->
    M (comparable_data (ret a b e)) :=
    mul _ _ _ (class_of a b e).

End mul.

Canonical Structure mul_nat_nat : mul.type nat nat :=
  mul.Pack _ _ _ (mul.Class nat nat nat (fun x y => Return _ (x * y)%N)).

Canonical Structure mul_nat_int : mul.type nat int :=
  mul.Pack _ _ _ (mul.Class nat int int (fun x y => Return _ (Z.of_N x * y)%Z)).

Canonical Structure mul_int_nat : mul.type int nat :=
  mul.Pack _ _ _ (mul.Class int nat int (fun x y => Return _ (x * Z.of_N y)%Z)).

Canonical Structure mul_int_int : mul.type int int :=
  mul.Pack _ _ _ (mul.Class int int int (fun x y => Return _ (x * y)%Z)).

Canonical Structure mul_timestamp_int : mul.type timestamp int :=
  mul.Pack _ _ _ (mul.Class timestamp int timestamp (fun x y => Return _ (x + y)%Z)).

Canonical Structure mul_int_timestamp : mul.type int timestamp :=
  mul.Pack _ _ _ (mul.Class int timestamp timestamp (fun x y => Return _ (x + y)%Z)).

Canonical Structure mul_tez_nat : mul.type mutez nat :=
  mul.Pack _ _ _ (mul.Class
    mutez nat mutez
    (fun x y =>
       match tez.of_Z (tez.to_Z x * Z.of_N y) with
       | None => Failed _ Overflow
       | Some t => Return _ t
       end)).

Canonical Structure mul_nat_tez : mul.type nat mutez :=
  mul.Pack _ _ _ (mul.Class
    nat mutez mutez
    (fun x y =>
       match tez.of_Z (Z.of_N x * tez.to_Z y) with
       | None => Failed _ Overflow
       | Some t => Return _ t
       end)).

Module ediv.
  Record class (a b c d : comparable_type) :=
    Class
      { ediv : comparable_data a -> comparable_data b ->
               M (option (comparable_data c * comparable_data d)) }.

  Structure type (a b : comparable_type) :=
    Pack { quo : comparable_type; rem : comparable_type;
           class_of : class a b quo rem }.

  Definition op (a b : comparable_type) {e : type a b} :
    comparable_data a -> comparable_data b ->
    M (option (comparable_data (quo a b e) * comparable_data (rem a b e))) :=
    ediv _ _ _ _ (class_of a b e).

End ediv.

Canonical Structure ediv_nat_nat : ediv.type nat nat :=
  ediv.Pack _ _ _ _ (ediv.Class
    nat nat nat nat
    (fun x y =>
       Return _
               (if (y =? 0)%N then None
                else Some ((x / y)%N, (x mod y)%N)))).

Canonical Structure ediv_nat_int : ediv.type nat int :=
  ediv.Pack _ _ _ _ (ediv.Class
    nat int int nat
    (fun x y =>
       Return _
               (if (y =? 0)%Z then None
                else Some ((Z.of_N x / y)%Z, Z.to_N (Z.of_N x mod y)%Z)))).

Canonical Structure ediv_int_nat : ediv.type int nat :=
  ediv.Pack _ _ _ _ (ediv.Class
    int nat int nat
    (fun x y =>
       Return _
               (if (y =? 0)%N then None
                else Some ((x / Z.of_N y)%Z, Z.to_N (x mod Z.of_N y)%Z)))).

Canonical Structure ediv_int_int : ediv.type int int :=
  ediv.Pack _ _ _ _ (ediv.Class
    int int int nat
    (fun x y =>
       Return _
               (if (y =? 0)%Z then None
                else Some ((x / y)%Z, Z.to_N (x mod y)%Z)))).

Canonical Structure ediv_tez_nat : ediv.type mutez nat :=
  ediv.Pack _ _ _ _ (ediv.Class
    mutez nat mutez mutez
    (fun x y =>
       Return _
               (if (y =? 0)%N then None
                else
                  match tez.of_Z (tez.to_Z x / Z.of_N y)%Z,
                        tez.of_Z (tez.to_Z x mod Z.of_N y)%Z
                  with
                  | Some quo, Some rem =>
                    Some (quo, rem)
                  | _, _ => None
                              (* Should not happen but I am a bit lazy to prove it *)
                  end))).

Canonical Structure ediv_tez_tez : ediv.type mutez mutez :=
  ediv.Pack _ _ _ _ (ediv.Class
    mutez mutez nat mutez
    (fun x y =>
       Return _
               (if (tez.to_Z y =? 0)%Z then None
                else
                  match Z.to_N (tez.to_Z x / tez.to_Z y)%Z,
                        tez.of_Z (tez.to_Z x mod tez.to_Z y)%Z
                  with
                  | quo, Some rem =>
                    Some (quo, rem)
                  | _, _ => None
                              (* Should not happen but I am a bit lazy to prove it *)
                  end))).

Module bitwise.
  Record class (a : comparable_type) :=
    Class
      { bitwise_and : comparable_data a -> comparable_data a -> M (comparable_data a);
        bitwise_or : comparable_data a -> comparable_data a -> M (comparable_data a);
        bitwise_xor : comparable_data a -> comparable_data a -> M (comparable_data a) }.

  Structure type (a : comparable_type) :=
    Pack { class_of : class a }.

  Definition and (a : comparable_type) {e : type a} :
    comparable_data a -> comparable_data a ->
    M (comparable_data a) :=
    bitwise_and _ (class_of a e).

  Definition or (a : comparable_type) {e : type a} :
    comparable_data a -> comparable_data a ->
    M (comparable_data a) :=
    bitwise_or _ (class_of a e).

  Definition xor (a : comparable_type) {e : type a} :
    comparable_data a -> comparable_data a ->
    M (comparable_data a) :=
    bitwise_xor _ (class_of a e).

End bitwise.

Canonical Structure bitwise_bool : bitwise.type bool :=
  bitwise.Pack _ (bitwise.Class
    bool
    (fun x y => Return _ (x && y)%bool)
    (fun x y => Return _ (x || y)%bool)
    (fun x y => Return _ (xorb x y))).

Canonical Structure bitwise_nat : bitwise.type nat :=
  bitwise.Pack _ (bitwise.Class
    nat
    (fun x y => Return _ (N.land x y))
    (fun x y => Return _ (N.lor x y))
    (fun x y => Return _ (N.lxor x y))).

Module not.
  Record class (a b : comparable_type) :=
    Class
      { bitwise_not : comparable_data a -> M (comparable_data b) }.

  Structure type (a : comparable_type) :=
    Pack { ret : comparable_type; class_of : class a ret }.

  Definition not (a : comparable_type) {e : type a} :
    comparable_data a ->
    M (comparable_data (ret a e)) :=
    bitwise_not _ _ (class_of a e).

End not.

Canonical Structure bitwise_not_bool : not.type bool :=
  not.Pack _ _ (not.Class bool bool (fun x => Return _ (negb x))).

Canonical Structure bitwise_not_int : not.type int :=
  not.Pack _ _ (not.Class
    int int
    (fun x => Return _ (- 1 - x)%Z)).

Canonical Structure bitwise_not_nat : not.type nat :=
  not.Pack _ _ (not.Class
    nat int
    (fun x => Return _ (- 1 - Z.of_N x)%Z)).

Module mem.
  Definition top_type := type.

  Record class (data : type -> Set) (key : comparable_type) (collection : type) : Set :=
    Class
      { mem : comparable_data key -> data collection ->
              M Datatypes.bool }.

  Structure type (data : type -> Set) (key : comparable_type) :=
    Pack { collection : top_type;
           class_of : class data key collection }.

  Definition op data key e := mem _ _ _ (class_of data key e).
End mem.

Module update.
  Definition top_type := type.

  Record class (data : type -> Set) (key : comparable_type) (collection : type)
               (opt_val : type) : Set :=
    Class
      { update : comparable_data key ->
                 data opt_val ->
                 data collection ->
                 M (data collection) }.
  Structure type (data : type -> Set) (key : comparable_type) :=
    Pack { collection : top_type;
           opt_val : top_type;
           class_of : class data key collection opt_val }.

  Definition op data key e := update _ _ _ _ (class_of data key e).
End update.

Module reduce.
  Definition top_type := type.

  Record class (data : type -> Set) (collection : type)
         (entry : type) : Set :=
    Class
      { reduce : forall b : type,
          ((data entry * data b) -> M (data b)) ->
          data collection -> data b -> M (data b) }.
  Structure type (data : type -> Set) :=
    Pack { collection : top_type;
           entry : top_type;
           class_of : class data collection entry }.

  Definition op data e := reduce _ _ _ (class_of data e).
End reduce.

Module size.
  Definition top_type := type.

  Record class (data : type -> Set) (collection : type) : Set :=
    Class
      { size : data collection -> M N }.

  Structure type (data : type -> Set) :=
    Pack { collection : top_type;
           class_of : class data collection }.

  Definition op data e := size _ _ (class_of data e).
End size.

Module get.
  Definition top_type := type.

  Record class (data : type -> Set) (collection : type) (key : comparable_type) (val : type) : Set :=
    Class
      { get : comparable_data key -> data collection -> M (data (option_ val)) }.

  Structure type (data : type -> Set) (key : comparable_type) :=
    Pack { collection : top_type;
           val : top_type;
           class_of : class data collection key val }.

  Definition op data key e := get _ _ _ _ (class_of data key e).
End get.

Module MAP.
  Definition top_type := type.

  Record class (data : type -> Set) (collection : type -> type)
         (val : type) (entry : type) : Set :=
    Class
      { map : forall b, (data entry -> M (data b)) ->
                        data (collection val) ->
                        M (data (collection b)) }.

  Structure type (data : type -> Set) :=
    Pack { collection : top_type -> top_type;
           val : top_type;
           entry : top_type;
           class_of : class data collection val entry }.

  Definition op data e := map _ _ _ _ (class_of data e).

End MAP.

Module string_like.
  Record class (a : comparable_type) :=
    Class
      { slice_ : comparable_data nat -> comparable_data nat ->
                 comparable_data a -> M (option (comparable_data string));
        concat_ : comparable_data a -> comparable_data a -> M (comparable_data a)}.

  Structure type (a : comparable_type) :=
    Pack { class_of : class a }.

  Definition slice (a : comparable_type) {e : type a} :
    comparable_data nat ->
    comparable_data nat ->
    comparable_data a ->
    M (option (comparable_data string)) :=
    slice_ _ (class_of a e).

  Definition concat (a : comparable_type) {e : type a} :
    comparable_data a ->
    comparable_data a ->
    M (comparable_data a) :=
    concat_ _ (class_of a e).

End string_like.

Definition str_slice (n1 n2 : N.t) (s : str) : M (option str) :=
  if (n1 + n2 <=? N.of_nat (String.length s))%N then
    Return _ (Some (String.substring (N.to_nat n1) (N.to_nat n2) s))
  else Return _ None.

Canonical Structure string_like_string : string_like.type string :=
  string_like.Pack _
    (string_like.Class string str_slice (fun s1 s2 => Return _ (String.append s1 s2))).

Canonical Structure string_like_bytes : string_like.type bytes :=
  string_like.Pack _
    (string_like.Class bytes str_slice (fun s1 s2 => Return _ (String.append s1 s2))).

Infix ":::" := (@cons type) (at level 60, right associativity).

Section syntax.

Parameter e : contract_env.
Parameter ae : address_constant -> type.

Fixpoint data (a : type) {struct a} : Set :=
  match a with
  | Comparable_type b => comparable_data b
  | address => address_constant
  | signature => signature_constant
  | operation => operation_constant
  | key => key_constant
  | unit => Datatypes.unit
  | pair a b => data a * data b
  | or a b => sum (data a) (data b)
  | option_ a => option (data a)
  | list_ a => list (data a)
  | set_ a => set.set (comparable_data a) (compare a)
  | map a b => map.map (comparable_data a) (data b) (compare a)
  | big_map a b => map.map (comparable_data a) (data b) (compare a)
  | lambda a b => data a -> M (data b)
  | contract a => {s : contract_constant | e s = a }
  end.

Record node : Set :=
  mk_node
    {
      create_contract : forall g p,
          comparable_data key_hash ->
          option (comparable_data key_hash) ->
          Datatypes.bool -> Datatypes.bool -> tez.mutez ->
          (data (pair p g) -> M (data (pair (list_ operation) g))) ->
          data g -> M (data (pair operation address));
      create_account :
          comparable_data key_hash ->
          option (comparable_data key_hash) ->
          Datatypes.bool -> tez.mutez ->
          M (data operation * data (contract unit));
      transfer_tokens : forall p,
          data p -> tez.mutez -> data (contract p) ->
          M (data operation);
      set_delegate : option (comparable_data key_hash) ->
                     M (data operation);
      balance : M tez.mutez;
      address_ : forall p, data (contract p) -> M (data address);
      contract_ : forall p, data address -> M (option (data (contract p)));
      source : M (data address);
      sender : M (data address);
      self : forall p, M (data (contract p));
      amount : M tez.mutez;
      implicit_account :
        comparable_data key_hash -> M (data (contract unit));
      steps_to_quota : M N;
      now : M (comparable_data timestamp);
      hash_key : data key -> M (comparable_data key_hash);
      pack : forall a, data a -> M str;
      unpack : forall a, str -> M (option (data a));
      blake2b : str -> M str;
      sha256 : str -> M str;
      sha512 : str -> M str;
      check_signature :
        data key -> data signature -> String.string -> M Datatypes.bool
    }.

Canonical Structure mem_set (key : comparable_type) :=
  {| mem.collection := set_ key;
     mem.class_of :=
       {| mem.mem := fun k (s : data (set_ key)) =>
                       Return _ (set.mem _ _ (compare_eq_iff key) k s) |} |}.

Canonical Structure update_set (key : comparable_type) :=
  {| update.collection := set_ key;
     update.opt_val := bool;
     update.class_of :=
       {| update.update := fun k (v : data bool) (s : data (set_ key)) =>
                             Return _
                                     (set.update _ _
                                                 (compare_eq_iff key)
                                                 (lt_trans key)
                                                 (gt_trans key) k s v) |} |}.

Canonical Structure mem_map (key : comparable_type) (val : type) :=
  {| mem.collection := map key val;
     mem.class_of :=
       {| mem.mem := fun k (s : data (map key val)) =>
                       Return _ (map.mem _ _ _ k s) |} |}.

Canonical Structure update_map (key : comparable_type) (val : type) :=
  {| update.collection := map key val;
     update.opt_val := option_ val;
     update.class_of :=
       {| update.update := fun k
                               (v : data (option_ val)) (s : data (map key val)) =>
                             Return _
                                     (map.update _ _ _
                                                 (comparable.compare_eq_iff key)
                                                 (comparable.lt_trans key)
                                                 (comparable.gt_trans key) k v s)
       |} |}.

Canonical Structure mem_big_map (key : comparable_type) (val : type) :=
  {| mem.collection := big_map key val;
     mem.class_of :=
       {| mem.mem := fun k (s : data (big_map key val)) =>
                       Return _ (map.mem _ _ _ k s) |} |}.

Canonical Structure update_big_map (key : comparable_type) (val : type) :=
  {| update.collection := big_map key val;
     update.opt_val := option_ val;
     update.class_of :=
       {| update.update := fun k (v : data (option_ val)) (s : data (big_map key val)) =>
                             Return _
                                     (map.update _ _ _
                                                 (comparable.compare_eq_iff key)
                                                 (comparable.lt_trans key)
                                                 (comparable.gt_trans key) k v s)
       |} |}.

Canonical Structure reduce_set (key : comparable_type) :=
  {| reduce.collection := set_ key;
     reduce.entry := key;
     reduce.class_of :=
       reduce.Class
         data (set_ key) key
         (fun (B : type) (f : (data key * data B) -> M (data B))
              (s : data (set_ key)) (b : data B) =>
            set.reduce
              (comparable_data key)
              (comparable.compare key)
              (data B) f b s) |}.

Canonical Structure reduce_map (key : comparable_type) (val : type) :=
  {| reduce.collection := map key val;
     reduce.entry := pair key val;
     reduce.class_of :=
       reduce.Class
         data (map key val) (pair key val)
         (fun (B : type) (f : (data (pair key val) * data B) -> M (data B))
              (s : data (map key val)) (b : data B) =>
            set.reduce
              (data key * data val)
              (map.map_compare (comparable_data key) (data val) _)
              (data B) f b s) |}.

Canonical Structure reduce_list (a : type) :=
  {| reduce.collection := list_ a;
     reduce.entry := a;
     reduce.class_of :=
       reduce.Class
         data (list_ a) a
         (fun (B : type) (f : (data a * data B) -> M (data B))
              (s : data (list_ a)) (b : data B) =>
            set.list_reduce
              (data a)
              (data B) f b s) |}.

Canonical Structure size_set (key : comparable_type) :=
  {| size.collection := set_ key;
     size.class_of :=
       {| size.size := fun (s : data (set_ key)) =>
                         let (l, _) := s in
                         Return _ (N.of_nat (List.length l)) |}
       |}.

Canonical Structure size_map (key : comparable_type) (val : type) :=
  {| size.collection := map key val;
     size.class_of :=
       {| size.size := fun (s : data (map key val)) =>
                         let (l, _) := s in
                         Return _ (N.of_nat (List.length l)) |}
       |}.

Canonical Structure size_list (a : type) :=
  {| size.collection := list_ a;
     size.class_of :=
       {| size.size := fun (l : data (list_ a)) =>
                         Return _ (N.of_nat (List.length l)) |}
       |}.

Canonical Structure size_string :=
  {| size.collection := string;
     size.class_of :=
       {| size.size := fun (s : data string) =>
                         Return _ (N.of_nat (String.length s)) |}
       |}.

Canonical Structure size_bytes :=
  {| size.collection := bytes;
     size.class_of :=
       {| size.size := fun (s : data bytes) =>
                         Return _ (N.of_nat (String.length s)) |}
       |}.

Canonical Structure get_map (key : comparable_type) (val : type) :=
  {| get.collection := map key val;
     get.class_of :=
       {| get.get := fun k (s : data (map key val)) =>
                       Return _ (map.get _ _ _ k s) |}
       |}.

Canonical Structure get_big_map (key : comparable_type) (val : type) :=
  {| get.collection := big_map key val;
     get.class_of :=
       {| get.get := fun k (s : data (big_map key val)) =>
                       Return _ (map.get _ _ _ k s) |}
       |}.

Canonical Structure map_map (key : comparable_type) (val : type) :=
  {| MAP.collection := map key;
     MAP.entry := pair key val;
     MAP.class_of :=
       MAP.Class
         data
         (map key)
         val
         (pair key val)
         (fun B f m => map.map_fun _ _ _ _ f m) |}.

Canonical Structure map_list (a : type) :=
  {| MAP.collection := list_;
     MAP.entry := a;
     MAP.class_of :=
       MAP.Class
         data
         list_
         a
         a
         (fun B f l => map.list_map _ _ f l) |}.

Inductive instruction : list type -> list type -> Set :=
| NOOP {A} : instruction A A
| FAILWITH {A B a} : instruction (a ::: A) B
| SEQ {A B C} : instruction A B -> instruction B C -> instruction A C
(* The instruction SEQ I C is written "{ I ; C }" in Michelson *)
| IF_ {A B} : instruction A B -> instruction A B -> instruction (bool ::: A) B
(* "IF" is a reserved keyword in file Coq.Init.Logic because it is
part of the notation "'IF' c1 'then' c2 'else' c3" so we cannot call
this constructor "IF" but we can make a notation for it. *)
| LOOP {A} : instruction A (bool ::: A) -> instruction (bool ::: A) A
| LOOP_LEFT {a b A} : instruction (a :: A) (or a b :: A) ->
                      instruction (or a b :: A) (b :: A)
| DIP {b A C} : instruction A C -> instruction (b :: A) (b :: C)
| EXEC {a b C} : instruction (a ::: lambda a b ::: C) (b :: C)
| DROP {a A} : instruction (a :: A) A
| DUP {a A} : instruction (a ::: A) (a ::: a ::: A)
| SWAP {a b A} : instruction (a ::: b ::: A) (b ::: a ::: A)
| PUSH (a : type) (x : data a) {A} : instruction A (a :: A)
| UNIT {A} : instruction A (unit :: A)
| LAMBDA (a b : type) {A} : instruction (a :: nil) (b :: nil) ->
                     instruction A (lambda a b :: A)
| EQ {S} : instruction (int ::: S) (bool ::: S)
| NEQ {S} : instruction (int ::: S) (bool ::: S)
| LT {S} : instruction (int ::: S) (bool ::: S)
| GT {S} : instruction (int ::: S) (bool ::: S)
| LE {S} : instruction (int ::: S) (bool ::: S)
| GE {S} : instruction (int ::: S) (bool ::: S)
| OR {b} {s : bitwise.type b} {S} : instruction (b ::: b ::: S) (b ::: S)
| AND {b} {s : bitwise.type b} {S} : instruction (b ::: b ::: S) (b ::: S)
| XOR {b} {s : bitwise.type b} {S} : instruction (b ::: b ::: S) (b ::: S)
| NOT {b} {s : not.type b} {S} : instruction (b ::: S) (not.ret _ s ::: S)
| NEG {n} {s : neg.type n} {S} : instruction (n ::: S) (int ::: S)
| ABS {S} : instruction (int ::: S) (nat ::: S)
| ADD {a b} {s : add.type a b} {S} :
    instruction (a ::: b ::: S) (add.ret _ _ s ::: S)
| SUB {a b} {s : sub.type a b} {S} :
    instruction (a ::: b ::: S) (sub.ret _ _ s ::: S)
| MUL {a b} {s : mul.type a b} {S} :
    instruction (a ::: b ::: S) (mul.ret _ _ s ::: S)
| EDIV {a b} {s : ediv.type a b} {S} : instruction (a ::: b ::: S) (option_ (pair (ediv.quo _ _ s) (ediv.rem _ _ s)) :: S)
| LSL {S} : instruction (nat ::: nat ::: S) (nat ::: S)
| LSR {S} : instruction (nat ::: nat ::: S) (nat ::: S)
| COMPARE {a : comparable_type} {S} : instruction (a ::: a ::: S) (int ::: S)
| CONCAT {S a} {i : string_like.type a} : instruction (a ::: a ::: S) (a ::: S)
| SIZE {i : size.type data} {S} :
    instruction (size.collection _ i ::: S) (nat ::: S)
| SLICE {S a} {i : string_like.type a} :
    instruction (nat ::: nat ::: a ::: S) (option_ string ::: S)
| PAIR {a b S} : instruction (a ::: b ::: S) (pair a b :: S)
| CAR {a b S} : instruction (pair a b :: S) (a :: S)
| CDR {a b S} : instruction (pair a b :: S) (b :: S)
| EMPTY_SET (elt : comparable_type) {S} : instruction S (set_ elt ::: S)
| MEM {elt : comparable_type} {i : mem.type data elt} {S} :
    instruction (elt ::: mem.collection _ _ i ::: S) (bool ::: S)
| UPDATE {elt : comparable_type} {i : update.type data elt} {S} :
    instruction (elt ::: update.opt_val _ _ i ::: update.collection _ _ i ::: S) (update.collection _ _ i ::: S)
| ITER_set {elt : comparable_type} {A} :
    instruction (elt ::: A) A -> instruction (set_ elt :: A) A
| EMPTY_MAP (key : comparable_type) (val : type) {S} :
    instruction S (map key val :: S)
| GET {key : comparable_type} {i : get.type data key} {S} :
    instruction (key ::: get.collection _ _ i ::: S) (option_ (get.val _ _ i) :: S)
| MAP_map_body {key : comparable_type} {val b A} :
    instruction (pair key val :: A) (b :: A) ->
    instruction (map key val :: A) (map key b :: A)
| ITER_map {elt : comparable_type} {val A} :
    instruction (pair elt val :: A) A ->
    instruction (map elt val :: A) A
| SOME {a S} : instruction (a :: S) (option_ a :: S)
| NONE (a : type) {S} : instruction S (option_ a :: S)
(* Not the one documented, see https://gitlab.com/tezos/tezos/issues/471 *)
| IF_NONE {a A B} :
    instruction A B -> instruction (a :: A) B ->
    instruction (option_ a :: A) B
| LEFT {a} (b : type) {S} : instruction (a :: S) (or a b :: S)
| RIGHT (a : type) {b S} : instruction (b :: S) (or a b :: S)
| IF_LEFT {a b A B} :
    instruction (a :: A) B ->
    instruction (b :: A) B ->
    instruction (or a b :: A) B
| IF_RIGHT {a b A B} :
    instruction (b :: A) B ->
    instruction (a :: A) B ->
    instruction (or a b :: A) B
| CONS {a S} : instruction (a ::: list_ a ::: S) (list_ a :: S)
| NIL (a : type) {S} : instruction S (list_ a :: S)
| IF_CONS {a A B} :
    instruction (a ::: list_ a ::: A) B ->
    instruction A B ->
    instruction (list_ a :: A) B
| MAP_list_body {elt b A} :
    instruction (elt ::: A) (b ::: A) ->
    instruction (list_ elt ::: A) (list_ b ::: A)
| ITER_list {elt A} : instruction (elt :: A) A -> instruction (list_ elt :: A) A
| CREATE_CONTRACT {p g S} :
    instruction
      (key_hash ::: option_ key_hash ::: bool ::: bool ::: mutez :::
       lambda (pair p g) (pair (list_ operation) g) ::: g ::: S)
      (operation ::: address ::: S)
| CREATE_CONTRACT_literal {S} (g p : type) :
    instruction (pair p g :: nil) (pair (list_ operation) g :: nil) ->
    instruction (key_hash ::: option_ key_hash ::: bool ::: bool ::: mutez ::: g ::: S)
                (operation ::: address ::: S)
| CREATE_ACCOUNT {S} :
    instruction (key_hash ::: option_ key_hash ::: bool ::: mutez ::: S)
                (operation ::: contract unit ::: S)
| TRANSFER_TOKENS {p S} :
    instruction (p ::: mutez ::: contract p ::: S) (operation ::: S)
| SET_DELEGATE {S} :
    instruction (option_ key_hash ::: S) (operation ::: S)
| BALANCE {S} : instruction S (mutez ::: S)
| ADDRESS {p S} : instruction (contract p ::: S) (address ::: S)
| CONTRACT {S} p : instruction (address ::: S) (option_ (contract p) ::: S)
(* Mistake in the doc: the return type must be an option *)
| SOURCE {S} : instruction S (address :: S)
| SENDER {S} : instruction S (address :: S)
| SELF {p S} : instruction S (contract p :: S)
(* p should be obtained from the node *)
| AMOUNT {S} : instruction S (mutez ::: S)
| IMPLICIT_ACCOUNT {S} : instruction (key_hash ::: S) (contract unit :: S)
| STEPS_TO_QUOTA {S} : instruction S (nat ::: S)
| NOW {S} : instruction S (timestamp ::: S)
| PACK {a S} : instruction (a ::: S) (bytes ::: S)
| UNPACK {a S} : instruction (bytes ::: S) (option_ a ::: S)
| HASH_KEY {S} : instruction (key ::: S) (key_hash ::: S)
| BLAKE2B {S} : instruction (bytes ::: S) (bytes ::: S)
| SHA256 {S} : instruction (bytes ::: S) (bytes ::: S)
| SHA512 {S} : instruction (bytes ::: S) (bytes ::: S)
| CHECK_SIGNATURE {S} : instruction (key ::: signature ::: bytes ::: S) (bool ::: S).

(* TODO: add the no-ops CAST and RENAME *)

Notation "'IF'" := (IF_).

Definition stack_type := list type.

Fixpoint stack (t : stack_type) : Set :=
  match t with
  | nil => Datatypes.unit
  | cons a A => data a * stack A
  end.


Definition full_contract params storage :=
  instruction ((pair params storage) ::: nil) ((pair (list_ operation) storage) ::: nil).

End syntax.

Notation "A ;; B" := (SEQ A B) (at level 100).

(* For debugging purpose, a version of ;; with explicit stack type *)
Notation "A ;;; S ;;;; B" := (@SEQ _ S _ A B) (at level 100).
