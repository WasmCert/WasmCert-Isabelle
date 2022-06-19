module Uint32 : sig
  val less : int32 -> int32 -> bool
  val less_eq : int32 -> int32 -> bool
  val set_bit : int32 -> Z.t -> bool -> int32
  val shiftl : int32 -> Z.t -> int32
  val shiftr : int32 -> Z.t -> int32
  val shiftr_signed : int32 -> Z.t -> int32
  val test_bit : int32 -> Z.t -> bool
end = struct

(* negative numbers have their highest bit set, 
   so they are greater than positive ones *)
let less x y =
  if Int32.compare x Int32.zero < 0 then
    Int32.compare y Int32.zero < 0 && Int32.compare x y < 0
  else Int32.compare y Int32.zero < 0 || Int32.compare x y < 0;;

let less_eq x y =
  if Int32.compare x Int32.zero < 0 then
    Int32.compare y Int32.zero < 0 && Int32.compare x y <= 0
  else Int32.compare y Int32.zero < 0 || Int32.compare x y <= 0;;

let set_bit x n b =
  let mask = Int32.shift_left Int32.one (Z.to_int n)
  in if b then Int32.logor x mask
     else Int32.logand x (Int32.lognot mask);;

let shiftl x n = Int32.shift_left x (Z.to_int n);;

let shiftr x n = Int32.shift_right_logical x (Z.to_int n);;

let shiftr_signed x n = Int32.shift_right x (Z.to_int n);;

let test_bit x n =
  Int32.compare 
    (Int32.logand x (Int32.shift_left Int32.one (Z.to_int n)))
    Int32.zero
  <> 0;;

end;; (*struct Uint32*)

module Uint64 : sig
  val less : int64 -> int64 -> bool
  val less_eq : int64 -> int64 -> bool
  val set_bit : int64 -> Z.t -> bool -> int64
  val shiftl : int64 -> Z.t -> int64
  val shiftr : int64 -> Z.t -> int64
  val shiftr_signed : int64 -> Z.t -> int64
  val test_bit : int64 -> Z.t -> bool
end = struct

(* negative numbers have their highest bit set, 
   so they are greater than positive ones *)
let less x y =
  if Int64.compare x Int64.zero < 0 then
    Int64.compare y Int64.zero < 0 && Int64.compare x y < 0
  else Int64.compare y Int64.zero < 0 || Int64.compare x y < 0;;

let less_eq x y =
  if Int64.compare x Int64.zero < 0 then
    Int64.compare y Int64.zero < 0 && Int64.compare x y <= 0
  else Int64.compare y Int64.zero < 0 || Int64.compare x y <= 0;;

let set_bit x n b =
  let mask = Int64.shift_left Int64.one (Z.to_int n)
  in if b then Int64.logor x mask
     else Int64.logand x (Int64.lognot mask);;

let shiftl x n = Int64.shift_left x (Z.to_int n);;

let shiftr x n = Int64.shift_right_logical x (Z.to_int n);;

let shiftr_signed x n = Int64.shift_right x (Z.to_int n);;

let test_bit x n =
  Int64.compare 
    (Int64.logand x (Int64.shift_left Int64.one (Z.to_int n)))
    Int64.zero
  <> 0;;

end;; (*struct Uint64*)

module Bits_Integer : sig
  val shiftl : Z.t -> Z.t -> Z.t
  val shiftr : Z.t -> Z.t -> Z.t
  val test_bit : Z.t -> Z.t -> bool
end = struct

(* We do not need an explicit range checks here,
   because Big_int.int_of_big_int raises Failure
   if the argument does not fit into an int. *)
let shiftl x n = Z.shift_left x (Z.to_int n);;

let shiftr x n = Z.shift_right x (Z.to_int n);;

let test_bit x n =  Z.testbit x (Z.to_int n);;

end;; (*struct Bits_Integer*)

module WasmRef_Isa : sig
  type int = Int_of_integer of Z.t
  val integer_of_int : int -> Z.t
  val equal_inta : int -> int -> bool
  type 'a equal = {equal : 'a -> 'a -> bool}
  val equal : 'a equal -> 'a -> 'a -> bool
  val equal_int : int equal
  val times_inta : int -> int -> int
  type 'a times = {times : 'a -> 'a -> 'a}
  val times : 'a times -> 'a -> 'a -> 'a
  type 'a dvd = {times_dvd : 'a times}
  val times_int : int times
  val dvd_int : int dvd
  type num = One | Bit0 of num | Bit1 of num
  val one_inta : int
  type 'a one = {one : 'a}
  val one : 'a one -> 'a
  val one_int : int one
  val uminus_inta : int -> int
  val minus_inta : int -> int -> int
  val zero_inta : int
  val plus_inta : int -> int -> int
  type 'a uminus = {uminus : 'a -> 'a}
  val uminus : 'a uminus -> 'a -> 'a
  type 'a minus = {minus : 'a -> 'a -> 'a}
  val minus : 'a minus -> 'a -> 'a -> 'a
  type 'a zero = {zero : 'a}
  val zero : 'a zero -> 'a
  type 'a plus = {plus : 'a -> 'a -> 'a}
  val plus : 'a plus -> 'a -> 'a -> 'a
  type 'a semigroup_add = {plus_semigroup_add : 'a plus}
  type 'a cancel_semigroup_add =
    {semigroup_add_cancel_semigroup_add : 'a semigroup_add}
  type 'a ab_semigroup_add = {semigroup_add_ab_semigroup_add : 'a semigroup_add}
  type 'a cancel_ab_semigroup_add =
    {ab_semigroup_add_cancel_ab_semigroup_add : 'a ab_semigroup_add;
      cancel_semigroup_add_cancel_ab_semigroup_add : 'a cancel_semigroup_add;
      minus_cancel_ab_semigroup_add : 'a minus}
  type 'a monoid_add =
    {semigroup_add_monoid_add : 'a semigroup_add; zero_monoid_add : 'a zero}
  type 'a comm_monoid_add =
    {ab_semigroup_add_comm_monoid_add : 'a ab_semigroup_add;
      monoid_add_comm_monoid_add : 'a monoid_add}
  type 'a cancel_comm_monoid_add =
    {cancel_ab_semigroup_add_cancel_comm_monoid_add :
       'a cancel_ab_semigroup_add;
      comm_monoid_add_cancel_comm_monoid_add : 'a comm_monoid_add}
  type 'a mult_zero = {times_mult_zero : 'a times; zero_mult_zero : 'a zero}
  type 'a semigroup_mult = {times_semigroup_mult : 'a times}
  type 'a semiring =
    {ab_semigroup_add_semiring : 'a ab_semigroup_add;
      semigroup_mult_semiring : 'a semigroup_mult}
  type 'a semiring_0 =
    {comm_monoid_add_semiring_0 : 'a comm_monoid_add;
      mult_zero_semiring_0 : 'a mult_zero; semiring_semiring_0 : 'a semiring}
  type 'a semiring_0_cancel =
    {cancel_comm_monoid_add_semiring_0_cancel : 'a cancel_comm_monoid_add;
      semiring_0_semiring_0_cancel : 'a semiring_0}
  type 'a group_add =
    {cancel_semigroup_add_group_add : 'a cancel_semigroup_add;
      minus_group_add : 'a minus; monoid_add_group_add : 'a monoid_add;
      uminus_group_add : 'a uminus}
  type 'a ab_group_add =
    {cancel_comm_monoid_add_ab_group_add : 'a cancel_comm_monoid_add;
      group_add_ab_group_add : 'a group_add}
  type 'a ring =
    {ab_group_add_ring : 'a ab_group_add;
      semiring_0_cancel_ring : 'a semiring_0_cancel}
  val plus_int : int plus
  val semigroup_add_int : int semigroup_add
  val cancel_semigroup_add_int : int cancel_semigroup_add
  val ab_semigroup_add_int : int ab_semigroup_add
  val minus_int : int minus
  val cancel_ab_semigroup_add_int : int cancel_ab_semigroup_add
  val zero_int : int zero
  val monoid_add_int : int monoid_add
  val comm_monoid_add_int : int comm_monoid_add
  val cancel_comm_monoid_add_int : int cancel_comm_monoid_add
  val mult_zero_int : int mult_zero
  val semigroup_mult_int : int semigroup_mult
  val semiring_int : int semiring
  val semiring_0_int : int semiring_0
  val semiring_0_cancel_int : int semiring_0_cancel
  val uminus_int : int uminus
  val group_add_int : int group_add
  val ab_group_add_int : int ab_group_add
  val ring_int : int ring
  type 'a numeral =
    {one_numeral : 'a one; semigroup_add_numeral : 'a semigroup_add}
  val numeral_int : int numeral
  type 'a power = {one_power : 'a one; times_power : 'a times}
  val power_int : int power
  val apsnd : ('a -> 'b) -> 'c * 'a -> 'c * 'b
  val divmod_integer : Z.t -> Z.t -> Z.t * Z.t
  val fst : 'a * 'b -> 'a
  val divide_integer : Z.t -> Z.t -> Z.t
  val divide_inta : int -> int -> int
  type 'a divide = {divide : 'a -> 'a -> 'a}
  val divide : 'a divide -> 'a -> 'a -> 'a
  val divide_int : int divide
  val snd : 'a * 'b -> 'b
  val modulo_integer : Z.t -> Z.t -> Z.t
  val modulo_inta : int -> int -> int
  type 'a modulo =
    {divide_modulo : 'a divide; dvd_modulo : 'a dvd; modulo : 'a -> 'a -> 'a}
  val modulo : 'a modulo -> 'a -> 'a -> 'a
  val modulo_int : int modulo
  type 'a monoid_mult =
    {semigroup_mult_monoid_mult : 'a semigroup_mult;
      power_monoid_mult : 'a power}
  type 'a semiring_numeral =
    {monoid_mult_semiring_numeral : 'a monoid_mult;
      numeral_semiring_numeral : 'a numeral;
      semiring_semiring_numeral : 'a semiring}
  type 'a zero_neq_one =
    {one_zero_neq_one : 'a one; zero_zero_neq_one : 'a zero}
  type 'a semiring_1 =
    {semiring_numeral_semiring_1 : 'a semiring_numeral;
      semiring_0_semiring_1 : 'a semiring_0;
      zero_neq_one_semiring_1 : 'a zero_neq_one}
  type 'a semiring_1_cancel =
    {semiring_0_cancel_semiring_1_cancel : 'a semiring_0_cancel;
      semiring_1_semiring_1_cancel : 'a semiring_1}
  type 'a neg_numeral =
    {group_add_neg_numeral : 'a group_add; numeral_neg_numeral : 'a numeral}
  type 'a ring_1 =
    {neg_numeral_ring_1 : 'a neg_numeral; ring_ring_1 : 'a ring;
      semiring_1_cancel_ring_1 : 'a semiring_1_cancel}
  val monoid_mult_int : int monoid_mult
  val semiring_numeral_int : int semiring_numeral
  val zero_neq_one_int : int zero_neq_one
  val semiring_1_int : int semiring_1
  val semiring_1_cancel_int : int semiring_1_cancel
  val neg_numeral_int : int neg_numeral
  val ring_1_int : int ring_1
  type 'a semiring_no_zero_divisors =
    {semiring_0_semiring_no_zero_divisors : 'a semiring_0}
  type 'a semiring_1_no_zero_divisors =
    {semiring_1_semiring_1_no_zero_divisors : 'a semiring_1;
      semiring_no_zero_divisors_semiring_1_no_zero_divisors :
        'a semiring_no_zero_divisors}
  type 'a ab_semigroup_mult =
    {semigroup_mult_ab_semigroup_mult : 'a semigroup_mult}
  type 'a comm_semiring =
    {ab_semigroup_mult_comm_semiring : 'a ab_semigroup_mult;
      semiring_comm_semiring : 'a semiring}
  type 'a comm_semiring_0 =
    {comm_semiring_comm_semiring_0 : 'a comm_semiring;
      semiring_0_comm_semiring_0 : 'a semiring_0}
  type 'a comm_semiring_0_cancel =
    {comm_semiring_0_comm_semiring_0_cancel : 'a comm_semiring_0;
      semiring_0_cancel_comm_semiring_0_cancel : 'a semiring_0_cancel}
  type 'a comm_monoid_mult =
    {ab_semigroup_mult_comm_monoid_mult : 'a ab_semigroup_mult;
      monoid_mult_comm_monoid_mult : 'a monoid_mult;
      dvd_comm_monoid_mult : 'a dvd}
  type 'a comm_semiring_1 =
    {comm_monoid_mult_comm_semiring_1 : 'a comm_monoid_mult;
      comm_semiring_0_comm_semiring_1 : 'a comm_semiring_0;
      semiring_1_comm_semiring_1 : 'a semiring_1}
  type 'a comm_semiring_1_cancel =
    {comm_semiring_0_cancel_comm_semiring_1_cancel : 'a comm_semiring_0_cancel;
      comm_semiring_1_comm_semiring_1_cancel : 'a comm_semiring_1;
      semiring_1_cancel_comm_semiring_1_cancel : 'a semiring_1_cancel}
  type 'a semidom =
    {comm_semiring_1_cancel_semidom : 'a comm_semiring_1_cancel;
      semiring_1_no_zero_divisors_semidom : 'a semiring_1_no_zero_divisors}
  val semiring_no_zero_divisors_int : int semiring_no_zero_divisors
  val semiring_1_no_zero_divisors_int : int semiring_1_no_zero_divisors
  val ab_semigroup_mult_int : int ab_semigroup_mult
  val comm_semiring_int : int comm_semiring
  val comm_semiring_0_int : int comm_semiring_0
  val comm_semiring_0_cancel_int : int comm_semiring_0_cancel
  val comm_monoid_mult_int : int comm_monoid_mult
  val comm_semiring_1_int : int comm_semiring_1
  val comm_semiring_1_cancel_int : int comm_semiring_1_cancel
  val semidom_int : int semidom
  type 'a comm_ring =
    {comm_semiring_0_cancel_comm_ring : 'a comm_semiring_0_cancel;
      ring_comm_ring : 'a ring}
  val comm_ring_int : int comm_ring
  type 'a comm_ring_1 =
    {comm_ring_comm_ring_1 : 'a comm_ring;
      comm_semiring_1_cancel_comm_ring_1 : 'a comm_semiring_1_cancel;
      ring_1_comm_ring_1 : 'a ring_1}
  val comm_ring_1_int : int comm_ring_1
  type 'a semiring_modulo =
    {comm_semiring_1_cancel_semiring_modulo : 'a comm_semiring_1_cancel;
      modulo_semiring_modulo : 'a modulo}
  type 'a semiring_parity =
    {semiring_modulo_semiring_parity : 'a semiring_modulo}
  type 'a ring_parity =
    {semiring_parity_ring_parity : 'a semiring_parity;
      comm_ring_1_ring_parity : 'a comm_ring_1}
  val semiring_modulo_int : int semiring_modulo
  val semiring_parity_int : int semiring_parity
  val ring_parity_int : int ring_parity
  type nat = Nat of Z.t
  val integer_of_nat : nat -> Z.t
  val bit_integer : Z.t -> nat -> bool
  val bit_int : int -> nat -> bool
  type 'a semiring_bits =
    {semiring_parity_semiring_bits : 'a semiring_parity;
      bit : 'a -> nat -> bool}
  val bit : 'a semiring_bits -> 'a -> nat -> bool
  val semiring_bits_int : int semiring_bits
  type 'a semiring_no_zero_divisors_cancel =
    {semiring_no_zero_divisors_semiring_no_zero_divisors_cancel :
       'a semiring_no_zero_divisors}
  type 'a semidom_divide =
    {divide_semidom_divide : 'a divide; semidom_semidom_divide : 'a semidom;
      semiring_no_zero_divisors_cancel_semidom_divide :
        'a semiring_no_zero_divisors_cancel}
  val semiring_no_zero_divisors_cancel_int :
    int semiring_no_zero_divisors_cancel
  val semidom_divide_int : int semidom_divide
  type 'a algebraic_semidom =
    {semidom_divide_algebraic_semidom : 'a semidom_divide}
  type 'a semidom_modulo =
    {algebraic_semidom_semidom_modulo : 'a algebraic_semidom;
      semiring_modulo_semidom_modulo : 'a semiring_modulo}
  val algebraic_semidom_int : int algebraic_semidom
  val semidom_modulo_int : int semidom_modulo
  type 'a ord = {less_eq : 'a -> 'a -> bool; less : 'a -> 'a -> bool}
  val less_eq : 'a ord -> 'a -> 'a -> bool
  val less : 'a ord -> 'a -> 'a -> bool
  val max : 'a ord -> 'a -> 'a -> 'a
  val ord_integer : Z.t ord
  val minus_nat : nat -> nat -> nat
  val equal_nat : nat -> nat -> bool
  val zero_nat : nat
  val one_nata : nat
  val power : 'a power -> 'a -> nat -> 'a
  val one_integera : Z.t
  val times_integer : Z.t times
  val one_integer : Z.t one
  val power_integer : Z.t power
  val take_bit_integer : nat -> Z.t -> Z.t
  val take_bit_int : nat -> int -> int
  val push_bit_integer : nat -> Z.t -> Z.t
  val push_bit_int : nat -> int -> int
  val drop_bit_integer : nat -> Z.t -> Z.t
  val drop_bit_int : nat -> int -> int
  type 'a semiring_bit_shifts =
    {semiring_bits_semiring_bit_shifts : 'a semiring_bits;
      push_bit : nat -> 'a -> 'a; drop_bit : nat -> 'a -> 'a;
      take_bit : nat -> 'a -> 'a}
  val push_bit : 'a semiring_bit_shifts -> nat -> 'a -> 'a
  val drop_bit : 'a semiring_bit_shifts -> nat -> 'a -> 'a
  val take_bit : 'a semiring_bit_shifts -> nat -> 'a -> 'a
  val semiring_bit_shifts : int semiring_bit_shifts
  val mask_int : nat -> int
  val xor_int : int -> int -> int
  val and_int : int -> int -> int
  val or_int : int -> int -> int
  val not_int : int -> int
  type 'a semiring_bit_operations =
    {semiring_bit_shifts_semiring_bit_operations : 'a semiring_bit_shifts;
      anda : 'a -> 'a -> 'a; ora : 'a -> 'a -> 'a; xor : 'a -> 'a -> 'a;
      mask : nat -> 'a}
  val anda : 'a semiring_bit_operations -> 'a -> 'a -> 'a
  val ora : 'a semiring_bit_operations -> 'a -> 'a -> 'a
  val xor : 'a semiring_bit_operations -> 'a -> 'a -> 'a
  val mask : 'a semiring_bit_operations -> nat -> 'a
  type 'a ring_bit_operations =
    {semiring_bit_operations_ring_bit_operations : 'a semiring_bit_operations;
      ring_parity_ring_bit_operations : 'a ring_parity; nota : 'a -> 'a}
  val nota : 'a ring_bit_operations -> 'a -> 'a
  val semiring_bit_operations_int : int semiring_bit_operations
  val ring_bit_operations_int : int ring_bit_operations
  type typerepa = Typerep of string * typerepa list
  type 'a itself = Type
  val typerep_nata : nat itself -> typerepa
  type 'a typerep = {typerep : 'a itself -> typerepa}
  val typerep : 'a typerep -> 'a itself -> typerepa
  type 'a countable = unit
  type 'a heap = {countable_heap : 'a countable; typerep_heap : 'a typerep}
  val countable_nat : nat countable
  val typerep_nat : nat typerep
  val heap_nat : nat heap
  val one_nat : nat one
  val times_nata : nat -> nat -> nat
  val times_nat : nat times
  val power_nat : nat power
  val less_eq_nat : nat -> nat -> bool
  val less_nat : nat -> nat -> bool
  val ord_nat : nat ord
  type 'a len0 = {len_of : 'a itself -> nat}
  val len_of : 'a len0 -> 'a itself -> nat
  type 'a len = {len0_len : 'a len0}
  type 'a word = Word of int
  val the_int : 'a len -> 'a word -> int
  val of_int : 'a len -> int -> 'a word
  val times_worda : 'a len -> 'a word -> 'a word -> 'a word
  val times_word : 'a len -> 'a word times
  val dvd_word : 'a len -> 'a word dvd
  val one_worda : 'a len -> 'a word
  val one_word : 'a len -> 'a word one
  val plus_worda : 'a len -> 'a word -> 'a word -> 'a word
  val plus_word : 'a len -> 'a word plus
  val zero_worda : 'a len -> 'a word
  val zero_word : 'a len -> 'a word zero
  val semigroup_add_word : 'a len -> 'a word semigroup_add
  val numeral_word : 'a len -> 'a word numeral
  val power_word : 'a len -> 'a word power
  val minus_worda : 'a len -> 'a word -> 'a word -> 'a word
  val minus_word : 'a len -> 'a word minus
  val divide_worda : 'a len -> 'a word -> 'a word -> 'a word
  val divide_word : 'a len -> 'a word divide
  val modulo_worda : 'a len -> 'a word -> 'a word -> 'a word
  val modulo_word : 'a len -> 'a word modulo
  val ab_semigroup_add_word : 'a len -> 'a word ab_semigroup_add
  val semigroup_mult_word : 'a len -> 'a word semigroup_mult
  val semiring_word : 'a len -> 'a word semiring
  val mult_zero_word : 'a len -> 'a word mult_zero
  val monoid_add_word : 'a len -> 'a word monoid_add
  val comm_monoid_add_word : 'a len -> 'a word comm_monoid_add
  val semiring_0_word : 'a len -> 'a word semiring_0
  val monoid_mult_word : 'a len -> 'a word monoid_mult
  val semiring_numeral_word : 'a len -> 'a word semiring_numeral
  val zero_neq_one_word : 'a len -> 'a word zero_neq_one
  val semiring_1_word : 'a len -> 'a word semiring_1
  val ab_semigroup_mult_word : 'a len -> 'a word ab_semigroup_mult
  val comm_semiring_word : 'a len -> 'a word comm_semiring
  val drop_bit_word : 'a len -> nat -> 'a word -> 'a word
  val and_word : 'a len -> 'a word -> 'a word -> 'a word
  val equal_word : 'a len -> 'a word -> 'a word -> bool
  val bit_word : 'a len -> 'a word -> nat -> bool
  val cancel_semigroup_add_word : 'a len -> 'a word cancel_semigroup_add
  val cancel_ab_semigroup_add_word : 'a len -> 'a word cancel_ab_semigroup_add
  val cancel_comm_monoid_add_word : 'a len -> 'a word cancel_comm_monoid_add
  val semiring_0_cancel_word : 'a len -> 'a word semiring_0_cancel
  val comm_semiring_0_word : 'a len -> 'a word comm_semiring_0
  val comm_semiring_0_cancel_word : 'a len -> 'a word comm_semiring_0_cancel
  val semiring_1_cancel_word : 'a len -> 'a word semiring_1_cancel
  val comm_monoid_mult_word : 'a len -> 'a word comm_monoid_mult
  val comm_semiring_1_word : 'a len -> 'a word comm_semiring_1
  val comm_semiring_1_cancel_word : 'a len -> 'a word comm_semiring_1_cancel
  val semiring_modulo_word : 'a len -> 'a word semiring_modulo
  val semiring_parity_word : 'a len -> 'a word semiring_parity
  val semiring_bits_word : 'a len -> 'a word semiring_bits
  val take_bit_word : 'a len -> nat -> 'a word -> 'a word
  val push_bit_word : 'a len -> nat -> 'a word -> 'a word
  val semiring_bit_shifts_word : 'a len -> 'a word semiring_bit_shifts
  type 'a semiring_bit_syntax =
    {semiring_bit_shifts_semiring_bit_syntax : 'a semiring_bit_shifts}
  val semiring_bit_syntax_word : 'a len -> 'a word semiring_bit_syntax
  val typerep_arraya : 'a typerep -> ('a array) itself -> typerepa
  val countable_array : ('a array) countable
  val typerep_array : 'a typerep -> ('a array) typerep
  val heap_array : 'a typerep -> ('a array) heap
  type t_vec = T_v128
  val equal_t_vec : t_vec -> t_vec -> bool
  type t_num = T_i32 | T_i64 | T_f32 | T_f64
  val equal_t_num : t_num -> t_num -> bool
  type t = T_num of t_num | T_vec of t_vec
  val equal_ta : t -> t -> bool
  val equal_t : t equal
  type v_vec = ConstVec128 of V128Wrapper.t
  type i64 = I64_impl_abs of int64
  type i32 = I32_impl_abs of int32
  type v_num = ConstInt32 of i32 | ConstInt64 of i64 |
    ConstFloat32 of F32Wrapper.t | ConstFloat64 of F64Wrapper.t
  type v = V_num of v_num | V_vec of v_vec
  val typerep_va : v itself -> typerepa
  val countable_v : v countable
  val typerep_v : v typerep
  val heap_v : v heap
  type num1 = One_num1
  type 'a finite = {countable_finite : 'a countable}
  type 'a bit0 = Abs_bit0 of int
  type uint8 = Abs_uint8 of num1 bit0 bit0 bit0 word
  val rep_uint8a : uint8 -> num1 bit0 bit0 bit0 word
  val len_of_num1 : num1 itself -> nat
  val len0_num1 : num1 len0
  val len_num1 : num1 len
  val nat_of_integer : Z.t -> nat
  val len_of_bit0 : 'a len0 -> 'a bit0 itself -> nat
  val len0_bit0 : 'a len0 -> 'a bit0 len0
  val len_bit0 : 'a len -> 'a bit0 len
  val times_uint8a : uint8 -> uint8 -> uint8
  val times_uint8 : uint8 times
  val dvd_uint8 : uint8 dvd
  val one_uint8a : uint8
  val one_uint8 : uint8 one
  val plus_uint8a : uint8 -> uint8 -> uint8
  val plus_uint8 : uint8 plus
  val zero_uint8a : uint8
  val zero_uint8 : uint8 zero
  val semigroup_add_uint8 : uint8 semigroup_add
  val numeral_uint8 : uint8 numeral
  val power_uint8 : uint8 power
  val minus_uint8a : uint8 -> uint8 -> uint8
  val minus_uint8 : uint8 minus
  val equal_uint8 : uint8 -> uint8 -> bool
  val shiftr : 'a semiring_bit_syntax -> 'a -> nat -> 'a
  val shiftl : 'a semiring_bit_syntax -> 'a -> nat -> 'a
  val less_eq_int : int -> int -> bool
  val less_eq_word : 'a len -> 'a word -> 'a word -> bool
  val less_eq_uint8 : uint8 -> uint8 -> bool
  val less_int : int -> int -> bool
  val less_word : 'a len -> 'a word -> 'a word -> bool
  val less_uint8 : uint8 -> uint8 -> bool
  val equal_bool : bool -> bool -> bool
  val abs_int : int -> int
  val plus_nat : nat -> nat -> nat
  val suc : nat -> nat
  val signed_take_bit : 'a ring_bit_operations -> nat -> 'a -> 'a
  val the_signed_int : 'a len -> 'a word -> int
  val signed_divide_word : 'a len -> 'a word -> 'a word -> 'a word
  val mod0_uint8 : uint8 -> uint8
  val div0_uint8 : uint8 -> uint8
  val int_of_integer_symbolic : Z.t -> int
  val uint8 : Z.t -> uint8
  val push_bit_uint8 : nat -> uint8 -> uint8
  val uint8_shiftl : uint8 -> Z.t -> uint8
  val or_word : 'a len -> 'a word -> 'a word -> 'a word
  val or_uint8 : uint8 -> uint8 -> uint8
  val mask_uint8 : nat -> uint8
  val and_uint8 : uint8 -> uint8 -> uint8
  val take_bit_uint8 : nat -> uint8 -> uint8
  val test_bit : 'a semiring_bit_syntax -> 'a -> nat -> bool
  val cancel_semigroup_add_uint8 : uint8 cancel_semigroup_add
  val ab_semigroup_add_uint8 : uint8 ab_semigroup_add
  val cancel_ab_semigroup_add_uint8 : uint8 cancel_ab_semigroup_add
  val monoid_add_uint8 : uint8 monoid_add
  val comm_monoid_add_uint8 : uint8 comm_monoid_add
  val cancel_comm_monoid_add_uint8 : uint8 cancel_comm_monoid_add
  val mult_zero_uint8 : uint8 mult_zero
  val semigroup_mult_uint8 : uint8 semigroup_mult
  val semiring_uint8 : uint8 semiring
  val semiring_0_uint8 : uint8 semiring_0
  val semiring_0_cancel_uint8 : uint8 semiring_0_cancel
  val ab_semigroup_mult_uint8 : uint8 ab_semigroup_mult
  val comm_semiring_uint8 : uint8 comm_semiring
  val comm_semiring_0_uint8 : uint8 comm_semiring_0
  val comm_semiring_0_cancel_uint8 : uint8 comm_semiring_0_cancel
  val monoid_mult_uint8 : uint8 monoid_mult
  val semiring_numeral_uint8 : uint8 semiring_numeral
  val zero_neq_one_uint8 : uint8 zero_neq_one
  val semiring_1_uint8 : uint8 semiring_1
  val semiring_1_cancel_uint8 : uint8 semiring_1_cancel
  val comm_monoid_mult_uint8 : uint8 comm_monoid_mult
  val comm_semiring_1_uint8 : uint8 comm_semiring_1
  val comm_semiring_1_cancel_uint8 : uint8 comm_semiring_1_cancel
  val divide_uint8 : uint8 divide
  val modulo_uint8 : uint8 modulo
  val semiring_modulo_uint8 : uint8 semiring_modulo
  val semiring_parity_uint8 : uint8 semiring_parity
  val semiring_bits_uint8 : uint8 semiring_bits
  val semiring_bit_shifts_uint8 : uint8 semiring_bit_shifts
  val semiring_bit_syntax_uint8 : uint8 semiring_bit_syntax
  val uint8_divmod : uint8 -> uint8 -> uint8 * uint8
  val uint8_div : uint8 -> uint8 -> uint8
  val divide_uint8a : uint8 -> uint8 -> uint8
  val uint8_sdiv : uint8 -> uint8 -> uint8
  val uint8_mod : uint8 -> uint8 -> uint8
  val modulo_uint8a : uint8 -> uint8 -> uint8
  val uint8_shiftr : uint8 -> Z.t -> uint8
  val drop_bit_uint8 : nat -> uint8 -> uint8
  val uint8_test_bit : uint8 -> Z.t -> bool
  val bit_uint8 : uint8 -> nat -> bool
  val eq : 'a equal -> 'a -> 'a -> bool
  val equal_list : 'a equal -> 'a list -> 'a list -> bool
  type tf = Tf of t list * t list
  val equal_tfa : tf -> tf -> bool
  val equal_tf : tf equal
  val typerep_tfa : tf itself -> typerepa
  val countable_tf : tf countable
  val typerep_tf : tf typerep
  val heap_tf : tf heap
  val zero_f32 : F32Wrapper.t zero
  type 'a wasm_base = {zero_wasm_base : 'a zero}
  val wasm_base_f32 : F32Wrapper.t wasm_base
  type 'a wasm_float =
    {wasm_base_wasm_float : 'a wasm_base; float_neg : 'a -> 'a;
      float_abs : 'a -> 'a; float_ceil : 'a -> 'a; float_floor : 'a -> 'a;
      float_trunc : 'a -> 'a; float_nearest : 'a -> 'a; float_sqrt : 'a -> 'a;
      float_add : 'a -> 'a -> 'a; float_sub : 'a -> 'a -> 'a;
      float_mul : 'a -> 'a -> 'a; float_div : 'a -> 'a -> 'a;
      float_min : 'a -> 'a -> 'a; float_max : 'a -> 'a -> 'a;
      float_copysign : 'a -> 'a -> 'a; float_eq : 'a -> 'a -> bool;
      float_lt : 'a -> 'a -> bool; float_gt : 'a -> 'a -> bool;
      float_le : 'a -> 'a -> bool; float_ge : 'a -> 'a -> bool}
  val float_neg : 'a wasm_float -> 'a -> 'a
  val float_abs : 'a wasm_float -> 'a -> 'a
  val float_ceil : 'a wasm_float -> 'a -> 'a
  val float_floor : 'a wasm_float -> 'a -> 'a
  val float_trunc : 'a wasm_float -> 'a -> 'a
  val float_nearest : 'a wasm_float -> 'a -> 'a
  val float_sqrt : 'a wasm_float -> 'a -> 'a
  val float_add : 'a wasm_float -> 'a -> 'a -> 'a
  val float_sub : 'a wasm_float -> 'a -> 'a -> 'a
  val float_mul : 'a wasm_float -> 'a -> 'a -> 'a
  val float_div : 'a wasm_float -> 'a -> 'a -> 'a
  val float_min : 'a wasm_float -> 'a -> 'a -> 'a
  val float_max : 'a wasm_float -> 'a -> 'a -> 'a
  val float_copysign : 'a wasm_float -> 'a -> 'a -> 'a
  val float_eq : 'a wasm_float -> 'a -> 'a -> bool
  val float_lt : 'a wasm_float -> 'a -> 'a -> bool
  val float_gt : 'a wasm_float -> 'a -> 'a -> bool
  val float_le : 'a wasm_float -> 'a -> 'a -> bool
  val float_ge : 'a wasm_float -> 'a -> 'a -> bool
  val wasm_float_f32 : F32Wrapper.t wasm_float
  val zero_f64 : F64Wrapper.t zero
  val wasm_base_f64 : F64Wrapper.t wasm_base
  val wasm_float_f64 : F64Wrapper.t wasm_float
  val zero_i32a : i32
  val zero_i32 : i32 zero
  val len_of_i32 : i32 itself -> nat
  val len0_i32 : i32 len0
  val len_i32 : i32 len
  val bit_uint32 : int32 -> nat -> bool
  val uint32 : Z.t -> int32
  val integer_of_uint32 : int32 -> Z.t
  val nat_of_uint32 : int32 -> nat
  val nat_of_int_i32 : i32 -> nat
  val fold_atLeastAtMost_nat : (nat -> 'a -> 'a) -> nat -> nat -> 'a -> 'a
  val int_of_nat : nat -> int
  val uint32_of_int : int -> int32
  val comp : ('a -> 'b) -> ('c -> 'a) -> 'c -> 'b
  val uint32_of_nat : nat -> int32
  val int_popcnt_i32 : i32 -> i32
  val int_of_nat_i32 : nat -> i32
  val int_shr_u_i32 : i32 -> i32 -> i32
  val int_shr_s_i32 : i32 -> i32 -> i32
  val drop_bit_uint32 : nat -> int32 -> int32
  val mod0_uint32 : int32 -> int32
  val div0_uint32 : int32 -> int32
  val push_bit_uint32 : nat -> int32 -> int32
  val plus_uint32 : int32 plus
  val semigroup_add_uint32 : int32 semigroup_add
  val cancel_semigroup_add_uint32 : int32 cancel_semigroup_add
  val ab_semigroup_add_uint32 : int32 ab_semigroup_add
  val minus_uint32 : int32 minus
  val cancel_ab_semigroup_add_uint32 : int32 cancel_ab_semigroup_add
  val zero_uint32 : int32 zero
  val monoid_add_uint32 : int32 monoid_add
  val comm_monoid_add_uint32 : int32 comm_monoid_add
  val cancel_comm_monoid_add_uint32 : int32 cancel_comm_monoid_add
  val times_uint32 : int32 times
  val mult_zero_uint32 : int32 mult_zero
  val semigroup_mult_uint32 : int32 semigroup_mult
  val semiring_uint32 : int32 semiring
  val semiring_0_uint32 : int32 semiring_0
  val semiring_0_cancel_uint32 : int32 semiring_0_cancel
  val ab_semigroup_mult_uint32 : int32 ab_semigroup_mult
  val comm_semiring_uint32 : int32 comm_semiring
  val comm_semiring_0_uint32 : int32 comm_semiring_0
  val comm_semiring_0_cancel_uint32 : int32 comm_semiring_0_cancel
  val one_uint32 : int32 one
  val power_uint32 : int32 power
  val monoid_mult_uint32 : int32 monoid_mult
  val numeral_uint32 : int32 numeral
  val semiring_numeral_uint32 : int32 semiring_numeral
  val zero_neq_one_uint32 : int32 zero_neq_one
  val semiring_1_uint32 : int32 semiring_1
  val semiring_1_cancel_uint32 : int32 semiring_1_cancel
  val dvd_uint32 : int32 dvd
  val comm_monoid_mult_uint32 : int32 comm_monoid_mult
  val comm_semiring_1_uint32 : int32 comm_semiring_1
  val comm_semiring_1_cancel_uint32 : int32 comm_semiring_1_cancel
  val uint32_mod : int32 -> int32 -> int32
  val modulo_uint32a : int32 -> int32 -> int32
  val semiring_bit_syntax_uint32 : int32 semiring_bit_syntax
  val uint32_divmod : int32 -> int32 -> int32 * int32
  val uint32_div : int32 -> int32 -> int32
  val divide_uint32a : int32 -> int32 -> int32
  val divide_uint32 : int32 divide
  val modulo_uint32 : int32 modulo
  val semiring_modulo_uint32 : int32 semiring_modulo
  val semiring_parity_uint32 : int32 semiring_parity
  val semiring_bits_uint32 : int32 semiring_bits
  val mask_uint32 : nat -> int32
  val take_bit_uint32 : nat -> int32 -> int32
  val semiring_bit_shifts_uint32 : int32 semiring_bit_shifts
  val int_rem_u_i32 : i32 -> i32 -> i32 option
  val int_rem_s_i32 : i32 -> i32 -> i32 option
  val int_div_u_i32 : i32 -> i32 -> i32 option
  val int_div_s_i32 : i32 -> i32 -> i32 option
  val int_rotr_i32 : i32 -> i32 -> i32
  val int_rotl_i32 : i32 -> i32 -> i32
  val int_lt_u_i32 : i32 -> i32 -> bool
  val msb_uint32 : int32 -> bool
  val int_lt_s_i32 : i32 -> i32 -> bool
  val int_le_u_i32 : i32 -> i32 -> bool
  val int_le_s_i32 : i32 -> i32 -> bool
  val int_gt_u_i32 : i32 -> i32 -> bool
  val int_gt_s_i32 : i32 -> i32 -> bool
  val int_ge_u_i32 : i32 -> i32 -> bool
  val int_ge_s_i32 : i32 -> i32 -> bool
  val int_xor_i32 : i32 -> i32 -> i32
  val int_sub_i32 : i32 -> i32 -> i32
  val int_shl_i32 : i32 -> i32 -> i32
  val int_mul_i32 : i32 -> i32 -> i32
  val int_eqz_i32 : i32 -> bool
  val gen_length : nat -> 'a list -> nat
  val size_list : 'a list -> nat
  val map : ('a -> 'b) -> 'a list -> 'b list
  val upt : nat -> nat -> nat list
  val fold : ('a -> 'b -> 'b) -> 'a list -> 'b -> 'b
  val rev : 'a list -> 'a list
  val to_bl : 'a len -> 'a word -> bool list
  val takeWhile : ('a -> bool) -> 'a list -> 'a list
  val word_ctz : 'a len -> 'a word -> nat
  val id : 'a -> 'a
  val foldr : ('a -> 'b -> 'b) -> 'a list -> 'b -> 'b
  val horner_sum : 'b comm_semiring_0 -> ('a -> 'b) -> 'b -> 'a list -> 'b
  val of_bool : 'a zero_neq_one -> bool -> 'a
  val set_bits_word : 'a len -> (nat -> bool) -> 'a word
  val rep_uint32 : int32 -> num1 bit0 bit0 bit0 bit0 bit0 word
  val abs_uint32 : num1 bit0 bit0 bit0 bit0 bit0 word -> int32
  val of_nat : 'a len -> nat -> 'a word
  val int_ctz_i32 : i32 -> i32
  val word_clz : 'a len -> 'a word -> nat
  val int_clz_i32 : i32 -> i32
  val int_and_i32 : i32 -> i32 -> i32
  val int_add_i32 : i32 -> i32 -> i32
  val int_or_i32 : i32 -> i32 -> i32
  val int_eq_i32 : i32 -> i32 -> bool
  type 'a wasm_int_ops =
    {len_wasm_int_ops : 'a len; wasm_base_wasm_int_ops : 'a wasm_base;
      int_clz : 'a -> 'a; int_ctz : 'a -> 'a; int_popcnt : 'a -> 'a;
      int_add : 'a -> 'a -> 'a; int_sub : 'a -> 'a -> 'a;
      int_mul : 'a -> 'a -> 'a; int_div_u : 'a -> 'a -> 'a option;
      int_div_s : 'a -> 'a -> 'a option; int_rem_u : 'a -> 'a -> 'a option;
      int_rem_s : 'a -> 'a -> 'a option; int_and : 'a -> 'a -> 'a;
      int_or : 'a -> 'a -> 'a; int_xor : 'a -> 'a -> 'a;
      int_shl : 'a -> 'a -> 'a; int_shr_u : 'a -> 'a -> 'a;
      int_shr_s : 'a -> 'a -> 'a; int_rotl : 'a -> 'a -> 'a;
      int_rotr : 'a -> 'a -> 'a; int_eqz : 'a -> bool;
      int_eq : 'a -> 'a -> bool; int_lt_u : 'a -> 'a -> bool;
      int_lt_s : 'a -> 'a -> bool; int_gt_u : 'a -> 'a -> bool;
      int_gt_s : 'a -> 'a -> bool; int_le_u : 'a -> 'a -> bool;
      int_le_s : 'a -> 'a -> bool; int_ge_u : 'a -> 'a -> bool;
      int_ge_s : 'a -> 'a -> bool; int_of_nata : nat -> 'a;
      nat_of_int : 'a -> nat}
  val int_clz : 'a wasm_int_ops -> 'a -> 'a
  val int_ctz : 'a wasm_int_ops -> 'a -> 'a
  val int_popcnt : 'a wasm_int_ops -> 'a -> 'a
  val int_add : 'a wasm_int_ops -> 'a -> 'a -> 'a
  val int_sub : 'a wasm_int_ops -> 'a -> 'a -> 'a
  val int_mul : 'a wasm_int_ops -> 'a -> 'a -> 'a
  val int_div_u : 'a wasm_int_ops -> 'a -> 'a -> 'a option
  val int_div_s : 'a wasm_int_ops -> 'a -> 'a -> 'a option
  val int_rem_u : 'a wasm_int_ops -> 'a -> 'a -> 'a option
  val int_rem_s : 'a wasm_int_ops -> 'a -> 'a -> 'a option
  val int_and : 'a wasm_int_ops -> 'a -> 'a -> 'a
  val int_or : 'a wasm_int_ops -> 'a -> 'a -> 'a
  val int_xor : 'a wasm_int_ops -> 'a -> 'a -> 'a
  val int_shl : 'a wasm_int_ops -> 'a -> 'a -> 'a
  val int_shr_u : 'a wasm_int_ops -> 'a -> 'a -> 'a
  val int_shr_s : 'a wasm_int_ops -> 'a -> 'a -> 'a
  val int_rotl : 'a wasm_int_ops -> 'a -> 'a -> 'a
  val int_rotr : 'a wasm_int_ops -> 'a -> 'a -> 'a
  val int_eqz : 'a wasm_int_ops -> 'a -> bool
  val int_eq : 'a wasm_int_ops -> 'a -> 'a -> bool
  val int_lt_u : 'a wasm_int_ops -> 'a -> 'a -> bool
  val int_lt_s : 'a wasm_int_ops -> 'a -> 'a -> bool
  val int_gt_u : 'a wasm_int_ops -> 'a -> 'a -> bool
  val int_gt_s : 'a wasm_int_ops -> 'a -> 'a -> bool
  val int_le_u : 'a wasm_int_ops -> 'a -> 'a -> bool
  val int_le_s : 'a wasm_int_ops -> 'a -> 'a -> bool
  val int_ge_u : 'a wasm_int_ops -> 'a -> 'a -> bool
  val int_ge_s : 'a wasm_int_ops -> 'a -> 'a -> bool
  val int_of_nata : 'a wasm_int_ops -> nat -> 'a
  val nat_of_int : 'a wasm_int_ops -> 'a -> nat
  type 'a wasm_int = {wasm_int_ops_wasm_int : 'a wasm_int_ops}
  val wasm_base_i32 : i32 wasm_base
  val wasm_int_ops_i32 : i32 wasm_int_ops
  val wasm_int_i32 : i32 wasm_int
  val zero_i64a : i64
  val zero_i64 : i64 zero
  val len_of_i64 : i64 itself -> nat
  val len0_i64 : i64 len0
  val len_i64 : i64 len
  val bit_uint64 : int64 -> nat -> bool
  val uint64 : Z.t -> int64
  val integer_of_uint64 : int64 -> Z.t
  val nat_of_uint64 : int64 -> nat
  val nat_of_int_i64 : i64 -> nat
  val uint64_of_int : int -> int64
  val uint64_of_nat : nat -> int64
  val int_popcnt_i64 : i64 -> i64
  val int_of_nat_i64 : nat -> i64
  val int_shr_u_i64 : i64 -> i64 -> i64
  val int_shr_s_i64 : i64 -> i64 -> i64
  val push_bit_uint64 : nat -> int64 -> int64
  val drop_bit_uint64 : nat -> int64 -> int64
  val mod0_uint64 : int64 -> int64
  val div0_uint64 : int64 -> int64
  val uint64_divmod : int64 -> int64 -> int64 * int64
  val uint64_mod : int64 -> int64 -> int64
  val int_rem_u_i64 : i64 -> i64 -> i64 option
  val int_rem_s_i64 : i64 -> i64 -> i64 option
  val uint64_div : int64 -> int64 -> int64
  val int_div_u_i64 : i64 -> i64 -> i64 option
  val int_div_s_i64 : i64 -> i64 -> i64 option
  val modulo_uint64a : int64 -> int64 -> int64
  val divide_uint64a : int64 -> int64 -> int64
  val plus_uint64 : int64 plus
  val semigroup_add_uint64 : int64 semigroup_add
  val cancel_semigroup_add_uint64 : int64 cancel_semigroup_add
  val ab_semigroup_add_uint64 : int64 ab_semigroup_add
  val minus_uint64 : int64 minus
  val cancel_ab_semigroup_add_uint64 : int64 cancel_ab_semigroup_add
  val zero_uint64 : int64 zero
  val monoid_add_uint64 : int64 monoid_add
  val comm_monoid_add_uint64 : int64 comm_monoid_add
  val cancel_comm_monoid_add_uint64 : int64 cancel_comm_monoid_add
  val times_uint64 : int64 times
  val mult_zero_uint64 : int64 mult_zero
  val semigroup_mult_uint64 : int64 semigroup_mult
  val semiring_uint64 : int64 semiring
  val semiring_0_uint64 : int64 semiring_0
  val semiring_0_cancel_uint64 : int64 semiring_0_cancel
  val ab_semigroup_mult_uint64 : int64 ab_semigroup_mult
  val comm_semiring_uint64 : int64 comm_semiring
  val comm_semiring_0_uint64 : int64 comm_semiring_0
  val comm_semiring_0_cancel_uint64 : int64 comm_semiring_0_cancel
  val one_uint64 : int64 one
  val power_uint64 : int64 power
  val monoid_mult_uint64 : int64 monoid_mult
  val numeral_uint64 : int64 numeral
  val semiring_numeral_uint64 : int64 semiring_numeral
  val zero_neq_one_uint64 : int64 zero_neq_one
  val semiring_1_uint64 : int64 semiring_1
  val semiring_1_cancel_uint64 : int64 semiring_1_cancel
  val dvd_uint64 : int64 dvd
  val comm_monoid_mult_uint64 : int64 comm_monoid_mult
  val comm_semiring_1_uint64 : int64 comm_semiring_1
  val comm_semiring_1_cancel_uint64 : int64 comm_semiring_1_cancel
  val divide_uint64 : int64 divide
  val modulo_uint64 : int64 modulo
  val semiring_modulo_uint64 : int64 semiring_modulo
  val semiring_parity_uint64 : int64 semiring_parity
  val semiring_bits_uint64 : int64 semiring_bits
  val take_bit_uint64 : nat -> int64 -> int64
  val semiring_bit_shifts_uint64 : int64 semiring_bit_shifts
  val semiring_bit_syntax_uint64 : int64 semiring_bit_syntax
  val mask_uint64 : nat -> int64
  val int_rotr_i64 : i64 -> i64 -> i64
  val int_rotl_i64 : i64 -> i64 -> i64
  val int_lt_u_i64 : i64 -> i64 -> bool
  val msb_uint64 : int64 -> bool
  val int_lt_s_i64 : i64 -> i64 -> bool
  val int_le_u_i64 : i64 -> i64 -> bool
  val int_le_s_i64 : i64 -> i64 -> bool
  val int_gt_u_i64 : i64 -> i64 -> bool
  val int_gt_s_i64 : i64 -> i64 -> bool
  val int_ge_u_i64 : i64 -> i64 -> bool
  val int_ge_s_i64 : i64 -> i64 -> bool
  val int_xor_i64 : i64 -> i64 -> i64
  val int_sub_i64 : i64 -> i64 -> i64
  val int_shl_i64 : i64 -> i64 -> i64
  val int_mul_i64 : i64 -> i64 -> i64
  val int_eqz_i64 : i64 -> bool
  val rep_uint64 : int64 -> num1 bit0 bit0 bit0 bit0 bit0 bit0 word
  val abs_uint64 : num1 bit0 bit0 bit0 bit0 bit0 bit0 word -> int64
  val int_ctz_i64 : i64 -> i64
  val int_clz_i64 : i64 -> i64
  val int_and_i64 : i64 -> i64 -> i64
  val int_add_i64 : i64 -> i64 -> i64
  val int_or_i64 : i64 -> i64 -> i64
  val int_eq_i64 : i64 -> i64 -> bool
  val wasm_base_i64 : i64 wasm_base
  val wasm_int_ops_i64 : i64 wasm_int_ops
  val wasm_int_i64 : i64 wasm_int
  type mut = T_immut | T_mut
  val equal_muta : mut -> mut -> bool
  val equal_mut : mut equal
  val typerep_optiona : 'a typerep -> ('a option) itself -> typerepa
  val countable_option : 'a countable -> ('a option) countable
  val typerep_option : 'a typerep -> ('a option) typerep
  val heap_option : 'a heap -> ('a option) heap
  val equal_literal : string equal
  type sx = S | U
  type binop_i = Add | Sub | Mul | Div of sx | Rem of sx | And | Or | Xor | Shl
    | Shr of sx | Rotl | Rotr
  type binop_f = Addf | Subf | Mulf | Divf | Min | Max | Copysign
  type binop = Binop_i of binop_i | Binop_f of binop_f
  val typerep_binopa : binop itself -> typerepa
  val typerep_binop : binop typerep
  type cvtop = Convert | Reinterpret
  val typerep_cvtopa : cvtop itself -> typerepa
  val typerep_cvtop : cvtop typerep
  val typerep_proda : 'a typerep -> 'b typerep -> ('a * 'b) itself -> typerepa
  val countable_prod : 'a countable -> 'b countable -> ('a * 'b) countable
  val typerep_prod : 'a typerep -> 'b typerep -> ('a * 'b) typerep
  val heap_prod : 'a heap -> 'b heap -> ('a * 'b) heap
  val equal_unita : unit -> unit -> bool
  val equal_unit : unit equal
  val typerep_unita : unit itself -> typerepa
  val countable_unit : unit countable
  val typerep_unit : unit typerep
  val heap_unit : unit heap
  val typerep_byte_arraya : Bytes.t itself -> typerepa
  val countable_byte_array : Bytes.t countable
  val typerep_byte_array : Bytes.t typerep
  val heap_byte_array : Bytes.t heap
  type 'a global_ext = Global_ext of mut * v * 'a
  val typerep_global_exta : 'a typerep -> 'a global_ext itself -> typerepa
  val countable_global_ext : 'a countable -> 'a global_ext countable
  val typerep_global_ext : 'a typerep -> 'a global_ext typerep
  val heap_global_ext : 'a heap -> 'a global_ext heap
  type 'a inst_m_ext =
    Inst_m_ext of tf array * nat array * nat array * nat array * nat array * 'a
  type shape_vec_i = I8_16 | I16_8 | I32_4 | I64_2
  type storeop_vec = Store_128 | Store_lane of shape_vec_i * nat
  type tp_vec = Tp_v8_8 | Tp_v16_4 | Tp_v32_2
  type loadop_vec = Load_128 | Load_packed_vec of tp_vec * sx | Load_32_zero |
    Load_64_zero | Load_splat of shape_vec_i
  type shape_vec_f = F32_4 | F64_2
  type shape_vec = Svi of shape_vec_i | Svf of shape_vec_f
  type tp_num = Tp_i8 | Tp_i16 | Tp_i32
  type testop = Eqz
  type relop_i = Eq | Ne | Lt of sx | Gt of sx | Le of sx | Ge of sx
  type relop_f = Eqf | Nef | Ltf | Gtf | Lef | Gef
  type relop = Relop_i of relop_i | Relop_f of relop_f
  type unop_i = Clz | Ctz | Popcnt
  type unop_f = Neg | Abs | Ceil | Floor | Trunc | Nearest | Sqrt
  type unop = Unop_i of unop_i | Unop_f of unop_f | Extend_s of tp_num
  type sat = Sat | Nonsat
  type tb = Tbf of nat | Tbv of t option
  type b_e = Unreachable | Nop | Drop | Select | Block of tb * b_e list |
    Loop of tb * b_e list | If of tb * b_e list * b_e list | Br of nat |
    Br_if of nat | Br_table of nat list * nat | Return | Call of nat |
    Call_indirect of nat | Get_local of nat | Set_local of nat |
    Tee_local of nat | Get_global of nat | Set_global of nat |
    Load of t_num * (tp_num * sx) option * nat * nat |
    Store of t_num * tp_num option * nat * nat |
    Load_vec of loadop_vec * nat * nat |
    Load_lane_vec of shape_vec_i * nat * nat * nat |
    Store_vec of storeop_vec * nat * nat | Current_memory | Grow_memory |
    EConst of v | Unop of t_num * unop | Binop of t_num * binop |
    Testop of t_num * testop | Relop of t_num * relop |
    Cvtop of t_num * cvtop * t_num * (sat * sx) option |
    Unop_vec of V128Wrapper.unop_vec_t | Binop_vec of V128Wrapper.binop_vec_t |
    Ternop_vec of V128Wrapper.ternop_vec_t |
    Test_vec of V128Wrapper.testop_vec_t |
    Shift_vec of V128Wrapper.shiftop_vec_t | Splat_vec of shape_vec |
    Extract_vec of shape_vec * sx * nat | Replace_vec of shape_vec * nat
  type cl_m = Func_native of unit inst_m_ext * tf * t list * b_e list |
    Func_host of tf * host
  and 'a s_m_ext =
    S_m_ext of
      cl_m array * ((nat option) array * nat option) array *
        (Bytes.t * nat option) array * unit global_ext array * 'a
  and host =
    Abs_host_m of
      (unit s_m_ext * v list -> (unit -> ((unit s_m_ext * v list) option)))
  val typerep_cl_ma : cl_m itself -> typerepa
  val countable_cl_m : cl_m countable
  val typerep_cl_m : cl_m typerep
  val heap_cl_m : cl_m heap
  type 'a inst_ext =
    Inst_ext of tf list * nat list * nat list * nat list * nat list * 'a
  type 'a f_ext = F_ext of v list * unit inst_ext * 'a
  type e = Basic of b_e | Trap | Invoke of nat | Label of nat * e list * e list
    | Frame of nat * unit f_ext * e list | Init_mem of nat * uint8 list |
    Init_tab of nat * nat list
  type 'a seq = Empty | Insert of 'a * 'a pred | Join of 'a pred * 'a seq
  and 'a pred = Seq of (unit -> 'a seq)
  type v_ext = Ext_func of nat | Ext_tab of nat | Ext_mem of nat |
    Ext_glob of nat
  type 'a tg_ext = Tg_ext of mut * t * 'a
  type 'a limit_t_ext = Limit_t_ext of nat * nat option * 'a
  type imp_desc = Imp_func of nat | Imp_tab of unit limit_t_ext |
    Imp_mem of unit limit_t_ext | Imp_glob of unit tg_ext
  type 'a module_import_ext =
    Module_import_ext of string * string * imp_desc * 'a
  type 'a module_export_ext = Module_export_ext of string * v_ext * 'a
  type 'a module_glob_ext = Module_glob_ext of unit tg_ext * b_e list * 'a
  type 'a module_elem_ext = Module_elem_ext of nat * b_e list * nat list * 'a
  type 'a module_data_ext = Module_data_ext of nat * b_e list * uint8 list * 'a
  type 'a m_ext =
    M_ext of
      tf list * (nat * (t list * b_e list)) list * unit limit_t_ext list *
        unit limit_t_ext list * unit module_glob_ext list *
        unit module_elem_ext list * unit module_data_ext list * nat option *
        unit module_import_ext list * unit module_export_ext list * 'a
  type res_error = Error_invalid of string | Error_invariant of string |
    Error_exhaustion of string
  type res = RCrash of res_error | RTrap of string | RValue of v list
  type extern_t = Te_func of tf | Te_tab of unit limit_t_ext |
    Te_mem of unit limit_t_ext | Te_glob of unit tg_ext
  type ct = TAny | TSome of t
  type redex = Redex of v list * e list * b_e list
  type res_step = Res_crash of res_error | Res_trap of string | Step_normal
  type label_context = Label_context of v list * b_e list * nat * b_e list
  type checker_type = TopType of ct list | Typea of t list | Bot
  type 'a t_context_ext =
    T_context_ext of
      tf list * tf list * unit tg_ext list * unit limit_t_ext list *
        unit limit_t_ext list * t list * (t list) list * (t list) option * 'a
  type res_inst_m = RI_crash_m of res_error | RI_trap_m of string |
    RI_res_m of unit inst_m_ext * unit module_export_ext list * e list
  type frame_context_m =
    Frame_context_m of
      redex * label_context list * nat * v array * unit inst_m_ext
  type config_m =
    Config_m of nat * unit s_m_ext * frame_context_m * frame_context_m list
  val nth : 'a list -> nat -> 'a
  val zip : 'a list -> 'b list -> ('a * 'b) list
  val len : 'a heap -> 'a array -> (unit -> nat)
  val newa : 'a heap -> nat -> 'a -> (unit -> ('a array))
  val array_nth : 'a heap -> 'a array -> nat -> (unit -> 'a)
  val upd : 'a heap -> nat -> 'a -> 'a array -> (unit -> ('a array))
  val drop : nat -> 'a list -> 'a list
  val find : ('a -> bool) -> 'a list -> 'a option
  val null : 'a list -> bool
  val last : 'a list -> 'a
  val take_tr : nat -> 'a list -> 'a list -> 'a list
  val take : nat -> 'a list -> 'a list
  val map_option : ('a -> 'b) -> 'a option -> 'b option
  val those : ('a option) list -> ('a list) option
  val concat : ('a list) list -> 'a list
  val member : 'a equal -> 'a list -> 'a -> bool
  val distinct : 'a equal -> 'a list -> bool
  val ki64 : nat
  val replicate_tr : nat -> 'a -> 'a list -> 'a list
  val replicate : nat -> 'a -> 'a list
  val is_none : 'a option -> bool
  val bind : 'a pred -> ('a -> 'b pred) -> 'b pred
  val apply : ('a -> 'b pred) -> 'a seq -> 'b seq
  val blit :
    'a heap -> 'a array -> nat -> 'a array -> nat -> nat -> (unit -> unit)
  val map_filter : ('a -> 'b option) -> 'a list -> 'b list
  val eval : 'a equal -> 'a pred -> 'a -> bool
  val membera : 'a equal -> 'a seq -> 'a -> bool
  val holds : unit pred -> bool
  val msbyte : uint8 list -> uint8
  val bot_pred : 'a pred
  val single : 'a -> 'a pred
  val abs_uint8 : num1 bit0 bit0 bit0 word -> uint8
  val rep_uint8 : uint8 -> num1 bit0 bit0 bit0 word
  val typeof_vec : v_vec -> t_vec
  val typeof_num : v_num -> t_num
  val typeof : v -> t
  val g_val : 'a global_ext -> v
  val g_mut : 'a global_ext -> mut
  val tg_mut : 'a tg_ext -> mut
  val tg_t : 'a tg_ext -> t
  val glob_typing : 'a global_ext -> 'b tg_ext -> bool
  val signed_cast : 'b len -> 'a len -> 'b word -> 'a word
  val adjunct : 'a pred -> 'a seq -> 'a seq
  val sup_pred : 'a pred -> 'a pred -> 'a pred
  val if_pred : bool -> unit pred
  val msb_uint8 : uint8 -> bool
  val msb_byte : uint8 -> bool
  val dvd : 'a equal * 'a semidom_modulo -> 'a -> 'a -> bool
  val bin_split : nat -> int -> int * int
  val list_all : ('a -> bool) -> 'a list -> bool
  val integer_of_uint8 : uint8 -> Z.t
  val integer_of_uint8_signed : uint8 -> Z.t
  val nat_of_uint8 : uint8 -> nat
  val uint8_of_int : int -> uint8
  val uint8_of_nat : nat -> uint8
  val pred_option : ('a -> bool) -> 'a option -> bool
  val l_min : 'a limit_t_ext -> nat
  val l_max : 'a limit_t_ext -> nat option
  val limits_compat : 'a limit_t_ext -> 'b limit_t_ext -> bool
  val zero_byte : uint8
  val ocaml_int64_to_isabelle_int64 : Int64.t -> i64
  val isabelle_i64_trunc_sat_u_f64 : F64Wrapper.t -> i64
  val ui64_trunc_sat_f64 : F64Wrapper.t -> i64
  val isabelle_i64_trunc_sat_u_f32 : F32Wrapper.t -> i64
  val ui64_trunc_sat_f32 : F32Wrapper.t -> i64
  val isabelle_i64_trunc_sat_s_f64 : F64Wrapper.t -> i64
  val si64_trunc_sat_f64 : F64Wrapper.t -> i64
  val isabelle_i64_trunc_sat_s_f32 : F32Wrapper.t -> i64
  val si64_trunc_sat_f32 : F32Wrapper.t -> i64
  val isabelle_i64_trunc_u_f64 : F64Wrapper.t -> i64 option
  val ui64_trunc_f64 : F64Wrapper.t -> i64 option
  val isabelle_i64_trunc_u_f32 : F32Wrapper.t -> i64 option
  val ui64_trunc_f32 : F32Wrapper.t -> i64 option
  val isabelle_i64_trunc_s_f64 : F64Wrapper.t -> i64 option
  val si64_trunc_f64 : F64Wrapper.t -> i64 option
  val isabelle_i64_trunc_s_f32 : F32Wrapper.t -> i64 option
  val si64_trunc_f32 : F32Wrapper.t -> i64 option
  val wasm_extend_u : i32 -> i64
  val wasm_extend_s : i32 -> i64
  val cvt_i64 : (sat * sx) option -> v_num -> i64 option
  val ocaml_int32_to_isabelle_int32 : Int32.t -> i32
  val isabelle_i32_trunc_sat_u_f64 : F64Wrapper.t -> i32
  val ui32_trunc_sat_f64 : F64Wrapper.t -> i32
  val isabelle_i32_trunc_sat_u_f32 : F32Wrapper.t -> i32
  val ui32_trunc_sat_f32 : F32Wrapper.t -> i32
  val isabelle_i32_trunc_sat_s_f64 : F64Wrapper.t -> i32
  val si32_trunc_sat_f64 : F64Wrapper.t -> i32
  val isabelle_i32_trunc_sat_s_f32 : F32Wrapper.t -> i32
  val si32_trunc_sat_f32 : F32Wrapper.t -> i32
  val isabelle_i32_trunc_u_f64 : F64Wrapper.t -> i32 option
  val ui32_trunc_f64 : F64Wrapper.t -> i32 option
  val isabelle_i32_trunc_u_f32 : F32Wrapper.t -> i32 option
  val ui32_trunc_f32 : F32Wrapper.t -> i32 option
  val isabelle_i32_trunc_s_f64 : F64Wrapper.t -> i32 option
  val si32_trunc_f64 : F64Wrapper.t -> i32 option
  val isabelle_i32_trunc_s_f32 : F32Wrapper.t -> i32 option
  val si32_trunc_f32 : F32Wrapper.t -> i32 option
  val wasm_wrap : i64 -> i32
  val cvt_i32 : (sat * sx) option -> v_num -> i32 option
  val i64_impl_rep : i64 -> int64
  val isabelle_int64_to_ocaml_int64 : i64 -> Int64.t
  val f64_convert_u_isabelle_i64 : i64 -> F64Wrapper.t
  val f64_convert_ui64 : i64 -> F64Wrapper.t
  val i32_impl_rep : i32 -> int32
  val isabelle_int32_to_ocaml_int32 : i32 -> Int32.t
  val f64_convert_u_isabelle_i32 : i32 -> F64Wrapper.t
  val f64_convert_ui32 : i32 -> F64Wrapper.t
  val f64_convert_s_isabelle_i64 : i64 -> F64Wrapper.t
  val f64_convert_si64 : i64 -> F64Wrapper.t
  val f64_convert_s_isabelle_i32 : i32 -> F64Wrapper.t
  val f64_convert_si32 : i32 -> F64Wrapper.t
  val cvt_f64 : (sat * sx) option -> v_num -> F64Wrapper.t option
  val f32_convert_u_isabelle_i64 : i64 -> F32Wrapper.t
  val f32_convert_ui64 : i64 -> F32Wrapper.t
  val f32_convert_u_isabelle_i32 : i32 -> F32Wrapper.t
  val f32_convert_ui32 : i32 -> F32Wrapper.t
  val f32_convert_s_isabelle_i64 : i64 -> F32Wrapper.t
  val f32_convert_si64 : i64 -> F32Wrapper.t
  val f32_convert_s_isabelle_i32 : i32 -> F32Wrapper.t
  val f32_convert_si32 : i32 -> F32Wrapper.t
  val cvt_f32 : (sat * sx) option -> v_num -> F32Wrapper.t option
  val cvt : t_num -> (sat * sx) option -> v_num -> v_num option
  val select_return_top : ct list -> ct -> ct -> checker_type
  val to_ct_list : t list -> ct list
  val produce : checker_type -> checker_type -> checker_type
  val ct_compat : ct -> ct -> bool
  val ct_prefix : ct list -> ct list -> bool
  val ct_suffix : ct list -> ct list -> bool
  val consume : checker_type -> ct list -> checker_type
  val type_update : checker_type -> ct list -> checker_type -> checker_type
  val type_update_select : checker_type -> checker_type
  val tp_num_length : tp_num -> nat
  val t_num_length : t_num -> nat
  val is_int_t_num : t_num -> bool
  val load_store_t_bounds : nat -> tp_num option -> t_num -> bool
  val vec_i_length : shape_vec_i -> nat
  val t_vec_length : t_vec -> nat
  val vec_i_num : shape_vec_i -> nat
  val store_vec_t_bounds : storeop_vec -> nat -> bool
  val is_float_t_num : t_num -> bool
  val relop_t_num_agree : relop -> t_num -> bool
  val tp_vec_length : tp_vec -> nat
  val tp_vec_num : tp_vec -> nat
  val load_vec_t_bounds : loadop_vec -> nat -> bool
  val binop_t_num_agree : binop -> t_num -> bool
  val unop_t_num_agree : unop -> t_num -> bool
  val label_update :
    ((t list) list -> (t list) list) -> 'a t_context_ext -> 'a t_context_ext
  val equal_sx : sx -> sx -> bool
  val c_types_agree : checker_type -> t list -> bool
  val option_projl : ('a * 'b) option -> 'a option
  val types_t : 'a t_context_ext -> tf list
  val convert_cond : t_num -> t_num -> (sat * sx) option -> bool
  val vec_f_length : shape_vec_f -> nat
  val vec_length : shape_vec -> nat
  val vec_lane_t : shape_vec -> t_num
  val return : 'a t_context_ext -> (t list) option
  val memory : 'a t_context_ext -> unit limit_t_ext list
  val global : 'a t_context_ext -> unit tg_ext list
  val func_t : 'a t_context_ext -> tf list
  val table : 'a t_context_ext -> unit limit_t_ext list
  val local : 'a t_context_ext -> t list
  val label : 'a t_context_ext -> (t list) list
  val vec_f_num : shape_vec_f -> nat
  val vec_num : shape_vec -> nat
  val tb_tf_t : unit t_context_ext -> tb -> tf option
  val same_lab_h : nat list -> (t list) list -> t list -> (t list) option
  val same_lab : nat list -> (t list) list -> (t list) option
  val is_mut : unit tg_ext -> bool
  val check : unit t_context_ext -> b_e list -> checker_type -> checker_type
  val b_e_type_checker : unit t_context_ext -> b_e list -> tf -> bool
  val check_single : unit t_context_ext -> b_e -> checker_type -> checker_type
  val eq_i_i : 'a equal -> 'a -> 'a -> unit pred
  val fold_map : ('a -> (unit -> 'b)) -> 'a list -> (unit -> ('b list))
  val list_all2 : ('a -> 'b -> bool) -> 'a list -> 'b list -> bool
  val byte_of_nat : nat -> uint8
  val nat_of_byte : uint8 -> nat
  val uminus_word : 'a len -> 'a word -> 'a word
  val uminus_uint8 : uint8 -> uint8
  val negone_byte : uint8
  val m_data : 'a m_ext -> unit module_data_ext list
  val m_elem : 'a m_ext -> unit module_elem_ext list
  val m_mems : 'a m_ext -> unit limit_t_ext list
  val m_tabs : 'a m_ext -> unit limit_t_ext list
  val map_Heap : ('a -> 'b) -> (unit -> 'a) -> (unit -> 'b)
  val load_uint8 : Bytes.t -> nat -> (unit -> uint8)
  val typerep_of : 'a typerep -> 'a -> typerepa
  val name : 'a typerep -> 'a -> string
  val m_funcs : 'a m_ext -> (nat * (t list * b_e list)) list
  val m_globs : 'a m_ext -> unit module_glob_ext list
  val m_start : 'a m_ext -> nat option
  val m_types : 'a m_ext -> tf list
  val load_uint32 : Bytes.t -> nat -> (unit -> int32)
  val load_uint64 : Bytes.t -> nat -> (unit -> int64)
  val store_uint8 : Bytes.t -> nat -> uint8 -> (unit -> unit)
  val bitzero_vec : t_vec -> v_vec
  val bitzero_num : t_num -> v_num
  val bitzero : t -> v
  val n_zeros : t list -> v list
  val const_expr_p : unit t_context_ext -> b_e -> unit pred
  val const_expr : unit t_context_ext -> b_e -> bool
  val store_uint32 : Bytes.t -> nat -> int32 -> (unit -> unit)
  val store_uint64 : Bytes.t -> nat -> int64 -> (unit -> unit)
  val min : 'a ord -> 'a -> 'a -> 'a
  val takefill : 'a -> nat -> 'a list -> 'a list
  val bytes_takefill : uint8 -> nat -> uint8 list -> uint8 list
  val app_unop_i : 'a wasm_int -> unop_i -> 'a -> 'a
  val app_unop_i_v : unop_i -> v_num -> v_num
  val app_unop_f : 'a wasm_float -> unop_f -> 'a -> 'a
  val app_unop_f_v : unop_f -> v_num -> v_num
  val word_rcat_rev : 'a len -> 'b len -> 'a word list -> 'b word
  val deserialise_i64 : uint8 list -> i64
  val deserialise_i32 : uint8 list -> i32
  val isabelle_byte_to_ocaml_char : uint8 -> Char.t
  val f64_deserialise_isabelle_bytes : uint8 list -> F64Wrapper.t
  val deserialise_f64 : uint8 list -> F64Wrapper.t
  val f32_deserialise_isabelle_bytes : uint8 list -> F32Wrapper.t
  val deserialise_f32 : uint8 list -> F32Wrapper.t
  val wasm_deserialise_num : uint8 list -> t_num -> v_num
  val sign_extend : sx -> nat -> uint8 list -> uint8 list
  val bin_rsplit_rev : nat -> nat -> int -> int list
  val word_rsplit_rev : 'a len -> 'b len -> 'a word -> 'b word list
  val serialise_i64 : i64 -> uint8 list
  val serialise_i32 : i32 -> uint8 list
  val ocaml_char_to_isabelle_byte : Char.t -> uint8
  val f64_serialise_isabelle_bytes : F64Wrapper.t -> uint8 list
  val serialise_f64 : F64Wrapper.t -> uint8 list
  val f32_serialise_isabelle_bytes : F32Wrapper.t -> uint8 list
  val serialise_f32 : F32Wrapper.t -> uint8 list
  val bits_num : v_num -> uint8 list
  val app_extend_s : tp_num -> v_num -> v_num
  val app_unop : unop -> v_num -> v_num
  val v128_serialise_isabelle_bytes : V128Wrapper.t -> uint8 list
  val serialise_v128 : V128Wrapper.t -> uint8 list
  val bits_vec : v_vec -> uint8 list
  val m_exports : 'a m_ext -> unit module_export_ext list
  val m_imports : 'a m_ext -> unit module_import_ext list
  val app_binop_i : 'a wasm_int -> binop_i -> 'a -> 'a -> 'a option
  val app_binop_i_v : binop_i -> v_num -> v_num -> v_num option
  val app_binop_f : 'a wasm_float -> binop_f -> 'a -> 'a -> 'a option
  val app_binop_f_v : binop_f -> v_num -> v_num -> v_num option
  val app_binop : binop -> v_num -> v_num -> v_num option
  val app_relop_i : 'a wasm_int -> relop_i -> 'a -> 'a -> bool
  val wasm_bool : bool -> i32
  val app_relop_i_v : relop_i -> v_num -> v_num -> v_num
  val app_relop_f : 'a wasm_float -> relop_f -> 'a -> 'a -> bool
  val app_relop_f_v : relop_f -> v_num -> v_num -> v_num
  val app_relop : relop -> v_num -> v_num -> v_num
  val split_n : v list -> nat -> v list * v list
  val limit_type_checker_p : unit limit_t_ext -> nat -> unit pred
  val limit_typing : unit limit_t_ext -> nat -> bool
  val len_byte_array : Bytes.t -> (unit -> nat)
  val app_testop_i : 'a wasm_int -> testop -> 'a -> bool
  val app_testop : testop -> v_num -> v_num
  val blit_byte_array :
    Bytes.t -> nat -> Bytes.t -> nat -> nat -> (unit -> unit)
  val load_uint8_list : Bytes.t -> nat -> nat -> (unit -> (uint8 list))
  val store_uint8_list : Bytes.t -> nat -> uint8 list -> (unit -> unit)
  val app_test_vec_v : V128Wrapper.testop_vec_t -> V128Wrapper.t -> i32
  val app_test_vec : V128Wrapper.testop_vec_t -> v_vec -> i32
  val app_unop_vec_v : V128Wrapper.unop_vec_t -> V128Wrapper.t -> V128Wrapper.t
  val app_unop_vec : V128Wrapper.unop_vec_t -> v_vec -> v_vec
  val crash_invalid : res_step
  val app_v_s_if :
    tb -> b_e list -> b_e list -> v list -> v list * (e list * res_step)
  val g_val_update : (v -> v) -> 'a global_ext -> 'a global_ext
  val app_binop_vec_v :
    V128Wrapper.binop_vec_t ->
      V128Wrapper.t -> V128Wrapper.t -> V128Wrapper.t option
  val app_binop_vec : V128Wrapper.binop_vec_t -> v_vec -> v_vec -> v_vec option
  val app_shift_vec_v :
    V128Wrapper.shiftop_vec_t -> V128Wrapper.t -> i32 -> V128Wrapper.t
  val app_shift_vec : V128Wrapper.shiftop_vec_t -> v_vec -> i32 -> v_vec
  val v128_deserialise_isabelle_bytes : uint8 list -> V128Wrapper.t
  val deserialise_v128 : uint8 list -> V128Wrapper.t
  val app_splat_vec : shape_vec -> v_num -> v_vec
  val typing : unit t_context_ext -> b_e list -> tf -> bool
  val make_empty_inst_m : (unit -> unit inst_m_ext)
  val globs : 'a s_m_ext -> unit global_ext array
  val funcs : 'a s_m_ext -> cl_m array
  val tabs : 'a s_m_ext -> ((nat option) array * nat option) array
  val mems : 'a s_m_ext -> (Bytes.t * nat option) array
  val globsa : 'a inst_m_ext -> nat array
  val funcsa : 'a inst_m_ext -> nat array
  val tabsa : 'a inst_m_ext -> nat array
  val memsa : 'a inst_m_ext -> nat array
  val export_get_v_ext_m : unit inst_m_ext -> v_ext -> (unit -> v_ext)
  val e_name : 'a module_export_ext -> string
  val e_desc : 'a module_export_ext -> v_ext
  val get_exports_m :
    unit inst_m_ext ->
      unit module_export_ext list -> (unit -> (unit module_export_ext list))
  val list_blit_array : 'a heap -> 'a list -> 'a array -> nat -> (unit -> unit)
  val array_blit_map :
    'b heap ->
      'a list -> ('a -> (unit -> 'b)) -> 'b array -> nat -> (unit -> unit)
  val g_type : 'a module_glob_ext -> unit tg_ext
  val alloc_globs_m :
    unit global_ext array ->
      nat -> unit module_glob_ext list -> v list -> (unit -> unit)
  val alloc_funcs_m :
    cl_m array ->
      nat ->
        (nat * (t list * b_e list)) list ->
          unit inst_m_ext -> tf array -> (unit -> unit)
  val alloc_tabs_m :
    ((nat option) array * nat option) array ->
      nat -> unit limit_t_ext list -> (unit -> unit)
  val new_zeroed_byte_array : nat -> (unit -> Bytes.t)
  val alloc_mems_m :
    (Bytes.t * nat option) array ->
      nat -> unit limit_t_ext list -> (unit -> unit)
  val interp_alloc_module_m :
    unit s_m_ext ->
      unit m_ext ->
        v_ext list ->
          v list ->
            (unit ->
              (unit s_m_ext * (unit inst_m_ext * unit module_export_ext list)))
  val list_all2_m :
    ('a -> 'b -> (unit -> bool)) -> 'a list -> 'b list -> (unit -> bool)
  val e_init : 'a module_elem_ext -> nat list
  val e_tab : 'a module_elem_ext -> nat
  val element_in_bounds_m :
    unit s_m_ext ->
      unit inst_m_ext -> i32 list -> unit module_elem_ext list -> (unit -> bool)
  val cl_m_type : cl_m -> tf
  val tab_typing_m :
    (nat option) array * nat option -> unit limit_t_ext -> (unit -> bool)
  val divide_nat : nat -> nat -> nat
  val mem_typing_m : Bytes.t * nat option -> unit limit_t_ext -> (unit -> bool)
  val external_typing_m : unit s_m_ext -> v_ext -> extern_t -> (unit -> bool)
  val update_redex_return : redex -> v list -> redex
  val update_fc_return_m : frame_context_m -> v list -> frame_context_m
  val store_uint32_of_uint64 : Bytes.t -> nat -> int64 -> (unit -> unit)
  val store_uint16_of_uint64 : Bytes.t -> nat -> int64 -> (unit -> unit)
  val store_uint8_of_uint64 : Bytes.t -> nat -> int64 -> (unit -> unit)
  val store_uint64_packed : Bytes.t -> nat -> int64 -> tp_num -> (unit -> unit)
  val store_uint16_of_uint32 : Bytes.t -> nat -> int32 -> (unit -> unit)
  val store_uint8_of_uint32 : Bytes.t -> nat -> int32 -> (unit -> unit)
  val store_uint32_packed : Bytes.t -> nat -> int32 -> tp_num -> (unit -> unit)
  val store_packed_m_v :
    Bytes.t * nat option ->
      nat -> nat -> v_num -> tp_num -> (unit -> (unit option))
  val store_m_v :
    Bytes.t * nat option -> nat -> nat -> v_num -> (unit -> (unit option))
  val app_s_f_v_s_store_maybe_packed_m :
    t_num ->
      tp_num option ->
        nat ->
          (Bytes.t * nat option) array ->
            unit inst_m_ext -> v list -> (unit -> (v list * res_step))
  val load_uint64_of_uint32 : Bytes.t -> nat -> (unit -> int64)
  val load_uint64_of_uint16 : Bytes.t -> nat -> (unit -> int64)
  val load_uint64_of_sint32 : Bytes.t -> nat -> (unit -> int64)
  val load_uint64_of_sint16 : Bytes.t -> nat -> (unit -> int64)
  val load_uint64_of_uint8 : Bytes.t -> nat -> (unit -> int64)
  val load_uint64_of_sint8 : Bytes.t -> nat -> (unit -> int64)
  val load_uint64_packed : Bytes.t -> nat -> tp_num -> sx -> (unit -> int64)
  val load_uint32_of_uint16 : Bytes.t -> nat -> (unit -> int32)
  val load_uint32_of_sint16 : Bytes.t -> nat -> (unit -> int32)
  val load_uint32_of_uint8 : Bytes.t -> nat -> (unit -> int32)
  val load_uint32_of_sint8 : Bytes.t -> nat -> (unit -> int32)
  val load_uint32_packed : Bytes.t -> nat -> tp_num -> sx -> (unit -> int32)
  val load_packed_m_v :
    Bytes.t * nat option ->
      nat -> nat -> t_num -> tp_num -> sx -> (unit -> (v_num option))
  val load_m_v :
    Bytes.t * nat option -> nat -> nat -> t_num -> (unit -> (v_num option))
  val app_s_f_v_s_load_maybe_packed_m :
    t_num ->
      (tp_num * sx) option ->
        nat ->
          (Bytes.t * nat option) array ->
            unit inst_m_ext -> v list -> (unit -> (v list * res_step))
  val load_bytes_m_v :
    Bytes.t * nat option -> nat -> nat -> nat -> (unit -> ((uint8 list) option))
  val insert_lane_vec_bs : nat -> nat -> uint8 list -> uint8 list -> uint8 list
  val insert_lane_vec :
    shape_vec_i -> nat -> uint8 list -> V128Wrapper.t -> V128Wrapper.t
  val app_s_f_v_s_load_lane_vec_m :
    shape_vec_i ->
      nat ->
        nat ->
          (Bytes.t * nat option) array ->
            unit inst_m_ext -> v list -> (unit -> (v list * res_step))
  val types : 'a inst_m_ext -> tf array
  val app_s_f_v_s_call_indirect_m :
    nat ->
      ((nat option) array * nat option) array ->
        cl_m array ->
          unit inst_m_ext -> v list -> (unit -> (v list * (e list * res_step)))
  val app_s_f_v_s_set_global_m :
    nat ->
      unit global_ext array ->
        unit inst_m_ext -> v list -> (unit -> (v list * res_step))
  val app_s_f_v_s_get_global_m :
    nat ->
      unit global_ext array ->
        unit inst_m_ext -> v list -> (unit -> (v list * res_step))
  val store_serialise_vec : storeop_vec -> V128Wrapper.t -> uint8 list
  val app_s_f_v_s_store_vec_m :
    storeop_vec ->
      nat ->
        (Bytes.t * nat option) array ->
          unit inst_m_ext -> v list -> (unit -> (v list * res_step))
  val app_s_f_v_s_mem_size_m :
    (Bytes.t * nat option) array ->
      unit inst_m_ext -> v list -> (unit -> (v list * res_step))
  val grow_zeroed_byte_array : Bytes.t -> nat -> (unit -> Bytes.t)
  val int32_minus_one : i32
  val app_s_f_v_s_mem_grow_m :
    (Bytes.t * nat option) array ->
      unit inst_m_ext -> v list -> (unit -> (v list * res_step))
  val load_bytes_vec_m_v :
    nat -> nat -> sx -> Bytes.t -> nat -> (unit -> (uint8 list))
  val load_packed_vec_m_v :
    tp_vec ->
      sx -> Bytes.t * nat option ->
              nat -> nat -> (unit -> ((uint8 list) option))
  val load_vec_m_v :
    loadop_vec ->
      Bytes.t * nat option -> nat -> nat -> (unit -> ((uint8 list) option))
  val app_s_f_v_s_load_vec_m :
    loadop_vec ->
      nat ->
        (Bytes.t * nat option) array ->
          unit inst_m_ext -> v list -> (unit -> (v list * res_step))
  val app_f_v_s_set_local_m :
    nat -> v array -> v list -> (unit -> (v list * res_step))
  val app_f_v_s_get_local_m :
    nat -> v array -> v list -> (unit -> (v list * res_step))
  val update_redex_step : redex -> v list -> e list -> redex
  val update_fc_step_m : frame_context_m -> v list -> e list -> frame_context_m
  val app_replace_vec : shape_vec -> nat -> v_vec -> v_num -> v_vec
  val app_v_s_replace_vec : shape_vec -> nat -> v list -> v list * res_step
  val app_extract_vec : shape_vec -> sx -> nat -> v_vec -> v_num
  val app_v_s_extract_vec :
    shape_vec -> sx -> nat -> v list -> v list * res_step
  val app_f_call_m : nat -> unit inst_m_ext -> (unit -> (e list * res_step))
  val app_ternop_vec_v :
    V128Wrapper.ternop_vec_t ->
      V128Wrapper.t -> V128Wrapper.t -> V128Wrapper.t -> V128Wrapper.t
  val app_ternop_vec :
    V128Wrapper.ternop_vec_t -> v_vec -> v_vec -> v_vec -> v_vec
  val app_v_s_ternop_vec :
    V128Wrapper.ternop_vec_t -> v list -> v list * res_step
  val app_v_s_tee_local : nat -> v list -> v list * (e list * res_step)
  val app_v_s_splat_vec : shape_vec -> v list -> v list * res_step
  val app_v_s_shift_vec :
    V128Wrapper.shiftop_vec_t -> v list -> v list * res_step
  val app_v_s_binop_vec : V128Wrapper.binop_vec_t -> v list -> v list * res_step
  val app_v_s_unop_vec : V128Wrapper.unop_vec_t -> v list -> v list * res_step
  val app_v_s_test_vec : V128Wrapper.testop_vec_t -> v list -> v list * res_step
  val app_v_s_br_table :
    nat list -> nat -> v list -> v list * (e list * res_step)
  val crash_invariant : res_step
  val app_v_s_testop : testop -> v list -> v list * res_step
  val app_v_s_select : v list -> v list * res_step
  val tb_tf_m : unit inst_m_ext -> tb -> (unit -> tf)
  val app_v_s_relop : relop -> v list -> v list * res_step
  val wasm_reinterpret : t_num -> v_num -> v_num
  val app_v_s_cvtop :
    cvtop -> t_num -> t_num -> (sat * sx) option -> v list -> v list * res_step
  val app_v_s_br_if : nat -> v list -> v list * (e list * res_step)
  val app_v_s_binop : binop -> v list -> v list * res_step
  val app_v_s_unop : unop -> v list -> v list * res_step
  val app_v_s_drop : v list -> v list * res_step
  val run_step_b_e_m : b_e -> config_m -> (unit -> (config_m * res_step))
  val init_tab_m_v :
    (nat option) array * nat option ->
      nat -> nat list -> (unit -> (unit option))
  val app_s_f_init_tab_m :
    nat ->
      nat list ->
        ((nat option) array * nat option) array ->
          unit inst_m_ext -> (unit -> res_step)
  val init_mem_m_v :
    Bytes.t * nat option -> nat -> uint8 list -> (unit -> (unit option))
  val app_s_f_init_mem_m :
    nat ->
      uint8 list ->
        (Bytes.t * nat option) array -> unit inst_m_ext -> (unit -> res_step)
  val rep_host_m :
    host -> unit s_m_ext * v list -> (unit -> ((unit s_m_ext * v list) option))
  val host_apply_impl_m :
    unit s_m_ext ->
      tf -> host -> v list -> (unit -> ((unit s_m_ext * v list) option))
  val crash_exhaustion : res_step
  val run_step_e_m : e -> config_m -> (unit -> (config_m * res_step))
  val res_crash_fuel : res
  val split_v_s_b_s_aux : v list -> b_e list -> v list * b_e list
  val split_v_s_b_s : b_e list -> v list * b_e list
  val run_iter_m : nat -> config_m -> (unit -> (config_m * res))
  val run_v_m :
    nat ->
      nat ->
        unit s_m_ext * (v array * (unit inst_m_ext * b_e list)) ->
          (unit -> (unit s_m_ext * res))
  val interp_get_v_m :
    unit s_m_ext -> unit inst_m_ext -> b_e list -> (unit -> v)
  val interp_get_i32_m :
    unit s_m_ext -> unit inst_m_ext -> b_e list -> (unit -> i32)
  val d_init : 'a module_data_ext -> uint8 list
  val d_data : 'a module_data_ext -> nat
  val data_in_bounds_m :
    unit s_m_ext ->
      unit inst_m_ext -> i32 list -> unit module_data_ext list -> (unit -> bool)
  val get_init_tab_m :
    unit inst_m_ext -> nat -> unit module_elem_ext -> (unit -> e)
  val get_init_tabs_m :
    unit inst_m_ext ->
      nat list -> unit module_elem_ext list -> (unit -> (e list))
  val get_init_mems_m :
    nat list -> unit module_data_ext list -> (unit -> (e list))
  val module_glob_type_checker :
    unit t_context_ext -> unit module_glob_ext -> bool
  val return_update :
    ((t list) option -> (t list) option) -> 'a t_context_ext -> 'a t_context_ext
  val local_update : (t list -> t list) -> 'a t_context_ext -> 'a t_context_ext
  val module_func_type_checker :
    unit t_context_ext -> nat * (t list * b_e list) -> bool
  val module_elem_type_checker :
    unit t_context_ext -> unit module_elem_ext -> bool
  val module_data_type_checker :
    unit t_context_ext -> unit module_data_ext -> bool
  val module_import_typer : tf list -> imp_desc -> extern_t option
  val module_export_typer : unit t_context_ext -> v_ext -> extern_t option
  val gather_m_f_type : tf list -> nat * (t list * b_e list) -> tf option
  val i_desc : 'a module_import_ext -> imp_desc
  val module_start_type_checker_p : unit t_context_ext -> nat -> unit pred
  val module_start_typing : unit t_context_ext -> nat -> bool
  val module_type_checker : unit m_ext -> (extern_t list * extern_t list) option
  val get_start_m : unit inst_m_ext -> nat option -> (unit -> (e list))
  val g_init : 'a module_glob_ext -> b_e list
  val e_off : 'a module_elem_ext -> b_e list
  val d_off : 'a module_data_ext -> b_e list
  val interp_instantiate_m :
    unit s_m_ext ->
      unit m_ext -> v_ext list -> (unit -> (unit s_m_ext * res_inst_m))
  val run_instantiate_m :
    nat ->
      nat ->
        unit s_m_ext * (unit inst_m_ext * e list) ->
          (unit -> (unit s_m_ext * res))
  val interp_instantiate_init_m :
    unit s_m_ext ->
      unit m_ext -> v_ext list -> (unit -> (unit s_m_ext * res_inst_m))
  val make_empty_frame_m : 'a heap -> (unit -> ('a array * unit inst_m_ext))
  val run_invoke_v_m :
    nat ->
      nat -> unit s_m_ext * (v list * nat) -> (unit -> (unit s_m_ext * res))
  val run_fuzz :
    nat ->
      nat ->
        unit s_m_ext ->
          unit m_ext ->
            v_ext list -> (v list) option -> (unit -> (unit s_m_ext * res))
  val run_m :
    unit s_m_ext * (v array * (unit inst_m_ext * b_e list)) ->
      (unit -> (unit s_m_ext * res))
  val make_empty_store_m : (unit -> unit s_m_ext)
  val run_invoke_m :
    unit s_m_ext * (v list * nat) -> (unit -> (unit s_m_ext * res))
end = struct

type int = Int_of_integer of Z.t;;

let rec integer_of_int (Int_of_integer k) = k;;

let rec equal_inta k l = Z.equal (integer_of_int k) (integer_of_int l);;

type 'a equal = {equal : 'a -> 'a -> bool};;
let equal _A = _A.equal;;

let equal_int = ({equal = equal_inta} : int equal);;

let rec times_inta
  k l = Int_of_integer (Z.mul (integer_of_int k) (integer_of_int l));;

type 'a times = {times : 'a -> 'a -> 'a};;
let times _A = _A.times;;

type 'a dvd = {times_dvd : 'a times};;

let times_int = ({times = times_inta} : int times);;

let dvd_int = ({times_dvd = times_int} : int dvd);;

type num = One | Bit0 of num | Bit1 of num;;

let one_inta : int = Int_of_integer (Z.of_int 1);;

type 'a one = {one : 'a};;
let one _A = _A.one;;

let one_int = ({one = one_inta} : int one);;

let rec uminus_inta k = Int_of_integer (Z.neg (integer_of_int k));;

let rec minus_inta
  k l = Int_of_integer (Z.sub (integer_of_int k) (integer_of_int l));;

let zero_inta : int = Int_of_integer Z.zero;;

let rec plus_inta
  k l = Int_of_integer (Z.add (integer_of_int k) (integer_of_int l));;

type 'a uminus = {uminus : 'a -> 'a};;
let uminus _A = _A.uminus;;

type 'a minus = {minus : 'a -> 'a -> 'a};;
let minus _A = _A.minus;;

type 'a zero = {zero : 'a};;
let zero _A = _A.zero;;

type 'a plus = {plus : 'a -> 'a -> 'a};;
let plus _A = _A.plus;;

type 'a semigroup_add = {plus_semigroup_add : 'a plus};;

type 'a cancel_semigroup_add =
  {semigroup_add_cancel_semigroup_add : 'a semigroup_add};;

type 'a ab_semigroup_add = {semigroup_add_ab_semigroup_add : 'a semigroup_add};;

type 'a cancel_ab_semigroup_add =
  {ab_semigroup_add_cancel_ab_semigroup_add : 'a ab_semigroup_add;
    cancel_semigroup_add_cancel_ab_semigroup_add : 'a cancel_semigroup_add;
    minus_cancel_ab_semigroup_add : 'a minus};;

type 'a monoid_add =
  {semigroup_add_monoid_add : 'a semigroup_add; zero_monoid_add : 'a zero};;

type 'a comm_monoid_add =
  {ab_semigroup_add_comm_monoid_add : 'a ab_semigroup_add;
    monoid_add_comm_monoid_add : 'a monoid_add};;

type 'a cancel_comm_monoid_add =
  {cancel_ab_semigroup_add_cancel_comm_monoid_add : 'a cancel_ab_semigroup_add;
    comm_monoid_add_cancel_comm_monoid_add : 'a comm_monoid_add};;

type 'a mult_zero = {times_mult_zero : 'a times; zero_mult_zero : 'a zero};;

type 'a semigroup_mult = {times_semigroup_mult : 'a times};;

type 'a semiring =
  {ab_semigroup_add_semiring : 'a ab_semigroup_add;
    semigroup_mult_semiring : 'a semigroup_mult};;

type 'a semiring_0 =
  {comm_monoid_add_semiring_0 : 'a comm_monoid_add;
    mult_zero_semiring_0 : 'a mult_zero; semiring_semiring_0 : 'a semiring};;

type 'a semiring_0_cancel =
  {cancel_comm_monoid_add_semiring_0_cancel : 'a cancel_comm_monoid_add;
    semiring_0_semiring_0_cancel : 'a semiring_0};;

type 'a group_add =
  {cancel_semigroup_add_group_add : 'a cancel_semigroup_add;
    minus_group_add : 'a minus; monoid_add_group_add : 'a monoid_add;
    uminus_group_add : 'a uminus};;

type 'a ab_group_add =
  {cancel_comm_monoid_add_ab_group_add : 'a cancel_comm_monoid_add;
    group_add_ab_group_add : 'a group_add};;

type 'a ring =
  {ab_group_add_ring : 'a ab_group_add;
    semiring_0_cancel_ring : 'a semiring_0_cancel};;

let plus_int = ({plus = plus_inta} : int plus);;

let semigroup_add_int = ({plus_semigroup_add = plus_int} : int semigroup_add);;

let cancel_semigroup_add_int =
  ({semigroup_add_cancel_semigroup_add = semigroup_add_int} :
    int cancel_semigroup_add);;

let ab_semigroup_add_int =
  ({semigroup_add_ab_semigroup_add = semigroup_add_int} :
    int ab_semigroup_add);;

let minus_int = ({minus = minus_inta} : int minus);;

let cancel_ab_semigroup_add_int =
  ({ab_semigroup_add_cancel_ab_semigroup_add = ab_semigroup_add_int;
     cancel_semigroup_add_cancel_ab_semigroup_add = cancel_semigroup_add_int;
     minus_cancel_ab_semigroup_add = minus_int}
    : int cancel_ab_semigroup_add);;

let zero_int = ({zero = zero_inta} : int zero);;

let monoid_add_int =
  ({semigroup_add_monoid_add = semigroup_add_int; zero_monoid_add = zero_int} :
    int monoid_add);;

let comm_monoid_add_int =
  ({ab_semigroup_add_comm_monoid_add = ab_semigroup_add_int;
     monoid_add_comm_monoid_add = monoid_add_int}
    : int comm_monoid_add);;

let cancel_comm_monoid_add_int =
  ({cancel_ab_semigroup_add_cancel_comm_monoid_add =
      cancel_ab_semigroup_add_int;
     comm_monoid_add_cancel_comm_monoid_add = comm_monoid_add_int}
    : int cancel_comm_monoid_add);;

let mult_zero_int =
  ({times_mult_zero = times_int; zero_mult_zero = zero_int} : int mult_zero);;

let semigroup_mult_int =
  ({times_semigroup_mult = times_int} : int semigroup_mult);;

let semiring_int =
  ({ab_semigroup_add_semiring = ab_semigroup_add_int;
     semigroup_mult_semiring = semigroup_mult_int}
    : int semiring);;

let semiring_0_int =
  ({comm_monoid_add_semiring_0 = comm_monoid_add_int;
     mult_zero_semiring_0 = mult_zero_int; semiring_semiring_0 = semiring_int}
    : int semiring_0);;

let semiring_0_cancel_int =
  ({cancel_comm_monoid_add_semiring_0_cancel = cancel_comm_monoid_add_int;
     semiring_0_semiring_0_cancel = semiring_0_int}
    : int semiring_0_cancel);;

let uminus_int = ({uminus = uminus_inta} : int uminus);;

let group_add_int =
  ({cancel_semigroup_add_group_add = cancel_semigroup_add_int;
     minus_group_add = minus_int; monoid_add_group_add = monoid_add_int;
     uminus_group_add = uminus_int}
    : int group_add);;

let ab_group_add_int =
  ({cancel_comm_monoid_add_ab_group_add = cancel_comm_monoid_add_int;
     group_add_ab_group_add = group_add_int}
    : int ab_group_add);;

let ring_int =
  ({ab_group_add_ring = ab_group_add_int;
     semiring_0_cancel_ring = semiring_0_cancel_int}
    : int ring);;

type 'a numeral =
  {one_numeral : 'a one; semigroup_add_numeral : 'a semigroup_add};;

let numeral_int =
  ({one_numeral = one_int; semigroup_add_numeral = semigroup_add_int} :
    int numeral);;

type 'a power = {one_power : 'a one; times_power : 'a times};;

let power_int = ({one_power = one_int; times_power = times_int} : int power);;

let rec apsnd f (x, y) = (x, f y);;

let rec divmod_integer
  k l = (if Z.equal k Z.zero then (Z.zero, Z.zero)
          else (if Z.lt Z.zero l
                 then (if Z.lt Z.zero k
                        then (fun k l -> if Z.equal Z.zero l then
                               (Z.zero, l) else Z.div_rem (Z.abs k) (Z.abs l))
                               k l
                        else (let (r, s) =
                                (fun k l -> if Z.equal Z.zero l then
                                  (Z.zero, l) else Z.div_rem (Z.abs k)
                                  (Z.abs l))
                                  k l
                                in
                               (if Z.equal s Z.zero then (Z.neg r, Z.zero)
                                 else (Z.sub (Z.neg r) (Z.of_int 1),
Z.sub l s))))
                 else (if Z.equal l Z.zero then (Z.zero, k)
                        else apsnd Z.neg
                               (if Z.lt k Z.zero
                                 then (fun k l -> if Z.equal Z.zero l then
(Z.zero, l) else Z.div_rem (Z.abs k) (Z.abs l))
k l
                                 else (let (r, s) =
 (fun k l -> if Z.equal Z.zero l then (Z.zero, l) else Z.div_rem (Z.abs k)
   (Z.abs l))
   k l
 in
(if Z.equal s Z.zero then (Z.neg r, Z.zero)
  else (Z.sub (Z.neg r) (Z.of_int 1), Z.sub (Z.neg l) s)))))));;

let rec fst (x1, x2) = x1;;

let rec divide_integer k l = fst (divmod_integer k l);;

let rec divide_inta
  k l = Int_of_integer (divide_integer (integer_of_int k) (integer_of_int l));;

type 'a divide = {divide : 'a -> 'a -> 'a};;
let divide _A = _A.divide;;

let divide_int = ({divide = divide_inta} : int divide);;

let rec snd (x1, x2) = x2;;

let rec modulo_integer k l = snd (divmod_integer k l);;

let rec modulo_inta
  k l = Int_of_integer (modulo_integer (integer_of_int k) (integer_of_int l));;

type 'a modulo =
  {divide_modulo : 'a divide; dvd_modulo : 'a dvd; modulo : 'a -> 'a -> 'a};;
let modulo _A = _A.modulo;;

let modulo_int =
  ({divide_modulo = divide_int; dvd_modulo = dvd_int; modulo = modulo_inta} :
    int modulo);;

type 'a monoid_mult =
  {semigroup_mult_monoid_mult : 'a semigroup_mult;
    power_monoid_mult : 'a power};;

type 'a semiring_numeral =
  {monoid_mult_semiring_numeral : 'a monoid_mult;
    numeral_semiring_numeral : 'a numeral;
    semiring_semiring_numeral : 'a semiring};;

type 'a zero_neq_one =
  {one_zero_neq_one : 'a one; zero_zero_neq_one : 'a zero};;

type 'a semiring_1 =
  {semiring_numeral_semiring_1 : 'a semiring_numeral;
    semiring_0_semiring_1 : 'a semiring_0;
    zero_neq_one_semiring_1 : 'a zero_neq_one};;

type 'a semiring_1_cancel =
  {semiring_0_cancel_semiring_1_cancel : 'a semiring_0_cancel;
    semiring_1_semiring_1_cancel : 'a semiring_1};;

type 'a neg_numeral =
  {group_add_neg_numeral : 'a group_add; numeral_neg_numeral : 'a numeral};;

type 'a ring_1 =
  {neg_numeral_ring_1 : 'a neg_numeral; ring_ring_1 : 'a ring;
    semiring_1_cancel_ring_1 : 'a semiring_1_cancel};;

let monoid_mult_int =
  ({semigroup_mult_monoid_mult = semigroup_mult_int;
     power_monoid_mult = power_int}
    : int monoid_mult);;

let semiring_numeral_int =
  ({monoid_mult_semiring_numeral = monoid_mult_int;
     numeral_semiring_numeral = numeral_int;
     semiring_semiring_numeral = semiring_int}
    : int semiring_numeral);;

let zero_neq_one_int =
  ({one_zero_neq_one = one_int; zero_zero_neq_one = zero_int} :
    int zero_neq_one);;

let semiring_1_int =
  ({semiring_numeral_semiring_1 = semiring_numeral_int;
     semiring_0_semiring_1 = semiring_0_int;
     zero_neq_one_semiring_1 = zero_neq_one_int}
    : int semiring_1);;

let semiring_1_cancel_int =
  ({semiring_0_cancel_semiring_1_cancel = semiring_0_cancel_int;
     semiring_1_semiring_1_cancel = semiring_1_int}
    : int semiring_1_cancel);;

let neg_numeral_int =
  ({group_add_neg_numeral = group_add_int; numeral_neg_numeral = numeral_int} :
    int neg_numeral);;

let ring_1_int =
  ({neg_numeral_ring_1 = neg_numeral_int; ring_ring_1 = ring_int;
     semiring_1_cancel_ring_1 = semiring_1_cancel_int}
    : int ring_1);;

type 'a semiring_no_zero_divisors =
  {semiring_0_semiring_no_zero_divisors : 'a semiring_0};;

type 'a semiring_1_no_zero_divisors =
  {semiring_1_semiring_1_no_zero_divisors : 'a semiring_1;
    semiring_no_zero_divisors_semiring_1_no_zero_divisors :
      'a semiring_no_zero_divisors};;

type 'a ab_semigroup_mult =
  {semigroup_mult_ab_semigroup_mult : 'a semigroup_mult};;

type 'a comm_semiring =
  {ab_semigroup_mult_comm_semiring : 'a ab_semigroup_mult;
    semiring_comm_semiring : 'a semiring};;

type 'a comm_semiring_0 =
  {comm_semiring_comm_semiring_0 : 'a comm_semiring;
    semiring_0_comm_semiring_0 : 'a semiring_0};;

type 'a comm_semiring_0_cancel =
  {comm_semiring_0_comm_semiring_0_cancel : 'a comm_semiring_0;
    semiring_0_cancel_comm_semiring_0_cancel : 'a semiring_0_cancel};;

type 'a comm_monoid_mult =
  {ab_semigroup_mult_comm_monoid_mult : 'a ab_semigroup_mult;
    monoid_mult_comm_monoid_mult : 'a monoid_mult;
    dvd_comm_monoid_mult : 'a dvd};;

type 'a comm_semiring_1 =
  {comm_monoid_mult_comm_semiring_1 : 'a comm_monoid_mult;
    comm_semiring_0_comm_semiring_1 : 'a comm_semiring_0;
    semiring_1_comm_semiring_1 : 'a semiring_1};;

type 'a comm_semiring_1_cancel =
  {comm_semiring_0_cancel_comm_semiring_1_cancel : 'a comm_semiring_0_cancel;
    comm_semiring_1_comm_semiring_1_cancel : 'a comm_semiring_1;
    semiring_1_cancel_comm_semiring_1_cancel : 'a semiring_1_cancel};;

type 'a semidom =
  {comm_semiring_1_cancel_semidom : 'a comm_semiring_1_cancel;
    semiring_1_no_zero_divisors_semidom : 'a semiring_1_no_zero_divisors};;

let semiring_no_zero_divisors_int =
  ({semiring_0_semiring_no_zero_divisors = semiring_0_int} :
    int semiring_no_zero_divisors);;

let semiring_1_no_zero_divisors_int =
  ({semiring_1_semiring_1_no_zero_divisors = semiring_1_int;
     semiring_no_zero_divisors_semiring_1_no_zero_divisors =
       semiring_no_zero_divisors_int}
    : int semiring_1_no_zero_divisors);;

let ab_semigroup_mult_int =
  ({semigroup_mult_ab_semigroup_mult = semigroup_mult_int} :
    int ab_semigroup_mult);;

let comm_semiring_int =
  ({ab_semigroup_mult_comm_semiring = ab_semigroup_mult_int;
     semiring_comm_semiring = semiring_int}
    : int comm_semiring);;

let comm_semiring_0_int =
  ({comm_semiring_comm_semiring_0 = comm_semiring_int;
     semiring_0_comm_semiring_0 = semiring_0_int}
    : int comm_semiring_0);;

let comm_semiring_0_cancel_int =
  ({comm_semiring_0_comm_semiring_0_cancel = comm_semiring_0_int;
     semiring_0_cancel_comm_semiring_0_cancel = semiring_0_cancel_int}
    : int comm_semiring_0_cancel);;

let comm_monoid_mult_int =
  ({ab_semigroup_mult_comm_monoid_mult = ab_semigroup_mult_int;
     monoid_mult_comm_monoid_mult = monoid_mult_int;
     dvd_comm_monoid_mult = dvd_int}
    : int comm_monoid_mult);;

let comm_semiring_1_int =
  ({comm_monoid_mult_comm_semiring_1 = comm_monoid_mult_int;
     comm_semiring_0_comm_semiring_1 = comm_semiring_0_int;
     semiring_1_comm_semiring_1 = semiring_1_int}
    : int comm_semiring_1);;

let comm_semiring_1_cancel_int =
  ({comm_semiring_0_cancel_comm_semiring_1_cancel = comm_semiring_0_cancel_int;
     comm_semiring_1_comm_semiring_1_cancel = comm_semiring_1_int;
     semiring_1_cancel_comm_semiring_1_cancel = semiring_1_cancel_int}
    : int comm_semiring_1_cancel);;

let semidom_int =
  ({comm_semiring_1_cancel_semidom = comm_semiring_1_cancel_int;
     semiring_1_no_zero_divisors_semidom = semiring_1_no_zero_divisors_int}
    : int semidom);;

type 'a comm_ring =
  {comm_semiring_0_cancel_comm_ring : 'a comm_semiring_0_cancel;
    ring_comm_ring : 'a ring};;

let comm_ring_int =
  ({comm_semiring_0_cancel_comm_ring = comm_semiring_0_cancel_int;
     ring_comm_ring = ring_int}
    : int comm_ring);;

type 'a comm_ring_1 =
  {comm_ring_comm_ring_1 : 'a comm_ring;
    comm_semiring_1_cancel_comm_ring_1 : 'a comm_semiring_1_cancel;
    ring_1_comm_ring_1 : 'a ring_1};;

let comm_ring_1_int =
  ({comm_ring_comm_ring_1 = comm_ring_int;
     comm_semiring_1_cancel_comm_ring_1 = comm_semiring_1_cancel_int;
     ring_1_comm_ring_1 = ring_1_int}
    : int comm_ring_1);;

type 'a semiring_modulo =
  {comm_semiring_1_cancel_semiring_modulo : 'a comm_semiring_1_cancel;
    modulo_semiring_modulo : 'a modulo};;

type 'a semiring_parity =
  {semiring_modulo_semiring_parity : 'a semiring_modulo};;

type 'a ring_parity =
  {semiring_parity_ring_parity : 'a semiring_parity;
    comm_ring_1_ring_parity : 'a comm_ring_1};;

let semiring_modulo_int =
  ({comm_semiring_1_cancel_semiring_modulo = comm_semiring_1_cancel_int;
     modulo_semiring_modulo = modulo_int}
    : int semiring_modulo);;

let semiring_parity_int =
  ({semiring_modulo_semiring_parity = semiring_modulo_int} :
    int semiring_parity);;

let ring_parity_int =
  ({semiring_parity_ring_parity = semiring_parity_int;
     comm_ring_1_ring_parity = comm_ring_1_int}
    : int ring_parity);;

type nat = Nat of Z.t;;

let rec integer_of_nat (Nat x) = x;;

let rec bit_integer x n = Bits_Integer.test_bit x (integer_of_nat n);;

let rec bit_int (Int_of_integer x) n = bit_integer x n;;

type 'a semiring_bits =
  {semiring_parity_semiring_bits : 'a semiring_parity;
    bit : 'a -> nat -> bool};;
let bit _A = _A.bit;;

let semiring_bits_int =
  ({semiring_parity_semiring_bits = semiring_parity_int; bit = bit_int} :
    int semiring_bits);;

type 'a semiring_no_zero_divisors_cancel =
  {semiring_no_zero_divisors_semiring_no_zero_divisors_cancel :
     'a semiring_no_zero_divisors};;

type 'a semidom_divide =
  {divide_semidom_divide : 'a divide; semidom_semidom_divide : 'a semidom;
    semiring_no_zero_divisors_cancel_semidom_divide :
      'a semiring_no_zero_divisors_cancel};;

let semiring_no_zero_divisors_cancel_int =
  ({semiring_no_zero_divisors_semiring_no_zero_divisors_cancel =
      semiring_no_zero_divisors_int}
    : int semiring_no_zero_divisors_cancel);;

let semidom_divide_int =
  ({divide_semidom_divide = divide_int; semidom_semidom_divide = semidom_int;
     semiring_no_zero_divisors_cancel_semidom_divide =
       semiring_no_zero_divisors_cancel_int}
    : int semidom_divide);;

type 'a algebraic_semidom =
  {semidom_divide_algebraic_semidom : 'a semidom_divide};;

type 'a semidom_modulo =
  {algebraic_semidom_semidom_modulo : 'a algebraic_semidom;
    semiring_modulo_semidom_modulo : 'a semiring_modulo};;

let algebraic_semidom_int =
  ({semidom_divide_algebraic_semidom = semidom_divide_int} :
    int algebraic_semidom);;

let semidom_modulo_int =
  ({algebraic_semidom_semidom_modulo = algebraic_semidom_int;
     semiring_modulo_semidom_modulo = semiring_modulo_int}
    : int semidom_modulo);;

type 'a ord = {less_eq : 'a -> 'a -> bool; less : 'a -> 'a -> bool};;
let less_eq _A = _A.less_eq;;
let less _A = _A.less;;

let rec max _A a b = (if less_eq _A a b then b else a);;

let ord_integer = ({less_eq = Z.leq; less = Z.lt} : Z.t ord);;

let rec minus_nat
  m n = Nat (max ord_integer Z.zero
              (Z.sub (integer_of_nat m) (integer_of_nat n)));;

let rec equal_nat m n = Z.equal (integer_of_nat m) (integer_of_nat n);;

let zero_nat : nat = Nat Z.zero;;

let one_nata : nat = Nat (Z.of_int 1);;

let rec power _A
  a n = (if equal_nat n zero_nat then one _A.one_power
          else times _A.times_power a (power _A a (minus_nat n one_nata)));;

let one_integera : Z.t = (Z.of_int 1);;

let times_integer = ({times = Z.mul} : Z.t times);;

let one_integer = ({one = one_integera} : Z.t one);;

let power_integer =
  ({one_power = one_integer; times_power = times_integer} : Z.t power);;

let rec take_bit_integer
  n k = modulo_integer k (power power_integer (Z.of_int 2) n);;

let rec take_bit_int
  n (Int_of_integer x) = Int_of_integer (take_bit_integer n x);;

let rec push_bit_integer n x = Bits_Integer.shiftl x (integer_of_nat n);;

let rec push_bit_int
  n (Int_of_integer x) = Int_of_integer (push_bit_integer n x);;

let rec drop_bit_integer n x = Bits_Integer.shiftr x (integer_of_nat n);;

let rec drop_bit_int
  n (Int_of_integer x) = Int_of_integer (drop_bit_integer n x);;

type 'a semiring_bit_shifts =
  {semiring_bits_semiring_bit_shifts : 'a semiring_bits;
    push_bit : nat -> 'a -> 'a; drop_bit : nat -> 'a -> 'a;
    take_bit : nat -> 'a -> 'a};;
let push_bit _A = _A.push_bit;;
let drop_bit _A = _A.drop_bit;;
let take_bit _A = _A.take_bit;;

let semiring_bit_shifts =
  ({semiring_bits_semiring_bit_shifts = semiring_bits_int;
     push_bit = push_bit_int; drop_bit = drop_bit_int; take_bit = take_bit_int}
    : int semiring_bit_shifts);;

let rec mask_int
  n = minus_inta (power power_int (Int_of_integer (Z.of_int 2)) n) one_inta;;

let rec xor_int
  (Int_of_integer i) (Int_of_integer j) = Int_of_integer (Z.logxor i j);;

let rec and_int
  (Int_of_integer i) (Int_of_integer j) = Int_of_integer (Z.logand i j);;

let rec or_int
  (Int_of_integer i) (Int_of_integer j) = Int_of_integer (Z.logor i j);;

let rec not_int (Int_of_integer i) = Int_of_integer (Z.lognot i);;

type 'a semiring_bit_operations =
  {semiring_bit_shifts_semiring_bit_operations : 'a semiring_bit_shifts;
    anda : 'a -> 'a -> 'a; ora : 'a -> 'a -> 'a; xor : 'a -> 'a -> 'a;
    mask : nat -> 'a};;
let anda _A = _A.anda;;
let ora _A = _A.ora;;
let xor _A = _A.xor;;
let mask _A = _A.mask;;

type 'a ring_bit_operations =
  {semiring_bit_operations_ring_bit_operations : 'a semiring_bit_operations;
    ring_parity_ring_bit_operations : 'a ring_parity; nota : 'a -> 'a};;
let nota _A = _A.nota;;

let semiring_bit_operations_int =
  ({semiring_bit_shifts_semiring_bit_operations = semiring_bit_shifts;
     anda = and_int; ora = or_int; xor = xor_int; mask = mask_int}
    : int semiring_bit_operations);;

let ring_bit_operations_int =
  ({semiring_bit_operations_ring_bit_operations = semiring_bit_operations_int;
     ring_parity_ring_bit_operations = ring_parity_int; nota = not_int}
    : int ring_bit_operations);;

type typerepa = Typerep of string * typerepa list;;

type 'a itself = Type;;

let rec typerep_nata t = Typerep ("Nat.nat", []);;

type 'a typerep = {typerep : 'a itself -> typerepa};;
let typerep _A = _A.typerep;;

type 'a countable = unit;;

type 'a heap = {countable_heap : 'a countable; typerep_heap : 'a typerep};;

let countable_nat = (() : nat countable);;

let typerep_nat = ({typerep = typerep_nata} : nat typerep);;

let heap_nat =
  ({countable_heap = countable_nat; typerep_heap = typerep_nat} : nat heap);;

let one_nat = ({one = one_nata} : nat one);;

let rec times_nata m n = Nat (Z.mul (integer_of_nat m) (integer_of_nat n));;

let times_nat = ({times = times_nata} : nat times);;

let power_nat = ({one_power = one_nat; times_power = times_nat} : nat power);;

let rec less_eq_nat m n = Z.leq (integer_of_nat m) (integer_of_nat n);;

let rec less_nat m n = Z.lt (integer_of_nat m) (integer_of_nat n);;

let ord_nat = ({less_eq = less_eq_nat; less = less_nat} : nat ord);;

type 'a len0 = {len_of : 'a itself -> nat};;
let len_of _A = _A.len_of;;

type 'a len = {len0_len : 'a len0};;

type 'a word = Word of int;;

let rec the_int _A (Word x) = x;;

let rec of_int _A k = Word (take_bit_int (len_of _A.len0_len Type) k);;

let rec times_worda _A
  a b = of_int _A (times_inta (the_int _A a) (the_int _A b));;

let rec times_word _A = ({times = times_worda _A} : 'a word times);;

let rec dvd_word _A = ({times_dvd = (times_word _A)} : 'a word dvd);;

let rec one_worda _A = Word one_inta;;

let rec one_word _A = ({one = one_worda _A} : 'a word one);;

let rec plus_worda _A
  a b = of_int _A (plus_inta (the_int _A a) (the_int _A b));;

let rec plus_word _A = ({plus = plus_worda _A} : 'a word plus);;

let rec zero_worda _A = Word zero_inta;;

let rec zero_word _A = ({zero = zero_worda _A} : 'a word zero);;

let rec semigroup_add_word _A =
  ({plus_semigroup_add = (plus_word _A)} : 'a word semigroup_add);;

let rec numeral_word _A =
  ({one_numeral = (one_word _A);
     semigroup_add_numeral = (semigroup_add_word _A)}
    : 'a word numeral);;

let rec power_word _A =
  ({one_power = (one_word _A); times_power = (times_word _A)} : 'a word power);;

let rec minus_worda _A
  a b = of_int _A (minus_inta (the_int _A a) (the_int _A b));;

let rec minus_word _A = ({minus = minus_worda _A} : 'a word minus);;

let rec divide_worda _A
  a b = of_int _A (divide_inta (the_int _A a) (the_int _A b));;

let rec divide_word _A = ({divide = divide_worda _A} : 'a word divide);;

let rec modulo_worda _A
  a b = of_int _A (modulo_inta (the_int _A a) (the_int _A b));;

let rec modulo_word _A =
  ({divide_modulo = (divide_word _A); dvd_modulo = (dvd_word _A);
     modulo = modulo_worda _A}
    : 'a word modulo);;

let rec ab_semigroup_add_word _A =
  ({semigroup_add_ab_semigroup_add = (semigroup_add_word _A)} :
    'a word ab_semigroup_add);;

let rec semigroup_mult_word _A =
  ({times_semigroup_mult = (times_word _A)} : 'a word semigroup_mult);;

let rec semiring_word _A =
  ({ab_semigroup_add_semiring = (ab_semigroup_add_word _A);
     semigroup_mult_semiring = (semigroup_mult_word _A)}
    : 'a word semiring);;

let rec mult_zero_word _A =
  ({times_mult_zero = (times_word _A); zero_mult_zero = (zero_word _A)} :
    'a word mult_zero);;

let rec monoid_add_word _A =
  ({semigroup_add_monoid_add = (semigroup_add_word _A);
     zero_monoid_add = (zero_word _A)}
    : 'a word monoid_add);;

let rec comm_monoid_add_word _A =
  ({ab_semigroup_add_comm_monoid_add = (ab_semigroup_add_word _A);
     monoid_add_comm_monoid_add = (monoid_add_word _A)}
    : 'a word comm_monoid_add);;

let rec semiring_0_word _A =
  ({comm_monoid_add_semiring_0 = (comm_monoid_add_word _A);
     mult_zero_semiring_0 = (mult_zero_word _A);
     semiring_semiring_0 = (semiring_word _A)}
    : 'a word semiring_0);;

let rec monoid_mult_word _A =
  ({semigroup_mult_monoid_mult = (semigroup_mult_word _A);
     power_monoid_mult = (power_word _A)}
    : 'a word monoid_mult);;

let rec semiring_numeral_word _A =
  ({monoid_mult_semiring_numeral = (monoid_mult_word _A);
     numeral_semiring_numeral = (numeral_word _A);
     semiring_semiring_numeral = (semiring_word _A)}
    : 'a word semiring_numeral);;

let rec zero_neq_one_word _A =
  ({one_zero_neq_one = (one_word _A); zero_zero_neq_one = (zero_word _A)} :
    'a word zero_neq_one);;

let rec semiring_1_word _A =
  ({semiring_numeral_semiring_1 = (semiring_numeral_word _A);
     semiring_0_semiring_1 = (semiring_0_word _A);
     zero_neq_one_semiring_1 = (zero_neq_one_word _A)}
    : 'a word semiring_1);;

let rec ab_semigroup_mult_word _A =
  ({semigroup_mult_ab_semigroup_mult = (semigroup_mult_word _A)} :
    'a word ab_semigroup_mult);;

let rec comm_semiring_word _A =
  ({ab_semigroup_mult_comm_semiring = (ab_semigroup_mult_word _A);
     semiring_comm_semiring = (semiring_word _A)}
    : 'a word comm_semiring);;

let rec drop_bit_word _A n w = Word (drop_bit_int n (the_int _A w));;

let rec and_word _A v w = Word (and_int (the_int _A v) (the_int _A w));;

let rec equal_word _A v w = equal_inta (the_int _A v) (the_int _A w);;

let rec bit_word _A
  a n = equal_word _A (and_word _A (drop_bit_word _A n a) (one_worda _A))
          (one_worda _A);;

let rec cancel_semigroup_add_word _A =
  ({semigroup_add_cancel_semigroup_add = (semigroup_add_word _A)} :
    'a word cancel_semigroup_add);;

let rec cancel_ab_semigroup_add_word _A =
  ({ab_semigroup_add_cancel_ab_semigroup_add = (ab_semigroup_add_word _A);
     cancel_semigroup_add_cancel_ab_semigroup_add =
       (cancel_semigroup_add_word _A);
     minus_cancel_ab_semigroup_add = (minus_word _A)}
    : 'a word cancel_ab_semigroup_add);;

let rec cancel_comm_monoid_add_word _A =
  ({cancel_ab_semigroup_add_cancel_comm_monoid_add =
      (cancel_ab_semigroup_add_word _A);
     comm_monoid_add_cancel_comm_monoid_add = (comm_monoid_add_word _A)}
    : 'a word cancel_comm_monoid_add);;

let rec semiring_0_cancel_word _A =
  ({cancel_comm_monoid_add_semiring_0_cancel = (cancel_comm_monoid_add_word _A);
     semiring_0_semiring_0_cancel = (semiring_0_word _A)}
    : 'a word semiring_0_cancel);;

let rec comm_semiring_0_word _A =
  ({comm_semiring_comm_semiring_0 = (comm_semiring_word _A);
     semiring_0_comm_semiring_0 = (semiring_0_word _A)}
    : 'a word comm_semiring_0);;

let rec comm_semiring_0_cancel_word _A =
  ({comm_semiring_0_comm_semiring_0_cancel = (comm_semiring_0_word _A);
     semiring_0_cancel_comm_semiring_0_cancel = (semiring_0_cancel_word _A)}
    : 'a word comm_semiring_0_cancel);;

let rec semiring_1_cancel_word _A =
  ({semiring_0_cancel_semiring_1_cancel = (semiring_0_cancel_word _A);
     semiring_1_semiring_1_cancel = (semiring_1_word _A)}
    : 'a word semiring_1_cancel);;

let rec comm_monoid_mult_word _A =
  ({ab_semigroup_mult_comm_monoid_mult = (ab_semigroup_mult_word _A);
     monoid_mult_comm_monoid_mult = (monoid_mult_word _A);
     dvd_comm_monoid_mult = (dvd_word _A)}
    : 'a word comm_monoid_mult);;

let rec comm_semiring_1_word _A =
  ({comm_monoid_mult_comm_semiring_1 = (comm_monoid_mult_word _A);
     comm_semiring_0_comm_semiring_1 = (comm_semiring_0_word _A);
     semiring_1_comm_semiring_1 = (semiring_1_word _A)}
    : 'a word comm_semiring_1);;

let rec comm_semiring_1_cancel_word _A =
  ({comm_semiring_0_cancel_comm_semiring_1_cancel =
      (comm_semiring_0_cancel_word _A);
     comm_semiring_1_comm_semiring_1_cancel = (comm_semiring_1_word _A);
     semiring_1_cancel_comm_semiring_1_cancel = (semiring_1_cancel_word _A)}
    : 'a word comm_semiring_1_cancel);;

let rec semiring_modulo_word _A =
  ({comm_semiring_1_cancel_semiring_modulo = (comm_semiring_1_cancel_word _A);
     modulo_semiring_modulo = (modulo_word _A)}
    : 'a word semiring_modulo);;

let rec semiring_parity_word _A =
  ({semiring_modulo_semiring_parity = (semiring_modulo_word _A)} :
    'a word semiring_parity);;

let rec semiring_bits_word _A =
  ({semiring_parity_semiring_bits = (semiring_parity_word _A);
     bit = bit_word _A}
    : 'a word semiring_bits);;

let rec take_bit_word _A
  n w = Word (if less_nat n (len_of _A.len0_len Type)
               then take_bit_int n (the_int _A w) else the_int _A w);;

let rec push_bit_word _A
  n w = times_worda _A w
          (power (power_word _A) (of_int _A (Int_of_integer (Z.of_int 2))) n);;

let rec semiring_bit_shifts_word _A =
  ({semiring_bits_semiring_bit_shifts = (semiring_bits_word _A);
     push_bit = push_bit_word _A; drop_bit = drop_bit_word _A;
     take_bit = take_bit_word _A}
    : 'a word semiring_bit_shifts);;

type 'a semiring_bit_syntax =
  {semiring_bit_shifts_semiring_bit_syntax : 'a semiring_bit_shifts};;

let rec semiring_bit_syntax_word _A =
  ({semiring_bit_shifts_semiring_bit_syntax = (semiring_bit_shifts_word _A)} :
    'a word semiring_bit_syntax);;

let rec typerep_arraya _A t = Typerep ("Heap.array", [typerep _A Type]);;

let countable_array = (() : ('a array) countable);;

let rec typerep_array _A =
  ({typerep = typerep_arraya _A} : ('a array) typerep);;

let rec heap_array _A =
  ({countable_heap = countable_array; typerep_heap = (typerep_array _A)} :
    ('a array) heap);;

type t_vec = T_v128;;

let rec equal_t_vec T_v128 T_v128 = true;;

type t_num = T_i32 | T_i64 | T_f32 | T_f64;;

let rec equal_t_num x0 x1 = match x0, x1 with T_f32, T_f64 -> false
                      | T_f64, T_f32 -> false
                      | T_i64, T_f64 -> false
                      | T_f64, T_i64 -> false
                      | T_i64, T_f32 -> false
                      | T_f32, T_i64 -> false
                      | T_i32, T_f64 -> false
                      | T_f64, T_i32 -> false
                      | T_i32, T_f32 -> false
                      | T_f32, T_i32 -> false
                      | T_i32, T_i64 -> false
                      | T_i64, T_i32 -> false
                      | T_f64, T_f64 -> true
                      | T_f32, T_f32 -> true
                      | T_i64, T_i64 -> true
                      | T_i32, T_i32 -> true;;

type t = T_num of t_num | T_vec of t_vec;;

let rec equal_ta x0 x1 = match x0, x1 with T_num x1, T_vec x2 -> false
                   | T_vec x2, T_num x1 -> false
                   | T_vec x2, T_vec y2 -> equal_t_vec x2 y2
                   | T_num x1, T_num y1 -> equal_t_num x1 y1;;

let equal_t = ({equal = equal_ta} : t equal);;

type v_vec = ConstVec128 of V128Wrapper.t;;

type i64 = I64_impl_abs of int64;;

type i32 = I32_impl_abs of int32;;

type v_num = ConstInt32 of i32 | ConstInt64 of i64 |
  ConstFloat32 of F32Wrapper.t | ConstFloat64 of F64Wrapper.t;;

type v = V_num of v_num | V_vec of v_vec;;

let rec typerep_va t = Typerep ("Wasm_Ast.v", []);;

let countable_v = (() : v countable);;

let typerep_v = ({typerep = typerep_va} : v typerep);;

let heap_v =
  ({countable_heap = countable_v; typerep_heap = typerep_v} : v heap);;

type num1 = One_num1;;

type 'a finite = {countable_finite : 'a countable};;

type 'a bit0 = Abs_bit0 of int;;

type uint8 = Abs_uint8 of num1 bit0 bit0 bit0 word;;

let rec rep_uint8a (Abs_uint8 x) = x;;

let rec len_of_num1 uu = one_nata;;

let len0_num1 = ({len_of = len_of_num1} : num1 len0);;

let len_num1 = ({len0_len = len0_num1} : num1 len);;

let rec nat_of_integer k = Nat (max ord_integer Z.zero k);;

let rec len_of_bit0 _A
  uu = times_nata (nat_of_integer (Z.of_int 2)) (len_of _A Type);;

let rec len0_bit0 _A = ({len_of = len_of_bit0 _A} : 'a bit0 len0);;

let rec len_bit0 _A = ({len0_len = (len0_bit0 _A.len0_len)} : 'a bit0 len);;

let rec times_uint8a
  xb xc =
    Abs_uint8
      (times_worda (len_bit0 (len_bit0 (len_bit0 len_num1))) (rep_uint8a xb)
        (rep_uint8a xc));;

let times_uint8 = ({times = times_uint8a} : uint8 times);;

let dvd_uint8 = ({times_dvd = times_uint8} : uint8 dvd);;

let one_uint8a : uint8
  = Abs_uint8 (one_worda (len_bit0 (len_bit0 (len_bit0 len_num1))));;

let one_uint8 = ({one = one_uint8a} : uint8 one);;

let rec plus_uint8a
  xb xc =
    Abs_uint8
      (plus_worda (len_bit0 (len_bit0 (len_bit0 len_num1))) (rep_uint8a xb)
        (rep_uint8a xc));;

let plus_uint8 = ({plus = plus_uint8a} : uint8 plus);;

let zero_uint8a : uint8
  = Abs_uint8 (zero_worda (len_bit0 (len_bit0 (len_bit0 len_num1))));;

let zero_uint8 = ({zero = zero_uint8a} : uint8 zero);;

let semigroup_add_uint8 =
  ({plus_semigroup_add = plus_uint8} : uint8 semigroup_add);;

let numeral_uint8 =
  ({one_numeral = one_uint8; semigroup_add_numeral = semigroup_add_uint8} :
    uint8 numeral);;

let power_uint8 =
  ({one_power = one_uint8; times_power = times_uint8} : uint8 power);;

let rec minus_uint8a
  xb xc =
    Abs_uint8
      (minus_worda (len_bit0 (len_bit0 (len_bit0 len_num1))) (rep_uint8a xb)
        (rep_uint8a xc));;

let minus_uint8 = ({minus = minus_uint8a} : uint8 minus);;

let rec equal_uint8
  x xa =
    equal_word (len_bit0 (len_bit0 (len_bit0 len_num1))) (rep_uint8a x)
      (rep_uint8a xa);;

let rec shiftr _A
  a n = drop_bit _A.semiring_bit_shifts_semiring_bit_syntax n a;;

let rec shiftl _A
  a n = push_bit _A.semiring_bit_shifts_semiring_bit_syntax n a;;

let rec less_eq_int k l = Z.leq (integer_of_int k) (integer_of_int l);;

let rec less_eq_word _A a b = less_eq_int (the_int _A a) (the_int _A b);;

let rec less_eq_uint8
  x xa =
    less_eq_word (len_bit0 (len_bit0 (len_bit0 len_num1))) (rep_uint8a x)
      (rep_uint8a xa);;

let rec less_int k l = Z.lt (integer_of_int k) (integer_of_int l);;

let rec less_word _A a b = less_int (the_int _A a) (the_int _A b);;

let rec less_uint8
  x xa =
    less_word (len_bit0 (len_bit0 (len_bit0 len_num1))) (rep_uint8a x)
      (rep_uint8a xa);;

let rec equal_bool p pa = match p, pa with p, true -> p
                     | p, false -> not p
                     | true, p -> p
                     | false, p -> not p;;

let rec abs_int i = (if less_int i zero_inta then uminus_inta i else i);;

let rec plus_nat m n = Nat (Z.add (integer_of_nat m) (integer_of_nat n));;

let rec suc n = plus_nat n one_nata;;

let rec signed_take_bit _A
  n a = (let l =
           take_bit
             _A.semiring_bit_operations_ring_bit_operations.semiring_bit_shifts_semiring_bit_operations
             (suc n) a
           in
          (if bit _A.semiring_bit_operations_ring_bit_operations.semiring_bit_shifts_semiring_bit_operations.semiring_bits_semiring_bit_shifts
                l n
            then plus _A.ring_parity_ring_bit_operations.comm_ring_1_ring_parity.ring_1_comm_ring_1.neg_numeral_ring_1.numeral_neg_numeral.semigroup_add_numeral.plus_semigroup_add
                   l (push_bit
                       _A.semiring_bit_operations_ring_bit_operations.semiring_bit_shifts_semiring_bit_operations
                       (suc n)
                       (uminus
                         _A.ring_parity_ring_bit_operations.comm_ring_1_ring_parity.ring_1_comm_ring_1.neg_numeral_ring_1.group_add_neg_numeral.uminus_group_add
                         (one _A.ring_parity_ring_bit_operations.comm_ring_1_ring_parity.ring_1_comm_ring_1.neg_numeral_ring_1.numeral_neg_numeral.one_numeral)))
            else l));;

let rec the_signed_int _A
  w = signed_take_bit ring_bit_operations_int
        (minus_nat (len_of _A.len0_len Type) (suc zero_nat)) (the_int _A w);;

let rec signed_divide_word _A
  x y = (let xa = the_signed_int _A x in
         let ya = the_signed_int _A y in
         let negative =
           not (equal_bool (less_int xa zero_inta) (less_int ya zero_inta)) in
         let result = divide_inta (abs_int xa) (abs_int ya) in
          of_int _A (if negative then uminus_inta result else result));;

let mod0_uint8 _ = failwith "Uint8.mod0_uint8";;

let div0_uint8 _ = failwith "Uint8.div0_uint8";;

let rec int_of_integer_symbolic x = Int_of_integer x;;

let rec uint8
  i = Abs_uint8
        (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
          (int_of_integer_symbolic i));;

let rec push_bit_uint8
  n x = (if less_nat n (nat_of_integer (Z.of_int 8))
          then uint8_shiftl x (integer_of_nat n) else zero_uint8a)
and uint8_shiftl
  w n = Abs_uint8
          (if Z.lt n Z.zero || Z.leq (Z.of_int 8) n
            then rep_uint8a (failwith "undefined" push_bit_uint8 w n)
            else push_bit_word (len_bit0 (len_bit0 (len_bit0 len_num1)))
                   (nat_of_integer n) (rep_uint8a w));;

let rec or_word _A v w = Word (or_int (the_int _A v) (the_int _A w));;

let rec or_uint8
  xb xc =
    Abs_uint8
      (or_word (len_bit0 (len_bit0 (len_bit0 len_num1))) (rep_uint8a xb)
        (rep_uint8a xc));;

let rec mask_uint8
  n = (if equal_nat n zero_nat then zero_uint8a
        else or_uint8 (push_bit_uint8 (minus_nat n one_nata) one_uint8a)
               (mask_uint8 (minus_nat n one_nata)));;

let rec and_uint8
  xb xc =
    Abs_uint8
      (and_word (len_bit0 (len_bit0 (len_bit0 len_num1))) (rep_uint8a xb)
        (rep_uint8a xc));;

let rec take_bit_uint8 n a = and_uint8 a (mask_uint8 n);;

let rec test_bit _A
  = bit _A.semiring_bit_shifts_semiring_bit_syntax.semiring_bits_semiring_bit_shifts;;

let cancel_semigroup_add_uint8 =
  ({semigroup_add_cancel_semigroup_add = semigroup_add_uint8} :
    uint8 cancel_semigroup_add);;

let ab_semigroup_add_uint8 =
  ({semigroup_add_ab_semigroup_add = semigroup_add_uint8} :
    uint8 ab_semigroup_add);;

let cancel_ab_semigroup_add_uint8 =
  ({ab_semigroup_add_cancel_ab_semigroup_add = ab_semigroup_add_uint8;
     cancel_semigroup_add_cancel_ab_semigroup_add = cancel_semigroup_add_uint8;
     minus_cancel_ab_semigroup_add = minus_uint8}
    : uint8 cancel_ab_semigroup_add);;

let monoid_add_uint8 =
  ({semigroup_add_monoid_add = semigroup_add_uint8;
     zero_monoid_add = zero_uint8}
    : uint8 monoid_add);;

let comm_monoid_add_uint8 =
  ({ab_semigroup_add_comm_monoid_add = ab_semigroup_add_uint8;
     monoid_add_comm_monoid_add = monoid_add_uint8}
    : uint8 comm_monoid_add);;

let cancel_comm_monoid_add_uint8 =
  ({cancel_ab_semigroup_add_cancel_comm_monoid_add =
      cancel_ab_semigroup_add_uint8;
     comm_monoid_add_cancel_comm_monoid_add = comm_monoid_add_uint8}
    : uint8 cancel_comm_monoid_add);;

let mult_zero_uint8 =
  ({times_mult_zero = times_uint8; zero_mult_zero = zero_uint8} :
    uint8 mult_zero);;

let semigroup_mult_uint8 =
  ({times_semigroup_mult = times_uint8} : uint8 semigroup_mult);;

let semiring_uint8 =
  ({ab_semigroup_add_semiring = ab_semigroup_add_uint8;
     semigroup_mult_semiring = semigroup_mult_uint8}
    : uint8 semiring);;

let semiring_0_uint8 =
  ({comm_monoid_add_semiring_0 = comm_monoid_add_uint8;
     mult_zero_semiring_0 = mult_zero_uint8;
     semiring_semiring_0 = semiring_uint8}
    : uint8 semiring_0);;

let semiring_0_cancel_uint8 =
  ({cancel_comm_monoid_add_semiring_0_cancel = cancel_comm_monoid_add_uint8;
     semiring_0_semiring_0_cancel = semiring_0_uint8}
    : uint8 semiring_0_cancel);;

let ab_semigroup_mult_uint8 =
  ({semigroup_mult_ab_semigroup_mult = semigroup_mult_uint8} :
    uint8 ab_semigroup_mult);;

let comm_semiring_uint8 =
  ({ab_semigroup_mult_comm_semiring = ab_semigroup_mult_uint8;
     semiring_comm_semiring = semiring_uint8}
    : uint8 comm_semiring);;

let comm_semiring_0_uint8 =
  ({comm_semiring_comm_semiring_0 = comm_semiring_uint8;
     semiring_0_comm_semiring_0 = semiring_0_uint8}
    : uint8 comm_semiring_0);;

let comm_semiring_0_cancel_uint8 =
  ({comm_semiring_0_comm_semiring_0_cancel = comm_semiring_0_uint8;
     semiring_0_cancel_comm_semiring_0_cancel = semiring_0_cancel_uint8}
    : uint8 comm_semiring_0_cancel);;

let monoid_mult_uint8 =
  ({semigroup_mult_monoid_mult = semigroup_mult_uint8;
     power_monoid_mult = power_uint8}
    : uint8 monoid_mult);;

let semiring_numeral_uint8 =
  ({monoid_mult_semiring_numeral = monoid_mult_uint8;
     numeral_semiring_numeral = numeral_uint8;
     semiring_semiring_numeral = semiring_uint8}
    : uint8 semiring_numeral);;

let zero_neq_one_uint8 =
  ({one_zero_neq_one = one_uint8; zero_zero_neq_one = zero_uint8} :
    uint8 zero_neq_one);;

let semiring_1_uint8 =
  ({semiring_numeral_semiring_1 = semiring_numeral_uint8;
     semiring_0_semiring_1 = semiring_0_uint8;
     zero_neq_one_semiring_1 = zero_neq_one_uint8}
    : uint8 semiring_1);;

let semiring_1_cancel_uint8 =
  ({semiring_0_cancel_semiring_1_cancel = semiring_0_cancel_uint8;
     semiring_1_semiring_1_cancel = semiring_1_uint8}
    : uint8 semiring_1_cancel);;

let comm_monoid_mult_uint8 =
  ({ab_semigroup_mult_comm_monoid_mult = ab_semigroup_mult_uint8;
     monoid_mult_comm_monoid_mult = monoid_mult_uint8;
     dvd_comm_monoid_mult = dvd_uint8}
    : uint8 comm_monoid_mult);;

let comm_semiring_1_uint8 =
  ({comm_monoid_mult_comm_semiring_1 = comm_monoid_mult_uint8;
     comm_semiring_0_comm_semiring_1 = comm_semiring_0_uint8;
     semiring_1_comm_semiring_1 = semiring_1_uint8}
    : uint8 comm_semiring_1);;

let comm_semiring_1_cancel_uint8 =
  ({comm_semiring_0_cancel_comm_semiring_1_cancel =
      comm_semiring_0_cancel_uint8;
     comm_semiring_1_comm_semiring_1_cancel = comm_semiring_1_uint8;
     semiring_1_cancel_comm_semiring_1_cancel = semiring_1_cancel_uint8}
    : uint8 comm_semiring_1_cancel);;

let rec divide_uint8 () = ({divide = divide_uint8a} : uint8 divide)
and modulo_uint8 () =
  ({divide_modulo = (divide_uint8 ()); dvd_modulo = dvd_uint8;
     modulo = modulo_uint8a}
    : uint8 modulo)
and semiring_modulo_uint8 () =
  ({comm_semiring_1_cancel_semiring_modulo = comm_semiring_1_cancel_uint8;
     modulo_semiring_modulo = (modulo_uint8 ())}
    : uint8 semiring_modulo)
and semiring_parity_uint8 () =
  ({semiring_modulo_semiring_parity = (semiring_modulo_uint8 ())} :
    uint8 semiring_parity)
and semiring_bits_uint8 () =
  ({semiring_parity_semiring_bits = (semiring_parity_uint8 ()); bit = bit_uint8}
    : uint8 semiring_bits)
and semiring_bit_shifts_uint8 () =
  ({semiring_bits_semiring_bit_shifts = (semiring_bits_uint8 ());
     push_bit = push_bit_uint8; drop_bit = drop_bit_uint8;
     take_bit = take_bit_uint8}
    : uint8 semiring_bit_shifts)
and semiring_bit_syntax_uint8 () =
  ({semiring_bit_shifts_semiring_bit_syntax = (semiring_bit_shifts_uint8 ())} :
    uint8 semiring_bit_syntax)
and uint8_divmod
  x y = (if less_eq_uint8 (uint8 (Z.of_int 128)) y
          then (if less_uint8 x y then (zero_uint8a, x)
                 else (one_uint8a, minus_uint8a x y))
          else (if equal_uint8 y zero_uint8a then (div0_uint8 x, mod0_uint8 x)
                 else (let q =
                         shiftl (semiring_bit_syntax_uint8 ())
                           (uint8_sdiv
                             (shiftr (semiring_bit_syntax_uint8 ()) x one_nata)
                             y)
                           one_nata
                         in
                       let r = minus_uint8a x (times_uint8a q y) in
                        (if less_eq_uint8 y r
                          then (plus_uint8a q one_uint8a, minus_uint8a r y)
                          else (q, r)))))
and uint8_div x y = fst (uint8_divmod x y)
and divide_uint8a
  x y = (if equal_uint8 y zero_uint8a then zero_uint8a else uint8_div x y)
and uint8_sdiv
  x y = Abs_uint8
          (if equal_uint8 y zero_uint8a
            then rep_uint8a (failwith "undefined" divide_uint8a x zero_uint8a)
            else signed_divide_word (len_bit0 (len_bit0 (len_bit0 len_num1)))
                   (rep_uint8a x) (rep_uint8a y))
and uint8_mod x y = snd (uint8_divmod x y)
and modulo_uint8a x y = (if equal_uint8 y zero_uint8a then x else uint8_mod x y)
and uint8_shiftr
  w n = Abs_uint8
          (if Z.lt n Z.zero || Z.leq (Z.of_int 8) n
            then rep_uint8a
                   (failwith "undefined" (shiftr (semiring_bit_syntax_uint8 ()))
                     w n)
            else drop_bit_word (len_bit0 (len_bit0 (len_bit0 len_num1)))
                   (nat_of_integer n) (rep_uint8a w))
and drop_bit_uint8
  n x = (if less_nat n (nat_of_integer (Z.of_int 8))
          then uint8_shiftr x (integer_of_nat n) else zero_uint8a)
and uint8_test_bit
  w n = (if Z.lt n Z.zero || Z.lt (Z.of_int 7) n
          then failwith "undefined" (test_bit (semiring_bit_syntax_uint8 ())) w
                 n
          else test_bit
                 (semiring_bit_syntax_word
                   (len_bit0 (len_bit0 (len_bit0 len_num1))))
                 (rep_uint8a w) (nat_of_integer n))
and bit_uint8
  x n = less_nat n (nat_of_integer (Z.of_int 8)) &&
          uint8_test_bit x (integer_of_nat n);;
let divide_uint8 = divide_uint8 ();;
let modulo_uint8 = modulo_uint8 ();;
let semiring_modulo_uint8 = semiring_modulo_uint8 ();;
let semiring_parity_uint8 = semiring_parity_uint8 ();;
let semiring_bits_uint8 = semiring_bits_uint8 ();;
let semiring_bit_shifts_uint8 = semiring_bit_shifts_uint8 ();;
let semiring_bit_syntax_uint8 = semiring_bit_syntax_uint8 ();;

let rec eq _A a b = equal _A a b;;

let rec equal_list _A
  x0 x1 = match x0, x1 with [], x21 :: x22 -> false
    | x21 :: x22, [] -> false
    | x21 :: x22, y21 :: y22 -> eq _A x21 y21 && equal_list _A x22 y22
    | [], [] -> true;;

type tf = Tf of t list * t list;;

let rec equal_tfa
  (Tf (x1, x2)) (Tf (y1, y2)) =
    equal_list equal_t x1 y1 && equal_list equal_t x2 y2;;

let equal_tf = ({equal = equal_tfa} : tf equal);;

let rec typerep_tfa t = Typerep ("Wasm_Ast.tf", []);;

let countable_tf = (() : tf countable);;

let typerep_tf = ({typerep = typerep_tfa} : tf typerep);;

let heap_tf =
  ({countable_heap = countable_tf; typerep_heap = typerep_tf} : tf heap);;

let zero_f32 = ({zero = F32Wrapper.zero} : F32Wrapper.t zero);;

type 'a wasm_base = {zero_wasm_base : 'a zero};;

let wasm_base_f32 = ({zero_wasm_base = zero_f32} : F32Wrapper.t wasm_base);;

type 'a wasm_float =
  {wasm_base_wasm_float : 'a wasm_base; float_neg : 'a -> 'a;
    float_abs : 'a -> 'a; float_ceil : 'a -> 'a; float_floor : 'a -> 'a;
    float_trunc : 'a -> 'a; float_nearest : 'a -> 'a; float_sqrt : 'a -> 'a;
    float_add : 'a -> 'a -> 'a; float_sub : 'a -> 'a -> 'a;
    float_mul : 'a -> 'a -> 'a; float_div : 'a -> 'a -> 'a;
    float_min : 'a -> 'a -> 'a; float_max : 'a -> 'a -> 'a;
    float_copysign : 'a -> 'a -> 'a; float_eq : 'a -> 'a -> bool;
    float_lt : 'a -> 'a -> bool; float_gt : 'a -> 'a -> bool;
    float_le : 'a -> 'a -> bool; float_ge : 'a -> 'a -> bool};;
let float_neg _A = _A.float_neg;;
let float_abs _A = _A.float_abs;;
let float_ceil _A = _A.float_ceil;;
let float_floor _A = _A.float_floor;;
let float_trunc _A = _A.float_trunc;;
let float_nearest _A = _A.float_nearest;;
let float_sqrt _A = _A.float_sqrt;;
let float_add _A = _A.float_add;;
let float_sub _A = _A.float_sub;;
let float_mul _A = _A.float_mul;;
let float_div _A = _A.float_div;;
let float_min _A = _A.float_min;;
let float_max _A = _A.float_max;;
let float_copysign _A = _A.float_copysign;;
let float_eq _A = _A.float_eq;;
let float_lt _A = _A.float_lt;;
let float_gt _A = _A.float_gt;;
let float_le _A = _A.float_le;;
let float_ge _A = _A.float_ge;;

let wasm_float_f32 =
  ({wasm_base_wasm_float = wasm_base_f32; float_neg = F32Wrapper.neg;
     float_abs = F32Wrapper.abs; float_ceil = F32Wrapper.ceil;
     float_floor = F32Wrapper.floor; float_trunc = F32Wrapper.trunc;
     float_nearest = F32Wrapper.nearest; float_sqrt = F32Wrapper.sqrt;
     float_add = F32Wrapper.add; float_sub = F32Wrapper.sub;
     float_mul = F32Wrapper.mul; float_div = F32Wrapper.div;
     float_min = F32Wrapper.min; float_max = F32Wrapper.max;
     float_copysign = F32Wrapper.copysign; float_eq = F32Wrapper.eq;
     float_lt = F32Wrapper.lt; float_gt = F32Wrapper.gt;
     float_le = F32Wrapper.le; float_ge = F32Wrapper.ge}
    : F32Wrapper.t wasm_float);;

let zero_f64 = ({zero = F64Wrapper.zero} : F64Wrapper.t zero);;

let wasm_base_f64 = ({zero_wasm_base = zero_f64} : F64Wrapper.t wasm_base);;

let wasm_float_f64 =
  ({wasm_base_wasm_float = wasm_base_f64; float_neg = F64Wrapper.neg;
     float_abs = F64Wrapper.abs; float_ceil = F64Wrapper.ceil;
     float_floor = F64Wrapper.floor; float_trunc = F64Wrapper.trunc;
     float_nearest = F64Wrapper.nearest; float_sqrt = F64Wrapper.sqrt;
     float_add = F64Wrapper.add; float_sub = F64Wrapper.sub;
     float_mul = F64Wrapper.mul; float_div = F64Wrapper.div;
     float_min = F64Wrapper.min; float_max = F64Wrapper.max;
     float_copysign = F64Wrapper.copysign; float_eq = F64Wrapper.eq;
     float_lt = F64Wrapper.lt; float_gt = F64Wrapper.gt;
     float_le = F64Wrapper.le; float_ge = F64Wrapper.ge}
    : F64Wrapper.t wasm_float);;

let zero_i32a : i32 = I32_impl_abs Int32.zero;;

let zero_i32 = ({zero = zero_i32a} : i32 zero);;

let rec len_of_i32 uu = nat_of_integer (Z.of_int 32);;

let len0_i32 = ({len_of = len_of_i32} : i32 len0);;

let len_i32 = ({len0_len = len0_i32} : i32 len);;

let rec bit_uint32
  x n = less_nat n (nat_of_integer (Z.of_int 32)) &&
          Uint32.test_bit x (integer_of_nat n);;

let rec uint32
  i = (let ia = Z.logand i (Z.of_string "4294967295") in
        (if bit_integer ia (nat_of_integer (Z.of_int 31))
          then Z.to_int32 (Z.sub ia (Z.of_string "4294967296"))
          else Z.to_int32 ia));;

let rec integer_of_uint32
  n = (if bit_uint32 n (nat_of_integer (Z.of_int 31))
        then Z.logor
               (Z.of_int32 (Int32.logand n (uint32 (Z.of_string "2147483647"))))
               (Z.of_string "2147483648")
        else Z.of_int32 n);;

let rec nat_of_uint32 x = nat_of_integer (integer_of_uint32 x);;

let rec nat_of_int_i32 (I32_impl_abs x) = nat_of_uint32 x;;

let rec fold_atLeastAtMost_nat
  f a b acc =
    (if less_nat b a then acc
      else fold_atLeastAtMost_nat f (plus_nat a one_nata) b (f a acc));;

let rec int_of_nat n = Int_of_integer (integer_of_nat n);;

let rec uint32_of_int i = uint32 (integer_of_int i);;

let rec comp f g = (fun x -> f (g x));;

let rec uint32_of_nat x = comp uint32_of_int int_of_nat x;;

let rec int_popcnt_i32
  (I32_impl_abs x) =
    I32_impl_abs
      (uint32_of_nat
        (fold_atLeastAtMost_nat
          (fun n acc -> (if bit_uint32 x n then plus_nat acc one_nata else acc))
          zero_nat (nat_of_integer (Z.of_int 31)) zero_nat));;

let rec int_of_nat_i32 n = I32_impl_abs (uint32_of_nat n);;

let rec int_shr_u_i32
  (I32_impl_abs x) (I32_impl_abs y) =
    I32_impl_abs
      (Uint32.shiftr x (modulo_integer (integer_of_uint32 y) (Z.of_int 32)));;

let rec int_shr_s_i32
  (I32_impl_abs x) (I32_impl_abs y) =
    I32_impl_abs
      (Uint32.shiftr_signed x
        (modulo_integer (integer_of_uint32 y) (Z.of_int 32)));;

let rec drop_bit_uint32
  n x = (if less_nat n (nat_of_integer (Z.of_int 32))
          then Uint32.shiftr x (integer_of_nat n) else Int32.zero);;

let mod0_uint32 _ = failwith "Uint32.mod0_uint32";;

let div0_uint32 _ = failwith "Uint32.div0_uint32";;

let rec push_bit_uint32
  n x = (if less_nat n (nat_of_integer (Z.of_int 32))
          then Uint32.shiftl x (integer_of_nat n) else Int32.zero);;

let plus_uint32 = ({plus = Int32.add} : int32 plus);;

let semigroup_add_uint32 =
  ({plus_semigroup_add = plus_uint32} : int32 semigroup_add);;

let cancel_semigroup_add_uint32 =
  ({semigroup_add_cancel_semigroup_add = semigroup_add_uint32} :
    int32 cancel_semigroup_add);;

let ab_semigroup_add_uint32 =
  ({semigroup_add_ab_semigroup_add = semigroup_add_uint32} :
    int32 ab_semigroup_add);;

let minus_uint32 = ({minus = Int32.sub} : int32 minus);;

let cancel_ab_semigroup_add_uint32 =
  ({ab_semigroup_add_cancel_ab_semigroup_add = ab_semigroup_add_uint32;
     cancel_semigroup_add_cancel_ab_semigroup_add = cancel_semigroup_add_uint32;
     minus_cancel_ab_semigroup_add = minus_uint32}
    : int32 cancel_ab_semigroup_add);;

let zero_uint32 = ({zero = Int32.zero} : int32 zero);;

let monoid_add_uint32 =
  ({semigroup_add_monoid_add = semigroup_add_uint32;
     zero_monoid_add = zero_uint32}
    : int32 monoid_add);;

let comm_monoid_add_uint32 =
  ({ab_semigroup_add_comm_monoid_add = ab_semigroup_add_uint32;
     monoid_add_comm_monoid_add = monoid_add_uint32}
    : int32 comm_monoid_add);;

let cancel_comm_monoid_add_uint32 =
  ({cancel_ab_semigroup_add_cancel_comm_monoid_add =
      cancel_ab_semigroup_add_uint32;
     comm_monoid_add_cancel_comm_monoid_add = comm_monoid_add_uint32}
    : int32 cancel_comm_monoid_add);;

let times_uint32 = ({times = Int32.mul} : int32 times);;

let mult_zero_uint32 =
  ({times_mult_zero = times_uint32; zero_mult_zero = zero_uint32} :
    int32 mult_zero);;

let semigroup_mult_uint32 =
  ({times_semigroup_mult = times_uint32} : int32 semigroup_mult);;

let semiring_uint32 =
  ({ab_semigroup_add_semiring = ab_semigroup_add_uint32;
     semigroup_mult_semiring = semigroup_mult_uint32}
    : int32 semiring);;

let semiring_0_uint32 =
  ({comm_monoid_add_semiring_0 = comm_monoid_add_uint32;
     mult_zero_semiring_0 = mult_zero_uint32;
     semiring_semiring_0 = semiring_uint32}
    : int32 semiring_0);;

let semiring_0_cancel_uint32 =
  ({cancel_comm_monoid_add_semiring_0_cancel = cancel_comm_monoid_add_uint32;
     semiring_0_semiring_0_cancel = semiring_0_uint32}
    : int32 semiring_0_cancel);;

let ab_semigroup_mult_uint32 =
  ({semigroup_mult_ab_semigroup_mult = semigroup_mult_uint32} :
    int32 ab_semigroup_mult);;

let comm_semiring_uint32 =
  ({ab_semigroup_mult_comm_semiring = ab_semigroup_mult_uint32;
     semiring_comm_semiring = semiring_uint32}
    : int32 comm_semiring);;

let comm_semiring_0_uint32 =
  ({comm_semiring_comm_semiring_0 = comm_semiring_uint32;
     semiring_0_comm_semiring_0 = semiring_0_uint32}
    : int32 comm_semiring_0);;

let comm_semiring_0_cancel_uint32 =
  ({comm_semiring_0_comm_semiring_0_cancel = comm_semiring_0_uint32;
     semiring_0_cancel_comm_semiring_0_cancel = semiring_0_cancel_uint32}
    : int32 comm_semiring_0_cancel);;

let one_uint32 = ({one = Int32.one} : int32 one);;

let power_uint32 =
  ({one_power = one_uint32; times_power = times_uint32} : int32 power);;

let monoid_mult_uint32 =
  ({semigroup_mult_monoid_mult = semigroup_mult_uint32;
     power_monoid_mult = power_uint32}
    : int32 monoid_mult);;

let numeral_uint32 =
  ({one_numeral = one_uint32; semigroup_add_numeral = semigroup_add_uint32} :
    int32 numeral);;

let semiring_numeral_uint32 =
  ({monoid_mult_semiring_numeral = monoid_mult_uint32;
     numeral_semiring_numeral = numeral_uint32;
     semiring_semiring_numeral = semiring_uint32}
    : int32 semiring_numeral);;

let zero_neq_one_uint32 =
  ({one_zero_neq_one = one_uint32; zero_zero_neq_one = zero_uint32} :
    int32 zero_neq_one);;

let semiring_1_uint32 =
  ({semiring_numeral_semiring_1 = semiring_numeral_uint32;
     semiring_0_semiring_1 = semiring_0_uint32;
     zero_neq_one_semiring_1 = zero_neq_one_uint32}
    : int32 semiring_1);;

let semiring_1_cancel_uint32 =
  ({semiring_0_cancel_semiring_1_cancel = semiring_0_cancel_uint32;
     semiring_1_semiring_1_cancel = semiring_1_uint32}
    : int32 semiring_1_cancel);;

let dvd_uint32 = ({times_dvd = times_uint32} : int32 dvd);;

let comm_monoid_mult_uint32 =
  ({ab_semigroup_mult_comm_monoid_mult = ab_semigroup_mult_uint32;
     monoid_mult_comm_monoid_mult = monoid_mult_uint32;
     dvd_comm_monoid_mult = dvd_uint32}
    : int32 comm_monoid_mult);;

let comm_semiring_1_uint32 =
  ({comm_monoid_mult_comm_semiring_1 = comm_monoid_mult_uint32;
     comm_semiring_0_comm_semiring_1 = comm_semiring_0_uint32;
     semiring_1_comm_semiring_1 = semiring_1_uint32}
    : int32 comm_semiring_1);;

let comm_semiring_1_cancel_uint32 =
  ({comm_semiring_0_cancel_comm_semiring_1_cancel =
      comm_semiring_0_cancel_uint32;
     comm_semiring_1_comm_semiring_1_cancel = comm_semiring_1_uint32;
     semiring_1_cancel_comm_semiring_1_cancel = semiring_1_cancel_uint32}
    : int32 comm_semiring_1_cancel);;

let rec uint32_mod x y = snd (uint32_divmod x y)
and modulo_uint32a
  x y = (if (Int32.compare y Int32.zero = 0) then x else uint32_mod x y)
and semiring_bit_syntax_uint32 () =
  ({semiring_bit_shifts_semiring_bit_syntax = (semiring_bit_shifts_uint32 ())} :
    int32 semiring_bit_syntax)
and uint32_divmod
  x y = (if Uint32.less_eq (uint32 (Z.of_string "2147483648")) y
          then (if Uint32.less x y then (Int32.zero, x)
                 else (Int32.one, Int32.sub x y))
          else (if (Int32.compare y Int32.zero = 0)
                 then (div0_uint32 x, mod0_uint32 x)
                 else (let q =
                         shiftl (semiring_bit_syntax_uint32 ())
                           (Int32.div (drop_bit_uint32 one_nata x) y) one_nata
                         in
                       let r = Int32.sub x (Int32.mul q y) in
                        (if Uint32.less_eq y r
                          then (Int32.add q Int32.one, Int32.sub r y)
                          else (q, r)))))
and uint32_div x y = fst (uint32_divmod x y)
and divide_uint32a
  x y = (if (Int32.compare y Int32.zero = 0) then Int32.zero
          else uint32_div x y)
and divide_uint32 () = ({divide = divide_uint32a} : int32 divide)
and modulo_uint32 () =
  ({divide_modulo = (divide_uint32 ()); dvd_modulo = dvd_uint32;
     modulo = modulo_uint32a}
    : int32 modulo)
and semiring_modulo_uint32 () =
  ({comm_semiring_1_cancel_semiring_modulo = comm_semiring_1_cancel_uint32;
     modulo_semiring_modulo = (modulo_uint32 ())}
    : int32 semiring_modulo)
and semiring_parity_uint32 () =
  ({semiring_modulo_semiring_parity = (semiring_modulo_uint32 ())} :
    int32 semiring_parity)
and semiring_bits_uint32 () =
  ({semiring_parity_semiring_bits = (semiring_parity_uint32 ());
     bit = bit_uint32}
    : int32 semiring_bits)
and mask_uint32
  n = shiftr (semiring_bit_syntax_uint32 ()) (Int32.neg Int32.one)
        (minus_nat (nat_of_integer (Z.of_int 32)) n)
and take_bit_uint32 n a = Int32.logand a (mask_uint32 n)
and semiring_bit_shifts_uint32 () =
  ({semiring_bits_semiring_bit_shifts = (semiring_bits_uint32 ());
     push_bit = push_bit_uint32; drop_bit = drop_bit_uint32;
     take_bit = take_bit_uint32}
    : int32 semiring_bit_shifts);;
let semiring_bit_syntax_uint32 = semiring_bit_syntax_uint32 ();;
let divide_uint32 = divide_uint32 ();;
let modulo_uint32 = modulo_uint32 ();;
let semiring_modulo_uint32 = semiring_modulo_uint32 ();;
let semiring_parity_uint32 = semiring_parity_uint32 ();;
let semiring_bits_uint32 = semiring_bits_uint32 ();;
let semiring_bit_shifts_uint32 = semiring_bit_shifts_uint32 ();;

let rec int_rem_u_i32
  (I32_impl_abs x) (I32_impl_abs y) =
    (if (Int32.compare y Int32.zero = 0) then None
      else Some (I32_impl_abs (uint32_mod x y)));;

let rec int_rem_s_i32
  (I32_impl_abs x) (I32_impl_abs y) =
    (if (Int32.compare y Int32.zero = 0) then None
      else Some (I32_impl_abs (Int32.sub x (Int32.mul (Int32.div x y) y))));;

let rec int_div_u_i32
  (I32_impl_abs x) (I32_impl_abs y) =
    (if (Int32.compare y Int32.zero = 0) then None
      else Some (I32_impl_abs (uint32_div x y)));;

let rec int_div_s_i32
  (I32_impl_abs x) (I32_impl_abs y) =
    (if (Int32.compare y Int32.zero = 0) ||
          (Int32.compare x (Int32.neg
                             (uint32 (Z.of_string "2147483648"))) = 0) &&
            (Int32.compare y (Int32.neg Int32.one) = 0)
      then None else Some (I32_impl_abs (Int32.div x y)));;

let rec int_rotr_i32
  (I32_impl_abs x) (I32_impl_abs y) =
    I32_impl_abs
      (let n = nat_of_uint32 (modulo_uint32a y (uint32 (Z.of_int 32))) in
        Int32.logor (drop_bit_uint32 n x)
          (push_bit_uint32 (minus_nat (nat_of_integer (Z.of_int 32)) n)
            (take_bit_uint32 n x)));;

let rec int_rotl_i32
  (I32_impl_abs x) (I32_impl_abs y) =
    I32_impl_abs
      (let n = nat_of_uint32 (modulo_uint32a y (uint32 (Z.of_int 32))) in
        Int32.logor
          (drop_bit_uint32 (minus_nat (nat_of_integer (Z.of_int 32)) n) x)
          (push_bit_uint32 n
            (take_bit_uint32 (minus_nat (nat_of_integer (Z.of_int 32)) n) x)));;

let rec int_lt_u_i32 (I32_impl_abs x) (I32_impl_abs y) = Uint32.less x y;;

let rec msb_uint32 x = Uint32.test_bit x (Z.of_int 31);;

let rec int_lt_s_i32
  (I32_impl_abs x) (I32_impl_abs y) =
    (if msb_uint32 y then msb_uint32 x else true) &&
      (msb_uint32 x && not (msb_uint32 y) || Uint32.less x y);;

let rec int_le_u_i32 (I32_impl_abs x) (I32_impl_abs y) = Uint32.less_eq x y;;

let rec int_le_s_i32
  (I32_impl_abs x) (I32_impl_abs y) =
    (if msb_uint32 y then msb_uint32 x else true) &&
      (msb_uint32 x && not (msb_uint32 y) || Uint32.less_eq x y);;

let rec int_gt_u_i32 (I32_impl_abs x) (I32_impl_abs y) = Uint32.less y x;;

let rec int_gt_s_i32
  (I32_impl_abs x) (I32_impl_abs y) =
    (if msb_uint32 x then msb_uint32 y else true) &&
      (msb_uint32 y && not (msb_uint32 x) || Uint32.less y x);;

let rec int_ge_u_i32 (I32_impl_abs x) (I32_impl_abs y) = Uint32.less_eq y x;;

let rec int_ge_s_i32
  (I32_impl_abs x) (I32_impl_abs y) =
    (if msb_uint32 x then msb_uint32 y else true) &&
      (msb_uint32 y && not (msb_uint32 x) || Uint32.less_eq y x);;

let rec int_xor_i32
  (I32_impl_abs x) (I32_impl_abs y) = I32_impl_abs (Int32.logxor x y);;

let rec int_sub_i32
  (I32_impl_abs x) (I32_impl_abs y) = I32_impl_abs (Int32.sub x y);;

let rec int_shl_i32
  (I32_impl_abs x) (I32_impl_abs y) =
    I32_impl_abs
      (Uint32.shiftl x (modulo_integer (integer_of_uint32 y) (Z.of_int 32)));;

let rec int_mul_i32
  (I32_impl_abs x) (I32_impl_abs y) = I32_impl_abs (Int32.mul x y);;

let rec int_eqz_i32 (I32_impl_abs x) = (Int32.compare x Int32.zero = 0);;

let rec gen_length n x1 = match n, x1 with n, x :: xs -> gen_length (suc n) xs
                     | n, [] -> n;;

let rec size_list x = gen_length zero_nat x;;

let rec map f x1 = match f, x1 with f, [] -> []
              | f, x21 :: x22 -> f x21 :: map f x22;;

let rec upt i j = (if less_nat i j then i :: upt (suc i) j else []);;

let rec fold f x1 s = match f, x1, s with f, x :: xs, s -> fold f xs (f x s)
               | f, [], s -> s;;

let rec rev xs = fold (fun a b -> a :: b) xs [];;

let rec to_bl _A
  w = map (bit_word _A w) (rev (upt zero_nat (len_of _A.len0_len Type)));;

let rec takeWhile p x1 = match p, x1 with p, [] -> []
                    | p, x :: xs -> (if p x then x :: takeWhile p xs else []);;

let rec word_ctz _A w = size_list (takeWhile not (rev (to_bl _A w)));;

let rec id x = (fun xa -> xa) x;;

let rec foldr f x1 = match f, x1 with f, [] -> id
                | f, x :: xs -> comp (f x) (foldr f xs);;

let rec horner_sum _B
  f a xs =
    foldr (fun x b ->
            plus _B.semiring_0_comm_semiring_0.comm_monoid_add_semiring_0.monoid_add_comm_monoid_add.semigroup_add_monoid_add.plus_semigroup_add
              (f x)
              (times
                _B.semiring_0_comm_semiring_0.mult_zero_semiring_0.times_mult_zero
                a b))
      xs (zero _B.semiring_0_comm_semiring_0.mult_zero_semiring_0.zero_mult_zero);;

let rec of_bool _A = function true -> one _A.one_zero_neq_one
                     | false -> zero _A.zero_zero_neq_one;;

let rec set_bits_word _A
  p = horner_sum (comm_semiring_0_word _A) (of_bool (zero_neq_one_word _A))
        (of_int _A (Int_of_integer (Z.of_int 2)))
        (map p (upt zero_nat (len_of _A.len0_len Type)));;

let rec rep_uint32
  x = set_bits_word
        (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
        (bit_uint32 x);;

let rec abs_uint32
  x = uint32
        (integer_of_int
          (the_int
            (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
            x));;

let rec of_nat _A
  n = Word (take_bit_int (len_of _A.len0_len Type) (int_of_nat n));;

let rec int_ctz_i32
  (I32_impl_abs x) =
    I32_impl_abs
      (abs_uint32
        (of_nat (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
          (word_ctz
            (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
            (rep_uint32 x))));;

let rec word_clz _A w = size_list (takeWhile not (to_bl _A w));;

let rec int_clz_i32
  (I32_impl_abs x) =
    I32_impl_abs
      (abs_uint32
        (of_nat (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
          (word_clz
            (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
            (rep_uint32 x))));;

let rec int_and_i32
  (I32_impl_abs x) (I32_impl_abs y) = I32_impl_abs (Int32.logand x y);;

let rec int_add_i32
  (I32_impl_abs x) (I32_impl_abs y) = I32_impl_abs (Int32.add x y);;

let rec int_or_i32
  (I32_impl_abs x) (I32_impl_abs y) = I32_impl_abs (Int32.logor x y);;

let rec int_eq_i32 (I32_impl_abs x) (I32_impl_abs y) = (Int32.compare x y = 0);;

type 'a wasm_int_ops =
  {len_wasm_int_ops : 'a len; wasm_base_wasm_int_ops : 'a wasm_base;
    int_clz : 'a -> 'a; int_ctz : 'a -> 'a; int_popcnt : 'a -> 'a;
    int_add : 'a -> 'a -> 'a; int_sub : 'a -> 'a -> 'a;
    int_mul : 'a -> 'a -> 'a; int_div_u : 'a -> 'a -> 'a option;
    int_div_s : 'a -> 'a -> 'a option; int_rem_u : 'a -> 'a -> 'a option;
    int_rem_s : 'a -> 'a -> 'a option; int_and : 'a -> 'a -> 'a;
    int_or : 'a -> 'a -> 'a; int_xor : 'a -> 'a -> 'a; int_shl : 'a -> 'a -> 'a;
    int_shr_u : 'a -> 'a -> 'a; int_shr_s : 'a -> 'a -> 'a;
    int_rotl : 'a -> 'a -> 'a; int_rotr : 'a -> 'a -> 'a; int_eqz : 'a -> bool;
    int_eq : 'a -> 'a -> bool; int_lt_u : 'a -> 'a -> bool;
    int_lt_s : 'a -> 'a -> bool; int_gt_u : 'a -> 'a -> bool;
    int_gt_s : 'a -> 'a -> bool; int_le_u : 'a -> 'a -> bool;
    int_le_s : 'a -> 'a -> bool; int_ge_u : 'a -> 'a -> bool;
    int_ge_s : 'a -> 'a -> bool; int_of_nata : nat -> 'a;
    nat_of_int : 'a -> nat};;
let int_clz _A = _A.int_clz;;
let int_ctz _A = _A.int_ctz;;
let int_popcnt _A = _A.int_popcnt;;
let int_add _A = _A.int_add;;
let int_sub _A = _A.int_sub;;
let int_mul _A = _A.int_mul;;
let int_div_u _A = _A.int_div_u;;
let int_div_s _A = _A.int_div_s;;
let int_rem_u _A = _A.int_rem_u;;
let int_rem_s _A = _A.int_rem_s;;
let int_and _A = _A.int_and;;
let int_or _A = _A.int_or;;
let int_xor _A = _A.int_xor;;
let int_shl _A = _A.int_shl;;
let int_shr_u _A = _A.int_shr_u;;
let int_shr_s _A = _A.int_shr_s;;
let int_rotl _A = _A.int_rotl;;
let int_rotr _A = _A.int_rotr;;
let int_eqz _A = _A.int_eqz;;
let int_eq _A = _A.int_eq;;
let int_lt_u _A = _A.int_lt_u;;
let int_lt_s _A = _A.int_lt_s;;
let int_gt_u _A = _A.int_gt_u;;
let int_gt_s _A = _A.int_gt_s;;
let int_le_u _A = _A.int_le_u;;
let int_le_s _A = _A.int_le_s;;
let int_ge_u _A = _A.int_ge_u;;
let int_ge_s _A = _A.int_ge_s;;
let int_of_nata _A = _A.int_of_nata;;
let nat_of_int _A = _A.nat_of_int;;

type 'a wasm_int = {wasm_int_ops_wasm_int : 'a wasm_int_ops};;

let wasm_base_i32 = ({zero_wasm_base = zero_i32} : i32 wasm_base);;

let wasm_int_ops_i32 =
  ({len_wasm_int_ops = len_i32; wasm_base_wasm_int_ops = wasm_base_i32;
     int_clz = int_clz_i32; int_ctz = int_ctz_i32; int_popcnt = int_popcnt_i32;
     int_add = int_add_i32; int_sub = int_sub_i32; int_mul = int_mul_i32;
     int_div_u = int_div_u_i32; int_div_s = int_div_s_i32;
     int_rem_u = int_rem_u_i32; int_rem_s = int_rem_s_i32;
     int_and = int_and_i32; int_or = int_or_i32; int_xor = int_xor_i32;
     int_shl = int_shl_i32; int_shr_u = int_shr_u_i32;
     int_shr_s = int_shr_s_i32; int_rotl = int_rotl_i32;
     int_rotr = int_rotr_i32; int_eqz = int_eqz_i32; int_eq = int_eq_i32;
     int_lt_u = int_lt_u_i32; int_lt_s = int_lt_s_i32; int_gt_u = int_gt_u_i32;
     int_gt_s = int_gt_s_i32; int_le_u = int_le_u_i32; int_le_s = int_le_s_i32;
     int_ge_u = int_ge_u_i32; int_ge_s = int_ge_s_i32;
     int_of_nata = int_of_nat_i32; nat_of_int = nat_of_int_i32}
    : i32 wasm_int_ops);;

let wasm_int_i32 = ({wasm_int_ops_wasm_int = wasm_int_ops_i32} : i32 wasm_int);;

let zero_i64a : i64 = I64_impl_abs Int64.zero;;

let zero_i64 = ({zero = zero_i64a} : i64 zero);;

let rec len_of_i64 uu = nat_of_integer (Z.of_int 64);;

let len0_i64 = ({len_of = len_of_i64} : i64 len0);;

let len_i64 = ({len0_len = len0_i64} : i64 len);;

let rec bit_uint64
  x n = less_nat n (nat_of_integer (Z.of_int 64)) &&
          Uint64.test_bit x (integer_of_nat n);;

let rec uint64
  i = (let ia = Z.logand i (Z.of_string "18446744073709551615") in
        (if bit_integer ia (nat_of_integer (Z.of_int 63))
          then Z.to_int64 (Z.sub ia (Z.of_string "18446744073709551616"))
          else Z.to_int64 ia));;

let rec integer_of_uint64
  n = (if bit_uint64 n (nat_of_integer (Z.of_int 63))
        then Z.logor
               (Z.of_int64
                 (Int64.logand n (uint64 (Z.of_string "9223372036854775807"))))
               (Z.of_string "9223372036854775808")
        else Z.of_int64 n);;

let rec nat_of_uint64 x = nat_of_integer (integer_of_uint64 x);;

let rec nat_of_int_i64 (I64_impl_abs x) = nat_of_uint64 x;;

let rec uint64_of_int i = uint64 (integer_of_int i);;

let rec uint64_of_nat x = comp uint64_of_int int_of_nat x;;

let rec int_popcnt_i64
  (I64_impl_abs x) =
    I64_impl_abs
      (uint64_of_nat
        (fold_atLeastAtMost_nat
          (fun n acc -> (if bit_uint64 x n then plus_nat acc one_nata else acc))
          zero_nat (nat_of_integer (Z.of_int 63)) zero_nat));;

let rec int_of_nat_i64 n = I64_impl_abs (uint64_of_nat n);;

let rec int_shr_u_i64
  (I64_impl_abs x) (I64_impl_abs y) =
    I64_impl_abs
      (Uint64.shiftr x (modulo_integer (integer_of_uint64 y) (Z.of_int 64)));;

let rec int_shr_s_i64
  (I64_impl_abs x) (I64_impl_abs y) =
    I64_impl_abs
      (Uint64.shiftr_signed x
        (modulo_integer (integer_of_uint64 y) (Z.of_int 64)));;

let rec push_bit_uint64
  n x = (if less_nat n (nat_of_integer (Z.of_int 64))
          then Uint64.shiftl x (integer_of_nat n) else Int64.zero);;

let rec drop_bit_uint64
  n x = (if less_nat n (nat_of_integer (Z.of_int 64))
          then Uint64.shiftr x (integer_of_nat n) else Int64.zero);;

let mod0_uint64 _ = failwith "Uint64.mod0_uint64";;

let div0_uint64 _ = failwith "Uint64.div0_uint64";;

let rec uint64_divmod
  x y = (if Uint64.less_eq (uint64 (Z.of_string "9223372036854775808")) y
          then (if Uint64.less x y then (Int64.zero, x)
                 else (Int64.one, Int64.sub x y))
          else (if (Int64.compare y Int64.zero = 0)
                 then (div0_uint64 x, mod0_uint64 x)
                 else (let q =
                         push_bit_uint64 one_nata
                           (Int64.div (drop_bit_uint64 one_nata x) y)
                         in
                       let r = Int64.sub x (Int64.mul q y) in
                        (if Uint64.less_eq y r
                          then (Int64.add q Int64.one, Int64.sub r y)
                          else (q, r)))));;

let rec uint64_mod x y = snd (uint64_divmod x y);;

let rec int_rem_u_i64
  (I64_impl_abs x) (I64_impl_abs y) =
    (if (Int64.compare y Int64.zero = 0) then None
      else Some (I64_impl_abs (uint64_mod x y)));;

let rec int_rem_s_i64
  (I64_impl_abs x) (I64_impl_abs y) =
    (if (Int64.compare y Int64.zero = 0) then None
      else Some (I64_impl_abs (Int64.sub x (Int64.mul (Int64.div x y) y))));;

let rec uint64_div x y = fst (uint64_divmod x y);;

let rec int_div_u_i64
  (I64_impl_abs x) (I64_impl_abs y) =
    (if (Int64.compare y Int64.zero = 0) then None
      else Some (I64_impl_abs (uint64_div x y)));;

let rec int_div_s_i64
  (I64_impl_abs x) (I64_impl_abs y) =
    (if (Int64.compare y Int64.zero = 0) ||
          (Int64.compare x (Int64.neg
                             (uint64
                               (Z.of_string "9223372036854775808"))) = 0) &&
            (Int64.compare y (Int64.neg Int64.one) = 0)
      then None else Some (I64_impl_abs (Int64.div x y)));;

let rec modulo_uint64a
  x y = (if (Int64.compare y Int64.zero = 0) then x else uint64_mod x y);;

let rec divide_uint64a
  x y = (if (Int64.compare y Int64.zero = 0) then Int64.zero
          else uint64_div x y);;

let plus_uint64 = ({plus = Int64.add} : int64 plus);;

let semigroup_add_uint64 =
  ({plus_semigroup_add = plus_uint64} : int64 semigroup_add);;

let cancel_semigroup_add_uint64 =
  ({semigroup_add_cancel_semigroup_add = semigroup_add_uint64} :
    int64 cancel_semigroup_add);;

let ab_semigroup_add_uint64 =
  ({semigroup_add_ab_semigroup_add = semigroup_add_uint64} :
    int64 ab_semigroup_add);;

let minus_uint64 = ({minus = Int64.sub} : int64 minus);;

let cancel_ab_semigroup_add_uint64 =
  ({ab_semigroup_add_cancel_ab_semigroup_add = ab_semigroup_add_uint64;
     cancel_semigroup_add_cancel_ab_semigroup_add = cancel_semigroup_add_uint64;
     minus_cancel_ab_semigroup_add = minus_uint64}
    : int64 cancel_ab_semigroup_add);;

let zero_uint64 = ({zero = Int64.zero} : int64 zero);;

let monoid_add_uint64 =
  ({semigroup_add_monoid_add = semigroup_add_uint64;
     zero_monoid_add = zero_uint64}
    : int64 monoid_add);;

let comm_monoid_add_uint64 =
  ({ab_semigroup_add_comm_monoid_add = ab_semigroup_add_uint64;
     monoid_add_comm_monoid_add = monoid_add_uint64}
    : int64 comm_monoid_add);;

let cancel_comm_monoid_add_uint64 =
  ({cancel_ab_semigroup_add_cancel_comm_monoid_add =
      cancel_ab_semigroup_add_uint64;
     comm_monoid_add_cancel_comm_monoid_add = comm_monoid_add_uint64}
    : int64 cancel_comm_monoid_add);;

let times_uint64 = ({times = Int64.mul} : int64 times);;

let mult_zero_uint64 =
  ({times_mult_zero = times_uint64; zero_mult_zero = zero_uint64} :
    int64 mult_zero);;

let semigroup_mult_uint64 =
  ({times_semigroup_mult = times_uint64} : int64 semigroup_mult);;

let semiring_uint64 =
  ({ab_semigroup_add_semiring = ab_semigroup_add_uint64;
     semigroup_mult_semiring = semigroup_mult_uint64}
    : int64 semiring);;

let semiring_0_uint64 =
  ({comm_monoid_add_semiring_0 = comm_monoid_add_uint64;
     mult_zero_semiring_0 = mult_zero_uint64;
     semiring_semiring_0 = semiring_uint64}
    : int64 semiring_0);;

let semiring_0_cancel_uint64 =
  ({cancel_comm_monoid_add_semiring_0_cancel = cancel_comm_monoid_add_uint64;
     semiring_0_semiring_0_cancel = semiring_0_uint64}
    : int64 semiring_0_cancel);;

let ab_semigroup_mult_uint64 =
  ({semigroup_mult_ab_semigroup_mult = semigroup_mult_uint64} :
    int64 ab_semigroup_mult);;

let comm_semiring_uint64 =
  ({ab_semigroup_mult_comm_semiring = ab_semigroup_mult_uint64;
     semiring_comm_semiring = semiring_uint64}
    : int64 comm_semiring);;

let comm_semiring_0_uint64 =
  ({comm_semiring_comm_semiring_0 = comm_semiring_uint64;
     semiring_0_comm_semiring_0 = semiring_0_uint64}
    : int64 comm_semiring_0);;

let comm_semiring_0_cancel_uint64 =
  ({comm_semiring_0_comm_semiring_0_cancel = comm_semiring_0_uint64;
     semiring_0_cancel_comm_semiring_0_cancel = semiring_0_cancel_uint64}
    : int64 comm_semiring_0_cancel);;

let one_uint64 = ({one = Int64.one} : int64 one);;

let power_uint64 =
  ({one_power = one_uint64; times_power = times_uint64} : int64 power);;

let monoid_mult_uint64 =
  ({semigroup_mult_monoid_mult = semigroup_mult_uint64;
     power_monoid_mult = power_uint64}
    : int64 monoid_mult);;

let numeral_uint64 =
  ({one_numeral = one_uint64; semigroup_add_numeral = semigroup_add_uint64} :
    int64 numeral);;

let semiring_numeral_uint64 =
  ({monoid_mult_semiring_numeral = monoid_mult_uint64;
     numeral_semiring_numeral = numeral_uint64;
     semiring_semiring_numeral = semiring_uint64}
    : int64 semiring_numeral);;

let zero_neq_one_uint64 =
  ({one_zero_neq_one = one_uint64; zero_zero_neq_one = zero_uint64} :
    int64 zero_neq_one);;

let semiring_1_uint64 =
  ({semiring_numeral_semiring_1 = semiring_numeral_uint64;
     semiring_0_semiring_1 = semiring_0_uint64;
     zero_neq_one_semiring_1 = zero_neq_one_uint64}
    : int64 semiring_1);;

let semiring_1_cancel_uint64 =
  ({semiring_0_cancel_semiring_1_cancel = semiring_0_cancel_uint64;
     semiring_1_semiring_1_cancel = semiring_1_uint64}
    : int64 semiring_1_cancel);;

let dvd_uint64 = ({times_dvd = times_uint64} : int64 dvd);;

let comm_monoid_mult_uint64 =
  ({ab_semigroup_mult_comm_monoid_mult = ab_semigroup_mult_uint64;
     monoid_mult_comm_monoid_mult = monoid_mult_uint64;
     dvd_comm_monoid_mult = dvd_uint64}
    : int64 comm_monoid_mult);;

let comm_semiring_1_uint64 =
  ({comm_monoid_mult_comm_semiring_1 = comm_monoid_mult_uint64;
     comm_semiring_0_comm_semiring_1 = comm_semiring_0_uint64;
     semiring_1_comm_semiring_1 = semiring_1_uint64}
    : int64 comm_semiring_1);;

let comm_semiring_1_cancel_uint64 =
  ({comm_semiring_0_cancel_comm_semiring_1_cancel =
      comm_semiring_0_cancel_uint64;
     comm_semiring_1_comm_semiring_1_cancel = comm_semiring_1_uint64;
     semiring_1_cancel_comm_semiring_1_cancel = semiring_1_cancel_uint64}
    : int64 comm_semiring_1_cancel);;

let divide_uint64 = ({divide = divide_uint64a} : int64 divide);;

let modulo_uint64 =
  ({divide_modulo = divide_uint64; dvd_modulo = dvd_uint64;
     modulo = modulo_uint64a}
    : int64 modulo);;

let semiring_modulo_uint64 =
  ({comm_semiring_1_cancel_semiring_modulo = comm_semiring_1_cancel_uint64;
     modulo_semiring_modulo = modulo_uint64}
    : int64 semiring_modulo);;

let semiring_parity_uint64 =
  ({semiring_modulo_semiring_parity = semiring_modulo_uint64} :
    int64 semiring_parity);;

let semiring_bits_uint64 =
  ({semiring_parity_semiring_bits = semiring_parity_uint64; bit = bit_uint64} :
    int64 semiring_bits);;

let rec take_bit_uint64 n a = Int64.logand a (mask_uint64 n)
and semiring_bit_shifts_uint64 () =
  ({semiring_bits_semiring_bit_shifts = semiring_bits_uint64;
     push_bit = push_bit_uint64; drop_bit = drop_bit_uint64;
     take_bit = take_bit_uint64}
    : int64 semiring_bit_shifts)
and semiring_bit_syntax_uint64 () =
  ({semiring_bit_shifts_semiring_bit_syntax = (semiring_bit_shifts_uint64 ())} :
    int64 semiring_bit_syntax)
and mask_uint64
  n = shiftr (semiring_bit_syntax_uint64 ()) (Int64.neg Int64.one)
        (minus_nat (nat_of_integer (Z.of_int 64)) n);;
let semiring_bit_shifts_uint64 = semiring_bit_shifts_uint64 ();;
let semiring_bit_syntax_uint64 = semiring_bit_syntax_uint64 ();;

let rec int_rotr_i64
  (I64_impl_abs x) (I64_impl_abs y) =
    I64_impl_abs
      (let n = nat_of_uint64 (modulo_uint64a y (uint64 (Z.of_int 64))) in
        Int64.logor (drop_bit_uint64 n x)
          (push_bit_uint64 (minus_nat (nat_of_integer (Z.of_int 64)) n)
            (take_bit_uint64 n x)));;

let rec int_rotl_i64
  (I64_impl_abs x) (I64_impl_abs y) =
    I64_impl_abs
      (let n = nat_of_uint64 (modulo_uint64a y (uint64 (Z.of_int 64))) in
        Int64.logor
          (drop_bit_uint64 (minus_nat (nat_of_integer (Z.of_int 64)) n) x)
          (push_bit_uint64 n
            (take_bit_uint64 (minus_nat (nat_of_integer (Z.of_int 64)) n) x)));;

let rec int_lt_u_i64 (I64_impl_abs x) (I64_impl_abs y) = Uint64.less x y;;

let rec msb_uint64 x = Uint64.test_bit x (Z.of_int 63);;

let rec int_lt_s_i64
  (I64_impl_abs x) (I64_impl_abs y) =
    (if msb_uint64 y then msb_uint64 x else true) &&
      (msb_uint64 x && not (msb_uint64 y) || Uint64.less x y);;

let rec int_le_u_i64 (I64_impl_abs x) (I64_impl_abs y) = Uint64.less_eq x y;;

let rec int_le_s_i64
  (I64_impl_abs x) (I64_impl_abs y) =
    (if msb_uint64 y then msb_uint64 x else true) &&
      (msb_uint64 x && not (msb_uint64 y) || Uint64.less_eq x y);;

let rec int_gt_u_i64 (I64_impl_abs x) (I64_impl_abs y) = Uint64.less y x;;

let rec int_gt_s_i64
  (I64_impl_abs x) (I64_impl_abs y) =
    (if msb_uint64 x then msb_uint64 y else true) &&
      (msb_uint64 y && not (msb_uint64 x) || Uint64.less y x);;

let rec int_ge_u_i64 (I64_impl_abs x) (I64_impl_abs y) = Uint64.less_eq y x;;

let rec int_ge_s_i64
  (I64_impl_abs x) (I64_impl_abs y) =
    (if msb_uint64 x then msb_uint64 y else true) &&
      (msb_uint64 y && not (msb_uint64 x) || Uint64.less_eq y x);;

let rec int_xor_i64
  (I64_impl_abs x) (I64_impl_abs y) = I64_impl_abs (Int64.logxor x y);;

let rec int_sub_i64
  (I64_impl_abs x) (I64_impl_abs y) = I64_impl_abs (Int64.sub x y);;

let rec int_shl_i64
  (I64_impl_abs x) (I64_impl_abs y) =
    I64_impl_abs
      (Uint64.shiftl x (modulo_integer (integer_of_uint64 y) (Z.of_int 64)));;

let rec int_mul_i64
  (I64_impl_abs x) (I64_impl_abs y) = I64_impl_abs (Int64.mul x y);;

let rec int_eqz_i64 (I64_impl_abs x) = (Int64.compare x Int64.zero = 0);;

let rec rep_uint64
  x = set_bits_word
        (len_bit0
          (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
        (bit_uint64 x);;

let rec abs_uint64
  x = uint64
        (integer_of_int
          (the_int
            (len_bit0
              (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
            x));;

let rec int_ctz_i64
  (I64_impl_abs x) =
    I64_impl_abs
      (abs_uint64
        (of_nat
          (len_bit0
            (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
          (word_ctz
            (len_bit0
              (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
            (rep_uint64 x))));;

let rec int_clz_i64
  (I64_impl_abs x) =
    I64_impl_abs
      (abs_uint64
        (of_nat
          (len_bit0
            (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
          (word_clz
            (len_bit0
              (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
            (rep_uint64 x))));;

let rec int_and_i64
  (I64_impl_abs x) (I64_impl_abs y) = I64_impl_abs (Int64.logand x y);;

let rec int_add_i64
  (I64_impl_abs x) (I64_impl_abs y) = I64_impl_abs (Int64.add x y);;

let rec int_or_i64
  (I64_impl_abs x) (I64_impl_abs y) = I64_impl_abs (Int64.logor x y);;

let rec int_eq_i64 (I64_impl_abs x) (I64_impl_abs y) = (Int64.compare x y = 0);;

let wasm_base_i64 = ({zero_wasm_base = zero_i64} : i64 wasm_base);;

let wasm_int_ops_i64 =
  ({len_wasm_int_ops = len_i64; wasm_base_wasm_int_ops = wasm_base_i64;
     int_clz = int_clz_i64; int_ctz = int_ctz_i64; int_popcnt = int_popcnt_i64;
     int_add = int_add_i64; int_sub = int_sub_i64; int_mul = int_mul_i64;
     int_div_u = int_div_u_i64; int_div_s = int_div_s_i64;
     int_rem_u = int_rem_u_i64; int_rem_s = int_rem_s_i64;
     int_and = int_and_i64; int_or = int_or_i64; int_xor = int_xor_i64;
     int_shl = int_shl_i64; int_shr_u = int_shr_u_i64;
     int_shr_s = int_shr_s_i64; int_rotl = int_rotl_i64;
     int_rotr = int_rotr_i64; int_eqz = int_eqz_i64; int_eq = int_eq_i64;
     int_lt_u = int_lt_u_i64; int_lt_s = int_lt_s_i64; int_gt_u = int_gt_u_i64;
     int_gt_s = int_gt_s_i64; int_le_u = int_le_u_i64; int_le_s = int_le_s_i64;
     int_ge_u = int_ge_u_i64; int_ge_s = int_ge_s_i64;
     int_of_nata = int_of_nat_i64; nat_of_int = nat_of_int_i64}
    : i64 wasm_int_ops);;

let wasm_int_i64 = ({wasm_int_ops_wasm_int = wasm_int_ops_i64} : i64 wasm_int);;

type mut = T_immut | T_mut;;

let rec equal_muta x0 x1 = match x0, x1 with T_immut, T_mut -> false
                     | T_mut, T_immut -> false
                     | T_mut, T_mut -> true
                     | T_immut, T_immut -> true;;

let equal_mut = ({equal = equal_muta} : mut equal);;

let rec typerep_optiona _A t = Typerep ("Option.option", [typerep _A Type]);;

let rec countable_option _A = (() : ('a option) countable);;

let rec typerep_option _A =
  ({typerep = typerep_optiona _A} : ('a option) typerep);;

let rec heap_option _A =
  ({countable_heap = (countable_option _A.countable_heap);
     typerep_heap = (typerep_option _A.typerep_heap)}
    : ('a option) heap);;

let equal_literal = ({equal = (fun a b -> ((a : string) = b))} : string equal);;

type sx = S | U;;

type binop_i = Add | Sub | Mul | Div of sx | Rem of sx | And | Or | Xor | Shl |
  Shr of sx | Rotl | Rotr;;

type binop_f = Addf | Subf | Mulf | Divf | Min | Max | Copysign;;

type binop = Binop_i of binop_i | Binop_f of binop_f;;

let rec typerep_binopa t = Typerep ("Wasm_Ast.binop", []);;

let typerep_binop = ({typerep = typerep_binopa} : binop typerep);;

type cvtop = Convert | Reinterpret;;

let rec typerep_cvtopa t = Typerep ("Wasm_Ast.cvtop", []);;

let typerep_cvtop = ({typerep = typerep_cvtopa} : cvtop typerep);;

let rec typerep_proda _A _B
  t = Typerep ("Product_Type.prod", [typerep _A Type; typerep _B Type]);;

let rec countable_prod _A _B = (() : ('a * 'b) countable);;

let rec typerep_prod _A _B =
  ({typerep = typerep_proda _A _B} : ('a * 'b) typerep);;

let rec heap_prod _A _B =
  ({countable_heap = (countable_prod _A.countable_heap _B.countable_heap);
     typerep_heap = (typerep_prod _A.typerep_heap _B.typerep_heap)}
    : ('a * 'b) heap);;

let rec equal_unita u v = true;;

let equal_unit = ({equal = equal_unita} : unit equal);;

let rec typerep_unita t = Typerep ("Product_Type.unit", []);;

let countable_unit = (() : unit countable);;

let typerep_unit = ({typerep = typerep_unita} : unit typerep);;

let heap_unit =
  ({countable_heap = countable_unit; typerep_heap = typerep_unit} : unit heap);;

let rec typerep_byte_arraya t = Typerep ("Byte_Array.byte_array", []);;

let countable_byte_array = (() : Bytes.t countable);;

let typerep_byte_array = ({typerep = typerep_byte_arraya} : Bytes.t typerep);;

let heap_byte_array =
  ({countable_heap = countable_byte_array; typerep_heap = typerep_byte_array} :
    Bytes.t heap);;

type 'a global_ext = Global_ext of mut * v * 'a;;

let rec typerep_global_exta _A
  t = Typerep ("Wasm_Ast.global.global_ext", [typerep _A Type]);;

let rec countable_global_ext _A = (() : 'a global_ext countable);;

let rec typerep_global_ext _A =
  ({typerep = typerep_global_exta _A} : 'a global_ext typerep);;

let rec heap_global_ext _A =
  ({countable_heap = (countable_global_ext _A.countable_heap);
     typerep_heap = (typerep_global_ext _A.typerep_heap)}
    : 'a global_ext heap);;

type 'a inst_m_ext =
  Inst_m_ext of tf array * nat array * nat array * nat array * nat array * 'a;;

type shape_vec_i = I8_16 | I16_8 | I32_4 | I64_2;;

type storeop_vec = Store_128 | Store_lane of shape_vec_i * nat;;

type tp_vec = Tp_v8_8 | Tp_v16_4 | Tp_v32_2;;

type loadop_vec = Load_128 | Load_packed_vec of tp_vec * sx | Load_32_zero |
  Load_64_zero | Load_splat of shape_vec_i;;

type shape_vec_f = F32_4 | F64_2;;

type shape_vec = Svi of shape_vec_i | Svf of shape_vec_f;;

type tp_num = Tp_i8 | Tp_i16 | Tp_i32;;

type testop = Eqz;;

type relop_i = Eq | Ne | Lt of sx | Gt of sx | Le of sx | Ge of sx;;

type relop_f = Eqf | Nef | Ltf | Gtf | Lef | Gef;;

type relop = Relop_i of relop_i | Relop_f of relop_f;;

type unop_i = Clz | Ctz | Popcnt;;

type unop_f = Neg | Abs | Ceil | Floor | Trunc | Nearest | Sqrt;;

type unop = Unop_i of unop_i | Unop_f of unop_f | Extend_s of tp_num;;

type sat = Sat | Nonsat;;

type tb = Tbf of nat | Tbv of t option;;

type b_e = Unreachable | Nop | Drop | Select | Block of tb * b_e list |
  Loop of tb * b_e list | If of tb * b_e list * b_e list | Br of nat |
  Br_if of nat | Br_table of nat list * nat | Return | Call of nat |
  Call_indirect of nat | Get_local of nat | Set_local of nat | Tee_local of nat
  | Get_global of nat | Set_global of nat |
  Load of t_num * (tp_num * sx) option * nat * nat |
  Store of t_num * tp_num option * nat * nat |
  Load_vec of loadop_vec * nat * nat |
  Load_lane_vec of shape_vec_i * nat * nat * nat |
  Store_vec of storeop_vec * nat * nat | Current_memory | Grow_memory |
  EConst of v | Unop of t_num * unop | Binop of t_num * binop |
  Testop of t_num * testop | Relop of t_num * relop |
  Cvtop of t_num * cvtop * t_num * (sat * sx) option |
  Unop_vec of V128Wrapper.unop_vec_t | Binop_vec of V128Wrapper.binop_vec_t |
  Ternop_vec of V128Wrapper.ternop_vec_t | Test_vec of V128Wrapper.testop_vec_t
  | Shift_vec of V128Wrapper.shiftop_vec_t | Splat_vec of shape_vec |
  Extract_vec of shape_vec * sx * nat | Replace_vec of shape_vec * nat;;

type cl_m = Func_native of unit inst_m_ext * tf * t list * b_e list |
  Func_host of tf * host
and 'a s_m_ext =
  S_m_ext of
    cl_m array * ((nat option) array * nat option) array *
      (Bytes.t * nat option) array * unit global_ext array * 'a
and host =
  Abs_host_m of
    (unit s_m_ext * v list -> (unit -> ((unit s_m_ext * v list) option)));;

let rec typerep_cl_ma t = Typerep ("Wasm_Interpreter_Monad_Config.cl_m", []);;

let countable_cl_m = (() : cl_m countable);;

let typerep_cl_m = ({typerep = typerep_cl_ma} : cl_m typerep);;

let heap_cl_m =
  ({countable_heap = countable_cl_m; typerep_heap = typerep_cl_m} : cl_m heap);;

type 'a inst_ext =
  Inst_ext of tf list * nat list * nat list * nat list * nat list * 'a;;

type 'a f_ext = F_ext of v list * unit inst_ext * 'a;;

type e = Basic of b_e | Trap | Invoke of nat | Label of nat * e list * e list |
  Frame of nat * unit f_ext * e list | Init_mem of nat * uint8 list |
  Init_tab of nat * nat list;;

type 'a seq = Empty | Insert of 'a * 'a pred | Join of 'a pred * 'a seq
and 'a pred = Seq of (unit -> 'a seq);;

type v_ext = Ext_func of nat | Ext_tab of nat | Ext_mem of nat |
  Ext_glob of nat;;

type 'a tg_ext = Tg_ext of mut * t * 'a;;

type 'a limit_t_ext = Limit_t_ext of nat * nat option * 'a;;

type imp_desc = Imp_func of nat | Imp_tab of unit limit_t_ext |
  Imp_mem of unit limit_t_ext | Imp_glob of unit tg_ext;;

type 'a module_import_ext =
  Module_import_ext of string * string * imp_desc * 'a;;

type 'a module_export_ext = Module_export_ext of string * v_ext * 'a;;

type 'a module_glob_ext = Module_glob_ext of unit tg_ext * b_e list * 'a;;

type 'a module_elem_ext = Module_elem_ext of nat * b_e list * nat list * 'a;;

type 'a module_data_ext = Module_data_ext of nat * b_e list * uint8 list * 'a;;

type 'a m_ext =
  M_ext of
    tf list * (nat * (t list * b_e list)) list * unit limit_t_ext list *
      unit limit_t_ext list * unit module_glob_ext list *
      unit module_elem_ext list * unit module_data_ext list * nat option *
      unit module_import_ext list * unit module_export_ext list * 'a;;

type res_error = Error_invalid of string | Error_invariant of string |
  Error_exhaustion of string;;

type res = RCrash of res_error | RTrap of string | RValue of v list;;

type extern_t = Te_func of tf | Te_tab of unit limit_t_ext |
  Te_mem of unit limit_t_ext | Te_glob of unit tg_ext;;

type ct = TAny | TSome of t;;

type redex = Redex of v list * e list * b_e list;;

type res_step = Res_crash of res_error | Res_trap of string | Step_normal;;

type label_context = Label_context of v list * b_e list * nat * b_e list;;

type checker_type = TopType of ct list | Typea of t list | Bot;;

type 'a t_context_ext =
  T_context_ext of
    tf list * tf list * unit tg_ext list * unit limit_t_ext list *
      unit limit_t_ext list * t list * (t list) list * (t list) option * 'a;;

type res_inst_m = RI_crash_m of res_error | RI_trap_m of string |
  RI_res_m of unit inst_m_ext * unit module_export_ext list * e list;;

type frame_context_m =
  Frame_context_m of
    redex * label_context list * nat * v array * unit inst_m_ext;;

type config_m =
  Config_m of nat * unit s_m_ext * frame_context_m * frame_context_m list;;

let rec nth
  x0 n = match x0, n with [], n -> failwith "nth"
    | x :: xs, n ->
        (if equal_nat n zero_nat then x else nth xs (minus_nat n one_nata));;

let rec zip xs ys = match xs, ys with x :: xs, y :: ys -> (x, y) :: zip xs ys
              | xs, [] -> []
              | [], ys -> [];;

let rec len _A
  a = (fun () ->
        (let i = (fun () -> Z.of_int (Array.length a)) () in
          nat_of_integer i));;

let rec newa _A
  = comp (fun a b -> (fun () -> Array.make (Z.to_int a) b)) integer_of_nat;;

let rec array_nth _A
  a n = (fun () -> Array.get a (Z.to_int (integer_of_nat n)));;

let rec upd _A
  i x a =
    (fun () ->
      (let _ = (fun () -> Array.set a (Z.to_int (integer_of_nat i)) x) () in
        a));;

let rec drop
  n x1 = match n, x1 with n, [] -> []
    | n, x :: xs ->
        (if equal_nat n zero_nat then x :: xs
          else drop (minus_nat n one_nata) xs);;

let rec find uu x1 = match uu, x1 with uu, [] -> None
               | p, x :: xs -> (if p x then Some x else find p xs);;

let rec null = function [] -> true
               | x :: xs -> false;;

let rec last (x :: xs) = (if null xs then x else last xs);;

let rec take_tr
  n x1 acc_r = match n, x1, acc_r with n, [], acc_r -> rev acc_r
    | n, x :: xs, acc_r ->
        (if equal_nat n zero_nat then rev acc_r
          else take_tr (minus_nat n one_nata) xs (x :: acc_r));;

let rec take n xs = take_tr n xs [];;

let rec map_option f x1 = match f, x1 with f, None -> None
                     | f, Some x2 -> Some (f x2);;

let rec those
  = function [] -> Some []
    | x :: xs ->
        (match x with None -> None
          | Some y -> map_option (fun a -> y :: a) (those xs));;

let rec concat xss = foldr (fun a b -> a @ b) xss [];;

let rec member _A x0 y = match x0, y with [], y -> false
                    | x :: xs, y -> eq _A x y || member _A xs y;;

let rec distinct _A = function [] -> true
                      | x :: xs -> not (member _A xs x) && distinct _A xs;;

let ki64 : nat = nat_of_integer (Z.of_int 65536);;

let rec replicate_tr
  n x acc =
    (if equal_nat n zero_nat then acc
      else replicate_tr (minus_nat n one_nata) x (x :: acc));;

let rec replicate n x = replicate_tr n x [];;

let rec is_none = function Some x -> false
                  | None -> true;;

let rec bind (Seq g) f = Seq (fun _ -> apply f (g ()))
and apply f x1 = match f, x1 with f, Empty -> Empty
            | f, Insert (x, p) -> Join (f x, Join (bind p f, Empty))
            | f, Join (p, xq) -> Join (bind p f, apply f xq);;

let rec blit _A
  uu uv uw ux l =
    (if equal_nat l zero_nat then (fun () -> ())
      else (fun () ->
             (let x = array_nth _A uu uv () in
              let _ = upd _A ux x uw () in
               blit _A uu (plus_nat uv one_nata) uw (plus_nat ux one_nata)
                 (minus_nat l one_nata) ())));;

let rec map_filter
  f x1 = match f, x1 with f, [] -> []
    | f, x :: xs ->
        (match f x with None -> map_filter f xs
          | Some y -> y :: map_filter f xs);;

let rec eval _A (Seq f) = membera _A (f ())
and membera _A xa0 x = match xa0, x with Empty, x -> false
                 | Insert (y, p), x -> eq _A x y || eval _A p x
                 | Join (p, xq), x -> eval _A p x || membera _A xq x;;

let rec holds p = eval equal_unit p ();;

let rec msbyte bs = last bs;;

let bot_pred : 'a pred = Seq (fun _ -> Empty);;

let rec single x = Seq (fun _ -> Insert (x, bot_pred));;

let rec abs_uint8
  x = uint8 (integer_of_int
              (the_int (len_bit0 (len_bit0 (len_bit0 len_num1))) x));;

let rec rep_uint8
  x = set_bits_word (len_bit0 (len_bit0 (len_bit0 len_num1))) (bit_uint8 x);;

let rec typeof_vec v = (let ConstVec128 _ = v in T_v128);;

let rec typeof_num
  v = (match v with ConstInt32 _ -> T_i32 | ConstInt64 _ -> T_i64
        | ConstFloat32 _ -> T_f32 | ConstFloat64 _ -> T_f64);;

let rec typeof
  v = (match v with V_num v_n -> T_num (typeof_num v_n)
        | V_vec v_v -> T_vec (typeof_vec v_v));;

let rec g_val (Global_ext (g_mut, g_val, more)) = g_val;;

let rec g_mut (Global_ext (g_mut, g_val, more)) = g_mut;;

let rec tg_mut (Tg_ext (tg_mut, tg_t, more)) = tg_mut;;

let rec tg_t (Tg_ext (tg_mut, tg_t, more)) = tg_t;;

let rec glob_typing
  g tg =
    equal_muta (tg_mut tg) (g_mut g) && equal_ta (tg_t tg) (typeof (g_val g));;

let rec signed_cast _B _A
  w = Word (take_bit_int (len_of _A.len0_len Type) (the_signed_int _B w));;

let rec adjunct p x1 = match p, x1 with p, Empty -> Join (p, Empty)
                  | p, Insert (x, q) -> Insert (x, sup_pred q p)
                  | p, Join (q, xq) -> Join (q, adjunct p xq)
and sup_pred
  (Seq f) (Seq g) =
    Seq (fun _ ->
          (match f () with Empty -> g ()
            | Insert (x, p) -> Insert (x, sup_pred p (Seq g))
            | Join (p, xq) -> adjunct (Seq g) (Join (p, xq))));;

let rec if_pred b = (if b then single () else bot_pred);;

let rec msb_uint8 x = uint8_test_bit x (Z.of_int 7);;

let rec msb_byte x = msb_uint8 x;;

let rec dvd (_A1, _A2)
  a b = eq _A1
          (modulo _A2.semiring_modulo_semidom_modulo.modulo_semiring_modulo b a)
          (zero _A2.algebraic_semidom_semidom_modulo.semidom_divide_algebraic_semidom.semidom_semidom_divide.comm_semiring_1_cancel_semidom.comm_semiring_1_comm_semiring_1_cancel.semiring_1_comm_semiring_1.semiring_0_semiring_1.mult_zero_semiring_0.zero_mult_zero);;

let rec bin_split
  n w = (if equal_nat n zero_nat then (w, zero_inta)
          else (let (w1, w2) =
                  bin_split (minus_nat n one_nata)
                    (divide_inta w (Int_of_integer (Z.of_int 2)))
                  in
                 (w1, plus_inta
                        (of_bool zero_neq_one_int
                          (not (dvd (equal_int, semidom_modulo_int)
                                 (Int_of_integer (Z.of_int 2)) w)))
                        (times_inta (Int_of_integer (Z.of_int 2)) w2))));;

let rec list_all p x1 = match p, x1 with p, [] -> true
                   | p, x :: xs -> p x && list_all p xs;;

let rec integer_of_uint8
  n = (if bit_uint8 n (nat_of_integer (Z.of_int 7))
        then Z.logor
               (integer_of_uint8_signed (and_uint8 n (uint8 (Z.of_int 127))))
               (Z.of_int 128)
        else integer_of_uint8_signed n)
and integer_of_uint8_signed
  n = (if bit_uint8 n (nat_of_integer (Z.of_int 7))
        then failwith "undefined" integer_of_uint8 n
        else integer_of_int
               (the_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                 (rep_uint8 n)));;

let rec nat_of_uint8 x = nat_of_integer (integer_of_uint8 x);;

let rec uint8_of_int i = uint8 (integer_of_int i);;

let rec uint8_of_nat x = comp uint8_of_int int_of_nat x;;

let rec pred_option p x1 = match p, x1 with p, Some a -> p a
                      | p, None -> true;;

let rec l_min (Limit_t_ext (l_min, l_max, more)) = l_min;;

let rec l_max (Limit_t_ext (l_min, l_max, more)) = l_max;;

let rec limits_compat
  lt1 lt2 =
    less_eq_nat (l_min lt2) (l_min lt1) &&
      pred_option
        (fun lt2_the ->
          (match l_max lt1 with None -> false
            | Some lt1_the -> less_eq_nat lt1_the lt2_the))
        (l_max lt2);;

let zero_byte : uint8 = zero_uint8a;;

let rec ocaml_int64_to_isabelle_int64
  n = I64_impl_abs (uint64 (LibAux.z_of_uint64 n));;

let rec isabelle_i64_trunc_sat_u_f64
  f = ocaml_int64_to_isabelle_int64 (I64Wrapper_convert.trunc_sat_u_f64 f);;

let rec ui64_trunc_sat_f64 x = isabelle_i64_trunc_sat_u_f64 x;;

let rec isabelle_i64_trunc_sat_u_f32
  f = ocaml_int64_to_isabelle_int64 (I64Wrapper_convert.trunc_sat_u_f32 f);;

let rec ui64_trunc_sat_f32 x = isabelle_i64_trunc_sat_u_f32 x;;

let rec isabelle_i64_trunc_sat_s_f64
  f = ocaml_int64_to_isabelle_int64 (I64Wrapper_convert.trunc_sat_s_f64 f);;

let rec si64_trunc_sat_f64 x = isabelle_i64_trunc_sat_s_f64 x;;

let rec isabelle_i64_trunc_sat_s_f32
  f = ocaml_int64_to_isabelle_int64 (I64Wrapper_convert.trunc_sat_s_f32 f);;

let rec si64_trunc_sat_f32 x = isabelle_i64_trunc_sat_s_f32 x;;

let rec isabelle_i64_trunc_u_f64
  f = map_option ocaml_int64_to_isabelle_int64
        (I64Wrapper_convert.trunc_u_f64 f);;

let rec ui64_trunc_f64 x = isabelle_i64_trunc_u_f64 x;;

let rec isabelle_i64_trunc_u_f32
  f = map_option ocaml_int64_to_isabelle_int64
        (I64Wrapper_convert.trunc_u_f32 f);;

let rec ui64_trunc_f32 x = isabelle_i64_trunc_u_f32 x;;

let rec isabelle_i64_trunc_s_f64
  f = map_option ocaml_int64_to_isabelle_int64
        (I64Wrapper_convert.trunc_s_f64 f);;

let rec si64_trunc_f64 x = isabelle_i64_trunc_s_f64 x;;

let rec isabelle_i64_trunc_s_f32
  f = map_option ocaml_int64_to_isabelle_int64
        (I64Wrapper_convert.trunc_s_f32 f);;

let rec si64_trunc_f32 x = isabelle_i64_trunc_s_f32 x;;

let rec wasm_extend_u
  (I32_impl_abs x) = I64_impl_abs (uint64 (integer_of_uint32 x));;

let rec wasm_extend_s
  (I32_impl_abs x) =
    I64_impl_abs
      (abs_uint64
        (signed_cast
          (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
          (len_bit0
            (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
          (rep_uint32 x)));;

let rec cvt_i64
  sat_sx v =
    (match v
      with ConstInt32 c ->
        (match sat_sx with None -> None | Some (_, S) -> Some (wasm_extend_s c)
          | Some (_, U) -> Some (wasm_extend_u c))
      | ConstInt64 _ -> None
      | ConstFloat32 c ->
        (match sat_sx with None -> None
          | Some (Sat, S) -> Some (si64_trunc_sat_f32 c)
          | Some (Sat, U) -> Some (ui64_trunc_sat_f32 c)
          | Some (Nonsat, S) -> si64_trunc_f32 c
          | Some (Nonsat, U) -> ui64_trunc_f32 c)
      | ConstFloat64 c ->
        (match sat_sx with None -> None
          | Some (Sat, S) -> Some (si64_trunc_sat_f64 c)
          | Some (Sat, U) -> Some (ui64_trunc_sat_f64 c)
          | Some (Nonsat, S) -> si64_trunc_f64 c
          | Some (Nonsat, U) -> ui64_trunc_f64 c));;

let rec ocaml_int32_to_isabelle_int32
  n = I32_impl_abs (uint32 (LibAux.z_of_uint32 n));;

let rec isabelle_i32_trunc_sat_u_f64
  f = ocaml_int32_to_isabelle_int32 (I32Wrapper_convert.trunc_sat_u_f64 f);;

let rec ui32_trunc_sat_f64 x = isabelle_i32_trunc_sat_u_f64 x;;

let rec isabelle_i32_trunc_sat_u_f32
  f = ocaml_int32_to_isabelle_int32 (I32Wrapper_convert.trunc_sat_u_f32 f);;

let rec ui32_trunc_sat_f32 x = isabelle_i32_trunc_sat_u_f32 x;;

let rec isabelle_i32_trunc_sat_s_f64
  f = ocaml_int32_to_isabelle_int32 (I32Wrapper_convert.trunc_sat_s_f64 f);;

let rec si32_trunc_sat_f64 x = isabelle_i32_trunc_sat_s_f64 x;;

let rec isabelle_i32_trunc_sat_s_f32
  f = ocaml_int32_to_isabelle_int32 (I32Wrapper_convert.trunc_sat_s_f32 f);;

let rec si32_trunc_sat_f32 x = isabelle_i32_trunc_sat_s_f32 x;;

let rec isabelle_i32_trunc_u_f64
  f = map_option ocaml_int32_to_isabelle_int32
        (I32Wrapper_convert.trunc_u_f64 f);;

let rec ui32_trunc_f64 x = isabelle_i32_trunc_u_f64 x;;

let rec isabelle_i32_trunc_u_f32
  f = map_option ocaml_int32_to_isabelle_int32
        (I32Wrapper_convert.trunc_u_f32 f);;

let rec ui32_trunc_f32 x = isabelle_i32_trunc_u_f32 x;;

let rec isabelle_i32_trunc_s_f64
  f = map_option ocaml_int32_to_isabelle_int32
        (I32Wrapper_convert.trunc_s_f64 f);;

let rec si32_trunc_f64 x = isabelle_i32_trunc_s_f64 x;;

let rec isabelle_i32_trunc_s_f32
  f = map_option ocaml_int32_to_isabelle_int32
        (I32Wrapper_convert.trunc_s_f32 f);;

let rec si32_trunc_f32 x = isabelle_i32_trunc_s_f32 x;;

let rec wasm_wrap
  (I64_impl_abs x) = I32_impl_abs (uint32 (integer_of_uint64 x));;

let rec cvt_i32
  sat_sx v =
    (match v with ConstInt32 _ -> None | ConstInt64 c -> Some (wasm_wrap c)
      | ConstFloat32 c ->
        (match sat_sx with None -> None
          | Some (Sat, S) -> Some (si32_trunc_sat_f32 c)
          | Some (Sat, U) -> Some (ui32_trunc_sat_f32 c)
          | Some (Nonsat, S) -> si32_trunc_f32 c
          | Some (Nonsat, U) -> ui32_trunc_f32 c)
      | ConstFloat64 c ->
        (match sat_sx with None -> None
          | Some (Sat, S) -> Some (si32_trunc_sat_f64 c)
          | Some (Sat, U) -> Some (ui32_trunc_sat_f64 c)
          | Some (Nonsat, S) -> si32_trunc_f64 c
          | Some (Nonsat, U) -> ui32_trunc_f64 c));;

let rec i64_impl_rep (I64_impl_abs x) = x;;

let rec isabelle_int64_to_ocaml_int64
  n = LibAux.uint64_of_z (integer_of_uint64 (i64_impl_rep n));;

let rec f64_convert_u_isabelle_i64
  i = F64Wrapper_convert.convert_u_i64 (isabelle_int64_to_ocaml_int64 i);;

let rec f64_convert_ui64 x = f64_convert_u_isabelle_i64 x;;

let rec i32_impl_rep (I32_impl_abs x) = x;;

let rec isabelle_int32_to_ocaml_int32
  n = LibAux.uint32_of_z (integer_of_uint32 (i32_impl_rep n));;

let rec f64_convert_u_isabelle_i32
  i = F64Wrapper_convert.convert_u_i32 (isabelle_int32_to_ocaml_int32 i);;

let rec f64_convert_ui32 x = f64_convert_u_isabelle_i32 x;;

let rec f64_convert_s_isabelle_i64
  i = F64Wrapper_convert.convert_s_i64 (isabelle_int64_to_ocaml_int64 i);;

let rec f64_convert_si64 x = f64_convert_s_isabelle_i64 x;;

let rec f64_convert_s_isabelle_i32
  i = F64Wrapper_convert.convert_s_i32 (isabelle_int32_to_ocaml_int32 i);;

let rec f64_convert_si32 x = f64_convert_s_isabelle_i32 x;;

let rec cvt_f64
  sat_sx v =
    (match v
      with ConstInt32 c ->
        (match sat_sx with None -> None
          | Some (_, S) -> Some (f64_convert_si32 c)
          | Some (_, U) -> Some (f64_convert_ui32 c))
      | ConstInt64 c ->
        (match sat_sx with None -> None
          | Some (_, S) -> Some (f64_convert_si64 c)
          | Some (_, U) -> Some (f64_convert_ui64 c))
      | ConstFloat32 c -> Some ((F64Wrapper_convert.promote_f32) c)
      | ConstFloat64 _ -> None);;

let rec f32_convert_u_isabelle_i64
  i = F32Wrapper_convert.convert_u_i64 (isabelle_int64_to_ocaml_int64 i);;

let rec f32_convert_ui64 x = f32_convert_u_isabelle_i64 x;;

let rec f32_convert_u_isabelle_i32
  i = F32Wrapper_convert.convert_u_i32 (isabelle_int32_to_ocaml_int32 i);;

let rec f32_convert_ui32 x = f32_convert_u_isabelle_i32 x;;

let rec f32_convert_s_isabelle_i64
  i = F32Wrapper_convert.convert_s_i64 (isabelle_int64_to_ocaml_int64 i);;

let rec f32_convert_si64 x = f32_convert_s_isabelle_i64 x;;

let rec f32_convert_s_isabelle_i32
  i = F32Wrapper_convert.convert_s_i32 (isabelle_int32_to_ocaml_int32 i);;

let rec f32_convert_si32 x = f32_convert_s_isabelle_i32 x;;

let rec cvt_f32
  sat_sx v =
    (match v
      with ConstInt32 c ->
        (match sat_sx with None -> None
          | Some (_, S) -> Some (f32_convert_si32 c)
          | Some (_, U) -> Some (f32_convert_ui32 c))
      | ConstInt64 c ->
        (match sat_sx with None -> None
          | Some (_, S) -> Some (f32_convert_si64 c)
          | Some (_, U) -> Some (f32_convert_ui64 c))
      | ConstFloat32 _ -> None
      | ConstFloat64 c -> Some ((F32Wrapper_convert.demote_f64) c));;

let rec cvt
  t sat_sx v =
    (match t
      with T_i32 ->
        (match cvt_i32 sat_sx v with None -> None
          | Some c -> Some (ConstInt32 c))
      | T_i64 ->
        (match cvt_i64 sat_sx v with None -> None
          | Some c -> Some (ConstInt64 c))
      | T_f32 ->
        (match cvt_f32 sat_sx v with None -> None
          | Some c -> Some (ConstFloat32 c))
      | T_f64 ->
        (match cvt_f64 sat_sx v with None -> None
          | Some c -> Some (ConstFloat64 c)));;

let rec select_return_top
  ts ct1 x2 = match ts, ct1, x2 with
    ts, ct1, TAny ->
      TopType
        (take (minus_nat (size_list ts) (nat_of_integer (Z.of_int 3))) ts @
          [ct1])
    | ts, TAny, TSome v ->
        TopType
          (take (minus_nat (size_list ts) (nat_of_integer (Z.of_int 3))) ts @
            [TSome v])
    | ts, TSome t1, TSome t2 ->
        (if equal_ta t1 t2
          then TopType
                 (take (minus_nat (size_list ts) (nat_of_integer (Z.of_int 3)))
                    ts @
                   [TSome t1])
          else Bot);;

let rec to_ct_list ts = map (fun a -> TSome a) ts;;

let rec produce
  uu uv = match uu, uv with
    TopType tsa, Typea ts -> TopType (tsa @ to_ct_list ts)
    | Typea tsa, Typea ts -> Typea (tsa @ ts)
    | Typea tsa, TopType ts -> TopType ts
    | TopType tsa, TopType ts -> TopType ts
    | Typea v, Bot -> Bot
    | Bot, uv -> Bot
    | uu, Bot -> Bot;;

let rec ct_compat x0 uu = match x0, uu with TSome ta, TSome t -> equal_ta ta t
                    | TAny, uu -> true
                    | TSome v, TAny -> true;;

let rec ct_prefix
  x0 xs = match x0, xs with x :: xs, y :: ys -> ct_compat x y && ct_prefix xs ys
    | x :: xs, [] -> false
    | [], xs -> true;;

let rec ct_suffix xs ys = ct_prefix (rev xs) (rev ys);;

let rec consume
  x0 cons = match x0, cons with
    Typea ts, cons ->
      (if ct_suffix cons (to_ct_list ts)
        then Typea (take (minus_nat (size_list ts) (size_list cons)) ts)
        else Bot)
    | TopType cts, cons ->
        (if ct_suffix cons cts
          then TopType (take (minus_nat (size_list cts) (size_list cons)) cts)
          else (if ct_suffix cts cons then TopType [] else Bot))
    | Bot, uv -> Bot;;

let rec type_update
  curr_type cons prods = produce (consume curr_type cons) prods;;

let rec type_update_select
  = function
    Typea ts ->
      (if less_eq_nat (nat_of_integer (Z.of_int 3)) (size_list ts) &&
            equal_ta
              (nth ts (minus_nat (size_list ts) (nat_of_integer (Z.of_int 2))))
              (nth ts (minus_nat (size_list ts) (nat_of_integer (Z.of_int 3))))
        then consume (Typea ts) [TAny; TSome (T_num T_i32)] else Bot)
    | TopType ts ->
        (if equal_nat (size_list ts) zero_nat then TopType [TAny]
          else (if equal_nat (minus_nat (size_list ts) one_nata) zero_nat
                 then type_update (TopType ts) [TSome (T_num T_i32)]
                        (TopType [TAny])
                 else (if equal_nat
                            (minus_nat (minus_nat (size_list ts) one_nata)
                              one_nata)
                            zero_nat
                        then consume (TopType ts) [TSome (T_num T_i32)]
                        else type_update (TopType ts)
                               [TAny; TAny; TSome (T_num T_i32)]
                               (select_return_top ts
                                 (nth ts
                                   (minus_nat (size_list ts)
                                     (nat_of_integer (Z.of_int 2))))
                                 (nth ts
                                   (minus_nat (size_list ts)
                                     (nat_of_integer (Z.of_int 3))))))))
    | Bot -> Bot;;

let rec tp_num_length
  tp = (match tp with Tp_i8 -> one_nata | Tp_i16 -> nat_of_integer (Z.of_int 2)
         | Tp_i32 -> nat_of_integer (Z.of_int 4));;

let rec t_num_length
  t = (match t with T_i32 -> nat_of_integer (Z.of_int 4)
        | T_i64 -> nat_of_integer (Z.of_int 8)
        | T_f32 -> nat_of_integer (Z.of_int 4)
        | T_f64 -> nat_of_integer (Z.of_int 8));;

let rec is_int_t_num
  t = (match t with T_i32 -> true | T_i64 -> true | T_f32 -> false
        | T_f64 -> false);;

let rec load_store_t_bounds
  a tp t =
    (match tp
      with None ->
        less_eq_nat (power power_nat (nat_of_integer (Z.of_int 2)) a)
          (t_num_length t)
      | Some tpa ->
        less_eq_nat (power power_nat (nat_of_integer (Z.of_int 2)) a)
          (tp_num_length tpa) &&
          (less_nat (tp_num_length tpa) (t_num_length t) && is_int_t_num t));;

let rec vec_i_length
  sv = (match sv with I8_16 -> one_nata | I16_8 -> nat_of_integer (Z.of_int 2)
         | I32_4 -> nat_of_integer (Z.of_int 4)
         | I64_2 -> nat_of_integer (Z.of_int 8));;

let rec t_vec_length t = (let T_v128 = t in nat_of_integer (Z.of_int 16));;

let rec vec_i_num
  sv = (match sv with I8_16 -> nat_of_integer (Z.of_int 16)
         | I16_8 -> nat_of_integer (Z.of_int 8)
         | I32_4 -> nat_of_integer (Z.of_int 4)
         | I64_2 -> nat_of_integer (Z.of_int 2));;

let rec store_vec_t_bounds
  sv a =
    (match sv
      with Store_128 ->
        less_eq_nat (power power_nat (nat_of_integer (Z.of_int 2)) a)
          (t_vec_length T_v128)
      | Store_lane (svi, i) ->
        less_nat i (vec_i_num svi) &&
          less_eq_nat (power power_nat (nat_of_integer (Z.of_int 2)) a)
            (vec_i_length svi));;

let rec is_float_t_num
  t = (match t with T_i32 -> false | T_i64 -> false | T_f32 -> true
        | T_f64 -> true);;

let rec relop_t_num_agree
  relop t =
    (match relop with Relop_i _ -> is_int_t_num t
      | Relop_f _ -> is_float_t_num t);;

let rec tp_vec_length
  tp = (match tp with Tp_v8_8 -> one_nata
         | Tp_v16_4 -> nat_of_integer (Z.of_int 2)
         | Tp_v32_2 -> nat_of_integer (Z.of_int 4));;

let rec tp_vec_num
  tp = (match tp with Tp_v8_8 -> nat_of_integer (Z.of_int 8)
         | Tp_v16_4 -> nat_of_integer (Z.of_int 4)
         | Tp_v32_2 -> nat_of_integer (Z.of_int 2));;

let rec load_vec_t_bounds
  lv a =
    (match lv
      with Load_128 ->
        less_eq_nat (power power_nat (nat_of_integer (Z.of_int 2)) a)
          (t_vec_length T_v128)
      | Load_packed_vec (tp, _) ->
        less_eq_nat (power power_nat (nat_of_integer (Z.of_int 2)) a)
          (times_nata (tp_vec_length tp) (tp_vec_num tp))
      | Load_32_zero ->
        less_eq_nat (power power_nat (nat_of_integer (Z.of_int 2)) a)
          (t_vec_length T_v128)
      | Load_64_zero ->
        less_eq_nat (power power_nat (nat_of_integer (Z.of_int 2)) a)
          (t_vec_length T_v128)
      | Load_splat svi ->
        less_eq_nat (power power_nat (nat_of_integer (Z.of_int 2)) a)
          (vec_i_length svi));;

let rec binop_t_num_agree
  binop t =
    (match binop with Binop_i _ -> is_int_t_num t
      | Binop_f _ -> is_float_t_num t);;

let rec unop_t_num_agree
  unop t =
    (match unop with Unop_i _ -> is_int_t_num t | Unop_f _ -> is_float_t_num t
      | Extend_s tp ->
        is_int_t_num t && less_nat (tp_num_length tp) (t_num_length t));;

let rec label_update
  labela
    (T_context_ext
      (types_t, func_t, global, table, memory, local, label, return, more))
    = T_context_ext
        (types_t, func_t, global, table, memory, local, labela label, return,
          more);;

let rec equal_sx x0 x1 = match x0, x1 with S, U -> false
                   | U, S -> false
                   | U, U -> true
                   | S, S -> true;;

let rec c_types_agree
  x0 ts = match x0, ts with Typea tsa, ts -> equal_list equal_t tsa ts
    | TopType tsa, ts -> ct_suffix tsa (to_ct_list ts)
    | Bot, uu -> false;;

let rec option_projl x = map_option fst x;;

let rec types_t
  (T_context_ext
    (types_t, func_t, global, table, memory, local, label, return, more))
    = types_t;;

let rec convert_cond
  t1 t2 sat_sx =
    not (equal_t_num t1 t2) &&
      equal_bool (is_none sat_sx)
        (is_float_t_num t1 && is_float_t_num t2 ||
          is_int_t_num t1 &&
            (is_int_t_num t2 && less_nat (t_num_length t1) (t_num_length t2)));;

let rec vec_f_length
  sv = (match sv with F32_4 -> nat_of_integer (Z.of_int 4)
         | F64_2 -> nat_of_integer (Z.of_int 8));;

let rec vec_length
  sv = (match sv with Svi a -> vec_i_length a | Svf a -> vec_f_length a);;

let rec vec_lane_t
  sv = (match sv with Svi I8_16 -> T_i32 | Svi I16_8 -> T_i32
         | Svi I32_4 -> T_i32 | Svi I64_2 -> T_i64 | Svf F32_4 -> T_f32
         | Svf F64_2 -> T_f64);;

let rec return
  (T_context_ext
    (types_t, func_t, global, table, memory, local, label, return, more))
    = return;;

let rec memory
  (T_context_ext
    (types_t, func_t, global, table, memory, local, label, return, more))
    = memory;;

let rec global
  (T_context_ext
    (types_t, func_t, global, table, memory, local, label, return, more))
    = global;;

let rec func_t
  (T_context_ext
    (types_t, func_t, global, table, memory, local, label, return, more))
    = func_t;;

let rec table
  (T_context_ext
    (types_t, func_t, global, table, memory, local, label, return, more))
    = table;;

let rec local
  (T_context_ext
    (types_t, func_t, global, table, memory, local, label, return, more))
    = local;;

let rec label
  (T_context_ext
    (types_t, func_t, global, table, memory, local, label, return, more))
    = label;;

let rec vec_f_num
  sv = (match sv with F32_4 -> nat_of_integer (Z.of_int 4)
         | F64_2 -> nat_of_integer (Z.of_int 2));;

let rec vec_num
  sv = (match sv with Svi a -> vec_i_num a | Svf a -> vec_f_num a);;

let rec tb_tf_t
  c tb =
    (match tb
      with Tbf i ->
        (let tfs = types_t c in
          (if less_nat i (size_list tfs) then Some (nth tfs i) else None))
      | Tbv None -> Some (Tf ([], [])) | Tbv (Some t) -> Some (Tf ([], [t])));;

let rec same_lab_h
  x0 uu ts = match x0, uu, ts with [], uu, ts -> Some ts
    | i :: is, lab_c, ts ->
        (if less_eq_nat (size_list lab_c) i then None
          else (if equal_list equal_t (nth lab_c i) ts
                 then same_lab_h is lab_c (nth lab_c i) else None));;

let rec same_lab
  x0 lab_c = match x0, lab_c with [], lab_c -> None
    | i :: is, lab_c ->
        (if less_eq_nat (size_list lab_c) i then None
          else same_lab_h is lab_c (nth lab_c i));;

let rec is_mut tg = equal_muta (tg_mut tg) T_mut;;

let rec check
  c es ts =
    (match es with [] -> ts
      | e :: esa ->
        (match ts with TopType _ -> check c esa (check_single c e ts)
          | Typea _ -> check c esa (check_single c e ts) | Bot -> Bot))
and b_e_type_checker
  c es (Tf (tn, tm)) = c_types_agree (check c es (Typea tn)) tm
and check_single
  c x1 ts = match c, x1, ts with
    c, EConst v, ts -> type_update ts [] (Typea [typeof v])
    | c, Unop (t, op), ts ->
        (if unop_t_num_agree op t
          then type_update ts [TSome (T_num t)] (Typea [T_num t]) else Bot)
    | c, Binop (t, op), ts ->
        (if binop_t_num_agree op t
          then type_update ts [TSome (T_num t); TSome (T_num t)]
                 (Typea [T_num t])
          else Bot)
    | c, Testop (t, uu), ts ->
        (if is_int_t_num t
          then type_update ts [TSome (T_num t)] (Typea [T_num T_i32]) else Bot)
    | c, Relop (t, op), ts ->
        (if relop_t_num_agree op t
          then type_update ts [TSome (T_num t); TSome (T_num t)]
                 (Typea [T_num T_i32])
          else Bot)
    | c, Unop_vec op, ts ->
        type_update ts [TSome (T_vec T_v128)] (Typea [T_vec T_v128])
    | c, Binop_vec op, ts ->
        (if V128Wrapper.binop_vec_wf op
          then type_update ts [TSome (T_vec T_v128); TSome (T_vec T_v128)]
                 (Typea [T_vec T_v128])
          else Bot)
    | c, Ternop_vec op, ts ->
        type_update ts
          [TSome (T_vec T_v128); TSome (T_vec T_v128); TSome (T_vec T_v128)]
          (Typea [T_vec T_v128])
    | c, Test_vec op, ts ->
        type_update ts [TSome (T_vec T_v128)] (Typea [T_num T_i32])
    | c, Shift_vec op, ts ->
        type_update ts [TSome (T_vec T_v128); TSome (T_num T_i32)]
          (Typea [T_vec T_v128])
    | c, Splat_vec sv, ts ->
        type_update ts [TSome (T_num (vec_lane_t sv))] (Typea [T_vec T_v128])
    | c, Extract_vec (sv, sx, i), ts ->
        (if less_nat i (vec_num sv) &&
              (equal_sx sx U ||
                less_eq_nat (vec_length sv) (nat_of_integer (Z.of_int 2)))
          then type_update ts [TSome (T_vec T_v128)]
                 (Typea [T_num (vec_lane_t sv)])
          else Bot)
    | c, Replace_vec (sv, i), ts ->
        (if less_nat i (vec_num sv)
          then type_update ts
                 [TSome (T_vec T_v128); TSome (T_num (vec_lane_t sv))]
                 (Typea [T_vec T_v128])
          else Bot)
    | c, Cvtop (t1, Convert, t2, sat_sx), ts ->
        (if convert_cond t1 t2 sat_sx
          then type_update ts [TSome (T_num t2)] (Typea [T_num t1]) else Bot)
    | c, Cvtop (t1, Reinterpret, t2, sx), ts ->
        (if not (equal_t_num t1 t2) &&
              (equal_nat (t_num_length t1) (t_num_length t2) && is_none sx)
          then type_update ts [TSome (T_num t2)] (Typea [T_num t1]) else Bot)
    | c, Unreachable, ts -> type_update ts [] (TopType [])
    | c, Nop, ts -> ts
    | c, Drop, ts -> type_update ts [TAny] (Typea [])
    | c, Select, ts -> type_update_select ts
    | c, Block (tb, es), ts ->
        (match tb_tf_t c tb with None -> Bot
          | Some (Tf (tn, tm)) ->
            (if b_e_type_checker (label_update (fun _ -> [tm] @ label c) c) es
                  (Tf (tn, tm))
              then type_update ts (to_ct_list tn) (Typea tm) else Bot))
    | c, Loop (tb, es), ts ->
        (match tb_tf_t c tb with None -> Bot
          | Some (Tf (tn, tm)) ->
            (if b_e_type_checker (label_update (fun _ -> [tn] @ label c) c) es
                  (Tf (tn, tm))
              then type_update ts (to_ct_list tn) (Typea tm) else Bot))
    | c, If (tb, es1, es2), ts ->
        (match tb_tf_t c tb with None -> Bot
          | Some (Tf (tn, tm)) ->
            (if b_e_type_checker (label_update (fun _ -> [tm] @ label c) c) es1
                  (Tf (tn, tm)) &&
                  b_e_type_checker (label_update (fun _ -> [tm] @ label c) c)
                    es2 (Tf (tn, tm))
              then type_update ts (to_ct_list (tn @ [T_num T_i32])) (Typea tm)
              else Bot))
    | c, Br i, ts ->
        (if less_nat i (size_list (label c))
          then type_update ts (to_ct_list (nth (label c) i)) (TopType [])
          else Bot)
    | c, Br_if i, ts ->
        (if less_nat i (size_list (label c))
          then type_update ts (to_ct_list (nth (label c) i @ [T_num T_i32]))
                 (Typea (nth (label c) i))
          else Bot)
    | c, Br_table (is, i), ts ->
        (match same_lab (is @ [i]) (label c) with None -> Bot
          | Some tls ->
            type_update ts (to_ct_list (tls @ [T_num T_i32])) (TopType []))
    | c, Return, ts ->
        (match return c with None -> Bot
          | Some tls -> type_update ts (to_ct_list tls) (TopType []))
    | c, Call i, ts ->
        (if less_nat i (size_list (func_t c))
          then (let Tf (tn, tm) = nth (func_t c) i in
                 type_update ts (to_ct_list tn) (Typea tm))
          else Bot)
    | c, Call_indirect i, ts ->
        (if less_eq_nat one_nata (size_list (table c)) &&
              less_nat i (size_list (types_t c))
          then (let Tf (tn, tm) = nth (types_t c) i in
                 type_update ts (to_ct_list (tn @ [T_num T_i32])) (Typea tm))
          else Bot)
    | c, Get_local i, ts ->
        (if less_nat i (size_list (local c))
          then type_update ts [] (Typea [nth (local c) i]) else Bot)
    | c, Set_local i, ts ->
        (if less_nat i (size_list (local c))
          then type_update ts [TSome (nth (local c) i)] (Typea []) else Bot)
    | c, Tee_local i, ts ->
        (if less_nat i (size_list (local c))
          then type_update ts [TSome (nth (local c) i)]
                 (Typea [nth (local c) i])
          else Bot)
    | c, Get_global i, ts ->
        (if less_nat i (size_list (global c))
          then type_update ts [] (Typea [tg_t (nth (global c) i)]) else Bot)
    | c, Set_global i, ts ->
        (if less_nat i (size_list (global c)) && is_mut (nth (global c) i)
          then type_update ts [TSome (tg_t (nth (global c) i))] (Typea [])
          else Bot)
    | c, Load (t, tp_sx, a, off), ts ->
        (if less_eq_nat one_nata (size_list (memory c)) &&
              load_store_t_bounds a (option_projl tp_sx) t
          then type_update ts [TSome (T_num T_i32)] (Typea [T_num t]) else Bot)
    | c, Store (t, tp, a, off), ts ->
        (if less_eq_nat one_nata (size_list (memory c)) &&
              load_store_t_bounds a tp t
          then type_update ts [TSome (T_num T_i32); TSome (T_num t)] (Typea [])
          else Bot)
    | c, Load_vec (lv, a, off), ts ->
        (if less_eq_nat one_nata (size_list (memory c)) &&
              load_vec_t_bounds lv a
          then type_update ts [TSome (T_num T_i32)] (Typea [T_vec T_v128])
          else Bot)
    | c, Load_lane_vec (svi, i, a, off), ts ->
        (if less_eq_nat one_nata (size_list (memory c)) &&
              (less_nat i (vec_i_num svi) &&
                less_eq_nat (power power_nat (nat_of_integer (Z.of_int 2)) a)
                  (vec_i_length svi))
          then type_update ts [TSome (T_num T_i32); TSome (T_vec T_v128)]
                 (Typea [T_vec T_v128])
          else Bot)
    | c, Store_vec (sv, a, off), ts ->
        (if less_eq_nat one_nata (size_list (memory c)) &&
              store_vec_t_bounds sv a
          then type_update ts [TSome (T_num T_i32); TSome (T_vec T_v128)]
                 (Typea [])
          else Bot)
    | c, Current_memory, ts ->
        (if less_eq_nat one_nata (size_list (memory c))
          then type_update ts [] (Typea [T_num T_i32]) else Bot)
    | c, Grow_memory, ts ->
        (if less_eq_nat one_nata (size_list (memory c))
          then type_update ts [TSome (T_num T_i32)] (Typea [T_num T_i32])
          else Bot);;

let rec eq_i_i _A
  xa xb =
    bind (single (xa, xb))
      (fun (x, xaa) -> (if eq _A x xaa then single () else bot_pred));;

let rec fold_map
  f x1 = match f, x1 with f, [] -> (fun () -> [])
    | f, x :: xs -> (fun () -> (let y = f x () in
                                let ys = fold_map f xs () in
                                 y :: ys));;

let rec list_all2
  p xs ys = match p, xs, ys with
    p, x :: xs, y :: ys -> p x y && list_all2 p xs ys
    | p, xs, [] -> null xs
    | p, [], ys -> null ys;;

let rec byte_of_nat x = uint8_of_nat x;;

let rec nat_of_byte x = nat_of_uint8 x;;

let rec uminus_word _A a = of_int _A (uminus_inta (the_int _A a));;

let rec uminus_uint8
  xa = Abs_uint8
         (uminus_word (len_bit0 (len_bit0 (len_bit0 len_num1)))
           (rep_uint8a xa));;

let negone_byte : uint8 = uminus_uint8 one_uint8a;;

let rec m_data
  (M_ext
    (m_types, m_funcs, m_tabs, m_mems, m_globs, m_elem, m_data, m_start,
      m_imports, m_exports, more))
    = m_data;;

let rec m_elem
  (M_ext
    (m_types, m_funcs, m_tabs, m_mems, m_globs, m_elem, m_data, m_start,
      m_imports, m_exports, more))
    = m_elem;;

let rec m_mems
  (M_ext
    (m_types, m_funcs, m_tabs, m_mems, m_globs, m_elem, m_data, m_start,
      m_imports, m_exports, more))
    = m_mems;;

let rec m_tabs
  (M_ext
    (m_types, m_funcs, m_tabs, m_mems, m_globs, m_elem, m_data, m_start,
      m_imports, m_exports, more))
    = m_tabs;;

let rec map_Heap f m = (fun () -> (let a = m () in f a));;

let rec load_uint8
  ba n =
    map_Heap uint8
      ((fun () -> 
        Z.of_int (Bytes.get_uint8 ba (Z.to_int (integer_of_nat n)))));;

let rec typerep_of _A x = typerep _A Type;;

let rec name _A a = (let Typerep (s, _) = typerep_of _A a in s);;

let rec m_funcs
  (M_ext
    (m_types, m_funcs, m_tabs, m_mems, m_globs, m_elem, m_data, m_start,
      m_imports, m_exports, more))
    = m_funcs;;

let rec m_globs
  (M_ext
    (m_types, m_funcs, m_tabs, m_mems, m_globs, m_elem, m_data, m_start,
      m_imports, m_exports, more))
    = m_globs;;

let rec m_start
  (M_ext
    (m_types, m_funcs, m_tabs, m_mems, m_globs, m_elem, m_data, m_start,
      m_imports, m_exports, more))
    = m_start;;

let rec m_types
  (M_ext
    (m_types, m_funcs, m_tabs, m_mems, m_globs, m_elem, m_data, m_start,
      m_imports, m_exports, more))
    = m_types;;

let rec load_uint32
  ba n = (fun () ->  Bytes.get_int32_le ba (Z.to_int (integer_of_nat n)));;

let rec load_uint64
  ba n = (fun () ->  Bytes.get_int64_le ba (Z.to_int (integer_of_nat n)));;

let rec store_uint8
  ba n b =
    (fun () -> 
      Bytes.set_uint8 ba (Z.to_int (integer_of_nat
                                     n)) (Z.to_int (integer_of_uint8 b)));;

let rec bitzero_vec t = (let T_v128 = t in ConstVec128 V128Wrapper.zero);;

let rec bitzero_num
  t = (match t with T_i32 -> ConstInt32 zero_i32a
        | T_i64 -> ConstInt64 zero_i64a | T_f32 -> ConstFloat32 F32Wrapper.zero
        | T_f64 -> ConstFloat64 F64Wrapper.zero);;

let rec bitzero
  t = (match t with T_num t_n -> V_num (bitzero_num t_n)
        | T_vec t_v -> V_vec (bitzero_vec t_v));;

let rec n_zeros ts = map bitzero ts;;

let rec const_expr_p
  x xa =
    sup_pred
      (bind (single (x, xa))
        (fun a ->
          (match a with (_, Unreachable) -> bot_pred | (_, Nop) -> bot_pred
            | (_, Drop) -> bot_pred | (_, Select) -> bot_pred
            | (_, Block (_, _)) -> bot_pred | (_, Loop (_, _)) -> bot_pred
            | (_, If (_, _, _)) -> bot_pred | (_, Br _) -> bot_pred
            | (_, Br_if _) -> bot_pred | (_, Br_table (_, _)) -> bot_pred
            | (_, Return) -> bot_pred | (_, Call _) -> bot_pred
            | (_, Call_indirect _) -> bot_pred | (_, Get_local _) -> bot_pred
            | (_, Set_local _) -> bot_pred | (_, Tee_local _) -> bot_pred
            | (_, Get_global _) -> bot_pred | (_, Set_global _) -> bot_pred
            | (_, Load (_, _, _, _)) -> bot_pred
            | (_, Store (_, _, _, _)) -> bot_pred
            | (_, Load_vec (_, _, _)) -> bot_pred
            | (_, Load_lane_vec (_, _, _, _)) -> bot_pred
            | (_, Store_vec (_, _, _)) -> bot_pred
            | (_, Current_memory) -> bot_pred | (_, Grow_memory) -> bot_pred
            | (_, EConst _) -> single () | (_, Unop (_, _)) -> bot_pred
            | (_, Binop (_, _)) -> bot_pred | (_, Testop (_, _)) -> bot_pred
            | (_, Relop (_, _)) -> bot_pred
            | (_, Cvtop (_, _, _, _)) -> bot_pred | (_, Unop_vec _) -> bot_pred
            | (_, Binop_vec _) -> bot_pred | (_, Ternop_vec _) -> bot_pred
            | (_, Test_vec _) -> bot_pred | (_, Shift_vec _) -> bot_pred
            | (_, Splat_vec _) -> bot_pred
            | (_, Extract_vec (_, _, _)) -> bot_pred
            | (_, Replace_vec (_, _)) -> bot_pred)))
      (bind (single (x, xa))
        (fun a ->
          (match a with (_, Unreachable) -> bot_pred | (_, Nop) -> bot_pred
            | (_, Drop) -> bot_pred | (_, Select) -> bot_pred
            | (_, Block (_, _)) -> bot_pred | (_, Loop (_, _)) -> bot_pred
            | (_, If (_, _, _)) -> bot_pred | (_, Br _) -> bot_pred
            | (_, Br_if _) -> bot_pred | (_, Br_table (_, _)) -> bot_pred
            | (_, Return) -> bot_pred | (_, Call _) -> bot_pred
            | (_, Call_indirect _) -> bot_pred | (_, Get_local _) -> bot_pred
            | (_, Set_local _) -> bot_pred | (_, Tee_local _) -> bot_pred
            | (c, Get_global k) ->
              bind (if_pred (less_nat k (size_list (global c))))
                (fun () ->
                  bind (eq_i_i equal_mut (tg_mut (nth (global c) k)) T_immut)
                    (fun () -> single ()))
            | (_, Set_global _) -> bot_pred | (_, Load (_, _, _, _)) -> bot_pred
            | (_, Store (_, _, _, _)) -> bot_pred
            | (_, Load_vec (_, _, _)) -> bot_pred
            | (_, Load_lane_vec (_, _, _, _)) -> bot_pred
            | (_, Store_vec (_, _, _)) -> bot_pred
            | (_, Current_memory) -> bot_pred | (_, Grow_memory) -> bot_pred
            | (_, EConst _) -> bot_pred | (_, Unop (_, _)) -> bot_pred
            | (_, Binop (_, _)) -> bot_pred | (_, Testop (_, _)) -> bot_pred
            | (_, Relop (_, _)) -> bot_pred
            | (_, Cvtop (_, _, _, _)) -> bot_pred | (_, Unop_vec _) -> bot_pred
            | (_, Binop_vec _) -> bot_pred | (_, Ternop_vec _) -> bot_pred
            | (_, Test_vec _) -> bot_pred | (_, Shift_vec _) -> bot_pred
            | (_, Splat_vec _) -> bot_pred
            | (_, Extract_vec (_, _, _)) -> bot_pred
            | (_, Replace_vec (_, _)) -> bot_pred)));;

let rec const_expr x1 x2 = holds (const_expr_p x1 x2);;

let rec store_uint32
  ba n v = (fun () ->  Bytes.set_int32_le ba (Z.to_int (integer_of_nat n)) v);;

let rec store_uint64
  ba n v = (fun () ->  Bytes.set_int64_le ba (Z.to_int (integer_of_nat n)) v);;

let rec min _A a b = (if less_eq _A a b then a else b);;

let rec takefill
  fill n xs =
    (if equal_nat n zero_nat then []
      else (match xs with [] -> fill :: takefill fill (minus_nat n one_nata) xs
             | y :: ys -> y :: takefill fill (minus_nat n one_nata) ys));;

let rec bytes_takefill x = takefill x;;

let rec app_unop_i _A
  iop c =
    (match iop with Clz -> int_clz _A.wasm_int_ops_wasm_int c
      | Ctz -> int_ctz _A.wasm_int_ops_wasm_int c
      | Popcnt -> int_popcnt _A.wasm_int_ops_wasm_int c);;

let rec app_unop_i_v
  iop v =
    (match v with ConstInt32 c -> ConstInt32 (app_unop_i wasm_int_i32 iop c)
      | ConstInt64 c -> ConstInt64 (app_unop_i wasm_int_i64 iop c)
      | ConstFloat32 a -> ConstFloat32 a | ConstFloat64 a -> ConstFloat64 a);;

let rec app_unop_f _A
  fop c =
    (match fop with Neg -> float_neg _A c | Abs -> float_abs _A c
      | Ceil -> float_ceil _A c | Floor -> float_floor _A c
      | Trunc -> float_trunc _A c | Nearest -> float_nearest _A c
      | Sqrt -> float_sqrt _A c);;

let rec app_unop_f_v
  fop v =
    (match v with ConstInt32 a -> ConstInt32 a | ConstInt64 a -> ConstInt64 a
      | ConstFloat32 c -> ConstFloat32 (app_unop_f wasm_float_f32 fop c)
      | ConstFloat64 c -> ConstFloat64 (app_unop_f wasm_float_f64 fop c));;

let rec word_rcat_rev _A _B
  = comp (of_int _B)
      (horner_sum comm_semiring_0_int (the_int _A)
        (power power_int (Int_of_integer (Z.of_int 2))
          (len_of _A.len0_len Type)));;

let rec deserialise_i64
  bs = I64_impl_abs
         (abs_uint64
           (word_rcat_rev (len_bit0 (len_bit0 (len_bit0 len_num1)))
             (len_bit0
               (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
             (map rep_uint8 bs)));;

let rec deserialise_i32
  bs = I32_impl_abs
         (abs_uint32
           (word_rcat_rev (len_bit0 (len_bit0 (len_bit0 len_num1)))
             (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
             (map rep_uint8 bs)));;

let rec isabelle_byte_to_ocaml_char n = LibAux.char_of_z (integer_of_uint8 n);;

let rec f64_deserialise_isabelle_bytes
  bs = ImplWrapper.deserialise_f64 (map isabelle_byte_to_ocaml_char bs);;

let rec deserialise_f64 x = f64_deserialise_isabelle_bytes x;;

let rec f32_deserialise_isabelle_bytes
  bs = ImplWrapper.deserialise_f32 (map isabelle_byte_to_ocaml_char bs);;

let rec deserialise_f32 x = f32_deserialise_isabelle_bytes x;;

let rec wasm_deserialise_num
  bs t =
    (match t with T_i32 -> ConstInt32 (deserialise_i32 bs)
      | T_i64 -> ConstInt64 (deserialise_i64 bs)
      | T_f32 -> ConstFloat32 (deserialise_f32 bs)
      | T_f64 -> ConstFloat64 (deserialise_f64 bs));;

let rec sign_extend
  sx l bytes =
    (let msb = msb_byte (msbyte bytes) in
     let byte =
       (match sx with S -> (if msb then negone_byte else zero_byte)
         | U -> zero_byte)
       in
      bytes_takefill byte l bytes);;

let rec bin_rsplit_rev
  n m c =
    (if equal_nat m zero_nat || equal_nat n zero_nat then []
      else (let a = bin_split n c in
            let (aa, b) = a in
             b :: bin_rsplit_rev n (minus_nat m n) aa));;

let rec word_rsplit_rev _A _B
  w = map (of_int _B)
        (bin_rsplit_rev (len_of _B.len0_len Type) (len_of _A.len0_len Type)
          (the_int _A w));;

let rec serialise_i64
  (I64_impl_abs x) =
    map abs_uint8
      (word_rsplit_rev
        (len_bit0
          (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
        (len_bit0 (len_bit0 (len_bit0 len_num1))) (rep_uint64 x));;

let rec serialise_i32
  (I32_impl_abs x) =
    map abs_uint8
      (word_rsplit_rev
        (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
        (len_bit0 (len_bit0 (len_bit0 len_num1))) (rep_uint32 x));;

let rec ocaml_char_to_isabelle_byte n = uint8 (LibAux.z_of_char n);;

let rec f64_serialise_isabelle_bytes
  f = map ocaml_char_to_isabelle_byte (ImplWrapper.serialise_f64 f);;

let rec serialise_f64 x = f64_serialise_isabelle_bytes x;;

let rec f32_serialise_isabelle_bytes
  f = map ocaml_char_to_isabelle_byte (ImplWrapper.serialise_f32 f);;

let rec serialise_f32 x = f32_serialise_isabelle_bytes x;;

let rec bits_num
  v = (match v with ConstInt32 a -> serialise_i32 a
        | ConstInt64 a -> serialise_i64 a | ConstFloat32 a -> serialise_f32 a
        | ConstFloat64 a -> serialise_f64 a);;

let rec app_extend_s
  tp v =
    wasm_deserialise_num
      (sign_extend S (t_num_length (typeof_num v))
        (take (tp_num_length tp) (bits_num v)))
      (typeof_num v);;

let rec app_unop
  uop v =
    (match uop with Unop_i iop -> app_unop_i_v iop v
      | Unop_f fop -> app_unop_f_v fop v | Extend_s tp -> app_extend_s tp v);;

let rec v128_serialise_isabelle_bytes
  v = map ocaml_char_to_isabelle_byte (ImplWrapper.serialise_v128 v);;

let rec serialise_v128 x = v128_serialise_isabelle_bytes x;;

let rec bits_vec v = (let ConstVec128 a = v in serialise_v128 a);;

let rec m_exports
  (M_ext
    (m_types, m_funcs, m_tabs, m_mems, m_globs, m_elem, m_data, m_start,
      m_imports, m_exports, more))
    = m_exports;;

let rec m_imports
  (M_ext
    (m_types, m_funcs, m_tabs, m_mems, m_globs, m_elem, m_data, m_start,
      m_imports, m_exports, more))
    = m_imports;;

let rec app_binop_i _A
  iop c1 c2 =
    (match iop with Add -> Some (int_add _A.wasm_int_ops_wasm_int c1 c2)
      | Sub -> Some (int_sub _A.wasm_int_ops_wasm_int c1 c2)
      | Mul -> Some (int_mul _A.wasm_int_ops_wasm_int c1 c2)
      | Div S -> int_div_s _A.wasm_int_ops_wasm_int c1 c2
      | Div U -> int_div_u _A.wasm_int_ops_wasm_int c1 c2
      | Rem S -> int_rem_s _A.wasm_int_ops_wasm_int c1 c2
      | Rem U -> int_rem_u _A.wasm_int_ops_wasm_int c1 c2
      | And -> Some (int_and _A.wasm_int_ops_wasm_int c1 c2)
      | Or -> Some (int_or _A.wasm_int_ops_wasm_int c1 c2)
      | Xor -> Some (int_xor _A.wasm_int_ops_wasm_int c1 c2)
      | Shl -> Some (int_shl _A.wasm_int_ops_wasm_int c1 c2)
      | Shr S -> Some (int_shr_s _A.wasm_int_ops_wasm_int c1 c2)
      | Shr U -> Some (int_shr_u _A.wasm_int_ops_wasm_int c1 c2)
      | Rotl -> Some (int_rotl _A.wasm_int_ops_wasm_int c1 c2)
      | Rotr -> Some (int_rotr _A.wasm_int_ops_wasm_int c1 c2));;

let rec app_binop_i_v
  iop v1 v2 =
    (match (v1, v2)
      with (ConstInt32 c1, ConstInt32 c2) ->
        map_option (fun a -> ConstInt32 a) (app_binop_i wasm_int_i32 iop c1 c2)
      | (ConstInt32 _, ConstInt64 _) -> None
      | (ConstInt32 _, ConstFloat32 _) -> None
      | (ConstInt32 _, ConstFloat64 _) -> None
      | (ConstInt64 _, ConstInt32 _) -> None
      | (ConstInt64 c1, ConstInt64 c2) ->
        map_option (fun a -> ConstInt64 a) (app_binop_i wasm_int_i64 iop c1 c2)
      | (ConstInt64 _, ConstFloat32 _) -> None
      | (ConstInt64 _, ConstFloat64 _) -> None | (ConstFloat32 _, _) -> None
      | (ConstFloat64 _, _) -> None);;

let rec app_binop_f _A
  fop c1 c2 =
    (match fop with Addf -> Some (float_add _A c1 c2)
      | Subf -> Some (float_sub _A c1 c2) | Mulf -> Some (float_mul _A c1 c2)
      | Divf -> Some (float_div _A c1 c2) | Min -> Some (float_min _A c1 c2)
      | Max -> Some (float_max _A c1 c2)
      | Copysign -> Some (float_copysign _A c1 c2));;

let rec app_binop_f_v
  fop v1 v2 =
    (match (v1, v2) with (ConstInt32 _, _) -> None | (ConstInt64 _, _) -> None
      | (ConstFloat32 _, ConstInt32 _) -> None
      | (ConstFloat32 _, ConstInt64 _) -> None
      | (ConstFloat32 c1, ConstFloat32 c2) ->
        map_option (fun a -> ConstFloat32 a)
          (app_binop_f wasm_float_f32 fop c1 c2)
      | (ConstFloat32 _, ConstFloat64 _) -> None
      | (ConstFloat64 _, ConstInt32 _) -> None
      | (ConstFloat64 _, ConstInt64 _) -> None
      | (ConstFloat64 _, ConstFloat32 _) -> None
      | (ConstFloat64 c1, ConstFloat64 c2) ->
        map_option (fun a -> ConstFloat64 a)
          (app_binop_f wasm_float_f64 fop c1 c2));;

let rec app_binop
  bop v1 v2 =
    (match bop with Binop_i iop -> app_binop_i_v iop v1 v2
      | Binop_f fop -> app_binop_f_v fop v1 v2);;

let rec app_relop_i _A
  rop c1 c2 =
    (match rop with Eq -> int_eq _A.wasm_int_ops_wasm_int c1 c2
      | Ne -> not (int_eq _A.wasm_int_ops_wasm_int c1 c2)
      | Lt S -> int_lt_s _A.wasm_int_ops_wasm_int c1 c2
      | Lt U -> int_lt_u _A.wasm_int_ops_wasm_int c1 c2
      | Gt S -> int_gt_s _A.wasm_int_ops_wasm_int c1 c2
      | Gt U -> int_gt_u _A.wasm_int_ops_wasm_int c1 c2
      | Le S -> int_le_s _A.wasm_int_ops_wasm_int c1 c2
      | Le U -> int_le_u _A.wasm_int_ops_wasm_int c1 c2
      | Ge S -> int_ge_s _A.wasm_int_ops_wasm_int c1 c2
      | Ge U -> int_ge_u _A.wasm_int_ops_wasm_int c1 c2);;

let rec wasm_bool b = I32_impl_abs (if b then Int32.one else Int32.zero);;

let rec app_relop_i_v
  iop v1 v2 =
    (match (v1, v2)
      with (ConstInt32 c1, ConstInt32 c2) ->
        ConstInt32 (wasm_bool (app_relop_i wasm_int_i32 iop c1 c2))
      | (ConstInt32 _, ConstInt64 _) -> ConstInt32 zero_i32a
      | (ConstInt32 _, ConstFloat32 _) -> ConstInt32 zero_i32a
      | (ConstInt32 _, ConstFloat64 _) -> ConstInt32 zero_i32a
      | (ConstInt64 _, ConstInt32 _) -> ConstInt32 zero_i32a
      | (ConstInt64 c1, ConstInt64 c2) ->
        ConstInt32 (wasm_bool (app_relop_i wasm_int_i64 iop c1 c2))
      | (ConstInt64 _, ConstFloat32 _) -> ConstInt32 zero_i32a
      | (ConstInt64 _, ConstFloat64 _) -> ConstInt32 zero_i32a
      | (ConstFloat32 _, _) -> ConstInt32 zero_i32a
      | (ConstFloat64 _, _) -> ConstInt32 zero_i32a);;

let rec app_relop_f _A
  rop c1 c2 =
    (match rop with Eqf -> float_eq _A c1 c2 | Nef -> not (float_eq _A c1 c2)
      | Ltf -> float_lt _A c1 c2 | Gtf -> float_gt _A c1 c2
      | Lef -> float_le _A c1 c2 | Gef -> float_ge _A c1 c2);;

let rec app_relop_f_v
  fop v1 v2 =
    (match (v1, v2) with (ConstInt32 _, _) -> ConstInt32 zero_i32a
      | (ConstInt64 _, _) -> ConstInt32 zero_i32a
      | (ConstFloat32 _, ConstInt32 _) -> ConstInt32 zero_i32a
      | (ConstFloat32 _, ConstInt64 _) -> ConstInt32 zero_i32a
      | (ConstFloat32 c1, ConstFloat32 c2) ->
        ConstInt32 (wasm_bool (app_relop_f wasm_float_f32 fop c1 c2))
      | (ConstFloat32 _, ConstFloat64 _) -> ConstInt32 zero_i32a
      | (ConstFloat64 _, ConstInt32 _) -> ConstInt32 zero_i32a
      | (ConstFloat64 _, ConstInt64 _) -> ConstInt32 zero_i32a
      | (ConstFloat64 _, ConstFloat32 _) -> ConstInt32 zero_i32a
      | (ConstFloat64 c1, ConstFloat64 c2) ->
        ConstInt32 (wasm_bool (app_relop_f wasm_float_f64 fop c1 c2)));;

let rec app_relop
  rop v1 v2 =
    (match rop with Relop_i iop -> app_relop_i_v iop v1 v2
      | Relop_f fop -> app_relop_f_v fop v1 v2);;

let rec split_n
  x0 n = match x0, n with [], n -> ([], [])
    | v :: va, n ->
        (if equal_nat n zero_nat then ([], v :: va)
          else (let a = split_n va (minus_nat n one_nata) in
                let (es, aa) = a in
                 (v :: es, aa)));;

let rec limit_type_checker_p
  x xa =
    bind (single (x, xa))
      (fun (Limit_t_ext (n, m_opt, ()), k) ->
        bind (if_pred
               (less_eq_nat k
                 (power power_nat (nat_of_integer (Z.of_int 2))
                   (nat_of_integer (Z.of_int 32)))))
          (fun () ->
            bind (if_pred (less_eq_nat n k))
              (fun () ->
                bind (if_pred (pred_option (fun m -> less_eq_nat m k) m_opt))
                  (fun () ->
                    bind (if_pred (pred_option (less_eq_nat n) m_opt))
                      (fun () -> single ())))));;

let rec limit_typing x1 x2 = holds (limit_type_checker_p x1 x2);;

let rec len_byte_array
  ba = map_Heap nat_of_integer ((fun () ->  Z.of_int (Bytes.length ba)));;

let rec app_testop_i _A
  testop c = (let Eqz = testop in int_eqz _A.wasm_int_ops_wasm_int c);;

let rec app_testop
  op v =
    (match v
      with ConstInt32 c ->
        ConstInt32 (wasm_bool (app_testop_i wasm_int_i32 op c))
      | ConstInt64 c -> ConstInt32 (wasm_bool (app_testop_i wasm_int_i64 op c))
      | ConstFloat32 _ -> ConstInt32 zero_i32a
      | ConstFloat64 _ -> ConstInt32 zero_i32a);;

let rec blit_byte_array
  baa sn ba dn ln =
    (fun () -> 
      Bytes.blit baa (Z.to_int (integer_of_nat
                                 sn)) ba (Z.to_int (integer_of_nat
             dn)) (Z.to_int (integer_of_nat ln)));;

let rec load_uint8_list
  a n l =
    (if equal_nat l zero_nat then (fun () -> [])
      else (fun () ->
             (let b = load_uint8 a n () in
              let bs = load_uint8_list a (suc n) (minus_nat l one_nata) () in
               b :: bs)));;

let rec store_uint8_list
  a n x2 = match a, n, x2 with a, n, [] -> (fun () -> ())
    | a, n, b :: bs ->
        (fun () ->
          (let _ = store_uint8 a n b () in store_uint8_list a (suc n) bs ()));;

let rec app_test_vec_v
  op1 v = ocaml_int32_to_isabelle_int32 (V128Wrapper.test_vec op1 v);;

let rec app_test_vec op v1 = (let ConstVec128 a = v1 in app_test_vec_v op a);;

let rec app_unop_vec_v x = V128Wrapper.unop_vec x;;

let rec app_unop_vec
  uop v1 = (let ConstVec128 c = v1 in ConstVec128 (app_unop_vec_v uop c));;

let crash_invalid : res_step
  = Res_crash (Error_invalid "type system violation");;

let rec app_v_s_if
  tb es1 es2 v_s =
    (match v_s with [] -> (v_s, ([], crash_invalid))
      | V_num (ConstInt32 c) :: v_sa ->
        (if int_eq_i32 c zero_i32a
          then (v_sa, ([Basic (Block (tb, es2))], Step_normal))
          else (v_sa, ([Basic (Block (tb, es1))], Step_normal)))
      | V_num (ConstInt64 _) :: _ -> (v_s, ([], crash_invalid))
      | V_num (ConstFloat32 _) :: _ -> (v_s, ([], crash_invalid))
      | V_num (ConstFloat64 _) :: _ -> (v_s, ([], crash_invalid))
      | V_vec _ :: _ -> (v_s, ([], crash_invalid)));;

let rec g_val_update
  g_vala (Global_ext (g_mut, g_val, more)) =
    Global_ext (g_mut, g_vala g_val, more);;

let rec app_binop_vec_v x = V128Wrapper.binop_vec x;;

let rec app_binop_vec
  bop v1 v2 =
    (let (ConstVec128 c1, ConstVec128 c2) = (v1, v2) in
      map_option (fun a -> ConstVec128 a) (app_binop_vec_v bop c1 c2));;

let rec app_shift_vec_v
  op2 v n = V128Wrapper.shift_vec op2 v (isabelle_int32_to_ocaml_int32 n);;

let rec app_shift_vec
  sop v cn =
    (let ConstVec128 cv = v in ConstVec128 (app_shift_vec_v sop cv cn));;

let rec v128_deserialise_isabelle_bytes
  bs = ImplWrapper.deserialise_v128 (map isabelle_byte_to_ocaml_char bs);;

let rec deserialise_v128 x = v128_deserialise_isabelle_bytes x;;

let rec app_splat_vec
  sv v =
    ConstVec128
      (deserialise_v128
        (concat (replicate (vec_num sv) (take (vec_length sv) (bits_num v)))));;

let rec typing x = b_e_type_checker x;;

let make_empty_inst_m : (unit -> unit inst_m_ext)
  = (fun () ->
      (let f_inst2_types = (fun () -> Array.of_list []) () in
       let f_inst2_funcs = (fun () -> Array.of_list []) () in
       let f_inst2_tabs = (fun () -> Array.of_list []) () in
       let f_inst2_mems = (fun () -> Array.of_list []) () in
       let f_inst2_globs = (fun () -> Array.of_list []) () in
        (let a =
           Inst_m_ext
             (f_inst2_types, f_inst2_funcs, f_inst2_tabs, f_inst2_mems,
               f_inst2_globs, ())
           in
          (fun () -> a))
          ()));;

let rec globs (S_m_ext (funcs, tabs, mems, globs, more)) = globs;;

let rec funcs (S_m_ext (funcs, tabs, mems, globs, more)) = funcs;;

let rec tabs (S_m_ext (funcs, tabs, mems, globs, more)) = tabs;;

let rec mems (S_m_ext (funcs, tabs, mems, globs, more)) = mems;;

let rec globsa (Inst_m_ext (types, funcs, tabs, mems, globs, more)) = globs;;

let rec funcsa (Inst_m_ext (types, funcs, tabs, mems, globs, more)) = funcs;;

let rec tabsa (Inst_m_ext (types, funcs, tabs, mems, globs, more)) = tabs;;

let rec memsa (Inst_m_ext (types, funcs, tabs, mems, globs, more)) = mems;;

let rec export_get_v_ext_m
  inst exp =
    (match exp
      with Ext_func i ->
        (fun () ->
          (let x = array_nth heap_nat (funcsa inst) i () in Ext_func x))
      | Ext_tab i ->
        (fun () -> (let x = array_nth heap_nat (tabsa inst) i () in Ext_tab x))
      | Ext_mem i ->
        (fun () -> (let x = array_nth heap_nat (memsa inst) i () in Ext_mem x))
      | Ext_glob i ->
        (fun () ->
          (let x = array_nth heap_nat (globsa inst) i () in Ext_glob x)));;

let rec e_name (Module_export_ext (e_name, e_desc, more)) = e_name;;

let rec e_desc (Module_export_ext (e_name, e_desc, more)) = e_desc;;

let rec get_exports_m
  inst m_exps =
    fold_map
      (fun m_exp () ->
        (let desc = export_get_v_ext_m inst (e_desc m_exp) () in
          Module_export_ext (e_name m_exp, desc, ())))
      m_exps;;

let rec list_blit_array _A
  src_list dst dst_pos =
    (match src_list with [] -> (fun () -> ())
      | y :: ys ->
        (fun () ->
          (let _ = upd _A dst_pos y dst () in
            list_blit_array _A ys dst (plus_nat dst_pos one_nata) ())));;

let rec array_blit_map _B
  src_list src_f dst dst_pos =
    (fun () ->
      (let ys = fold_map src_f src_list () in
        list_blit_array _B ys dst dst_pos ()));;

let rec g_type (Module_glob_ext (g_type, g_init, more)) = g_type;;

let rec alloc_globs_m
  s_globs n m_gs gvs =
    array_blit_map (heap_global_ext heap_unit) (zip m_gs gvs)
      (fun (m_g, v) -> (fun () -> (Global_ext (tg_mut (g_type m_g), v, ()))))
      s_globs n;;

let rec alloc_funcs_m
  s_funcs n m_fs inst_m inst_types =
    array_blit_map heap_cl_m m_fs
      (fun (i, (tlocs, b_es)) () ->
        (let ft = array_nth heap_tf inst_types i () in
          Func_native (inst_m, ft, tlocs, b_es)))
      s_funcs n;;

let rec alloc_tabs_m
  s_tabs n m_ts =
    array_blit_map
      (heap_prod (heap_array (typerep_option typerep_nat))
        (heap_option heap_nat))
      m_ts
      (fun tt () ->
        (let t = newa (heap_option heap_nat) (l_min tt) None () in
          (t, l_max tt)))
      s_tabs n;;

let rec new_zeroed_byte_array
  n = (fun () ->  Bytes.make (Z.to_int (integer_of_nat n)) (Char.chr 0));;

let rec alloc_mems_m
  s_mems n m_ms =
    array_blit_map (heap_prod heap_byte_array (heap_option heap_nat)) m_ms
      (fun mt () ->
        (let m = new_zeroed_byte_array (times_nata (l_min mt) ki64) () in
          (m, l_max mt)))
      s_mems n;;

let rec interp_alloc_module_m
  s_m m imps gvs =
    (fun () ->
      (let length_funcs_s = len heap_cl_m (funcs s_m) () in
       let length_tabs_s =
         len (heap_prod (heap_array (typerep_option typerep_nat))
               (heap_option heap_nat))
           (tabs s_m) ()
         in
       let length_mems_s =
         len (heap_prod heap_byte_array (heap_option heap_nat)) (mems s_m) () in
       let length_globs_s = len (heap_global_ext heap_unit) (globs s_m) () in
        (let i_fs =
           upt length_funcs_s (plus_nat length_funcs_s (size_list (m_funcs m)))
           in
         let i_ts =
           upt length_tabs_s (plus_nat length_tabs_s (size_list (m_tabs m))) in
         let i_ms =
           upt length_mems_s (plus_nat length_mems_s (size_list (m_mems m))) in
         let i_gs =
           upt length_globs_s
             (plus_nat length_globs_s
               (min ord_nat (size_list (m_globs m)) (size_list gvs)))
           in
          (fun f_ () -> f_ (((fun () -> Array.of_list (m_types m))) ()) ())
            (fun inst_types ->
              (fun f_ () -> f_
                (((fun () -> Array.of_list
                   (map_filter
                      (fun a ->
                        (match a with Ext_func aa -> Some aa | Ext_tab _ -> None
                          | Ext_mem _ -> None | Ext_glob _ -> None))
                      imps @
                     i_fs)))
                ()) ())
                (fun inst_funcs ->
                  (fun f_ () -> f_
                    (((fun () -> Array.of_list
                       (map_filter
                          (fun a ->
                            (match a with Ext_func _ -> None
                              | Ext_tab aa -> Some aa | Ext_mem _ -> None
                              | Ext_glob _ -> None))
                          imps @
                         i_ts)))
                    ()) ())
                    (fun inst_tabs ->
                      (fun f_ () -> f_
                        (((fun () -> Array.of_list
                           (map_filter
                              (fun a ->
                                (match a with Ext_func _ -> None
                                  | Ext_tab _ -> None | Ext_mem aa -> Some aa
                                  | Ext_glob _ -> None))
                              imps @
                             i_ms)))
                        ()) ())
                        (fun inst_mems ->
                          (fun f_ () -> f_
                            (((fun () -> Array.of_list
                               (map_filter
                                  (fun a ->
                                    (match a with Ext_func _ -> None
                                      | Ext_tab _ -> None | Ext_mem _ -> None
                                      | Ext_glob aa -> Some aa))
                                  imps @
                                 i_gs)))
                            ()) ())
                            (fun inst_globs ->
                              (let inst_m =
                                 Inst_m_ext
                                   (inst_types, inst_funcs, inst_tabs,
                                     inst_mems, inst_globs, ())
                                 in
                                (fun f_ () -> f_ (make_empty_inst_m ()) ())
                                  (fun empty_inst ->
                                    (fun f_ () -> f_
                                      (((fun () -> Array.of_list [])) ()) ())
                                      (fun empty_tab ->
(fun f_ () -> f_ ((new_zeroed_byte_array zero_nat) ()) ())
  (fun empty_mem ->
    (let dummy_func = Func_native (empty_inst, Tf ([], []), [], []) in
     let dummy_tab = (empty_tab, None) in
     let dummy_mem = (empty_mem, None) in
     let dummy_glob = Global_ext (T_mut, V_num (ConstInt32 zero_i32a), ()) in
      (fun f_ () -> f_
        ((newa heap_cl_m (plus_nat length_funcs_s (size_list (m_funcs m)))
           dummy_func)
        ()) ())
        (fun s_funcs ->
          (fun f_ () -> f_
            ((newa (heap_prod (heap_array (typerep_option typerep_nat))
                     (heap_option heap_nat))
               (plus_nat length_tabs_s (size_list (m_tabs m))) dummy_tab)
            ()) ())
            (fun s_tabs ->
              (fun f_ () -> f_
                ((newa (heap_prod heap_byte_array (heap_option heap_nat))
                   (plus_nat length_mems_s (size_list (m_mems m))) dummy_mem)
                ()) ())
                (fun s_mems ->
                  (fun f_ () -> f_
                    ((newa (heap_global_ext heap_unit)
                       (plus_nat length_globs_s
                         (min ord_nat (size_list (m_globs m)) (size_list gvs)))
                       dummy_glob)
                    ()) ())
                    (fun s_globs ->
                      (fun f_ () -> f_
                        ((blit heap_cl_m (funcs s_m) zero_nat s_funcs zero_nat
                           length_funcs_s)
                        ()) ())
                        (fun _ ->
                          (fun f_ () -> f_
                            ((blit (heap_prod
                                     (heap_array (typerep_option typerep_nat))
                                     (heap_option heap_nat))
                               (tabs s_m) zero_nat s_tabs zero_nat
                               length_tabs_s)
                            ()) ())
                            (fun _ ->
                              (fun f_ () -> f_
                                ((blit (heap_prod heap_byte_array
 (heap_option heap_nat))
                                   (mems s_m) zero_nat s_mems zero_nat
                                   length_mems_s)
                                ()) ())
                                (fun _ ->
                                  (fun f_ () -> f_
                                    ((blit (heap_global_ext heap_unit)
                                       (globs s_m) zero_nat s_globs zero_nat
                                       length_globs_s)
                                    ()) ())
                                    (fun _ ->
                                      (fun f_ () -> f_
((alloc_funcs_m s_funcs length_funcs_s (m_funcs m) inst_m inst_types) ()) ())
(fun _ ->
  (fun f_ () -> f_ ((alloc_tabs_m s_tabs length_tabs_s (m_tabs m)) ()) ())
    (fun _ ->
      (fun f_ () -> f_ ((alloc_mems_m s_mems length_mems_s (m_mems m)) ()) ())
        (fun _ ->
          (fun f_ () -> f_
            ((alloc_globs_m s_globs length_globs_s (m_globs m) gvs) ()) ())
            (fun _ ->
              (fun f_ () -> f_ ((get_exports_m inst_m (m_exports m)) ()) ())
                (fun exps ->
                  (let s_res = S_m_ext (s_funcs, s_tabs, s_mems, s_globs, ()) in
                    (fun () -> (s_res, (inst_m, exps))))))))))))))))))))))))))))
          ()));;

let rec list_all2_m
  r x1 x2 = match r, x1, x2 with r, [], [] -> (fun () -> true)
    | r, x :: xs, [] -> (fun () -> false)
    | r, [], y :: ys -> (fun () -> false)
    | r, x :: xs, y :: ys ->
        (fun () -> (let b = r x y () in
                    let ba = list_all2_m r xs ys () in
                     b && ba));;

let rec e_init (Module_elem_ext (e_tab, e_off, e_init, more)) = e_init;;

let rec e_tab (Module_elem_ext (e_tab, e_off, e_init, more)) = e_tab;;

let rec element_in_bounds_m
  s_m inst_m e_offs m_elems =
    list_all2_m
      (fun e_off e () ->
        (let t_ind = array_nth heap_nat (tabsa inst_m) (e_tab e) () in
         let a =
           array_nth
             (heap_prod (heap_array (typerep_option typerep_nat))
               (heap_option heap_nat))
             (tabs s_m) t_ind ()
           in
          (let (tab_e, _) = a in
            (fun f_ () -> f_ ((len (heap_option heap_nat) tab_e) ()) ())
              (fun tab_e_len ->
                (fun () ->
                  (less_eq_nat
                    (plus_nat (nat_of_int_i32 e_off) (size_list (e_init e)))
                    tab_e_len))))
            ()))
      e_offs m_elems;;

let rec cl_m_type = function Func_native (x11, x12, x13, x14) -> x12
                    | Func_host (x21, x22) -> x21;;

let rec tab_typing_m
  t tt =
    (fun () ->
      (let t_min = len (heap_option heap_nat) (fst t) () in
        limits_compat (Limit_t_ext (t_min, snd t, ())) tt));;

let rec divide_nat
  m n = Nat (divide_integer (integer_of_nat m) (integer_of_nat n));;

let rec mem_typing_m
  m mt =
    (fun () ->
      (let m_min = len_byte_array (fst m) () in
        limits_compat (Limit_t_ext (divide_nat m_min ki64, snd m, ())) mt));;

let rec external_typing_m
  s_m x1 x2 = match s_m, x1, x2 with
    s_m, Ext_func i, Te_func tf ->
      (fun () ->
        (let f_len = len heap_cl_m (funcs s_m) () in
          (if less_nat i f_len
            then (fun f_ () -> f_ ((array_nth heap_cl_m (funcs s_m) i) ()) ())
                   (fun f -> (fun () -> (equal_tfa (cl_m_type f) tf)))
            else (fun () -> false))
            ()))
    | s_m, Ext_tab i, Te_tab tt ->
        (fun () ->
          (let t_len =
             len (heap_prod (heap_array (typerep_option typerep_nat))
                   (heap_option heap_nat))
               (tabs s_m) ()
             in
            (if less_nat i t_len
              then (fun f_ () -> f_
                     ((array_nth
                        (heap_prod (heap_array (typerep_option typerep_nat))
                          (heap_option heap_nat))
                        (tabs s_m) i)
                     ()) ())
                     (fun t -> tab_typing_m t tt)
              else (fun () -> false))
              ()))
    | s_m, Ext_mem i, Te_mem mt ->
        (fun () ->
          (let m_len =
             len (heap_prod heap_byte_array (heap_option heap_nat)) (mems s_m)
               ()
             in
            (if less_nat i m_len
              then (fun f_ () -> f_
                     ((array_nth
                        (heap_prod heap_byte_array (heap_option heap_nat))
                        (mems s_m) i)
                     ()) ())
                     (fun m -> mem_typing_m m mt)
              else (fun () -> false))
              ()))
    | s_m, Ext_glob i, Te_glob gt ->
        (fun () ->
          (let g_len = len (heap_global_ext heap_unit) (globs s_m) () in
            (if less_nat i g_len
              then (fun f_ () -> f_
                     ((array_nth (heap_global_ext heap_unit) (globs s_m) i) ())
                     ())
                     (fun g -> (fun () -> (glob_typing g gt)))
              else (fun () -> false))
              ()))
    | s_m, Ext_tab v, Te_func va -> (fun () -> false)
    | s_m, Ext_tab v, Te_mem va -> (fun () -> false)
    | s_m, Ext_tab v, Te_glob va -> (fun () -> false)
    | s_m, Ext_mem v, Te_func va -> (fun () -> false)
    | s_m, Ext_mem v, Te_tab va -> (fun () -> false)
    | s_m, Ext_mem v, Te_glob va -> (fun () -> false)
    | s_m, Ext_glob v, Te_func va -> (fun () -> false)
    | s_m, Ext_glob v, Te_tab va -> (fun () -> false)
    | s_m, Ext_glob v, Te_mem va -> (fun () -> false)
    | s_m, Ext_func va, Te_tab v -> (fun () -> false)
    | s_m, Ext_func va, Te_mem v -> (fun () -> false)
    | s_m, Ext_func va, Te_glob v -> (fun () -> false);;

let rec update_redex_return
  (Redex (v_sa, es, b_es)) v_s = Redex (v_s @ v_sa, es, b_es);;

let rec update_fc_return_m
  (Frame_context_m (rdx, lcs, nf, f1, f2)) v_s =
    Frame_context_m (update_redex_return rdx v_s, lcs, nf, f1, f2);;

let rec store_uint32_of_uint64
  ba n v =
    (fun () -> 
      Bytes.set_int32_le ba (Z.to_int (integer_of_nat n)) (Int64.to_int32 v));;

let rec store_uint16_of_uint64
  ba n v =
    (fun () -> 
      Bytes.set_uint16_le ba (Z.to_int (integer_of_nat n)) (Int64.to_int v));;

let rec store_uint8_of_uint64
  ba n v =
    (fun () -> 
      Bytes.set_uint8 ba (Z.to_int (integer_of_nat n)) (Int64.to_int v));;

let rec store_uint64_packed
  a n v tp =
    (match tp with Tp_i8 -> store_uint8_of_uint64 a n v
      | Tp_i16 -> store_uint16_of_uint64 a n v
      | Tp_i32 -> store_uint32_of_uint64 a n v);;

let rec store_uint16_of_uint32
  ba n v =
    (fun () -> 
      Bytes.set_uint16_le ba (Z.to_int (integer_of_nat n)) (Int32.to_int v));;

let rec store_uint8_of_uint32
  ba n v =
    (fun () -> 
      Bytes.set_uint8 ba (Z.to_int (integer_of_nat n)) (Int32.to_int v));;

let rec store_uint32_packed
  a n v tp =
    (match tp with Tp_i8 -> store_uint8_of_uint32 a n v
      | Tp_i16 -> store_uint16_of_uint32 a n v | Tp_i32 -> store_uint32 a n v);;

let rec store_packed_m_v
  m n off v tp =
    (fun () ->
      (let m_len = len_byte_array (fst m) () in
        (if less_eq_nat (plus_nat (plus_nat n off) (tp_num_length tp)) m_len
          then (match v
                 with ConstInt32 c ->
                   (fun f_ () -> f_
                     ((store_uint32_packed (fst m) (plus_nat n off)
                        (i32_impl_rep c) tp)
                     ()) ())
                     (fun _ -> (fun () -> (Some ())))
                 | ConstInt64 c ->
                   (fun f_ () -> f_
                     ((store_uint64_packed (fst m) (plus_nat n off)
                        (i64_impl_rep c) tp)
                     ()) ())
                     (fun _ -> (fun () -> (Some ())))
                 | ConstFloat32 c ->
                   (fun f_ () -> f_
                     ((store_uint32_packed (fst m) (plus_nat n off)
                        (i32_impl_rep (deserialise_i32 (serialise_f32 c))) tp)
                     ()) ())
                     (fun _ -> (fun () -> (Some ())))
                 | ConstFloat64 c ->
                   (fun f_ () -> f_
                     ((store_uint64_packed (fst m) (plus_nat n off)
                        (i64_impl_rep (deserialise_i64 (serialise_f64 c))) tp)
                     ()) ())
                     (fun _ -> (fun () -> (Some ()))))
          else (fun () -> None))
          ()));;

let rec store_m_v
  m n off v =
    (fun () ->
      (let m_len = len_byte_array (fst m) () in
        (if less_eq_nat
              (plus_nat (plus_nat n off) (t_num_length (typeof_num v))) m_len
          then (match v
                 with ConstInt32 c ->
                   (fun f_ () -> f_
                     ((store_uint32 (fst m) (plus_nat n off) (i32_impl_rep c))
                     ()) ())
                     (fun _ -> (fun () -> (Some ())))
                 | ConstInt64 c ->
                   (fun f_ () -> f_
                     ((store_uint64 (fst m) (plus_nat n off) (i64_impl_rep c))
                     ()) ())
                     (fun _ -> (fun () -> (Some ())))
                 | ConstFloat32 c ->
                   (fun f_ () -> f_
                     ((store_uint32 (fst m) (plus_nat n off)
                        (i32_impl_rep (deserialise_i32 (serialise_f32 c))))
                     ()) ())
                     (fun _ -> (fun () -> (Some ())))
                 | ConstFloat64 c ->
                   (fun f_ () -> f_
                     ((store_uint64 (fst m) (plus_nat n off)
                        (i64_impl_rep (deserialise_i64 (serialise_f64 c))))
                     ()) ())
                     (fun _ -> (fun () -> (Some ()))))
          else (fun () -> None))
          ()));;

let rec app_s_f_v_s_store_maybe_packed_m
  t tp_opt off ms i_m v_s =
    (match v_s with [] -> (fun () -> (v_s, crash_invalid))
      | [V_num _] -> (fun () -> (v_s, crash_invalid))
      | V_num v :: V_num (ConstInt32 c) :: v_sa ->
        (if equal_t_num (typeof_num v) t
          then (fun () ->
                 (let j = array_nth heap_nat (memsa i_m) zero_nat () in
                  let m =
                    array_nth (heap_prod heap_byte_array (heap_option heap_nat))
                      ms j ()
                    in
                  let a =
                    (match tp_opt
                      with None -> store_m_v m (nat_of_int_i32 c) off v
                      | Some a -> store_packed_m_v m (nat_of_int_i32 c) off v a)
                      ()
                    in
                   (match a with None -> (fun () -> (v_sa, Res_trap "store"))
                     | Some _ -> (fun () -> (v_sa, Step_normal)))
                     ()))
          else (fun () -> (v_s, crash_invalid)))
      | V_num _ :: V_num (ConstInt64 _) :: _ -> (fun () -> (v_s, crash_invalid))
      | V_num _ :: V_num (ConstFloat32 _) :: _ ->
        (fun () -> (v_s, crash_invalid))
      | V_num _ :: V_num (ConstFloat64 _) :: _ ->
        (fun () -> (v_s, crash_invalid))
      | V_num _ :: V_vec _ :: _ -> (fun () -> (v_s, crash_invalid))
      | V_vec _ :: _ -> (fun () -> (v_s, crash_invalid)));;

let rec load_uint64_of_uint32
  ba n =
    (fun () -> 
      Int64.of_int (Option.get (Int32.unsigned_to_int (Bytes.get_int32_le ba (Z.to_int (integer_of_nat
         n))))));;

let rec load_uint64_of_uint16
  ba n =
    (fun () -> 
      Int64.of_int (Bytes.get_uint16_le ba (Z.to_int (integer_of_nat n))));;

let rec load_uint64_of_sint32
  ba n =
    (fun () -> 
      Int64.of_int32 (Bytes.get_int32_le ba (Z.to_int (integer_of_nat n))));;

let rec load_uint64_of_sint16
  ba n =
    (fun () -> 
      Int64.of_int (Bytes.get_int16_le ba (Z.to_int (integer_of_nat n))));;

let rec load_uint64_of_uint8
  ba n =
    (fun () -> 
      Int64.of_int (Bytes.get_uint8 ba (Z.to_int (integer_of_nat n))));;

let rec load_uint64_of_sint8
  ba n =
    (fun () -> 
      Int64.of_int (Bytes.get_int8 ba (Z.to_int (integer_of_nat n))));;

let rec load_uint64_packed
  a n tp sx =
    (fun () ->
      (let x =
         (match (tp, sx) with (Tp_i8, S) -> load_uint64_of_sint8 a n
           | (Tp_i8, U) -> load_uint64_of_uint8 a n
           | (Tp_i16, S) -> load_uint64_of_sint16 a n
           | (Tp_i16, U) -> load_uint64_of_uint16 a n
           | (Tp_i32, S) -> load_uint64_of_sint32 a n
           | (Tp_i32, U) -> load_uint64_of_uint32 a n)
           ()
         in
        x));;

let rec load_uint32_of_uint16
  ba n =
    (fun () -> 
      Int32.of_int (Bytes.get_uint16_le ba (Z.to_int (integer_of_nat n))));;

let rec load_uint32_of_sint16
  ba n =
    (fun () -> 
      Int32.of_int (Bytes.get_int16_le ba (Z.to_int (integer_of_nat n))));;

let rec load_uint32_of_uint8
  ba n =
    (fun () -> 
      Int32.of_int (Bytes.get_uint8 ba (Z.to_int (integer_of_nat n))));;

let rec load_uint32_of_sint8
  ba n =
    (fun () -> 
      Int32.of_int (Bytes.get_int8 ba (Z.to_int (integer_of_nat n))));;

let rec load_uint32_packed
  a n tp sx =
    (fun () ->
      (let x =
         (match (tp, sx) with (Tp_i8, S) -> load_uint32_of_sint8 a n
           | (Tp_i8, U) -> load_uint32_of_uint8 a n
           | (Tp_i16, S) -> load_uint32_of_sint16 a n
           | (Tp_i16, U) -> load_uint32_of_uint16 a n
           | (Tp_i32, S) -> load_uint32 a n | (Tp_i32, U) -> load_uint32 a n)
           ()
         in
        x));;

let rec load_packed_m_v
  m n off t tp sx =
    (fun () ->
      (let m_len = len_byte_array (fst m) () in
        (if less_eq_nat (plus_nat (plus_nat n off) (tp_num_length tp)) m_len
          then (match t
                 with T_i32 ->
                   (fun f_ () -> f_
                     ((load_uint32_packed (fst m) (plus_nat n off) tp sx) ())
                     ())
                     (fun v -> (fun () -> (Some (ConstInt32 (I32_impl_abs v)))))
                 | T_i64 ->
                   (fun f_ () -> f_
                     ((load_uint64_packed (fst m) (plus_nat n off) tp sx) ())
                     ())
                     (fun v -> (fun () -> (Some (ConstInt64 (I64_impl_abs v)))))
                 | T_f32 ->
                   (fun f_ () -> f_
                     ((load_uint32_packed (fst m) (plus_nat n off) tp sx) ())
                     ())
                     (fun v ->
                       (fun () ->
                         (Some (ConstFloat32
                                 (deserialise_f32
                                   (serialise_i32 (I32_impl_abs v)))))))
                 | T_f64 ->
                   (fun f_ () -> f_
                     ((load_uint64_packed (fst m) (plus_nat n off) tp sx) ())
                     ())
                     (fun v ->
                       (fun () ->
                         (Some (ConstFloat64
                                 (deserialise_f64
                                   (serialise_i64 (I64_impl_abs v))))))))
          else (fun () -> None))
          ()));;

let rec load_m_v
  m n off t =
    (fun () ->
      (let m_len = len_byte_array (fst m) () in
        (if less_eq_nat (plus_nat (plus_nat n off) (t_num_length t)) m_len
          then (match t
                 with T_i32 ->
                   (fun f_ () -> f_ ((load_uint32 (fst m) (plus_nat n off)) ())
                     ())
                     (fun v -> (fun () -> (Some (ConstInt32 (I32_impl_abs v)))))
                 | T_i64 ->
                   (fun f_ () -> f_ ((load_uint64 (fst m) (plus_nat n off)) ())
                     ())
                     (fun v -> (fun () -> (Some (ConstInt64 (I64_impl_abs v)))))
                 | T_f32 ->
                   (fun f_ () -> f_ ((load_uint32 (fst m) (plus_nat n off)) ())
                     ())
                     (fun v ->
                       (fun () ->
                         (Some (ConstFloat32
                                 (deserialise_f32
                                   (serialise_i32 (I32_impl_abs v)))))))
                 | T_f64 ->
                   (fun f_ () -> f_ ((load_uint64 (fst m) (plus_nat n off)) ())
                     ())
                     (fun v ->
                       (fun () ->
                         (Some (ConstFloat64
                                 (deserialise_f64
                                   (serialise_i64 (I64_impl_abs v))))))))
          else (fun () -> None))
          ()));;

let rec app_s_f_v_s_load_maybe_packed_m
  t tp_sx off ms i_m v_s =
    (match v_s with [] -> (fun () -> (v_s, crash_invalid))
      | V_num (ConstInt32 c) :: v_sa ->
        (fun () ->
          (let j = array_nth heap_nat (memsa i_m) zero_nat () in
           let m =
             array_nth (heap_prod heap_byte_array (heap_option heap_nat)) ms j
               ()
             in
           let a =
             (match tp_sx with None -> load_m_v m (nat_of_int_i32 c) off t
               | Some a ->
                 (let (aa, b) = a in
                   load_packed_m_v m (nat_of_int_i32 c) off t aa b))
               ()
             in
            (match a with None -> (fun () -> (v_sa, Res_trap "load"))
              | Some v -> (fun () -> (V_num v :: v_sa, Step_normal)))
              ()))
      | V_num (ConstInt64 _) :: _ -> (fun () -> (v_s, crash_invalid))
      | V_num (ConstFloat32 _) :: _ -> (fun () -> (v_s, crash_invalid))
      | V_num (ConstFloat64 _) :: _ -> (fun () -> (v_s, crash_invalid))
      | V_vec _ :: _ -> (fun () -> (v_s, crash_invalid)));;

let rec load_bytes_m_v
  m n off l =
    (fun () ->
      (let m_len = len_byte_array (fst m) () in
        (let ind = plus_nat n off in
          (if less_eq_nat (plus_nat ind l) m_len
            then (fun f_ () -> f_ ((load_uint8_list (fst m) ind l) ()) ())
                   (fun bs -> (fun () -> (Some bs)))
            else (fun () -> None)))
          ()));;

let rec insert_lane_vec_bs
  len_lane i bs_lane bs_vec =
    take (times_nata i len_lane) bs_vec @
      take len_lane bs_lane @
        drop (times_nata (plus_nat i one_nata) len_lane) bs_vec;;

let rec insert_lane_vec
  svi i bs v =
    (let bs_v = serialise_v128 v in
      deserialise_v128 (insert_lane_vec_bs (vec_i_length svi) i bs bs_v));;

let rec app_s_f_v_s_load_lane_vec_m
  svi i_n off ms i_m v_s =
    (match v_s with [] -> (fun () -> (v_s, crash_invalid))
      | V_num _ :: _ -> (fun () -> (v_s, crash_invalid))
      | [V_vec (ConstVec128 _)] -> (fun () -> (v_s, crash_invalid))
      | V_vec (ConstVec128 v) :: V_num (ConstInt32 c) :: v_sa ->
        (fun () ->
          (let j = array_nth heap_nat (memsa i_m) zero_nat () in
           let m =
             array_nth (heap_prod heap_byte_array (heap_option heap_nat)) ms j
               ()
             in
           let a = load_bytes_m_v m (nat_of_int_i32 c) off (vec_i_length svi) ()
             in
            (match a with None -> (fun () -> (v_sa, Res_trap "load_lane_vec"))
              | Some bs ->
                (fun () ->
                  (V_vec (ConstVec128 (insert_lane_vec svi i_n bs v)) :: v_sa,
                    Step_normal)))
              ()))
      | V_vec (ConstVec128 _) :: V_num (ConstInt64 _) :: _ ->
        (fun () -> (v_s, crash_invalid))
      | V_vec (ConstVec128 _) :: V_num (ConstFloat32 _) :: _ ->
        (fun () -> (v_s, crash_invalid))
      | V_vec (ConstVec128 _) :: V_num (ConstFloat64 _) :: _ ->
        (fun () -> (v_s, crash_invalid))
      | V_vec (ConstVec128 _) :: V_vec _ :: _ ->
        (fun () -> (v_s, crash_invalid)));;

let rec types (Inst_m_ext (types, funcs, tabs, mems, globs, more)) = types;;

let rec app_s_f_v_s_call_indirect_m
  k tinsts cls inst_m v_s =
    (match v_s with [] -> (fun () -> (v_s, ([], crash_invalid)))
      | V_num (ConstInt32 c) :: v_sa ->
        (fun () ->
          (let j = array_nth heap_nat (tabsa inst_m) zero_nat () in
           let tab_j =
             array_nth
               (heap_prod (heap_array (typerep_option typerep_nat))
                 (heap_option heap_nat))
               tinsts j ()
             in
           let tab_j_len = len (heap_option heap_nat) (fst tab_j) () in
            (if less_nat (nat_of_int_i32 c) tab_j_len
              then (fun f_ () -> f_
                     ((array_nth (heap_option heap_nat) (fst tab_j)
                        (nat_of_int_i32 c))
                     ()) ())
                     (fun a ->
                       (match a
                         with None ->
                           (fun () -> (v_sa, ([], Res_trap "call_indirect")))
                         | Some i_cl ->
                           (fun f_ () -> f_ ((array_nth heap_cl_m cls i_cl) ())
                             ())
                             (fun cl_i ->
                               (fun f_ () -> f_
                                 ((array_nth heap_tf (types inst_m) k) ()) ())
                                 (fun t_k ->
                                   (if equal_tfa t_k (cl_m_type cl_i)
                                     then (fun () ->
    (v_sa, ([Invoke i_cl], Step_normal)))
                                     else (fun () ->
    (v_sa, ([], Res_trap "call_indirect"))))))))
              else (fun () -> (v_sa, ([], Res_trap "call_indirect"))))
              ()))
      | V_num (ConstInt64 _) :: _ -> (fun () -> (v_s, ([], crash_invalid)))
      | V_num (ConstFloat32 _) :: _ -> (fun () -> (v_s, ([], crash_invalid)))
      | V_num (ConstFloat64 _) :: _ -> (fun () -> (v_s, ([], crash_invalid)))
      | V_vec _ :: _ -> (fun () -> (v_s, ([], crash_invalid))));;

let rec app_s_f_v_s_set_global_m
  k gs inst_m v_s =
    (match v_s with [] -> (fun () -> (v_s, crash_invalid))
      | v1 :: v_sa ->
        (fun () ->
          (let g_ind = array_nth heap_nat (globsa inst_m) k () in
           let g = array_nth (heap_global_ext heap_unit) gs g_ind () in
           let _ =
             upd (heap_global_ext heap_unit) g_ind
               (g_val_update (fun _ -> v1) g) gs ()
             in
            (v_sa, Step_normal))));;

let rec app_s_f_v_s_get_global_m
  k gs inst_m v_s =
    (fun () ->
      (let g_ind = array_nth heap_nat (globsa inst_m) k () in
       let g = array_nth (heap_global_ext heap_unit) gs g_ind () in
        (g_val g :: v_s, Step_normal)));;

let rec store_serialise_vec
  svop v =
    (match svop with Store_128 -> serialise_v128 v
      | Store_lane (svi, i) ->
        take (vec_i_length svi)
          (drop (times_nata i (vec_i_length svi)) (serialise_v128 v)));;

let rec app_s_f_v_s_store_vec_m
  sv off ms i_m v_s =
    (match v_s with [] -> (fun () -> (v_s, crash_invalid))
      | V_num _ :: _ -> (fun () -> (v_s, crash_invalid))
      | [V_vec (ConstVec128 _)] -> (fun () -> (v_s, crash_invalid))
      | V_vec (ConstVec128 v) :: V_num (ConstInt32 c) :: v_sa ->
        (fun () ->
          (let j = array_nth heap_nat (memsa i_m) zero_nat () in
           let m =
             array_nth (heap_prod heap_byte_array (heap_option heap_nat)) ms j
               ()
             in
           let m_len = len_byte_array (fst m) () in
            (let bs = store_serialise_vec sv v in
             let n = plus_nat (nat_of_int_i32 c) off in
              (if less_eq_nat (plus_nat n (size_list bs)) m_len
                then (fun f_ () -> f_ ((store_uint8_list (fst m) n bs) ()) ())
                       (fun _ -> (fun () -> (v_sa, Step_normal)))
                else (fun () -> (v_sa, Res_trap "store_vec"))))
              ()))
      | V_vec (ConstVec128 _) :: V_num (ConstInt64 _) :: _ ->
        (fun () -> (v_s, crash_invalid))
      | V_vec (ConstVec128 _) :: V_num (ConstFloat32 _) :: _ ->
        (fun () -> (v_s, crash_invalid))
      | V_vec (ConstVec128 _) :: V_num (ConstFloat64 _) :: _ ->
        (fun () -> (v_s, crash_invalid))
      | V_vec (ConstVec128 _) :: V_vec _ :: _ ->
        (fun () -> (v_s, crash_invalid)));;

let rec app_s_f_v_s_mem_size_m
  ms i_m v_s =
    (fun () ->
      (let j = array_nth heap_nat (memsa i_m) zero_nat () in
       let m =
         array_nth (heap_prod heap_byte_array (heap_option heap_nat)) ms j () in
       let m_len = len_byte_array (fst m) () in
        (V_num (ConstInt32 (int_of_nat_i32 (divide_nat m_len ki64))) :: v_s,
          Step_normal)));;

let rec grow_zeroed_byte_array
  a n = (if equal_nat n zero_nat then (fun () -> a)
          else (fun () ->
                 (let l = len_byte_array a () in
                  let aa = new_zeroed_byte_array (plus_nat l n) () in
                  let _ = blit_byte_array a zero_nat aa zero_nat l () in
                   aa)));;

let int32_minus_one : i32 = I32_impl_abs (Int32.neg Int32.one);;

let rec app_s_f_v_s_mem_grow_m
  ms i_m v_s =
    (match v_s with [] -> (fun () -> (v_s, crash_invalid))
      | V_num (ConstInt32 c) :: v_sa ->
        (fun () ->
          (let j = array_nth heap_nat (memsa i_m) zero_nat () in
           let m =
             array_nth (heap_prod heap_byte_array (heap_option heap_nat)) ms j
               ()
             in
           let m_len = len_byte_array (fst m) () in
            (let new_m_len = plus_nat (divide_nat m_len ki64) (nat_of_int_i32 c)
               in
              (if less_eq_nat new_m_len
                    (power power_nat (nat_of_integer (Z.of_int 2))
                      (nat_of_integer (Z.of_int 16))) &&
                    pred_option (less_eq_nat new_m_len) (snd m)
                then (fun f_ () -> f_
                       ((grow_zeroed_byte_array (fst m)
                          (times_nata (nat_of_int_i32 c) ki64))
                       ()) ())
                       (fun m_new_fst ->
                         (fun f_ () -> f_
                           ((upd (heap_prod heap_byte_array
                                   (heap_option heap_nat))
                              j (m_new_fst, snd m) ms)
                           ()) ())
                           (fun _ ->
                             (fun () ->
                               (V_num (ConstInt32
(int_of_nat_i32 (divide_nat m_len ki64))) ::
                                  v_sa,
                                 Step_normal))))
                else (fun () ->
                       (V_num (ConstInt32 int32_minus_one) :: v_sa,
                         Step_normal))))
              ()))
      | V_num (ConstInt64 _) :: _ -> (fun () -> (v_s, crash_invalid))
      | V_num (ConstFloat32 _) :: _ -> (fun () -> (v_s, crash_invalid))
      | V_num (ConstFloat64 _) :: _ -> (fun () -> (v_s, crash_invalid))
      | V_vec _ :: _ -> (fun () -> (v_s, crash_invalid)));;

let rec load_bytes_vec_m_v
  n len sx m ind =
    (if equal_nat n zero_nat then (fun () -> [])
      else (fun () ->
             (let bs = load_uint8_list m ind len () in
              let bsa =
                load_bytes_vec_m_v (minus_nat n one_nata) len sx m
                  (plus_nat ind len) ()
                in
               sign_extend sx (times_nata len (nat_of_integer (Z.of_int 2)))
                 bs @
                 bsa)));;

let rec load_packed_vec_m_v
  tp sx m n off =
    (fun () ->
      (let m_len = len_byte_array (fst m) () in
        (if less_eq_nat
              (plus_nat (plus_nat n off)
                (times_nata (tp_vec_num tp) (tp_vec_length tp)))
              m_len
          then (fun f_ () -> f_
                 ((load_bytes_vec_m_v (tp_vec_num tp) (tp_vec_length tp) sx
                    (fst m) (plus_nat n off))
                 ()) ())
                 (fun bs -> (fun () -> (Some bs)))
          else (fun () -> None))
          ()));;

let rec load_vec_m_v
  lv m n off =
    (match lv with Load_128 -> load_bytes_m_v m n off (t_vec_length T_v128)
      | Load_packed_vec (tp, sx) -> load_packed_vec_m_v tp sx m n off
      | Load_32_zero ->
        (fun () ->
          (let bs_maybe =
             load_bytes_m_v m n off (nat_of_integer (Z.of_int 4)) () in
            map_option (bytes_takefill zero_byte (t_vec_length T_v128))
              bs_maybe))
      | Load_64_zero ->
        (fun () ->
          (let bs_maybe =
             load_bytes_m_v m n off (nat_of_integer (Z.of_int 8)) () in
            map_option (bytes_takefill zero_byte (t_vec_length T_v128))
              bs_maybe))
      | Load_splat svi ->
        (fun () ->
          (let bs_maybe = load_bytes_m_v m n off (vec_i_length svi) () in
            map_option (fun bs -> concat (replicate (vec_i_num svi) bs))
              bs_maybe)));;

let rec app_s_f_v_s_load_vec_m
  lv off ms i_m v_s =
    (match v_s with [] -> (fun () -> (v_s, crash_invalid))
      | V_num (ConstInt32 c) :: v_sa ->
        (fun () ->
          (let j = array_nth heap_nat (memsa i_m) zero_nat () in
           let m =
             array_nth (heap_prod heap_byte_array (heap_option heap_nat)) ms j
               ()
             in
           let a = load_vec_m_v lv m (nat_of_int_i32 c) off () in
            (match a with None -> (fun () -> (v_sa, Res_trap "load_vec"))
              | Some v ->
                (fun () ->
                  (V_vec (ConstVec128 (deserialise_v128 v)) :: v_sa,
                    Step_normal)))
              ()))
      | V_num (ConstInt64 _) :: _ -> (fun () -> (v_s, crash_invalid))
      | V_num (ConstFloat32 _) :: _ -> (fun () -> (v_s, crash_invalid))
      | V_num (ConstFloat64 _) :: _ -> (fun () -> (v_s, crash_invalid))
      | V_vec _ :: _ -> (fun () -> (v_s, crash_invalid)));;

let rec app_f_v_s_set_local_m
  k loc_arr v_s =
    (match v_s with [] -> (fun () -> (v_s, crash_invalid))
      | v1 :: v_sa ->
        (fun () ->
          (let _ = upd heap_v k v1 loc_arr () in (v_sa, Step_normal))));;

let rec app_f_v_s_get_local_m
  k loc_arr v_s =
    (fun () ->
      (let v = array_nth heap_v loc_arr k () in (v :: v_s, Step_normal)));;

let rec update_redex_step
  (Redex (v_sa, es, b_es)) v_s es_cont = Redex (v_s, es_cont @ es, b_es);;

let rec update_fc_step_m
  (Frame_context_m (rdx, lcs, nf, f1, f2)) v_s es_cont =
    Frame_context_m (update_redex_step rdx v_s es_cont, lcs, nf, f1, f2);;

let rec app_replace_vec
  sv i vv vn =
    (let bs_v = bits_vec vv in
     let bs_n = bits_num vn in
      ConstVec128
        (deserialise_v128 (insert_lane_vec_bs (vec_length sv) i bs_n bs_v)));;

let rec app_v_s_replace_vec
  sv i v_s =
    (match v_s with [] -> (v_s, crash_invalid)
      | [V_num _] -> (v_s, crash_invalid)
      | V_num _ :: V_num _ :: _ -> (v_s, crash_invalid)
      | V_num v2 :: V_vec v1 :: v_sa ->
        (V_vec (app_replace_vec sv i v1 v2) :: v_sa, Step_normal)
      | V_vec _ :: _ -> (v_s, crash_invalid));;

let rec app_extract_vec
  sv sx i vv =
    (let bs_v = bits_vec vv in
     let len_lane = vec_length sv in
     let bs_n = take len_lane (drop (times_nata i len_lane) bs_v) in
      (match sv
        with Svi I8_16 ->
          ConstInt32
            (deserialise_i32
              (sign_extend sx (nat_of_integer (Z.of_int 4)) bs_n))
        | Svi I16_8 ->
          ConstInt32
            (deserialise_i32
              (sign_extend sx (nat_of_integer (Z.of_int 4)) bs_n))
        | Svi I32_4 -> ConstInt32 (deserialise_i32 bs_n)
        | Svi I64_2 -> ConstInt64 (deserialise_i64 bs_n)
        | Svf F32_4 -> ConstFloat32 (deserialise_f32 bs_n)
        | Svf F64_2 -> ConstFloat64 (deserialise_f64 bs_n)));;

let rec app_v_s_extract_vec
  sv sx i v_s =
    (match v_s with [] -> (v_s, crash_invalid)
      | V_num _ :: _ -> (v_s, crash_invalid)
      | V_vec v1 :: v_sa ->
        (V_num (app_extract_vec sv sx i v1) :: v_sa, Step_normal));;

let rec app_f_call_m
  k inst_m =
    (fun () ->
      (let i_cl = array_nth heap_nat (funcsa inst_m) k () in
        ([Invoke i_cl], Step_normal)));;

let rec app_ternop_vec_v x = V128Wrapper.ternop_vec x;;

let rec app_ternop_vec
  op v1 v2 v3 =
    (let (ConstVec128 c1, (ConstVec128 c2, ConstVec128 c3)) = (v1, (v2, v3)) in
      ConstVec128 (app_ternop_vec_v op c1 c2 c3));;

let rec app_v_s_ternop_vec
  op v_s =
    (match v_s with [] -> (v_s, crash_invalid)
      | V_num _ :: _ -> (v_s, crash_invalid) | [V_vec _] -> (v_s, crash_invalid)
      | V_vec _ :: V_num _ :: _ -> (v_s, crash_invalid)
      | [V_vec _; V_vec _] -> (v_s, crash_invalid)
      | V_vec _ :: V_vec _ :: V_num _ :: _ -> (v_s, crash_invalid)
      | V_vec v3 :: V_vec v2 :: V_vec v1 :: v_sa ->
        (V_vec (app_ternop_vec op v1 v2 v3) :: v_sa, Step_normal));;

let rec app_v_s_tee_local
  k v_s =
    (match v_s with [] -> (v_s, ([], crash_invalid))
      | v1 :: v_sa ->
        (v1 :: v1 :: v_sa, ([Basic (Set_local k)], Step_normal)));;

let rec app_v_s_splat_vec
  sv v_s =
    (match v_s with [] -> (v_s, crash_invalid)
      | V_num v1 :: v_sa -> (V_vec (app_splat_vec sv v1) :: v_sa, Step_normal)
      | V_vec _ :: _ -> (v_s, crash_invalid));;

let rec app_v_s_shift_vec
  op v_s =
    (match v_s with [] -> (v_s, crash_invalid)
      | [V_num (ConstInt32 _)] -> (v_s, crash_invalid)
      | V_num (ConstInt32 _) :: V_num _ :: _ -> (v_s, crash_invalid)
      | V_num (ConstInt32 v2) :: V_vec v1 :: v_sa ->
        (V_vec (app_shift_vec op v1 v2) :: v_sa, Step_normal)
      | V_num (ConstInt64 _) :: _ -> (v_s, crash_invalid)
      | V_num (ConstFloat32 _) :: _ -> (v_s, crash_invalid)
      | V_num (ConstFloat64 _) :: _ -> (v_s, crash_invalid)
      | V_vec _ :: _ -> (v_s, crash_invalid));;

let rec app_v_s_binop_vec
  op v_s =
    (match v_s with [] -> (v_s, crash_invalid)
      | V_num _ :: _ -> (v_s, crash_invalid) | [V_vec _] -> (v_s, crash_invalid)
      | V_vec _ :: V_num _ :: _ -> (v_s, crash_invalid)
      | V_vec v2 :: V_vec v1 :: v_sa ->
        (match app_binop_vec op v1 v2 with None -> (v_sa, Res_trap "binop_vec")
          | Some a -> (V_vec a :: v_sa, Step_normal)));;

let rec app_v_s_unop_vec
  op v_s =
    (match v_s with [] -> (v_s, crash_invalid)
      | V_num _ :: _ -> (v_s, crash_invalid)
      | V_vec v1 :: v_sa -> (V_vec (app_unop_vec op v1) :: v_sa, Step_normal));;

let rec app_v_s_test_vec
  op v_s =
    (match v_s with [] -> (v_s, crash_invalid)
      | V_num _ :: _ -> (v_s, crash_invalid)
      | V_vec v1 :: v_sa ->
        (V_num (ConstInt32 (app_test_vec op v1)) :: v_sa, Step_normal));;

let rec app_v_s_br_table
  ks k v_s =
    (match v_s with [] -> (v_s, ([], crash_invalid))
      | V_num (ConstInt32 c) :: v_sa ->
        (let j = nat_of_int_i32 c in
          (if less_nat j (size_list ks)
            then (v_sa, ([Basic (Br (nth ks j))], Step_normal))
            else (v_sa, ([Basic (Br k)], Step_normal))))
      | V_num (ConstInt64 _) :: _ -> (v_s, ([], crash_invalid))
      | V_num (ConstFloat32 _) :: _ -> (v_s, ([], crash_invalid))
      | V_num (ConstFloat64 _) :: _ -> (v_s, ([], crash_invalid))
      | V_vec _ :: _ -> (v_s, ([], crash_invalid)));;

let crash_invariant : res_step
  = Res_crash (Error_invariant "interpreter invariant violation");;

let rec app_v_s_testop
  testop v_s =
    (match v_s with [] -> (v_s, crash_invalid)
      | V_num v1 :: v_sa -> (V_num (app_testop testop v1) :: v_sa, Step_normal)
      | V_vec _ :: _ -> (v_s, crash_invalid));;

let rec app_v_s_select
  v_s = (match v_s with [] -> (v_s, crash_invalid)
          | [V_num (ConstInt32 _)] -> (v_s, crash_invalid)
          | [V_num (ConstInt32 _); _] -> (v_s, crash_invalid)
          | V_num (ConstInt32 c) :: v2 :: v1 :: v_sa ->
            (if int_eq_i32 c zero_i32a then (v2 :: v_sa, Step_normal)
              else (v1 :: v_sa, Step_normal))
          | V_num (ConstInt64 _) :: _ -> (v_s, crash_invalid)
          | V_num (ConstFloat32 _) :: _ -> (v_s, crash_invalid)
          | V_num (ConstFloat64 _) :: _ -> (v_s, crash_invalid)
          | V_vec _ :: _ -> (v_s, crash_invalid));;

let rec tb_tf_m
  tfa tb =
    (match tb with Tbf a -> array_nth heap_tf (types tfa) a
      | Tbv None -> (fun () -> (Tf ([], [])))
      | Tbv (Some t) -> (fun () -> (Tf ([], [t]))));;

let rec app_v_s_relop
  relop v_s =
    (match v_s with [] -> (v_s, crash_invalid)
      | [V_num _] -> (v_s, crash_invalid)
      | V_num v2 :: V_num v1 :: v_sa ->
        (V_num (app_relop relop v1 v2) :: v_sa, Step_normal)
      | V_num _ :: V_vec _ :: _ -> (v_s, crash_invalid)
      | V_vec _ :: _ -> (v_s, crash_invalid));;

let rec wasm_reinterpret
  t v = (match (t, v)
          with (T_i32, ConstInt32 _) -> wasm_deserialise_num (bits_num v) t
          | (T_i32, ConstInt64 _) -> wasm_deserialise_num (bits_num v) t
          | (T_i32, ConstFloat32 c) ->
            ConstInt32
              (ocaml_int32_to_isabelle_int32
                (I32Wrapper_convert.reinterpret_of_f32 c))
          | (T_i32, ConstFloat64 _) -> wasm_deserialise_num (bits_num v) t
          | (T_i64, ConstInt32 _) -> wasm_deserialise_num (bits_num v) t
          | (T_i64, ConstInt64 _) -> wasm_deserialise_num (bits_num v) t
          | (T_i64, ConstFloat32 _) -> wasm_deserialise_num (bits_num v) t
          | (T_i64, ConstFloat64 c) ->
            ConstInt64
              (ocaml_int64_to_isabelle_int64
                (I64Wrapper_convert.reinterpret_of_f64 c))
          | (T_f32, ConstInt32 c) ->
            ConstFloat32
              (I32Wrapper_convert.reinterpret_to_f32
                (isabelle_int32_to_ocaml_int32 c))
          | (T_f32, ConstInt64 _) -> wasm_deserialise_num (bits_num v) t
          | (T_f32, ConstFloat32 _) -> wasm_deserialise_num (bits_num v) t
          | (T_f32, ConstFloat64 _) -> wasm_deserialise_num (bits_num v) t
          | (T_f64, ConstInt32 _) -> wasm_deserialise_num (bits_num v) t
          | (T_f64, ConstInt64 c) ->
            ConstFloat64
              (I64Wrapper_convert.reinterpret_to_f64
                (isabelle_int64_to_ocaml_int64 c))
          | (T_f64, ConstFloat32 _) -> wasm_deserialise_num (bits_num v) t
          | (T_f64, ConstFloat64 _) -> wasm_deserialise_num (bits_num v) t);;

let rec app_v_s_cvtop
  cvtop t1 t2 tp_sx v_s =
    (match v_s with [] -> (v_s, crash_invalid)
      | V_num v1 :: v_sa ->
        (if equal_t_num (typeof_num v1) t1
          then (match cvtop
                 with Convert ->
                   (match cvt t2 tp_sx v1
                     with None -> (v_sa, Res_trap (name typerep_cvtop cvtop))
                     | Some a -> (V_num a :: v_sa, Step_normal))
                 | Reinterpret ->
                   (if is_none tp_sx
                     then (V_num (wasm_reinterpret t2 v1) :: v_sa, Step_normal)
                     else (v_s, crash_invalid)))
          else (v_s, crash_invalid))
      | V_vec _ :: _ -> (v_s, crash_invalid));;

let rec app_v_s_br_if
  k v_s =
    (match v_s with [] -> (v_s, ([], crash_invalid))
      | V_num (ConstInt32 c) :: v_sa ->
        (if int_eq_i32 c zero_i32a then (v_sa, ([], Step_normal))
          else (v_sa, ([Basic (Br k)], Step_normal)))
      | V_num (ConstInt64 _) :: _ -> (v_s, ([], crash_invalid))
      | V_num (ConstFloat32 _) :: _ -> (v_s, ([], crash_invalid))
      | V_num (ConstFloat64 _) :: _ -> (v_s, ([], crash_invalid))
      | V_vec _ :: _ -> (v_s, ([], crash_invalid)));;

let rec app_v_s_binop
  binop v_s =
    (match v_s with [] -> (v_s, crash_invalid)
      | [V_num _] -> (v_s, crash_invalid)
      | V_num v2 :: V_num v1 :: v_sa ->
        (match app_binop binop v1 v2
          with None -> (v_sa, Res_trap (name typerep_binop binop))
          | Some a -> (V_num a :: v_sa, Step_normal))
      | V_num _ :: V_vec _ :: _ -> (v_s, crash_invalid)
      | V_vec _ :: _ -> (v_s, crash_invalid));;

let rec app_v_s_unop
  unop v_s =
    (match v_s with [] -> (v_s, crash_invalid)
      | V_num v1 :: v_sa -> (V_num (app_unop unop v1) :: v_sa, Step_normal)
      | V_vec _ :: _ -> (v_s, crash_invalid));;

let rec app_v_s_drop
  v_s = (match v_s with [] -> (v_s, crash_invalid)
          | _ :: v_sa -> (v_sa, Step_normal));;

let rec run_step_b_e_m
  b_e (Config_m (d, s, fc, fcs)) =
    (let Frame_context_m (Redex (v_s, es, b_es), lcs, nf, f_locs1, f_inst2) = fc
       in
      (match b_e
        with Unreachable ->
          (fun () -> (Config_m (d, s, fc, fcs), Res_trap "unreachable"))
        | Nop -> (fun () -> (Config_m (d, s, fc, fcs), Step_normal))
        | Drop ->
          (let (v_sa, res) = app_v_s_drop v_s in
            (fun () ->
              (Config_m (d, s, update_fc_step_m fc v_sa [], fcs), res)))
        | Select ->
          (let (v_sa, res) = app_v_s_select v_s in
            (fun () ->
              (Config_m (d, s, update_fc_step_m fc v_sa [], fcs), res)))
        | Block (tb, b_ebs) ->
          (if not (null es)
            then (fun () -> (Config_m (d, s, fc, fcs), crash_invariant))
            else (fun () ->
                   (let a = tb_tf_m f_inst2 tb () in
                     (let Tf (t1s, t2s) = a in
                      let n = size_list t1s in
                      let m = size_list t2s in
                       (if less_eq_nat n (size_list v_s)
                         then (let (v_bs, v_sa) = split_n v_s n in
                               let lc = Label_context (v_sa, b_es, m, []) in
                               let fca =
                                 Frame_context_m
                                   (Redex (v_bs, [], b_ebs), lc :: lcs, nf,
                                     f_locs1, f_inst2)
                                 in
                                (fun () ->
                                  (Config_m (d, s, fca, fcs), Step_normal)))
                         else (fun () ->
                                (Config_m (d, s, fc, fcs), crash_invalid))))
                       ())))
        | Loop (tb, b_els) ->
          (if not (null es)
            then (fun () -> (Config_m (d, s, fc, fcs), crash_invariant))
            else (fun () ->
                   (let a = tb_tf_m f_inst2 tb () in
                     (let Tf (t1s, t2s) = a in
                      let n = size_list t1s in
                      let _ = size_list t2s in
                       (if less_eq_nat n (size_list v_s)
                         then (let (v_bs, v_sa) = split_n v_s n in
                               let lc =
                                 Label_context
                                   (v_sa, b_es, n, [Loop (tb, b_els)])
                                 in
                               let fca =
                                 Frame_context_m
                                   (Redex (v_bs, [], b_els), lc :: lcs, nf,
                                     f_locs1, f_inst2)
                                 in
                                (fun () ->
                                  (Config_m (d, s, fca, fcs), Step_normal)))
                         else (fun () ->
                                (Config_m (d, s, fc, fcs), crash_invalid))))
                       ())))
        | If (tb, es1, es2) ->
          (let (v_sa, (es_cont, res)) = app_v_s_if tb es1 es2 v_s in
            (fun () ->
              (Config_m (d, s, update_fc_step_m fc v_sa es_cont, fcs), res)))
        | Br k ->
          (if less_nat k (size_list lcs)
            then (let Label_context (v_ls, b_els, nl, b_ecls) = nth lcs k in
                   (if less_eq_nat nl (size_list v_s)
                     then (let v_sa = take nl v_s in
                           let fca =
                             Frame_context_m
                               (Redex (v_sa @ v_ls, [], b_ecls @ b_els),
                                 drop (suc k) lcs, nf, f_locs1, f_inst2)
                             in
                            (fun () ->
                              (Config_m (d, s, fca, fcs), Step_normal)))
                     else (fun () ->
                            (Config_m (d, s, fc, fcs), crash_invalid))))
            else (fun () -> (Config_m (d, s, fc, fcs), crash_invalid)))
        | Br_if k ->
          (let (v_sa, (es_cont, res)) = app_v_s_br_if k v_s in
            (fun () ->
              (Config_m (d, s, update_fc_step_m fc v_sa es_cont, fcs), res)))
        | Br_table (ks, k) ->
          (let (v_sa, (es_cont, res)) = app_v_s_br_table ks k v_s in
            (fun () ->
              (Config_m (d, s, update_fc_step_m fc v_sa es_cont, fcs), res)))
        | Return ->
          (match fcs
            with [] -> (fun () -> (Config_m (d, s, fc, fcs), crash_invalid))
            | fca :: fcsa ->
              (if less_eq_nat nf (size_list v_s)
                then (fun () ->
                       (Config_m
                          (suc d, s, update_fc_return_m fca (take nf v_s),
                            fcsa),
                         Step_normal))
                else (fun () -> (Config_m (d, s, fc, fcs), crash_invalid))))
        | Call k ->
          (fun () ->
            (let a = app_f_call_m k f_inst2 () in
              (let (es_cont, res) = a in
                (fun () ->
                  (Config_m (d, s, update_fc_step_m fc v_s es_cont, fcs), res)))
                ()))
        | Call_indirect k ->
          (fun () ->
            (let a =
               app_s_f_v_s_call_indirect_m k (tabs s) (funcs s) f_inst2 v_s ()
               in
              (let (v_sa, (es_cont, res)) = a in
                (fun () ->
                  (Config_m (d, s, update_fc_step_m fc v_sa es_cont, fcs),
                    res)))
                ()))
        | Get_local k ->
          (fun () ->
            (let a = app_f_v_s_get_local_m k f_locs1 v_s () in
              (let (v_sa, res) = a in
                (fun () ->
                  (Config_m (d, s, update_fc_step_m fc v_sa [], fcs), res)))
                ()))
        | Set_local k ->
          (fun () ->
            (let a = app_f_v_s_set_local_m k f_locs1 v_s () in
              (let (v_sa, res) = a in
               let fca =
                 Frame_context_m
                   (Redex (v_sa, es, b_es), lcs, nf, f_locs1, f_inst2)
                 in
                (fun () -> (Config_m (d, s, fca, fcs), res)))
                ()))
        | Tee_local k ->
          (let (v_sa, (es_cont, res)) = app_v_s_tee_local k v_s in
            (fun () ->
              (Config_m (d, s, update_fc_step_m fc v_sa es_cont, fcs), res)))
        | Get_global k ->
          (fun () ->
            (let a = app_s_f_v_s_get_global_m k (globs s) f_inst2 v_s () in
              (let (v_sa, res) = a in
                (fun () ->
                  (Config_m (d, s, update_fc_step_m fc v_sa [], fcs), res)))
                ()))
        | Set_global k ->
          (fun () ->
            (let a = app_s_f_v_s_set_global_m k (globs s) f_inst2 v_s () in
              (let (v_sa, res) = a in
                (fun () ->
                  (Config_m (d, s, update_fc_step_m fc v_sa [], fcs), res)))
                ()))
        | Load (t, tp_sx, _, off) ->
          (fun () ->
            (let a =
               app_s_f_v_s_load_maybe_packed_m t tp_sx off (mems s) f_inst2 v_s
                 ()
               in
              (let (v_sa, res) = a in
                (fun () ->
                  (Config_m (d, s, update_fc_step_m fc v_sa [], fcs), res)))
                ()))
        | Store (t, tp, _, off) ->
          (fun () ->
            (let a =
               app_s_f_v_s_store_maybe_packed_m t tp off (mems s) f_inst2 v_s ()
               in
              (let (v_sa, res) = a in
                (fun () ->
                  (Config_m (d, s, update_fc_step_m fc v_sa [], fcs), res)))
                ()))
        | Load_vec (lv, _, off) ->
          (fun () ->
            (let a = app_s_f_v_s_load_vec_m lv off (mems s) f_inst2 v_s () in
              (let (v_sa, res) = a in
                (fun () ->
                  (Config_m (d, s, update_fc_step_m fc v_sa [], fcs), res)))
                ()))
        | Load_lane_vec (svi, i, _, off) ->
          (fun () ->
            (let a =
               app_s_f_v_s_load_lane_vec_m svi i off (mems s) f_inst2 v_s () in
              (let (v_sa, res) = a in
                (fun () ->
                  (Config_m (d, s, update_fc_step_m fc v_sa [], fcs), res)))
                ()))
        | Store_vec (sv, _, off) ->
          (fun () ->
            (let a = app_s_f_v_s_store_vec_m sv off (mems s) f_inst2 v_s () in
              (let (v_sa, res) = a in
                (fun () ->
                  (Config_m (d, s, update_fc_step_m fc v_sa [], fcs), res)))
                ()))
        | Current_memory ->
          (fun () ->
            (let a = app_s_f_v_s_mem_size_m (mems s) f_inst2 v_s () in
              (let (v_sa, res) = a in
                (fun () ->
                  (Config_m (d, s, update_fc_step_m fc v_sa [], fcs), res)))
                ()))
        | Grow_memory ->
          (fun () ->
            (let a = app_s_f_v_s_mem_grow_m (mems s) f_inst2 v_s () in
              (let (v_sa, res) = a in
                (fun () ->
                  (Config_m (d, s, update_fc_step_m fc v_sa [], fcs), res)))
                ()))
        | EConst _ -> (fun () -> (Config_m (d, s, fc, fcs), crash_invariant))
        | Unop (_, op) ->
          (let (v_sa, res) = app_v_s_unop op v_s in
            (fun () ->
              (Config_m (d, s, update_fc_step_m fc v_sa [], fcs), res)))
        | Binop (_, op) ->
          (let (v_sa, res) = app_v_s_binop op v_s in
            (fun () ->
              (Config_m (d, s, update_fc_step_m fc v_sa [], fcs), res)))
        | Testop (_, op) ->
          (let (v_sa, res) = app_v_s_testop op v_s in
            (fun () ->
              (Config_m (d, s, update_fc_step_m fc v_sa [], fcs), res)))
        | Relop (_, op) ->
          (let (v_sa, res) = app_v_s_relop op v_s in
            (fun () ->
              (Config_m (d, s, update_fc_step_m fc v_sa [], fcs), res)))
        | Cvtop (t2, op, t1, tp_sx) ->
          (let (v_sa, res) = app_v_s_cvtop op t1 t2 tp_sx v_s in
            (fun () ->
              (Config_m (d, s, update_fc_step_m fc v_sa [], fcs), res)))
        | Unop_vec op ->
          (let (v_sa, res) = app_v_s_unop_vec op v_s in
            (fun () ->
              (Config_m (d, s, update_fc_step_m fc v_sa [], fcs), res)))
        | Binop_vec op ->
          (let (v_sa, res) = app_v_s_binop_vec op v_s in
            (fun () ->
              (Config_m (d, s, update_fc_step_m fc v_sa [], fcs), res)))
        | Ternop_vec op ->
          (let (v_sa, res) = app_v_s_ternop_vec op v_s in
            (fun () ->
              (Config_m (d, s, update_fc_step_m fc v_sa [], fcs), res)))
        | Test_vec op ->
          (let (v_sa, res) = app_v_s_test_vec op v_s in
            (fun () ->
              (Config_m (d, s, update_fc_step_m fc v_sa [], fcs), res)))
        | Shift_vec op ->
          (let (v_sa, res) = app_v_s_shift_vec op v_s in
            (fun () ->
              (Config_m (d, s, update_fc_step_m fc v_sa [], fcs), res)))
        | Splat_vec sv ->
          (let (v_sa, res) = app_v_s_splat_vec sv v_s in
            (fun () ->
              (Config_m (d, s, update_fc_step_m fc v_sa [], fcs), res)))
        | Extract_vec (sv, sx, i) ->
          (let (v_sa, res) = app_v_s_extract_vec sv sx i v_s in
            (fun () ->
              (Config_m (d, s, update_fc_step_m fc v_sa [], fcs), res)))
        | Replace_vec (sv, i) ->
          (let (v_sa, res) = app_v_s_replace_vec sv i v_s in
            (fun () ->
              (Config_m (d, s, update_fc_step_m fc v_sa [], fcs), res)))));;

let rec init_tab_m_v
  t n icls =
    (fun () ->
      (let t_len = len (heap_option heap_nat) (fst t) () in
        (if less_eq_nat (plus_nat n (size_list icls)) t_len
          then (fun f_ () -> f_
                 ((list_blit_array (heap_option heap_nat)
                    (map (fun a -> Some a) icls) (fst t) n)
                 ()) ())
                 (fun _ -> (fun () -> (Some ())))
          else (fun () -> None))
          ()));;

let rec app_s_f_init_tab_m
  off icls ts i_m =
    (fun () ->
      (let j = array_nth heap_nat (tabsa i_m) zero_nat () in
       let t =
         array_nth
           (heap_prod (heap_array (typerep_option typerep_nat))
             (heap_option heap_nat))
           ts j ()
         in
       let a = init_tab_m_v t off icls () in
        (match a with None -> (fun () -> (Res_trap "init_tab"))
          | Some _ -> (fun () -> Step_normal))
          ()));;

let rec init_mem_m_v
  m n bs =
    (fun () ->
      (let m_len = len_byte_array (fst m) () in
        (if less_eq_nat (plus_nat n (size_list bs)) m_len
          then (fun f_ () -> f_ ((store_uint8_list (fst m) n bs) ()) ())
                 (fun _ -> (fun () -> (Some ())))
          else (fun () -> None))
          ()));;

let rec app_s_f_init_mem_m
  off bs ms i_m =
    (fun () ->
      (let j = array_nth heap_nat (memsa i_m) zero_nat () in
       let m =
         array_nth (heap_prod heap_byte_array (heap_option heap_nat)) ms j () in
       let a = init_mem_m_v m off bs () in
        (match a with None -> (fun () -> (Res_trap "init_mem"))
          | Some _ -> (fun () -> Step_normal))
          ()));;

let rec rep_host_m (Abs_host_m x) = x;;

let rec host_apply_impl_m s tf h vs = rep_host_m h (s, vs);;

let crash_exhaustion : res_step
  = Res_crash (Error_exhaustion "call stack exhausted");;

let rec run_step_e_m
  e (Config_m (d, s, fc, fcs)) =
    (let Frame_context_m (Redex (v_s, es, b_es), lcs, nf, f_locs1, f_inst2) = fc
       in
      (match e with Basic b_e -> run_step_b_e_m b_e (Config_m (d, s, fc, fcs))
        | Trap -> (fun () -> (Config_m (d, s, fc, fcs), crash_invariant))
        | Invoke i_cl ->
          (fun () ->
            (let a = array_nth heap_cl_m (funcs s) i_cl () in
              (match a
                with Func_native (i, Tf (t1s, t2s), ts, es_f) ->
                  (if equal_nat d zero_nat
                    then (fun () ->
                           (Config_m (d, s, fc, fcs), crash_exhaustion))
                    else (let n = size_list t1s in
                          let m = size_list t2s in
                           (if less_eq_nat n (size_list v_s)
                             then (let (v_fs, v_sa) = split_n v_s n in
                                   let fca =
                                     Frame_context_m
                                       (Redex (v_sa, es, b_es), lcs, nf,
 f_locs1, f_inst2)
                                     in
                                   let zs = n_zeros ts in
                                    (fun f_ () -> f_
                                      (((fun () -> Array.of_list
 (rev v_fs @ zs)))
                                      ()) ())
                                      (fun ff_locs1 ->
(let lc = Label_context ([], [], m, []) in
 let fcf = Frame_context_m (Redex ([], [], es_f), [lc], m, ff_locs1, i) in
  (fun () ->
    (Config_m (minus_nat d one_nata, s, fcf, fca :: fcs), Step_normal)))))
                             else (fun () ->
                                    (Config_m (d, s, fc, fcs),
                                      crash_invalid)))))
                | Func_host (Tf (t1s, t2s), h) ->
                  (let n = size_list t1s in
                   let _ = size_list t2s in
                    (if less_eq_nat n (size_list v_s)
                      then (let (v_fs, v_sa) = split_n v_s n in
                             (fun f_ () -> f_
                               ((host_apply_impl_m s (Tf (t1s, t2s)) h
                                  (rev v_fs))
                               ()) ())
                               (fun aa ->
                                 (match aa
                                   with None ->
                                     (fun () ->
                                       (Config_m
  (d, s, Frame_context_m (Redex (v_sa, es, b_es), lcs, nf, f_locs1, f_inst2),
    fcs),
 Res_trap "host_apply"))
                                   | Some (sa, rvs) ->
                                     (if list_all2
   (fun t v -> equal_ta (typeof v) t) t2s rvs
                                       then (let fca =
       Frame_context_m
         (Redex (rev rvs @ v_sa, es, b_es), lcs, nf, f_locs1, f_inst2)
       in
      (fun () -> (Config_m (d, sa, fca, fcs), Step_normal)))
                                       else (fun () ->
      (Config_m (d, sa, fc, fcs), crash_invalid))))))
                      else (fun () ->
                             (Config_m (d, s, fc, fcs), crash_invalid)))))
                ()))
        | Label (_, _, _) ->
          (fun () -> (Config_m (d, s, fc, fcs), crash_invariant))
        | Frame (_, _, _) ->
          (fun () -> (Config_m (d, s, fc, fcs), crash_invariant))
        | Init_mem (n, bs) ->
          (fun () ->
            (let res = app_s_f_init_mem_m n bs (mems s) f_inst2 () in
              (Config_m (d, s, fc, fcs), res)))
        | Init_tab (n, icls) ->
          (fun () ->
            (let res = app_s_f_init_tab_m n icls (tabs s) f_inst2 () in
              (Config_m (d, s, fc, fcs), res)))));;

let res_crash_fuel : res = RCrash (Error_invariant "fuel exhausted");;

let rec split_v_s_b_s_aux
  v_s x1 = match v_s, x1 with
    v_s, EConst v :: b_es -> split_v_s_b_s_aux (v :: v_s) b_es
    | v_s, [] -> (v_s, [])
    | v_s, Unreachable :: va -> (v_s, Unreachable :: va)
    | v_s, Nop :: va -> (v_s, Nop :: va)
    | v_s, Drop :: va -> (v_s, Drop :: va)
    | v_s, Select :: va -> (v_s, Select :: va)
    | v_s, Block (vb, vc) :: va -> (v_s, Block (vb, vc) :: va)
    | v_s, Loop (vb, vc) :: va -> (v_s, Loop (vb, vc) :: va)
    | v_s, If (vb, vc, vd) :: va -> (v_s, If (vb, vc, vd) :: va)
    | v_s, Br vb :: va -> (v_s, Br vb :: va)
    | v_s, Br_if vb :: va -> (v_s, Br_if vb :: va)
    | v_s, Br_table (vb, vc) :: va -> (v_s, Br_table (vb, vc) :: va)
    | v_s, Return :: va -> (v_s, Return :: va)
    | v_s, Call vb :: va -> (v_s, Call vb :: va)
    | v_s, Call_indirect vb :: va -> (v_s, Call_indirect vb :: va)
    | v_s, Get_local vb :: va -> (v_s, Get_local vb :: va)
    | v_s, Set_local vb :: va -> (v_s, Set_local vb :: va)
    | v_s, Tee_local vb :: va -> (v_s, Tee_local vb :: va)
    | v_s, Get_global vb :: va -> (v_s, Get_global vb :: va)
    | v_s, Set_global vb :: va -> (v_s, Set_global vb :: va)
    | v_s, Load (vb, vc, vd, ve) :: va -> (v_s, Load (vb, vc, vd, ve) :: va)
    | v_s, Store (vb, vc, vd, ve) :: va -> (v_s, Store (vb, vc, vd, ve) :: va)
    | v_s, Load_vec (vb, vc, vd) :: va -> (v_s, Load_vec (vb, vc, vd) :: va)
    | v_s, Load_lane_vec (vb, vc, vd, ve) :: va ->
        (v_s, Load_lane_vec (vb, vc, vd, ve) :: va)
    | v_s, Store_vec (vb, vc, vd) :: va -> (v_s, Store_vec (vb, vc, vd) :: va)
    | v_s, Current_memory :: va -> (v_s, Current_memory :: va)
    | v_s, Grow_memory :: va -> (v_s, Grow_memory :: va)
    | v_s, Unop (vb, vc) :: va -> (v_s, Unop (vb, vc) :: va)
    | v_s, Binop (vb, vc) :: va -> (v_s, Binop (vb, vc) :: va)
    | v_s, Testop (vb, vc) :: va -> (v_s, Testop (vb, vc) :: va)
    | v_s, Relop (vb, vc) :: va -> (v_s, Relop (vb, vc) :: va)
    | v_s, Cvtop (vb, vc, vd, ve) :: va -> (v_s, Cvtop (vb, vc, vd, ve) :: va)
    | v_s, Unop_vec vb :: va -> (v_s, Unop_vec vb :: va)
    | v_s, Binop_vec vb :: va -> (v_s, Binop_vec vb :: va)
    | v_s, Ternop_vec vb :: va -> (v_s, Ternop_vec vb :: va)
    | v_s, Test_vec vb :: va -> (v_s, Test_vec vb :: va)
    | v_s, Shift_vec vb :: va -> (v_s, Shift_vec vb :: va)
    | v_s, Splat_vec vb :: va -> (v_s, Splat_vec vb :: va)
    | v_s, Extract_vec (vb, vc, vd) :: va ->
        (v_s, Extract_vec (vb, vc, vd) :: va)
    | v_s, Replace_vec (vb, vc) :: va -> (v_s, Replace_vec (vb, vc) :: va);;

let rec split_v_s_b_s es = split_v_s_b_s_aux [] es;;

let rec run_iter_m
  n cfg =
    (if equal_nat n zero_nat then (fun () -> (cfg, res_crash_fuel))
      else (let Config_m
                  (d, s,
                    Frame_context_m
                      (Redex (v_s, es, b_es), lcs, nf, f_locs1, f_inst2),
                    fcs)
              = cfg in
             (match es
               with [] ->
                 (match b_es
                   with [] ->
                     (match lcs
                       with [] ->
                         (match fcs
                           with [] ->
                             (fun () ->
                               (Config_m
                                  (d, s,
                                    Frame_context_m
                                      (Redex (v_s, [], []), [], nf, f_locs1,
f_inst2),
                                    []),
                                 RValue v_s))
                           | fc :: fcsa ->
                             run_iter_m (minus_nat n one_nata)
                               (Config_m
                                 (suc d, s, update_fc_return_m fc v_s, fcsa)))
                       | Label_context (v_ls, b_els, _, _) :: lcsa ->
                         (let f_new =
                            Frame_context_m
                              (Redex (v_s @ v_ls, [], b_els), lcsa, nf, f_locs1,
                                f_inst2)
                            in
                           run_iter_m (minus_nat n one_nata)
                             (Config_m (d, s, f_new, fcs))))
                   | a :: lista ->
                     (match split_v_s_b_s (a :: lista)
                       with (v_sa, []) ->
                         run_iter_m (minus_nat n one_nata)
                           (Config_m
                             (d, s,
                               Frame_context_m
                                 (Redex (v_sa @ v_s, [], []), lcs, nf, f_locs1,
                                   f_inst2),
                               fcs))
                       | (v_sa, b_e :: b_esa) ->
                         (fun () ->
                           (let aa =
                              run_step_b_e_m b_e
                                (Config_m
                                  (d, s,
                                    Frame_context_m
                                      (Redex (v_sa @ v_s, [], b_esa), lcs, nf,
f_locs1, f_inst2),
                                    fcs))
                                ()
                              in
                             (match aa
                               with (cfga, Res_crash str) ->
                                 (fun () -> (cfga, RCrash str))
                               | (cfga, Res_trap str) ->
                                 (fun () -> (cfga, RTrap str))
                               | (cfga, Step_normal) ->
                                 run_iter_m (minus_nat n one_nata) cfga)
                               ()))))
               | e :: esa ->
                 (fun () ->
                   (let a =
                      run_step_e_m e
                        (Config_m
                          (d, s,
                            Frame_context_m
                              (Redex (v_s, esa, b_es), lcs, nf, f_locs1,
                                f_inst2),
                            fcs))
                        ()
                      in
                     (match a
                       with (cfga, Res_crash str) ->
                         (fun () -> (cfga, RCrash str))
                       | (cfga, Res_trap str) -> (fun () -> (cfga, RTrap str))
                       | (cfga, Step_normal) ->
                         run_iter_m (minus_nat n one_nata) cfga)
                       ())))));;

let rec run_v_m
  n d (s, (f_locs1, (f_inst2, b_es))) =
    (fun () ->
      (let a =
         run_iter_m n
           (Config_m
             (d, s,
               Frame_context_m
                 (Redex ([], [], b_es), [], zero_nat, f_locs1, f_inst2),
               []))
           ()
         in
        (let (Config_m (_, sa, _, _), res) = a in (fun () -> (sa, res))) ()));;

let rec interp_get_v_m
  s inst b_es =
    (fun () ->
      (let f_locs1 = (fun () -> Array.of_list []) () in
       let a =
         run_v_m (nat_of_integer (Z.of_int 2)) zero_nat
           (s, (f_locs1, (inst, b_es))) ()
         in
        (match a with (_, RCrash _) -> (fun () -> (failwith "undefined"))
          | (_, RTrap _) -> (fun () -> (failwith "undefined"))
          | (_, RValue []) -> (fun () -> (failwith "undefined"))
          | (_, RValue [v]) -> (fun () -> v)
          | (_, RValue (_ :: _ :: _)) -> (fun () -> (failwith "undefined")))
          ()));;

let rec interp_get_i32_m
  s inst b_es =
    (fun () ->
      (let v = interp_get_v_m s inst b_es () in
        (match v with V_num (ConstInt32 c) -> c
          | V_num (ConstInt64 _) -> zero_i32a
          | V_num (ConstFloat32 _) -> zero_i32a
          | V_num (ConstFloat64 _) -> zero_i32a | V_vec _ -> zero_i32a)));;

let rec d_init (Module_data_ext (d_data, d_off, d_init, more)) = d_init;;

let rec d_data (Module_data_ext (d_data, d_off, d_init, more)) = d_data;;

let rec data_in_bounds_m
  s_m inst_m d_offs m_datas =
    list_all2_m
      (fun d_off d () ->
        (let m_ind = array_nth heap_nat (memsa inst_m) (d_data d) () in
         let a =
           array_nth (heap_prod heap_byte_array (heap_option heap_nat))
             (mems s_m) m_ind ()
           in
          (let (mem_e, _) = a in
            (fun f_ () -> f_ ((len_byte_array mem_e) ()) ())
              (fun mem_e_len ->
                (fun () ->
                  (less_eq_nat
                    (plus_nat (nat_of_int_i32 d_off) (size_list (d_init d)))
                    mem_e_len))))
            ()))
      d_offs m_datas;;

let rec get_init_tab_m
  inst e_ind e =
    (fun () ->
      (let i_cls = fold_map (array_nth heap_nat (funcsa inst)) (e_init e) () in
        Init_tab (e_ind, i_cls)));;

let rec get_init_tabs_m
  inst e_inds es =
    fold_map (fun (a, b) -> get_init_tab_m inst a b) (zip e_inds es);;

let rec get_init_mems_m
  d_inds ds =
    (fun () -> (map (fun (x, y) -> Init_mem (x, d_init y)) (zip d_inds ds)));;

let rec module_glob_type_checker
  c (Module_glob_ext (tg, es, ())) =
    list_all (const_expr c) es && b_e_type_checker c es (Tf ([], [tg_t tg]));;

let rec return_update
  returna
    (T_context_ext
      (types_t, func_t, global, table, memory, local, label, return, more))
    = T_context_ext
        (types_t, func_t, global, table, memory, local, label, returna return,
          more);;

let rec local_update
  locala
    (T_context_ext
      (types_t, func_t, global, table, memory, local, label, return, more))
    = T_context_ext
        (types_t, func_t, global, table, memory, locala local, label, return,
          more);;

let rec module_func_type_checker
  c (i, (t_locs, b_es)) =
    less_nat i (size_list (types_t c)) &&
      (let Tf (tn, tm) = nth (types_t c) i in
        b_e_type_checker
          (return_update (fun _ -> Some tm)
            (label_update (fun _ -> [tm] @ label c)
              (local_update (fun _ -> tn @ t_locs) c)))
          b_es (Tf ([], tm)));;

let rec module_elem_type_checker
  c (Module_elem_ext (t, es, is, ())) =
    equal_nat t zero_nat &&
      (list_all (const_expr c) es &&
        (b_e_type_checker c es (Tf ([], [T_num T_i32])) &&
          (less_nat t (size_list (table c)) &&
            list_all (fun i -> less_nat i (size_list (func_t c))) is)));;

let rec module_data_type_checker
  c (Module_data_ext (d, es, bs, ())) =
    equal_nat d zero_nat &&
      (list_all (const_expr c) es &&
        (b_e_type_checker c es (Tf ([], [T_num T_i32])) &&
          less_nat d (size_list (memory c))));;

let rec module_import_typer
  tfs x1 = match tfs, x1 with
    tfs, Imp_func i ->
      (if less_nat i (size_list tfs) then Some (Te_func (nth tfs i)) else None)
    | tfs, Imp_tab tt ->
        (if limit_typing tt
              (power power_nat (nat_of_integer (Z.of_int 2))
                (nat_of_integer (Z.of_int 32)))
          then Some (Te_tab tt) else None)
    | tfs, Imp_mem mt ->
        (if limit_typing mt
              (power power_nat (nat_of_integer (Z.of_int 2))
                (nat_of_integer (Z.of_int 16)))
          then Some (Te_mem mt) else None)
    | tfs, Imp_glob gt -> Some (Te_glob gt);;

let rec module_export_typer
  c x1 = match c, x1 with
    c, Ext_func i ->
      (if less_nat i (size_list (func_t c))
        then Some (Te_func (nth (func_t c) i)) else None)
    | c, Ext_tab i ->
        (if less_nat i (size_list (table c))
          then Some (Te_tab (nth (table c) i)) else None)
    | c, Ext_mem i ->
        (if less_nat i (size_list (memory c))
          then Some (Te_mem (nth (memory c) i)) else None)
    | c, Ext_glob i ->
        (if less_nat i (size_list (global c))
          then Some (Te_glob (nth (global c) i)) else None);;

let rec gather_m_f_type
  tfs m_f =
    (if less_nat (fst m_f) (size_list tfs) then Some (nth tfs (fst m_f))
      else None);;

let rec i_desc (Module_import_ext (i_module, i_name, i_desc, more)) = i_desc;;

let rec module_start_type_checker_p
  x xa =
    bind (single (x, xa))
      (fun (c, i) ->
        bind (if_pred (less_nat i (size_list (func_t c))))
          (fun () ->
            bind (eq_i_i equal_tf (nth (func_t c) i) (Tf ([], [])))
              (fun () -> single ())));;

let rec module_start_typing x1 x2 = holds (module_start_type_checker_p x1 x2);;

let rec module_type_checker
  (M_ext (tfs, fs, ts, ms, gs, els, ds, i_opt, imps, exps, ())) =
    (match
      (those (map (gather_m_f_type tfs) fs),
        those (map (fun imp -> module_import_typer tfs (i_desc imp)) imps))
      with (None, _) -> None | (Some _, None) -> None
      | (Some fts, Some impts) ->
        (let ifts =
           map_filter
             (fun a ->
               (match a with Te_func aa -> Some aa | Te_tab _ -> None
                 | Te_mem _ -> None | Te_glob _ -> None))
             impts
           in
         let its =
           map_filter
             (fun a ->
               (match a with Te_func _ -> None | Te_tab aa -> Some aa
                 | Te_mem _ -> None | Te_glob _ -> None))
             impts
           in
         let ims =
           map_filter
             (fun a ->
               (match a with Te_func _ -> None | Te_tab _ -> None
                 | Te_mem aa -> Some aa | Te_glob _ -> None))
             impts
           in
         let igs =
           map_filter
             (fun a ->
               (match a with Te_func _ -> None | Te_tab _ -> None
                 | Te_mem _ -> None | Te_glob aa -> Some aa))
             impts
           in
         let gts = map g_type gs in
         let c =
           T_context_ext
             (tfs, ifts @ fts, igs @ gts, its @ ts, ims @ ms, [], [], None, ())
           in
         let ca = T_context_ext ([], [], igs, [], [], [], [], None, ()) in
          (if list_all (module_func_type_checker c) fs &&
                (list_all
                   (fun t ->
                     limit_typing t
                       (power power_nat (nat_of_integer (Z.of_int 2))
                         (nat_of_integer (Z.of_int 32))))
                   ts &&
                  (list_all
                     (fun t ->
                       limit_typing t
                         (power power_nat (nat_of_integer (Z.of_int 2))
                           (nat_of_integer (Z.of_int 16))))
                     ms &&
                    (list_all (module_glob_type_checker ca) gs &&
                      (list_all (module_elem_type_checker c) els &&
                        (list_all (module_data_type_checker c) ds &&
                          (pred_option (module_start_typing c) i_opt &&
                            (distinct equal_literal (map e_name exps) &&
                              (less_eq_nat (size_list (its @ ts)) one_nata &&
                                less_eq_nat (size_list (ims @ ms))
                                  one_nata))))))))
            then (match
                   those (map (fun exp -> module_export_typer c (e_desc exp))
                           exps)
                   with None -> None | Some expts -> Some (impts, expts))
            else None)));;

let rec get_start_m
  inst i_s =
    (match i_s with None -> (fun () -> [])
      | Some i_sa ->
        (fun () ->
          (let i_s_s = array_nth heap_nat (funcsa inst) i_sa () in
            [Invoke i_s_s])));;

let rec g_init (Module_glob_ext (g_type, g_init, more)) = g_init;;

let rec e_off (Module_elem_ext (e_tab, e_off, e_init, more)) = e_off;;

let rec d_off (Module_data_ext (d_data, d_off, d_init, more)) = d_off;;

let rec interp_instantiate_m
  s_m m v_imps =
    (match module_type_checker m
      with None -> (fun () -> (s_m, RI_trap_m "invalid module"))
      | Some (t_imps, _) ->
        (fun () ->
          (let exps_well_typed =
             list_all2_m (external_typing_m s_m) v_imps t_imps () in
            (if exps_well_typed
              then (fun f_ () -> f_
                     ((fold_map
                        (fun g ->
                          (fun f_ () -> f_ (((fun () -> Array.of_list [])) ())
                            ())
                            (fun i_types ->
                              (fun f_ () -> f_ (((fun () -> Array.of_list []))
                                ()) ())
                                (fun i_funcs ->
                                  (fun f_ () -> f_
                                    (((fun () -> Array.of_list [])) ()) ())
                                    (fun i_tabs ->
                                      (fun f_ () -> f_
(((fun () -> Array.of_list [])) ()) ())
(fun i_mems ->
  (fun f_ () -> f_
    (((fun () -> Array.of_list
       (map_filter
         (fun a ->
           (match a with Ext_func _ -> None | Ext_tab _ -> None
             | Ext_mem _ -> None | Ext_glob aa -> Some aa))
         v_imps)))
    ()) ())
    (fun i_globs ->
      (let inst_m = Inst_m_ext (i_types, i_funcs, i_tabs, i_mems, i_globs, ())
         in
        (fun f_ () -> f_ ((interp_get_v_m s_m inst_m (g_init g)) ()) ())
          (fun a -> (fun () -> a)))))))))
                        (m_globs m))
                     ()) ())
                     (fun g_inits ->
                       (fun f_ () -> f_
                         ((interp_alloc_module_m s_m m v_imps g_inits) ()) ())
                         (fun (s_ma, (inst_m, v_exps)) ->
                           (fun f_ () -> f_
                             ((fold_map
                                (fun e ->
                                  interp_get_i32_m s_ma inst_m (e_off e))
                                (m_elem m))
                             ()) ())
                             (fun e_offs ->
                               (fun f_ () -> f_
                                 ((fold_map
                                    (fun d ->
                                      interp_get_i32_m s_ma inst_m (d_off d))
                                    (m_data m))
                                 ()) ())
                                 (fun d_offs ->
                                   (fun f_ () -> f_
                                     ((element_in_bounds_m s_ma inst_m e_offs
(m_elem m))
                                     ()) ())
                                     (fun e_in_bounds ->
                                       (fun f_ () -> f_
 ((data_in_bounds_m s_ma inst_m d_offs (m_data m)) ()) ())
 (fun d_in_bounds ->
   (if e_in_bounds && d_in_bounds
     then (fun f_ () -> f_ ((get_start_m inst_m (m_start m)) ()) ())
            (fun start ->
              (fun f_ () -> f_
                ((get_init_tabs_m inst_m (map nat_of_int_i32 e_offs) (m_elem m))
                ()) ())
                (fun e_init_tabs ->
                  (fun f_ () -> f_
                    ((get_init_mems_m (map nat_of_int_i32 d_offs) (m_data m))
                    ()) ())
                    (fun e_init_mems ->
                      (fun () ->
                        (s_ma,
                          RI_res_m
                            (inst_m, v_exps,
                              e_init_tabs @ e_init_mems @ start))))))
     else (fun () -> (s_ma, RI_trap_m "segment out of bounds")))))))))
              else (fun () -> (s_m, RI_trap_m "invalid import")))
              ())));;

let rec run_instantiate_m
  n d (s, (f_inst2, es)) =
    (fun () ->
      (let f_locs1 = (fun () -> Array.of_list []) () in
       let a =
         run_iter_m n
           (Config_m
             (d, s,
               Frame_context_m
                 (Redex ([], es, []), [], zero_nat, f_locs1, f_inst2),
               []))
           ()
         in
        (let (Config_m (_, sa, _, _), res) = a in (fun () -> (sa, res))) ()));;

let rec interp_instantiate_init_m
  s m v_imps =
    (fun () ->
      (let a = interp_instantiate_m s m v_imps () in
        (match a
          with (sa, RI_crash_m res_error) ->
            (fun () -> (sa, RI_crash_m res_error))
          | (sa, RI_trap_m literal) -> (fun () -> (sa, RI_trap_m literal))
          | (sa, RI_res_m (inst, v_exps, init_es)) ->
            (fun f_ () -> f_
              ((run_instantiate_m
                 (power power_nat (nat_of_integer (Z.of_int 2))
                   (nat_of_integer (Z.of_int 63)))
                 (nat_of_integer (Z.of_int 300)) (sa, (inst, init_es)))
              ()) ())
              (fun aa ->
                (match aa with (sb, RCrash r) -> (fun () -> (sb, RI_crash_m r))
                  | (sb, RTrap r) -> (fun () -> (sb, RI_trap_m r))
                  | (sb, RValue []) ->
                    (fun () -> (sb, RI_res_m (inst, v_exps, [])))
                  | (sb, RValue (_ :: _)) ->
                    (fun () ->
                      (sb, RI_crash_m (Error_invalid "start function"))))))
          ()));;

let rec make_empty_frame_m _A
  = (fun () ->
      (let f_locs1 = (fun () -> Array.of_list []) () in
       let f_inst2 = make_empty_inst_m () in
        (f_locs1, f_inst2)));;

let rec run_invoke_v_m
  n d (s, (vs, i)) =
    (fun () ->
      (let a = make_empty_frame_m heap_v () in
        (let (f_locs1, f_inst2) = a in
          (fun f_ () -> f_
            ((run_iter_m n
               (Config_m
                 (d, s,
                   Frame_context_m
                     (Redex (rev vs, [Invoke i], []), [], zero_nat, f_locs1,
                       f_inst2),
                   [])))
            ()) ())
            (fun (Config_m (_, sa, _, _), res) -> (fun () -> (sa, res))))
          ()));;

let rec run_fuzz
  n d s m v_imps opt_vs =
    (fun () ->
      (let a = interp_instantiate_init_m s m v_imps () in
        (match a with (sa, RI_crash_m res) -> (fun () -> (sa, RCrash res))
          | (sa, RI_trap_m msg) -> (fun () -> (sa, RTrap msg))
          | (sa, RI_res_m (_, v_exps, _)) ->
            (match
              find (fun exp ->
                     (match e_desc exp with Ext_func _ -> true
                       | Ext_tab _ -> false | Ext_mem _ -> false
                       | Ext_glob _ -> false))
                v_exps
              with None ->
                (fun () -> (sa, RCrash (Error_invariant "no import to invoke")))
              | Some exp ->
                (let Ext_func i = e_desc exp in
                  (fun f_ () -> f_ ((array_nth heap_cl_m (funcs sa) i) ()) ())
                    (fun cl ->
                      (let Tf (t1, _) = cl_m_type cl in
                       let params =
                         (match opt_vs with None -> map bitzero t1
                           | Some aa -> rev aa)
                         in
                        run_invoke_v_m n d (sa, (params, i)))))))
          ()));;

let rec run_m
  x = run_v_m
        (power power_nat (nat_of_integer (Z.of_int 2))
          (nat_of_integer (Z.of_int 63)))
        (nat_of_integer (Z.of_int 300)) x;;

let make_empty_store_m : (unit -> unit s_m_ext)
  = (fun () ->
      (let s_funcs = (fun () -> Array.of_list []) () in
       let s_tabs = (fun () -> Array.of_list []) () in
       let s_mems = (fun () -> Array.of_list []) () in
       let s_globs = (fun () -> Array.of_list []) () in
        S_m_ext (s_funcs, s_tabs, s_mems, s_globs, ())));;

let rec run_invoke_m
  x = run_invoke_v_m
        (power power_nat (nat_of_integer (Z.of_int 2))
          (nat_of_integer (Z.of_int 63)))
        (nat_of_integer (Z.of_int 300)) x;;

end;; (*struct WasmRef_Isa*)
