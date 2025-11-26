module Uint32 : sig
  val less : int32 -> int32 -> bool
  val less_eq : int32 -> int32 -> bool
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

let shiftl x n = Int64.shift_left x (Z.to_int n);;

let shiftr x n = Int64.shift_right_logical x (Z.to_int n);;

let shiftr_signed x n = Int64.shift_right x (Z.to_int n);;

let test_bit x n =
  Int64.compare 
    (Int64.logand x (Int64.shift_left Int64.one (Z.to_int n)))
    Int64.zero
  <> 0;;

end;; (*struct Uint64*)


module Bit_Shifts : sig
  val push : Z.t -> Z.t -> Z.t
  val drop : Z.t -> Z.t -> Z.t
end = struct

let rec fold f xs y = match xs with
  [] -> y
  | (x :: xs) -> fold f xs (f x y);;

let rec replicate n x = (if Z.leq n Z.zero then [] else x :: replicate (Z.pred n) x);;

let max_index = Z.of_int max_int;;

let splitIndex i = let (b, s) = Z.div_rem i max_index
  in Z.to_int s :: (replicate b max_int);;

let push' i k = Z.shift_left k i;;

let drop' i k = Z.shift_right k i;;

(* The implementations are formally total, though indices >~ max_index will produce heavy computation load *)

let push i = fold push' (splitIndex (Z.abs i));;

let drop i = fold drop' (splitIndex (Z.abs i));;

end;;


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
  type 'a divide_trivial =
    {one_divide_trivial : 'a one; zero_divide_trivial : 'a zero;
      divide_divide_trivial : 'a divide}
  val divide_trivial_int : int divide_trivial
  type 'a semiring_no_zero_divisors_cancel =
    {semiring_no_zero_divisors_semiring_no_zero_divisors_cancel :
       'a semiring_no_zero_divisors}
  type 'a semidom_divide =
    {divide_trivial_semidom_divide : 'a divide_trivial;
      semidom_semidom_divide : 'a semidom;
      semiring_no_zero_divisors_cancel_semidom_divide :
        'a semiring_no_zero_divisors_cancel}
  val semiring_no_zero_divisors_cancel_int :
    int semiring_no_zero_divisors_cancel
  val semidom_divide_int : int semidom_divide
  type 'a semiring_modulo_trivial =
    {divide_trivial_semiring_modulo_trivial : 'a divide_trivial;
      semiring_modulo_semiring_modulo_trivial : 'a semiring_modulo}
  type 'a algebraic_semidom =
    {semidom_divide_algebraic_semidom : 'a semidom_divide}
  type 'a semidom_modulo =
    {algebraic_semidom_semidom_modulo : 'a algebraic_semidom;
      semiring_modulo_trivial_semidom_modulo : 'a semiring_modulo_trivial}
  val semiring_modulo_trivial_int : int semiring_modulo_trivial
  val algebraic_semidom_int : int algebraic_semidom
  val semidom_modulo_int : int semidom_modulo
  type nat = Nat of Z.t
  val integer_of_nat : nat -> Z.t
  val push_bit_integer : nat -> Z.t -> Z.t
  val bit_integer : Z.t -> nat -> bool
  val bit_int : int -> nat -> bool
  type 'a semiring_bits =
    {semiring_parity_semiring_bits : 'a semiring_parity;
      semiring_modulo_trivial_semiring_bits : 'a semiring_modulo_trivial;
      bit : 'a -> nat -> bool}
  val bit : 'a semiring_bits -> 'a -> nat -> bool
  val semiring_bits_int : int semiring_bits
  val unset_bit_integer : nat -> Z.t -> Z.t
  val unset_bit_int : nat -> int -> int
  val mask_integer : nat -> Z.t
  val take_bit_integer : nat -> Z.t -> Z.t
  val take_bit_int : nat -> int -> int
  val push_bit_int : nat -> int -> int
  val flip_bit_integer : nat -> Z.t -> Z.t
  val flip_bit_int : nat -> int -> int
  val drop_bit_integer : nat -> Z.t -> Z.t
  val drop_bit_int : nat -> int -> int
  val set_bit_integer : nat -> Z.t -> Z.t
  val set_bit_int : nat -> int -> int
  val mask_int : nat -> int
  val xor_int : int -> int -> int
  val and_int : int -> int -> int
  val or_int : int -> int -> int
  type 'a semiring_bit_operations =
    {semiring_bits_semiring_bit_operations : 'a semiring_bits;
      anda : 'a -> 'a -> 'a; ora : 'a -> 'a -> 'a; xor : 'a -> 'a -> 'a;
      mask : nat -> 'a; set_bit : nat -> 'a -> 'a; unset_bit : nat -> 'a -> 'a;
      flip_bit : nat -> 'a -> 'a; push_bit : nat -> 'a -> 'a;
      drop_bit : nat -> 'a -> 'a; take_bit : nat -> 'a -> 'a}
  val anda : 'a semiring_bit_operations -> 'a -> 'a -> 'a
  val ora : 'a semiring_bit_operations -> 'a -> 'a -> 'a
  val xor : 'a semiring_bit_operations -> 'a -> 'a -> 'a
  val mask : 'a semiring_bit_operations -> nat -> 'a
  val set_bit : 'a semiring_bit_operations -> nat -> 'a -> 'a
  val unset_bit : 'a semiring_bit_operations -> nat -> 'a -> 'a
  val flip_bit : 'a semiring_bit_operations -> nat -> 'a -> 'a
  val push_bit : 'a semiring_bit_operations -> nat -> 'a -> 'a
  val drop_bit : 'a semiring_bit_operations -> nat -> 'a -> 'a
  val take_bit : 'a semiring_bit_operations -> nat -> 'a -> 'a
  val not_int : int -> int
  type 'a ring_bit_operations =
    {semiring_bit_operations_ring_bit_operations : 'a semiring_bit_operations;
      ring_parity_ring_bit_operations : 'a ring_parity; nota : 'a -> 'a}
  val nota : 'a ring_bit_operations -> 'a -> 'a
  val semiring_bit_operations_int : int semiring_bit_operations
  val ring_bit_operations_int : int ring_bit_operations
  val equal_nata : nat -> nat -> bool
  val equal_nat : nat equal
  val one_nata : nat
  val one_nat : nat one
  val times_nata : nat -> nat -> nat
  val times_nat : nat times
  val power_nat : nat power
  val less_eq_nat : nat -> nat -> bool
  type 'a ord = {less_eq : 'a -> 'a -> bool; less : 'a -> 'a -> bool}
  val less_eq : 'a ord -> 'a -> 'a -> bool
  val less : 'a ord -> 'a -> 'a -> bool
  val less_nat : nat -> nat -> bool
  val ord_nat : nat ord
  type 'a itself = Type
  type 'a len0 = {len_of : 'a itself -> nat}
  val len_of : 'a len0 -> 'a itself -> nat
  type 'a len = {len0_len : 'a len0}
  type 'a word = Word of int
  val one_worda : 'a len -> 'a word
  val one_word : 'a len -> 'a word one
  val the_int : 'a len -> 'a word -> int
  val of_int : 'a len -> int -> 'a word
  val plus_worda : 'a len -> 'a word -> 'a word -> 'a word
  val plus_word : 'a len -> 'a word plus
  val zero_worda : 'a len -> 'a word
  val zero_word : 'a len -> 'a word zero
  val times_worda : 'a len -> 'a word -> 'a word -> 'a word
  val times_word : 'a len -> 'a word times
  val semigroup_add_word : 'a len -> 'a word semigroup_add
  val ab_semigroup_add_word : 'a len -> 'a word ab_semigroup_add
  val semigroup_mult_word : 'a len -> 'a word semigroup_mult
  val semiring_word : 'a len -> 'a word semiring
  val mult_zero_word : 'a len -> 'a word mult_zero
  val monoid_add_word : 'a len -> 'a word monoid_add
  val comm_monoid_add_word : 'a len -> 'a word comm_monoid_add
  val semiring_0_word : 'a len -> 'a word semiring_0
  val zero_neq_one_word : 'a len -> 'a word zero_neq_one
  val ab_semigroup_mult_word : 'a len -> 'a word ab_semigroup_mult
  val comm_semiring_word : 'a len -> 'a word comm_semiring
  val comm_semiring_0_word : 'a len -> 'a word comm_semiring_0
  type t_vec = T_v128
  val equal_t_vec : t_vec -> t_vec -> bool
  type t_ref = T_func_ref | T_ext_ref
  val equal_t_ref : t_ref -> t_ref -> bool
  type t_num = T_i32 | T_i64 | T_f32 | T_f64
  val equal_t_num : t_num -> t_num -> bool
  type t = T_num of t_num | T_vec of t_vec | T_ref of t_ref | T_bot
  val equal_ta : t -> t -> bool
  val equal_t : t equal
  val eq : 'a equal -> 'a -> 'a -> bool
  val equal_list : 'a equal -> 'a list -> 'a list -> bool
  type tf = Tf of t list * t list
  val equal_tfa : tf -> tf -> bool
  val equal_tf : tf equal
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
  type i32 = I32_impl_abs of int32
  val zero_i32a : i32
  val zero_i32 : i32 zero
  val max : 'a ord -> 'a -> 'a -> 'a
  val ord_integer : Z.t ord
  val nat_of_integer : Z.t -> nat
  val len_of_i32 : i32 itself -> nat
  val len0_i32 : i32 len0
  val len_i32 : i32 len
  val bit_uint32 : int32 -> nat -> bool
  val uint32 : Z.t -> int32
  val integer_of_uint32 : int32 -> Z.t
  val nat_of_uint32 : int32 -> nat
  val nat_of_int_i32 : i32 -> nat
  val plus_nat : nat -> nat -> nat
  val fold_atLeastAtMost_nat : (nat -> 'a -> 'a) -> nat -> nat -> 'a -> 'a
  val zero_nat : nat
  val int_of_nat : nat -> int
  val uint32_of_int : int -> int32
  val comp : ('a -> 'b) -> ('c -> 'a) -> 'c -> 'b
  val uint32_of_nat : nat -> int32
  val int_popcnt_i32 : i32 -> i32
  val int_of_nat_i32 : nat -> i32
  val int_shr_u_i32 : i32 -> i32 -> i32
  val int_shr_s_i32 : i32 -> i32 -> i32
  val push_bit_uint32 : nat -> int32 -> int32
  val drop_bit_uint32 : nat -> int32 -> int32
  val mod0_uint32 : int32 -> int32
  val div0_uint32 : int32 -> int32
  val uint32_divmod : int32 -> int32 -> int32 * int32
  val uint32_mod : int32 -> int32 -> int32
  val int_rem_u_i32 : i32 -> i32 -> i32 option
  val int_rem_s_i32 : i32 -> i32 -> i32 option
  val uint32_div : int32 -> int32 -> int32
  val int_div_u_i32 : i32 -> i32 -> i32 option
  val int_div_s_i32 : i32 -> i32 -> i32 option
  val minus_nat : nat -> nat -> nat
  val mask_uint32 : nat -> int32
  val take_bit_uint32 : nat -> int32 -> int32
  val modulo_uint32 : int32 -> int32 -> int32
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
  val suc : nat -> nat
  val gen_length : nat -> 'a list -> nat
  val size_list : 'a list -> nat
  val drop_bit_word : 'a len -> nat -> 'a word -> 'a word
  val and_word : 'a len -> 'a word -> 'a word -> 'a word
  val equal_word : 'a len -> 'a word -> 'a word -> bool
  val bit_word : 'a len -> 'a word -> nat -> bool
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
  type num1 = One_num1
  type 'a finite = unit
  type 'a bit0 = Abs_bit0 of int
  val len_of_num1 : num1 itself -> nat
  val len0_num1 : num1 len0
  val len_num1 : num1 len
  val len_of_bit0 : 'a len0 -> 'a bit0 itself -> nat
  val len0_bit0 : 'a len0 -> 'a bit0 len0
  val len_bit0 : 'a len -> 'a bit0 len
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
  type i64 = I64_impl_abs of int64
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
  val mask_uint64 : nat -> int64
  val take_bit_uint64 : nat -> int64 -> int64
  val modulo_uint64 : int64 -> int64 -> int64
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
  val equal_literal : string equal
  type typerepa = Typerep of string * typerepa list
  type sx = S | U
  type binop_i = Add | Sub | Mul | Div of sx | Rem of sx | And | Or | Xor | Shl
    | Shr of sx | Rotl | Rotr
  type binop_f = Addf | Subf | Mulf | Divf | Min | Max | Copysign
  type binop = Binop_i of binop_i | Binop_f of binop_f
  val typerep_binopa : binop itself -> typerepa
  type 'a typerep = {typerep : 'a itself -> typerepa}
  val typerep : 'a typerep -> 'a itself -> typerepa
  val typerep_binop : binop typerep
  type cvtop = Convert | Reinterpret
  val typerep_cvtopa : cvtop itself -> typerepa
  val typerep_cvtop : cvtop typerep
  val equal_unita : unit -> unit -> bool
  val equal_unit : unit equal
  type 'a inst_ext =
    Inst_ext of
      tf list * nat list * nat list * nat list * nat list * nat list *
        nat list * 'a
  type v_vec = ConstVec128 of V128Wrapper.t
  type 'a limit_t_ext = Limit_t_ext of nat * nat option * 'a
  type tab_t = T_tab of unit limit_t_ext * t_ref
  type shape_vec_i = I8_16 | I16_8 | I32_4 | I64_2
  type storeop_vec = Store_128 | Store_lane of shape_vec_i * nat
  type tp_vec = Tp_v8_8 | Tp_v16_4 | Tp_v32_2
  type loadop_vec = Load_128 | Load_packed_vec of tp_vec * sx | Load_32_zero |
    Load_64_zero | Load_splat of shape_vec_i
  type shape_vec_f = F32_4 | F64_2
  type shape_vec = Svi of shape_vec_i | Svf of shape_vec_f
  type tp_num = Tp_i8 | Tp_i16 | Tp_i32
  type testop = Eqz
  type v_num = ConstInt32 of i32 | ConstInt64 of i64 |
    ConstFloat32 of F32Wrapper.t | ConstFloat64 of F64Wrapper.t
  type relop_i = Eq | Ne | Lt of sx | Gt of sx | Le of sx | Ge of sx
  type relop_f = Eqf | Nef | Ltf | Gtf | Lef | Gef
  type relop = Relop_i of relop_i | Relop_f of relop_f
  type unop_i = Clz | Ctz | Popcnt
  type unop_f = Neg | Abs | Ceil | Floor | Trunc | Nearest | Sqrt
  type unop = Unop_i of unop_i | Unop_f of unop_f | Extend_s of tp_num
  type sat = Sat | Nonsat
  type tb = Tbf of nat | Tbv of t option
  type b_e = Unreachable | Nop | Drop | Select of t option |
    Block of tb * b_e list | Loop of tb * b_e list |
    If of tb * b_e list * b_e list | Br of nat | Br_if of nat |
    Br_table of nat list * nat | Return | Call of nat |
    Call_indirect of nat * nat | Local_get of nat | Local_set of nat |
    Local_tee of nat | Global_get of nat | Global_set of nat | Table_get of nat
    | Table_set of nat | Table_size of nat | Table_grow of nat |
    Load of t_num * (tp_num * sx) option * nat * nat |
    Store of t_num * tp_num option * nat * nat |
    Load_vec of loadop_vec * nat * nat |
    Load_lane_vec of shape_vec_i * nat * nat * nat |
    Store_vec of storeop_vec * nat * nat | Memory_size | Memory_grow |
    Memory_init of nat | Memory_fill | Memory_copy | Table_init of nat * nat |
    Table_copy of nat * nat | Table_fill of nat | Elem_drop of nat |
    Data_drop of nat | EConstNum of v_num | EConstVec of v_vec |
    Unop of t_num * unop | Binop of t_num * binop | Testop of t_num * testop |
    Relop of t_num * relop | Cvtop of t_num * cvtop * t_num * (sat * sx) option
    | Ref_null of t_ref | Ref_is_null | Ref_func of nat |
    Unop_vec of V128Wrapper.unop_vec_t | Binop_vec of V128Wrapper.binop_vec_t |
    Ternop_vec of V128Wrapper.ternop_vec_t |
    Test_vec of V128Wrapper.testop_vec_t |
    Shift_vec of V128Wrapper.shiftop_vec_t | Splat_vec of shape_vec |
    Extract_vec of shape_vec * sx * nat | Replace_vec of shape_vec * nat
  type uint8 = Abs_uint8 of num1 bit0 bit0 bit0 word
  type v = V_num of v_num | V_vec of v_vec | V_ref of v_ref
  and 'a global_ext = Global_ext of mut * v * 'a
  and 'a s_ext =
    S_ext of
      cl list * (tab_t * v_ref list) list *
        (unit limit_t_ext * Pbytes.pbt) list * unit global_ext list *
        (t_ref * v_ref list) list * (uint8 list) list * 'a
  and host_func =
    Abs_host_func of (unit s_ext * v list -> (unit s_ext * v list) option)
  and host = Host_func of host_func | Host_ref of int32
  and cl = Func_native of unit inst_ext * tf * t list * b_e list |
    Func_host of tf * host
  and v_ref = ConstNull of t_ref | ConstRefFunc of nat | ConstRefExtern of host
  type 'a f_ext = F_ext of v list * unit inst_ext * 'a
  type e = Basic of b_e | Trap | Invoke of nat | Label of nat * e list * e list
    | Frame of nat * unit f_ext * e list | Ref of v_ref
  type 'a seq = Empty | Insert of 'a * 'a pred | Join of 'a pred * 'a seq
  and 'a pred = Seq of (unit -> 'a seq)
  type v_ext = Ext_func of nat | Ext_tab of nat | Ext_mem of nat |
    Ext_glob of nat
  type 'a tg_ext = Tg_ext of mut * t * 'a
  type imp_desc = Imp_func of nat | Imp_tab of tab_t |
    Imp_mem of unit limit_t_ext | Imp_glob of unit tg_ext
  type 'a module_import_ext =
    Module_import_ext of string * string * imp_desc * 'a
  type 'a module_export_ext = Module_export_ext of string * v_ext * 'a
  type 'a module_glob_ext = Module_glob_ext of unit tg_ext * b_e list * 'a
  type elem_mode = Em_passive | Em_active of nat * b_e list | Em_declarative
  type 'a module_elem_ext =
    Module_elem_ext of t_ref * (b_e list) list * elem_mode * 'a
  type data_mode = Dm_passive | Dm_active of nat * b_e list
  type 'a module_data_ext = Module_data_ext of uint8 list * data_mode * 'a
  type 'a m_ext =
    M_ext of
      tf list * (nat * (t list * b_e list)) list * tab_t list *
        unit limit_t_ext list * unit module_glob_ext list *
        unit module_elem_ext list * unit module_data_ext list * nat option *
        unit module_import_ext list * unit module_export_ext list * 'a
  type res_error = Error_invalid of string | Error_invariant of string |
    Error_exhaustion of string
  type res = RCrash of res_error | RTrap of string | RValue of v list
  type extern_t = Te_func of tf | Te_tab of tab_t | Te_mem of unit limit_t_ext |
    Te_glob of unit tg_ext
  type redex = Redex of v list * e list * b_e list
  type label_context = Label_context of v list * b_e list * nat * b_e list
  type frame_context =
    Frame_context of redex * label_context list * nat * unit f_ext
  type config = Config of nat * unit s_ext * frame_context * frame_context list
  type reach = Reach | Unreach
  type res_step = Res_crash of res_error | Res_trap of string | Step_normal
  type res_inst = RI_crash of res_error | RI_trap of string |
    RI_res of unit inst_ext * unit module_export_ext list * e list
  type 'a t_context_ext =
    T_context_ext of
      tf list * tf list * unit tg_ext list * t_ref list * unit list *
        tab_t list * unit limit_t_ext list * t list * (t list) list *
        (t list) option * nat list * 'a
  val failwith_nth : nat -> 'a
  val nth : 'a list -> nat -> 'a
  val zip : 'a list -> 'b list -> ('a * 'b) list
  val drop : nat -> 'a list -> 'a list
  val null : 'a list -> bool
  val last : 'a list -> 'a
  val maps : ('a -> 'b list) -> 'a list -> 'b list
  val take_tr : nat -> 'a list -> 'a list -> 'a list
  val take : nat -> 'a list -> 'a list
  val map_option : ('a -> 'b) -> 'a option -> 'b option
  val those : ('a option) list -> ('a list) option
  val concat : ('a list) list -> 'a list
  val member : 'a equal -> 'a list -> 'a -> bool
  val int_of_integer_symbolic : Z.t -> int
  val uint8 : Z.t -> uint8
  val remdups : 'a equal -> 'a list -> 'a list
  val distinct : 'a equal -> 'a list -> bool
  val ki64 : nat
  val replicate_tr : nat -> 'a -> 'a list -> 'a list
  val replicate : nat -> 'a -> 'a list
  val is_none : 'a option -> bool
  val bind : 'a pred -> ('a -> 'b pred) -> 'b pred
  val apply : ('a -> 'b pred) -> 'a seq -> 'b seq
  val map_filter : ('a -> 'b option) -> 'a list -> 'b list
  val eval : 'a equal -> 'a pred -> 'a -> bool
  val membera : 'a equal -> 'a seq -> 'a -> bool
  val holds : unit pred -> bool
  val l_min : 'a limit_t_ext -> nat
  val rep_uint8a : uint8 -> num1 bit0 bit0 bit0 word
  val and_uint8 : uint8 -> uint8 -> uint8
  val bit_uint8 : uint8 -> nat -> bool
  val uint8_test_bit : uint8 -> Z.t -> bool
  val rep_uint8 : uint8 -> num1 bit0 bit0 bit0 word
  val integer_of_uint8 : uint8 -> Z.t
  val integer_of_uint8_signed : uint8 -> Z.t
  val isabelle_byte_to_ocaml_char : uint8 -> Char.t
  val nat_to_ocaml_int : nat -> Int.t
  val zero_uint8 : uint8
  val zero_byte : uint8
  val mem_rep_mk : nat -> Pbytes.pbt
  val mem_mk : unit limit_t_ext -> unit limit_t_ext * Pbytes.pbt
  val msbyte : uint8 list -> uint8
  val mems : 'a s_ext -> (unit limit_t_ext * Pbytes.pbt) list
  val tabs : 'a s_ext -> (tab_t * v_ref list) list
  val list_update : 'a list -> nat -> 'a -> 'a list
  val bot_pred : 'a pred
  val single : 'a -> 'a pred
  val dvd : 'a equal * 'a semidom_modulo -> 'a -> 'a -> bool
  val bin_split : nat -> int -> int * int
  val abs_uint8 : num1 bit0 bit0 bit0 word -> uint8
  val empty_frame : unit f_ext
  val typeof_vec : v_vec -> t_vec
  val typeof_ref : v_ref -> t_ref
  val typeof_num : v_num -> t_num
  val typeof : v -> t
  val g_val : 'a global_ext -> v
  val g_mut : 'a global_ext -> mut
  val tg_mut : 'a tg_ext -> mut
  val tg_t : 'a tg_ext -> t
  val glob_typing : 'a global_ext -> 'b tg_ext -> bool
  val l_max : 'a limit_t_ext -> nat option
  val mem_max : unit limit_t_ext * Pbytes.pbt -> nat option
  val datas : 'a s_ext -> (uint8 list) list
  val elems : 'a s_ext -> (t_ref * v_ref list) list
  val funcs : 'a s_ext -> cl list
  val globs : 'a s_ext -> unit global_ext list
  val tab_max : tab_t * v_ref list -> nat option
  val signed_take_bit : 'a ring_bit_operations -> nat -> 'a -> 'a
  val the_signed_int : 'a len -> 'a word -> int
  val signed_cast : 'b len -> 'a len -> 'b word -> 'a word
  val adjunct : 'a pred -> 'a seq -> 'a seq
  val sup_pred : 'a pred -> 'a pred -> 'a pred
  val if_pred : bool -> unit pred
  val f_inst : 'a f_ext -> unit inst_ext
  val f_locs : 'a f_ext -> v list
  val msb_uint8 : uint8 -> bool
  val msb_byte : uint8 -> bool
  val list_all : ('a -> bool) -> 'a list -> bool
  val nat_of_uint8 : uint8 -> nat
  val uint8_of_int : int -> uint8
  val uint8_of_nat : nat -> uint8
  val memsa : 'a inst_ext -> nat list
  val tabsa : 'a inst_ext -> nat list
  val tab_t_lim : tab_t -> unit limit_t_ext
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
  val is_ref_type : t -> bool
  val push : t list * reach -> t -> t list * reach
  val pop : t list * reach -> (t * (t list * reach)) option
  val type_update_ref_is_null : t list * reach -> (t list * reach) option
  val push_rev_list : t list * reach -> t list -> t list * reach
  val produce : t list * reach -> t list -> t list * reach
  val t_subtyping : t -> t -> bool
  val pop_expect : t list * reach -> t -> (t list * reach) option
  val pop_expect_list : t list * reach -> t list -> (t list * reach) option
  val consume : t list * reach -> t list -> (t list * reach) option
  val type_update :
    t list * reach -> t list -> t list -> (t list * reach) option
  val is_vec_type : t -> bool
  val is_num_type : t -> bool
  val type_update_select : t list * reach -> t option -> (t list * reach) option
  val type_update_drop : t list * reach -> (t list * reach) option
  val tp_num_length : tp_num -> nat
  val t_num_length : t_num -> nat
  val is_int_t_num : t_num -> bool
  val power : 'a power -> 'a -> nat -> 'a
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
  val c_types_agree : t list * reach -> t list -> bool
  val option_projl : ('a * 'b) option -> 'a option
  val types_t : 'a t_context_ext -> tf list
  val equal_bool : bool -> bool -> bool
  val convert_cond : t_num -> t_num -> (sat * sx) option -> bool
  val vec_f_length : shape_vec_f -> nat
  val vec_length : shape_vec -> nat
  val vec_lane_t : shape_vec -> t_num
  val return : 'a t_context_ext -> (t list) option
  val memory : 'a t_context_ext -> unit limit_t_ext list
  val global : 'a t_context_ext -> unit tg_ext list
  val func_t : 'a t_context_ext -> tf list
  val table : 'a t_context_ext -> tab_t list
  val local : 'a t_context_ext -> t list
  val label : 'a t_context_ext -> (t list) list
  val refs : 'a t_context_ext -> nat list
  val elem : 'a t_context_ext -> t_ref list
  val data : 'a t_context_ext -> unit list
  val vec_f_num : shape_vec_f -> nat
  val vec_num : shape_vec -> nat
  val tb_tf_t : unit t_context_ext -> tb -> tf option
  val tab_t_reftype : tab_t -> t_ref
  val is_mut : unit tg_ext -> bool
  val min_t : t -> t -> t
  val min_ts : t list -> t list -> (t list) option
  val min_lab_h : nat list -> (t list) list -> t list -> (t list) option
  val min_lab : nat list -> (t list) list -> (t list) option
  val check :
    unit t_context_ext -> b_e list -> t list * reach -> (t list * reach) option
  val b_e_type_checker : unit t_context_ext -> b_e list -> tf -> bool
  val check_single :
    unit t_context_ext -> b_e -> t list * reach -> (t list * reach) option
  val eq_i_i : 'a equal -> 'a -> 'a -> unit pred
  val list_all2 : ('a -> 'b -> bool) -> 'a list -> 'b list -> bool
  val datasa : 'a inst_ext -> nat list
  val elemsa : 'a inst_ext -> nat list
  val funcsa : 'a inst_ext -> nat list
  val globsa : 'a inst_ext -> nat list
  val types : 'a inst_ext -> tf list
  val divide_nat : nat -> nat -> nat
  val l_min_update : (nat -> nat) -> 'a limit_t_ext -> 'a limit_t_ext
  val mem_rep_append : Pbytes.pbt -> nat -> uint8 -> Pbytes.pbt
  val mem_append :
    unit limit_t_ext * Pbytes.pbt ->
      nat -> uint8 -> unit limit_t_ext * Pbytes.pbt
  val ocaml_int_to_nat : Int.t -> nat
  val mem_rep_length : Pbytes.pbt -> nat
  val mem_length : unit limit_t_ext * Pbytes.pbt -> nat
  val ocaml_char_to_isabelle_byte : Char.t -> uint8
  val mem_rep_read_bytes : Pbytes.pbt -> nat -> nat -> uint8 list
  val read_bytes : unit limit_t_ext * Pbytes.pbt -> nat -> nat -> uint8 list
  val load :
    unit limit_t_ext * Pbytes.pbt -> nat -> nat -> nat -> (uint8 list) option
  val byte_of_nat : nat -> uint8
  val nat_of_byte : uint8 -> nat
  val uminus_word : 'a len -> 'a word -> 'a word
  val uminus_uint8 : uint8 -> uint8
  val one_uint8 : uint8
  val negone_byte : uint8
  val mem_rep_write_bytes : Pbytes.pbt -> nat -> uint8 list -> Pbytes.pbt
  val write_bytes :
    unit limit_t_ext * Pbytes.pbt ->
      nat -> uint8 list -> unit limit_t_ext * Pbytes.pbt
  val takefill : 'a -> nat -> 'a list -> 'a list
  val bytes_takefill : uint8 -> nat -> uint8 list -> uint8 list
  val store :
    unit limit_t_ext * Pbytes.pbt ->
      nat -> nat -> uint8 list -> nat -> (unit limit_t_ext * Pbytes.pbt) option
  val tb_tf : unit inst_ext -> tb -> tf
  val m_mems : 'a m_ext -> unit limit_t_ext list
  val m_tabs : 'a m_ext -> tab_t list
  val stypes : unit inst_ext -> nat -> tf
  val v_to_e : v -> e
  val typerep_of : 'a typerep -> 'a -> typerepa
  val name : 'a typerep -> 'a -> string
  val m_datas : 'a m_ext -> unit module_data_ext list
  val m_elems : 'a m_ext -> unit module_elem_ext list
  val m_funcs : 'a m_ext -> (nat * (t list * b_e list)) list
  val m_globs : 'a m_ext -> unit module_glob_ext list
  val m_start : 'a m_ext -> nat option
  val m_types : 'a m_ext -> tf list
  val mems_update :
    ((unit limit_t_ext * Pbytes.pbt) list ->
      (unit limit_t_ext * Pbytes.pbt) list) ->
      'a s_ext -> 'a s_ext
  val tabs_update :
    ((tab_t * v_ref list) list -> (tab_t * v_ref list) list) ->
      'a s_ext -> 'a s_ext
  val bitzero_vec : t_vec -> v_vec
  val bitzero_ref : t_ref -> v_ref
  val bitzero_num : t_num -> v_num
  val bitzero : t -> v option
  val cl_type : cl -> tf
  val n_zeros : t list -> (v list) option
  val update_redex_return : redex -> v list -> redex
  val update_fc_return : frame_context -> v list -> frame_context
  val res_crash_fuel : res
  val split_v_s_b_s_aux : v list -> b_e list -> v list * b_e list
  val split_v_s_b_s : b_e list -> v list * b_e list
  val split_v_s_es_aux : v list -> e list -> v list * e list
  val split_v_s_es : e list -> v list * e list
  val mem_rep_write_i32_of_i64 : Pbytes.pbt -> nat -> i64 -> Pbytes.pbt
  val mem_rep_write_i32 : Pbytes.pbt -> nat -> i32 -> Pbytes.pbt
  val mem_rep_write_i32_of_i32 : Pbytes.pbt -> nat -> i32 -> Pbytes.pbt
  val mem_rep_write_i16_of_i64 : Pbytes.pbt -> nat -> i64 -> Pbytes.pbt
  val mem_rep_write_i16_of_i32 : Pbytes.pbt -> nat -> i32 -> Pbytes.pbt
  val mem_rep_write_i8_of_i64 : Pbytes.pbt -> nat -> i64 -> Pbytes.pbt
  val mem_rep_write_i8_of_i32 : Pbytes.pbt -> nat -> i32 -> Pbytes.pbt
  val f64_serialise_isabelle_bytes : F64Wrapper.t -> uint8 list
  val serialise_f64 : F64Wrapper.t -> uint8 list
  val f32_serialise_isabelle_bytes : F32Wrapper.t -> uint8 list
  val serialise_f32 : F32Wrapper.t -> uint8 list
  val store_packed_v_numa :
    unit limit_t_ext * Pbytes.pbt ->
      nat -> nat -> v_num -> tp_num -> (unit limit_t_ext * Pbytes.pbt) option
  val store_packed_v_num :
    unit limit_t_ext * Pbytes.pbt ->
      nat -> nat -> v_num -> tp_num -> (unit limit_t_ext * Pbytes.pbt) option
  val crash_invalid : res_step
  val smem_ind : unit inst_ext -> nat option
  val app_s_f_v_s_store_packed :
    t_num ->
      tp_num ->
        nat ->
          (unit limit_t_ext * Pbytes.pbt) list ->
            unit f_ext ->
              v list ->
                (unit limit_t_ext * Pbytes.pbt) list * (v list * res_step)
  val mem_rep_write_i64 : Pbytes.pbt -> nat -> i64 -> Pbytes.pbt
  val mem_rep_write_f64 : Pbytes.pbt -> nat -> F64Wrapper.t -> Pbytes.pbt
  val mem_rep_write_f32 : Pbytes.pbt -> nat -> F32Wrapper.t -> Pbytes.pbt
  val store_v_numa :
    unit limit_t_ext * Pbytes.pbt ->
      nat -> nat -> v_num -> (unit limit_t_ext * Pbytes.pbt) option
  val store_v_num :
    unit limit_t_ext * Pbytes.pbt ->
      nat -> nat -> v_num -> (unit limit_t_ext * Pbytes.pbt) option
  val app_s_f_v_s_store :
    t_num ->
      nat ->
        (unit limit_t_ext * Pbytes.pbt) list ->
          unit f_ext ->
            v list -> (unit limit_t_ext * Pbytes.pbt) list * (v list * res_step)
  val app_s_f_v_s_store_maybe_packed :
    t_num ->
      tp_num option ->
        nat ->
          (unit limit_t_ext * Pbytes.pbt) list ->
            unit f_ext ->
              v list ->
                (unit limit_t_ext * Pbytes.pbt) list * (v list * res_step)
  val mem_rep_read_i64_of_u32 : Pbytes.pbt -> nat -> i64
  val mem_rep_read_i64_of_u16 : Pbytes.pbt -> nat -> i64
  val mem_rep_read_i64_of_i32 : Pbytes.pbt -> nat -> i64
  val mem_rep_read_i64_of_i16 : Pbytes.pbt -> nat -> i64
  val mem_rep_read_i64_of_u8 : Pbytes.pbt -> nat -> i64
  val mem_rep_read_i64_of_i8 : Pbytes.pbt -> nat -> i64
  val mem_rep_read_i64_packed : Pbytes.pbt -> nat -> sx -> tp_num -> i64
  val mem_rep_read_i32_of_u32 : Pbytes.pbt -> nat -> i32
  val mem_rep_read_i32_of_u16 : Pbytes.pbt -> nat -> i32
  val mem_rep_read_i32_of_i32 : Pbytes.pbt -> nat -> i32
  val mem_rep_read_i32_of_i16 : Pbytes.pbt -> nat -> i32
  val mem_rep_read_i32_of_u8 : Pbytes.pbt -> nat -> i32
  val mem_rep_read_i32_of_i8 : Pbytes.pbt -> nat -> i32
  val mem_rep_read_i32_packed : Pbytes.pbt -> nat -> sx -> tp_num -> i32
  val f64_deserialise_isabelle_bytes : uint8 list -> F64Wrapper.t
  val deserialise_f64 : uint8 list -> F64Wrapper.t
  val f32_deserialise_isabelle_bytes : uint8 list -> F32Wrapper.t
  val deserialise_f32 : uint8 list -> F32Wrapper.t
  val sign_extend : sx -> nat -> uint8 list -> uint8 list
  val load_packed_v_numa :
    sx -> unit limit_t_ext * Pbytes.pbt ->
            nat -> nat -> t_num -> tp_num -> v_num option
  val load_packed_v_num :
    sx -> unit limit_t_ext * Pbytes.pbt ->
            nat -> nat -> t_num -> tp_num -> v_num option
  val app_s_f_v_s_load_packed :
    t_num ->
      tp_num ->
        sx -> nat ->
                (unit limit_t_ext * Pbytes.pbt) list ->
                  unit f_ext -> v list -> v list * res_step
  val mem_rep_read_i64 : Pbytes.pbt -> nat -> i64
  val mem_rep_read_i32 : Pbytes.pbt -> nat -> i32
  val mem_rep_read_f64 : Pbytes.pbt -> nat -> F64Wrapper.t
  val mem_rep_read_f32 : Pbytes.pbt -> nat -> F32Wrapper.t
  val load_v_numa :
    unit limit_t_ext * Pbytes.pbt -> nat -> nat -> t_num -> v_num option
  val load_v_num :
    unit limit_t_ext * Pbytes.pbt -> nat -> nat -> t_num -> v_num option
  val app_s_f_v_s_load :
    t_num ->
      nat ->
        (unit limit_t_ext * Pbytes.pbt) list ->
          unit f_ext -> v list -> v list * res_step
  val app_s_f_v_s_load_maybe_packed :
    t_num ->
      (tp_num * sx) option ->
        nat ->
          (unit limit_t_ext * Pbytes.pbt) list ->
            unit f_ext -> v list -> v list * res_step
  val insert_lane_vec_bs : nat -> nat -> uint8 list -> uint8 list -> uint8 list
  val v128_deserialise_isabelle_bytes : uint8 list -> V128Wrapper.t
  val deserialise_v128 : uint8 list -> V128Wrapper.t
  val v128_serialise_isabelle_bytes : V128Wrapper.t -> uint8 list
  val serialise_v128 : V128Wrapper.t -> uint8 list
  val insert_lane_vec :
    shape_vec_i -> nat -> uint8 list -> V128Wrapper.t -> V128Wrapper.t
  val app_s_f_v_s_load_lane_vec :
    shape_vec_i ->
      nat ->
        nat ->
          (unit limit_t_ext * Pbytes.pbt) list ->
            unit f_ext -> v list -> v list * res_step
  val tab_cl_ind : (tab_t * v_ref list) list -> nat -> nat -> v_ref option
  val app_s_f_v_s_call_indirect :
    nat ->
      nat ->
        (tab_t * v_ref list) list ->
          cl list -> unit f_ext -> v list -> v list * (e list * res_step)
  val app_s_f_v_s_memory_init :
    nat ->
      (unit limit_t_ext * Pbytes.pbt) list ->
        (uint8 list) list ->
          unit f_ext -> v list -> v list * (e list * res_step)
  val app_s_f_v_s_memory_fill :
    (unit limit_t_ext * Pbytes.pbt) list ->
      unit f_ext -> v list -> v list * (e list * res_step)
  val app_s_f_v_s_memory_copy :
    (unit limit_t_ext * Pbytes.pbt) list ->
      unit f_ext -> v list -> v list * (e list * res_step)
  val stab_ind : unit inst_ext -> nat -> nat option
  val app_s_f_v_s_table_size :
    nat ->
      (tab_t * v_ref list) list -> unit f_ext -> v list -> v list * res_step
  val app_s_f_v_s_table_init :
    nat ->
      nat ->
        (tab_t * v_ref list) list ->
          (t_ref * v_ref list) list ->
            unit f_ext -> v list -> v list * (e list * res_step)
  val int32_minus_one : i32
  val pred_option : ('a -> bool) -> 'a option -> bool
  val grow_tab :
    tab_t * v_ref list -> nat -> v_ref -> (tab_t * v_ref list) option
  val app_s_f_v_s_table_grow :
    nat ->
      (tab_t * v_ref list) list ->
        unit f_ext -> v list -> (tab_t * v_ref list) list * (v list * res_step)
  val app_s_f_v_s_table_fill :
    nat ->
      (tab_t * v_ref list) list ->
        unit f_ext -> v list -> v list * (e list * res_step)
  val app_s_f_v_s_table_copy :
    nat ->
      nat ->
        (tab_t * v_ref list) list ->
          unit f_ext -> v list -> v list * (e list * res_step)
  val g_val_update : (v -> v) -> 'a global_ext -> 'a global_ext
  val sglob_ind : unit inst_ext -> nat -> nat
  val update_glob :
    unit global_ext list -> unit inst_ext -> nat -> v -> unit global_ext list
  val app_s_f_v_s_global_set :
    nat ->
      unit global_ext list ->
        unit f_ext -> v list -> unit global_ext list * (v list * res_step)
  val app_s_f_v_s_global_get :
    nat -> unit global_ext list -> unit f_ext -> v list -> v list * res_step
  val store_tab1 :
    tab_t * v_ref list -> nat -> v_ref -> (tab_t * v_ref list) option
  val store_tabs1 :
    (tab_t * v_ref list) list ->
      nat -> nat -> v_ref -> ((tab_t * v_ref list) list) option
  val app_s_f_v_s_table_set :
    nat ->
      (tab_t * v_ref list) list ->
        unit f_ext -> v list -> (tab_t * v_ref list) list * (v list * res_step)
  val load_tabs1 : (tab_t * v_ref list) list -> nat -> nat -> v_ref option
  val app_s_f_v_s_table_get :
    nat ->
      (tab_t * v_ref list) list -> unit f_ext -> v list -> v list * res_step
  val store_serialise_vec : storeop_vec -> V128Wrapper.t -> uint8 list
  val app_s_f_v_s_store_vec :
    storeop_vec ->
      nat ->
        (unit limit_t_ext * Pbytes.pbt) list ->
          unit f_ext ->
            v list -> (unit limit_t_ext * Pbytes.pbt) list * (v list * res_step)
  val mem_size : unit limit_t_ext * Pbytes.pbt -> nat
  val app_s_f_v_s_mem_size :
    (unit limit_t_ext * Pbytes.pbt) list ->
      unit f_ext -> v list -> v list * res_step
  val mem_grow :
    unit limit_t_ext * Pbytes.pbt ->
      nat -> (unit limit_t_ext * Pbytes.pbt) option
  val app_s_f_v_s_mem_grow :
    (unit limit_t_ext * Pbytes.pbt) list ->
      unit f_ext ->
        v list -> (unit limit_t_ext * Pbytes.pbt) list * (v list * res_step)
  val read_bytes_vec :
    nat -> nat -> sx -> unit limit_t_ext * Pbytes.pbt -> nat -> uint8 list
  val load_packed_vec :
    tp_vec ->
      sx -> unit limit_t_ext * Pbytes.pbt -> nat -> nat -> (uint8 list) option
  val load_vec :
    loadop_vec ->
      unit limit_t_ext * Pbytes.pbt -> nat -> nat -> (uint8 list) option
  val app_s_f_v_s_load_vec :
    loadop_vec ->
      nat ->
        (unit limit_t_ext * Pbytes.pbt) list ->
          unit f_ext -> v list -> v list * res_step
  val bits_vec : v_vec -> uint8 list
  val bin_rsplit_rev : nat -> nat -> int -> int list
  val word_rsplit_rev : 'a len -> 'b len -> 'a word -> 'b word list
  val serialise_i64 : i64 -> uint8 list
  val serialise_i32 : i32 -> uint8 list
  val bits_num : v_num -> uint8 list
  val app_replace_vec : shape_vec -> nat -> v_vec -> v_num -> v_vec
  val app_v_s_replace_vec : shape_vec -> nat -> v list -> v list * res_step
  val is_null_ref : v_ref -> bool
  val wasm_bool : bool -> i32
  val app_v_s_ref_is_null : v list -> v list * res_step
  val word_rcat_rev : 'a len -> 'b len -> 'a word list -> 'b word
  val deserialise_i64 : uint8 list -> i64
  val deserialise_i32 : uint8 list -> i32
  val app_extract_vec : shape_vec -> sx -> nat -> v_vec -> v_num
  val app_v_s_extract_vec :
    shape_vec -> sx -> nat -> v list -> v list * res_step
  val app_f_v_s_local_set :
    nat -> unit f_ext -> v list -> unit f_ext * (v list * res_step)
  val app_f_v_s_local_get : nat -> unit f_ext -> v list -> v list * res_step
  val app_ternop_vec_v :
    V128Wrapper.ternop_vec_t ->
      V128Wrapper.t -> V128Wrapper.t -> V128Wrapper.t -> V128Wrapper.t
  val app_ternop_vec :
    V128Wrapper.ternop_vec_t -> v_vec -> v_vec -> v_vec -> v_vec
  val app_v_s_ternop_vec :
    V128Wrapper.ternop_vec_t -> v list -> v list * res_step
  val app_f_v_s_ref_func : nat -> unit f_ext -> v list -> v list * res_step
  val app_splat_vec : shape_vec -> v_num -> v_vec
  val app_v_s_splat_vec : shape_vec -> v list -> v list * res_step
  val app_shift_vec_v :
    V128Wrapper.shiftop_vec_t -> V128Wrapper.t -> i32 -> V128Wrapper.t
  val app_shift_vec : V128Wrapper.shiftop_vec_t -> v_vec -> i32 -> v_vec
  val app_v_s_shift_vec :
    V128Wrapper.shiftop_vec_t -> v list -> v list * res_step
  val app_v_s_local_tee : nat -> v list -> v list * (e list * res_step)
  val app_binop_vec_v :
    V128Wrapper.binop_vec_t ->
      V128Wrapper.t -> V128Wrapper.t -> V128Wrapper.t option
  val app_binop_vec : V128Wrapper.binop_vec_t -> v_vec -> v_vec -> v_vec option
  val app_v_s_binop_vec : V128Wrapper.binop_vec_t -> v list -> v list * res_step
  val app_s_f_elem_drop :
    nat ->
      (t_ref * v_ref list) list ->
        unit f_ext -> (t_ref * v_ref list) list * res_step
  val app_s_f_data_drop :
    nat -> (uint8 list) list -> unit f_ext -> (uint8 list) list * res_step
  val app_unop_vec_v : V128Wrapper.unop_vec_t -> V128Wrapper.t -> V128Wrapper.t
  val app_unop_vec : V128Wrapper.unop_vec_t -> v_vec -> v_vec
  val app_v_s_unop_vec : V128Wrapper.unop_vec_t -> v list -> v list * res_step
  val app_test_vec_v : V128Wrapper.testop_vec_t -> V128Wrapper.t -> i32
  val app_test_vec : V128Wrapper.testop_vec_t -> v_vec -> i32
  val app_v_s_test_vec : V128Wrapper.testop_vec_t -> v list -> v list * res_step
  val app_v_s_ref_null : t_ref -> v list -> v list * res_step
  val app_v_s_br_table :
    nat list -> nat -> v list -> v list * (e list * res_step)
  val crash_invariant : res_step
  val update_redex_step : redex -> v list -> e list -> redex
  val update_fc_step : frame_context -> v list -> e list -> frame_context
  val app_testop_i : 'a wasm_int -> testop -> 'a -> bool
  val app_testop : testop -> v_num -> v_num
  val app_v_s_testop : testop -> v list -> v list * res_step
  val select_types_agree : t option -> v -> v -> bool
  val app_v_s_select : t option -> v list -> v list * res_step
  val app_relop_i : 'a wasm_int -> relop_i -> 'a -> 'a -> bool
  val app_relop_i_v : relop_i -> v_num -> v_num -> v_num
  val app_relop_f : 'a wasm_float -> relop_f -> 'a -> 'a -> bool
  val app_relop_f_v : relop_f -> v_num -> v_num -> v_num
  val app_relop : relop -> v_num -> v_num -> v_num
  val app_v_s_relop : relop -> v list -> v list * res_step
  val wasm_deserialise_num : uint8 list -> t_num -> v_num
  val wasm_reinterpret : t_num -> v_num -> v_num
  val app_v_s_cvtop :
    cvtop -> t_num -> t_num -> (sat * sx) option -> v list -> v list * res_step
  val app_v_s_br_if : nat -> v list -> v list * (e list * res_step)
  val app_binop_i : 'a wasm_int -> binop_i -> 'a -> 'a -> 'a option
  val app_binop_i_v : binop_i -> v_num -> v_num -> v_num option
  val app_binop_f : 'a wasm_float -> binop_f -> 'a -> 'a -> 'a option
  val app_binop_f_v : binop_f -> v_num -> v_num -> v_num option
  val app_binop : binop -> v_num -> v_num -> v_num option
  val app_v_s_binop : binop -> v list -> v list * res_step
  val app_unop_i : 'a wasm_int -> unop_i -> 'a -> 'a
  val app_unop_i_v : unop_i -> v_num -> v_num
  val app_unop_f : 'a wasm_float -> unop_f -> 'a -> 'a
  val app_unop_f_v : unop_f -> v_num -> v_num
  val app_extend_s : tp_num -> v_num -> v_num
  val app_unop : unop -> v_num -> v_num
  val app_v_s_unop : unop -> v list -> v list * res_step
  val app_v_s_drop : v list -> v list * res_step
  val app_v_s_if :
    tb -> b_e list -> b_e list -> v list -> v list * (e list * res_step)
  val sfunc_ind : unit inst_ext -> nat -> nat
  val app_f_call : nat -> unit f_ext -> e list * res_step
  val split_n : v list -> nat -> v list * v list
  val globs_update :
    (unit global_ext list -> unit global_ext list) -> 'a s_ext -> 'a s_ext
  val elems_update :
    ((t_ref * v_ref list) list -> (t_ref * v_ref list) list) ->
      'a s_ext -> 'a s_ext
  val datas_update :
    ((uint8 list) list -> (uint8 list) list) -> 'a s_ext -> 'a s_ext
  val run_step_b_e : b_e -> config -> config * res_step
  val rep_host_func :
    host_func -> unit s_ext * v list -> (unit s_ext * v list) option
  val host_func_apply_impl :
    unit s_ext -> tf -> host_func -> v list -> (unit s_ext * v list) option
  val crash_exhaustion : res_step
  val run_step_e : e -> config -> config * res_step
  val run_iter : nat -> config -> config * res
  val run_v :
    nat -> nat -> unit s_ext * (unit f_ext * b_e list) -> unit s_ext * res
  val const_expr_p : unit t_context_ext -> b_e -> unit pred
  val const_expr : unit t_context_ext -> b_e -> bool
  val min : 'a ord -> 'a -> 'a -> 'a
  val funcs_update : (cl list -> cl list) -> 'a s_ext -> 'a s_ext
  val m_exports : 'a m_ext -> unit module_export_ext list
  val m_imports : 'a m_ext -> unit module_import_ext list
  val limit_type_checker_p : unit limit_t_ext -> nat -> unit pred
  val limit_typing : unit limit_t_ext -> nat -> bool
  val alloc_Xs :
    (unit s_ext -> 'a -> unit s_ext * nat) ->
      unit s_ext -> 'a list -> unit s_ext * nat list
  val d_mode : 'a module_data_ext -> data_mode
  val d_init : 'a module_data_ext -> uint8 list
  val run_data : unit module_data_ext -> nat -> b_e list
  val e_mode : 'a module_elem_ext -> elem_mode
  val e_init : 'a module_elem_ext -> (b_e list) list
  val run_elem : unit module_elem_ext -> nat -> b_e list
  val limits_compat : 'a limit_t_ext -> 'b limit_t_ext -> bool
  val tab_subtyping : tab_t -> tab_t -> bool
  val mem_subtyping : unit limit_t_ext -> unit limit_t_ext -> bool
  val external_checker : unit s_ext -> v_ext -> extern_t -> unit pred
  val external_typing : unit s_ext -> v_ext -> extern_t -> bool
  val typing : unit t_context_ext -> b_e list -> tf -> bool
  val alloc_mem : unit s_ext -> unit limit_t_ext -> unit s_ext * nat
  val alloc_tab : unit s_ext -> tab_t -> unit s_ext * nat
  val run_datas : unit module_data_ext list -> e list
  val run_elems : unit module_elem_ext list -> e list
  val export_get_v_ext : unit inst_ext -> v_ext -> v_ext
  val m_funcs_update :
    ((nat * (t list * b_e list)) list -> (nat * (t list * b_e list)) list) ->
      'a m_ext -> 'a m_ext
  val m_start_update : (nat option -> nat option) -> 'a m_ext -> 'a m_ext
  val alloc_data : unit s_ext -> unit module_data_ext -> unit s_ext * nat
  val e_type : 'a module_elem_ext -> t_ref
  val alloc_elem :
    unit s_ext -> unit module_elem_ext * v_ref list -> unit s_ext * nat
  val alloc_func :
    unit s_ext -> nat * (t list * b_e list) -> unit inst_ext -> unit s_ext * nat
  val g_type : 'a module_glob_ext -> unit tg_ext
  val alloc_glob : unit s_ext -> unit module_glob_ext * v -> unit s_ext * nat
  val run_invoke_v :
    nat -> nat -> unit s_ext * (v list * nat) -> unit s_ext * res
  val run : unit s_ext * (unit f_ext * b_e list) -> unit s_ext * res
  val module_tab_type_checker_p : tab_t -> unit pred
  val module_tab_typing : tab_t -> bool
  val g_init : 'a module_glob_ext -> b_e list
  val local_update : (t list -> t list) -> 'a t_context_ext -> 'a t_context_ext
  val interp_get_v : unit s_ext -> unit inst_ext -> b_e list -> v
  val extract_funcidx_b_e : b_e -> nat option
  val module_start_type_checker_p : unit t_context_ext -> nat -> unit pred
  val module_start_typing : unit t_context_ext -> nat -> bool
  val global_update :
    (unit tg_ext list -> unit tg_ext list) ->
      'a t_context_ext -> 'a t_context_ext
  val return_update :
    ((t list) option -> (t list) option) -> 'a t_context_ext -> 'a t_context_ext
  val run_instantiate :
    nat -> nat -> unit s_ext * (unit inst_ext * e list) -> unit s_ext * res
  val e_desc : 'a module_export_ext -> v_ext
  val e_name : 'a module_export_ext -> string
  val i_desc : 'a module_import_ext -> imp_desc
  val interp_get_v_ref : unit s_ext -> unit inst_ext -> b_e list -> v_ref
  val collect_funcidxs_module_import : unit module_import_ext -> nat list
  val collect_funcidxs_module_export : unit module_export_ext -> nat list
  val collect_funcidxs_module_glob : unit module_glob_ext -> nat list
  val collect_funcidxs_module_func : nat * (t list * b_e list) -> nat list
  val collect_funcidxs_b_e_list : b_e list -> nat list
  val collect_funcidxs_elem_mode : elem_mode -> nat list
  val collect_funcidxs_module_elem : unit module_elem_ext -> nat list
  val collect_funcidxs_module_data : unit module_data_ext -> nat list
  val collect_funcidxs_module : unit m_ext -> nat list
  val gather_m_f_type : tf list -> nat * (t list * b_e list) -> tf option
  val interp_get_v_refs :
    unit s_ext -> unit inst_ext -> (b_e list) list -> v_ref list
  val run_invoke : unit s_ext * (v list * nat) -> unit s_ext * res
  val module_glob_type_checker :
    unit t_context_ext -> unit module_glob_ext -> bool
  val module_func_type_checker :
    unit t_context_ext -> nat * (t list * b_e list) -> bool
  val elem_mode_type_checker : unit t_context_ext -> elem_mode -> t_ref -> bool
  val module_elem_type_checker :
    unit t_context_ext -> unit module_elem_ext -> t_ref -> bool
  val data_mode_type_checker : unit t_context_ext -> data_mode -> bool
  val module_data_type_checker :
    unit t_context_ext -> unit module_data_ext -> bool
  val module_import_typer : tf list -> imp_desc -> extern_t option
  val module_export_typer : unit t_context_ext -> v_ext -> extern_t option
  val module_type_checker : unit m_ext -> (extern_t list * extern_t list) option
  val interp_alloc_module :
    unit s_ext ->
      unit m_ext ->
        v_ext list ->
          v list ->
            (v_ref list) list ->
              unit s_ext * (unit inst_ext * unit module_export_ext list)
  val interp_instantiate :
    unit s_ext -> unit m_ext -> v_ext list -> unit s_ext * res_inst
  val interp_instantiate_init :
    unit s_ext -> unit m_ext -> v_ext list -> unit s_ext * res_inst
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

type 'a divide_trivial =
  {one_divide_trivial : 'a one; zero_divide_trivial : 'a zero;
    divide_divide_trivial : 'a divide};;

let divide_trivial_int =
  ({one_divide_trivial = one_int; zero_divide_trivial = zero_int;
     divide_divide_trivial = divide_int}
    : int divide_trivial);;

type 'a semiring_no_zero_divisors_cancel =
  {semiring_no_zero_divisors_semiring_no_zero_divisors_cancel :
     'a semiring_no_zero_divisors};;

type 'a semidom_divide =
  {divide_trivial_semidom_divide : 'a divide_trivial;
    semidom_semidom_divide : 'a semidom;
    semiring_no_zero_divisors_cancel_semidom_divide :
      'a semiring_no_zero_divisors_cancel};;

let semiring_no_zero_divisors_cancel_int =
  ({semiring_no_zero_divisors_semiring_no_zero_divisors_cancel =
      semiring_no_zero_divisors_int}
    : int semiring_no_zero_divisors_cancel);;

let semidom_divide_int =
  ({divide_trivial_semidom_divide = divide_trivial_int;
     semidom_semidom_divide = semidom_int;
     semiring_no_zero_divisors_cancel_semidom_divide =
       semiring_no_zero_divisors_cancel_int}
    : int semidom_divide);;

type 'a semiring_modulo_trivial =
  {divide_trivial_semiring_modulo_trivial : 'a divide_trivial;
    semiring_modulo_semiring_modulo_trivial : 'a semiring_modulo};;

type 'a algebraic_semidom =
  {semidom_divide_algebraic_semidom : 'a semidom_divide};;

type 'a semidom_modulo =
  {algebraic_semidom_semidom_modulo : 'a algebraic_semidom;
    semiring_modulo_trivial_semidom_modulo : 'a semiring_modulo_trivial};;

let semiring_modulo_trivial_int =
  ({divide_trivial_semiring_modulo_trivial = divide_trivial_int;
     semiring_modulo_semiring_modulo_trivial = semiring_modulo_int}
    : int semiring_modulo_trivial);;

let algebraic_semidom_int =
  ({semidom_divide_algebraic_semidom = semidom_divide_int} :
    int algebraic_semidom);;

let semidom_modulo_int =
  ({algebraic_semidom_semidom_modulo = algebraic_semidom_int;
     semiring_modulo_trivial_semidom_modulo = semiring_modulo_trivial_int}
    : int semidom_modulo);;

type nat = Nat of Z.t;;

let rec integer_of_nat (Nat x) = x;;

let rec push_bit_integer n k = Bit_Shifts.push (integer_of_nat n) k;;

let rec bit_integer
  k n = not (Z.equal (Z.logand k (push_bit_integer n (Z.of_int 1))) Z.zero);;

let rec bit_int (Int_of_integer k) n = bit_integer k n;;

type 'a semiring_bits =
  {semiring_parity_semiring_bits : 'a semiring_parity;
    semiring_modulo_trivial_semiring_bits : 'a semiring_modulo_trivial;
    bit : 'a -> nat -> bool};;
let bit _A = _A.bit;;

let semiring_bits_int =
  ({semiring_parity_semiring_bits = semiring_parity_int;
     semiring_modulo_trivial_semiring_bits = semiring_modulo_trivial_int;
     bit = bit_int}
    : int semiring_bits);;

let rec unset_bit_integer
  n k = Z.logand k (Z.lognot (push_bit_integer n (Z.of_int 1)));;

let rec unset_bit_int
  n (Int_of_integer k) = Int_of_integer (unset_bit_integer n k);;

let rec mask_integer n = Z.sub (push_bit_integer n (Z.of_int 1)) (Z.of_int 1);;

let rec take_bit_integer n k = Z.logand k (mask_integer n);;

let rec take_bit_int
  n (Int_of_integer k) = Int_of_integer (take_bit_integer n k);;

let rec push_bit_int
  n (Int_of_integer k) = Int_of_integer (push_bit_integer n k);;

let rec flip_bit_integer n k = Z.logxor k (push_bit_integer n (Z.of_int 1));;

let rec flip_bit_int
  n (Int_of_integer k) = Int_of_integer (flip_bit_integer n k);;

let rec drop_bit_integer n k = Bit_Shifts.drop (integer_of_nat n) k;;

let rec drop_bit_int
  n (Int_of_integer k) = Int_of_integer (drop_bit_integer n k);;

let rec set_bit_integer n k = Z.logor k (push_bit_integer n (Z.of_int 1));;

let rec set_bit_int
  n (Int_of_integer k) = Int_of_integer (set_bit_integer n k);;

let rec mask_int n = Int_of_integer (mask_integer n);;

let rec xor_int
  (Int_of_integer k) (Int_of_integer l) = Int_of_integer (Z.logxor k l);;

let rec and_int
  (Int_of_integer k) (Int_of_integer l) = Int_of_integer (Z.logand k l);;

let rec or_int
  (Int_of_integer k) (Int_of_integer l) = Int_of_integer (Z.logor k l);;

type 'a semiring_bit_operations =
  {semiring_bits_semiring_bit_operations : 'a semiring_bits;
    anda : 'a -> 'a -> 'a; ora : 'a -> 'a -> 'a; xor : 'a -> 'a -> 'a;
    mask : nat -> 'a; set_bit : nat -> 'a -> 'a; unset_bit : nat -> 'a -> 'a;
    flip_bit : nat -> 'a -> 'a; push_bit : nat -> 'a -> 'a;
    drop_bit : nat -> 'a -> 'a; take_bit : nat -> 'a -> 'a};;
let anda _A = _A.anda;;
let ora _A = _A.ora;;
let xor _A = _A.xor;;
let mask _A = _A.mask;;
let set_bit _A = _A.set_bit;;
let unset_bit _A = _A.unset_bit;;
let flip_bit _A = _A.flip_bit;;
let push_bit _A = _A.push_bit;;
let drop_bit _A = _A.drop_bit;;
let take_bit _A = _A.take_bit;;

let rec not_int (Int_of_integer k) = Int_of_integer (Z.lognot k);;

type 'a ring_bit_operations =
  {semiring_bit_operations_ring_bit_operations : 'a semiring_bit_operations;
    ring_parity_ring_bit_operations : 'a ring_parity; nota : 'a -> 'a};;
let nota _A = _A.nota;;

let semiring_bit_operations_int =
  ({semiring_bits_semiring_bit_operations = semiring_bits_int; anda = and_int;
     ora = or_int; xor = xor_int; mask = mask_int; set_bit = set_bit_int;
     unset_bit = unset_bit_int; flip_bit = flip_bit_int;
     push_bit = push_bit_int; drop_bit = drop_bit_int; take_bit = take_bit_int}
    : int semiring_bit_operations);;

let ring_bit_operations_int =
  ({semiring_bit_operations_ring_bit_operations = semiring_bit_operations_int;
     ring_parity_ring_bit_operations = ring_parity_int; nota = not_int}
    : int ring_bit_operations);;

let rec equal_nata m n = Z.equal (integer_of_nat m) (integer_of_nat n);;

let equal_nat = ({equal = equal_nata} : nat equal);;

let one_nata : nat = Nat (Z.of_int 1);;

let one_nat = ({one = one_nata} : nat one);;

let rec times_nata m n = Nat (Z.mul (integer_of_nat m) (integer_of_nat n));;

let times_nat = ({times = times_nata} : nat times);;

let power_nat = ({one_power = one_nat; times_power = times_nat} : nat power);;

let rec less_eq_nat m n = Z.leq (integer_of_nat m) (integer_of_nat n);;

type 'a ord = {less_eq : 'a -> 'a -> bool; less : 'a -> 'a -> bool};;
let less_eq _A = _A.less_eq;;
let less _A = _A.less;;

let rec less_nat m n = Z.lt (integer_of_nat m) (integer_of_nat n);;

let ord_nat = ({less_eq = less_eq_nat; less = less_nat} : nat ord);;

type 'a itself = Type;;

type 'a len0 = {len_of : 'a itself -> nat};;
let len_of _A = _A.len_of;;

type 'a len = {len0_len : 'a len0};;

type 'a word = Word of int;;

let rec one_worda _A = Word one_inta;;

let rec one_word _A = ({one = one_worda _A} : 'a word one);;

let rec the_int _A (Word x) = x;;

let rec of_int _A k = Word (take_bit_int (len_of _A.len0_len Type) k);;

let rec plus_worda _A
  a b = of_int _A (plus_inta (the_int _A a) (the_int _A b));;

let rec plus_word _A = ({plus = plus_worda _A} : 'a word plus);;

let rec zero_worda _A = Word zero_inta;;

let rec zero_word _A = ({zero = zero_worda _A} : 'a word zero);;

let rec times_worda _A
  a b = of_int _A (times_inta (the_int _A a) (the_int _A b));;

let rec times_word _A = ({times = times_worda _A} : 'a word times);;

let rec semigroup_add_word _A =
  ({plus_semigroup_add = (plus_word _A)} : 'a word semigroup_add);;

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

let rec zero_neq_one_word _A =
  ({one_zero_neq_one = (one_word _A); zero_zero_neq_one = (zero_word _A)} :
    'a word zero_neq_one);;

let rec ab_semigroup_mult_word _A =
  ({semigroup_mult_ab_semigroup_mult = (semigroup_mult_word _A)} :
    'a word ab_semigroup_mult);;

let rec comm_semiring_word _A =
  ({ab_semigroup_mult_comm_semiring = (ab_semigroup_mult_word _A);
     semiring_comm_semiring = (semiring_word _A)}
    : 'a word comm_semiring);;

let rec comm_semiring_0_word _A =
  ({comm_semiring_comm_semiring_0 = (comm_semiring_word _A);
     semiring_0_comm_semiring_0 = (semiring_0_word _A)}
    : 'a word comm_semiring_0);;

type t_vec = T_v128;;

let rec equal_t_vec T_v128 T_v128 = true;;

type t_ref = T_func_ref | T_ext_ref;;

let rec equal_t_ref x0 x1 = match x0, x1 with T_func_ref, T_ext_ref -> false
                      | T_ext_ref, T_func_ref -> false
                      | T_ext_ref, T_ext_ref -> true
                      | T_func_ref, T_func_ref -> true;;

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

type t = T_num of t_num | T_vec of t_vec | T_ref of t_ref | T_bot;;

let rec equal_ta x0 x1 = match x0, x1 with T_ref x3, T_bot -> false
                   | T_bot, T_ref x3 -> false
                   | T_vec x2, T_bot -> false
                   | T_bot, T_vec x2 -> false
                   | T_vec x2, T_ref x3 -> false
                   | T_ref x3, T_vec x2 -> false
                   | T_num x1, T_bot -> false
                   | T_bot, T_num x1 -> false
                   | T_num x1, T_ref x3 -> false
                   | T_ref x3, T_num x1 -> false
                   | T_num x1, T_vec x2 -> false
                   | T_vec x2, T_num x1 -> false
                   | T_ref x3, T_ref y3 -> equal_t_ref x3 y3
                   | T_vec x2, T_vec y2 -> equal_t_vec x2 y2
                   | T_num x1, T_num y1 -> equal_t_num x1 y1
                   | T_bot, T_bot -> true;;

let equal_t = ({equal = equal_ta} : t equal);;

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

type i32 = I32_impl_abs of int32;;

let zero_i32a : i32 = I32_impl_abs Int32.zero;;

let zero_i32 = ({zero = zero_i32a} : i32 zero);;

let rec max _A a b = (if less_eq _A a b then b else a);;

let ord_integer = ({less_eq = Z.leq; less = Z.lt} : Z.t ord);;

let rec nat_of_integer k = Nat (max ord_integer Z.zero k);;

let rec len_of_i32 uu = nat_of_integer (Z.of_int 32);;

let len0_i32 = ({len_of = len_of_i32} : i32 len0);;

let len_i32 = ({len0_len = len0_i32} : i32 len);;

let rec bit_uint32
  w n = less_nat n (nat_of_integer (Z.of_int 32)) &&
          Uint32.test_bit w (integer_of_nat n);;

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

let rec plus_nat m n = Nat (Z.add (integer_of_nat m) (integer_of_nat n));;

let rec fold_atLeastAtMost_nat
  f a b acc =
    (if less_nat b a then acc
      else fold_atLeastAtMost_nat f (plus_nat a one_nata) b (f a acc));;

let zero_nat : nat = Nat Z.zero;;

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

let rec push_bit_uint32
  k w = (if less_nat k (nat_of_integer (Z.of_int 32))
          then Uint32.shiftl w (integer_of_nat k) else Int32.zero);;

let rec drop_bit_uint32
  k w = (if less_nat k (nat_of_integer (Z.of_int 32))
          then Uint32.shiftr w (integer_of_nat k) else Int32.zero);;

let mod0_uint32 _ = failwith "Uint32.mod0_uint32";;

let div0_uint32 _ = failwith "Uint32.div0_uint32";;

let rec uint32_divmod
  x y = (if Uint32.less_eq (uint32 (Z.of_string "2147483648")) y
          then (if Uint32.less x y then (Int32.zero, x)
                 else (Int32.one, Int32.sub x y))
          else (if (Int32.compare y Int32.zero = 0)
                 then (div0_uint32 x, mod0_uint32 x)
                 else (let q =
                         push_bit_uint32 one_nata
                           (Int32.div (drop_bit_uint32 one_nata x) y)
                         in
                       let r = Int32.sub x (Int32.mul q y) in
                        (if Uint32.less_eq y r
                          then (Int32.add q Int32.one, Int32.sub r y)
                          else (q, r)))));;

let rec uint32_mod x y = snd (uint32_divmod x y);;

let rec int_rem_u_i32
  (I32_impl_abs x) (I32_impl_abs y) =
    (if (Int32.compare y Int32.zero = 0) then None
      else Some (I32_impl_abs (uint32_mod x y)));;

let rec int_rem_s_i32
  (I32_impl_abs x) (I32_impl_abs y) =
    (if (Int32.compare y Int32.zero = 0) then None
      else Some (I32_impl_abs (Int32.sub x (Int32.mul (Int32.div x y) y))));;

let rec uint32_div x y = fst (uint32_divmod x y);;

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

let rec minus_nat
  m n = Nat (max ord_integer Z.zero
              (Z.sub (integer_of_nat m) (integer_of_nat n)));;

let rec mask_uint32
  n = (if equal_nata n zero_nat then Int32.zero
        else Int32.logor (push_bit_uint32 (minus_nat n one_nata) Int32.one)
               (mask_uint32 (minus_nat n one_nata)));;

let rec take_bit_uint32 n a = Int32.logand a (mask_uint32 n);;

let rec modulo_uint32
  x y = (if (Int32.compare y Int32.zero = 0) then x else uint32_mod x y);;

let rec int_rotr_i32
  (I32_impl_abs x) (I32_impl_abs y) =
    I32_impl_abs
      (let n = nat_of_uint32 (modulo_uint32 y (uint32 (Z.of_int 32))) in
        Int32.logor (drop_bit_uint32 n x)
          (push_bit_uint32 (minus_nat (nat_of_integer (Z.of_int 32)) n)
            (take_bit_uint32 n x)));;

let rec int_rotl_i32
  (I32_impl_abs x) (I32_impl_abs y) =
    I32_impl_abs
      (let n = nat_of_uint32 (modulo_uint32 y (uint32 (Z.of_int 32))) in
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

let rec suc n = plus_nat n one_nata;;

let rec gen_length n x1 = match n, x1 with n, x :: xs -> gen_length (suc n) xs
                     | n, [] -> n;;

let rec size_list x = gen_length zero_nat x;;

let rec drop_bit_word _A n w = Word (drop_bit_int n (the_int _A w));;

let rec and_word _A v w = Word (and_int (the_int _A v) (the_int _A w));;

let rec equal_word _A v w = equal_inta (the_int _A v) (the_int _A w);;

let rec bit_word _A
  a n = equal_word _A (and_word _A (drop_bit_word _A n a) (one_worda _A))
          (one_worda _A);;

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

type num1 = One_num1;;

type 'a finite = unit;;

type 'a bit0 = Abs_bit0 of int;;

let rec len_of_num1 uu = one_nata;;

let len0_num1 = ({len_of = len_of_num1} : num1 len0);;

let len_num1 = ({len0_len = len0_num1} : num1 len);;

let rec len_of_bit0 _A
  uu = times_nata (nat_of_integer (Z.of_int 2)) (len_of _A Type);;

let rec len0_bit0 _A = ({len_of = len_of_bit0 _A} : 'a bit0 len0);;

let rec len_bit0 _A = ({len0_len = (len0_bit0 _A.len0_len)} : 'a bit0 len);;

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

type i64 = I64_impl_abs of int64;;

let zero_i64a : i64 = I64_impl_abs Int64.zero;;

let zero_i64 = ({zero = zero_i64a} : i64 zero);;

let rec len_of_i64 uu = nat_of_integer (Z.of_int 64);;

let len0_i64 = ({len_of = len_of_i64} : i64 len0);;

let len_i64 = ({len0_len = len0_i64} : i64 len);;

let rec bit_uint64
  w n = less_nat n (nat_of_integer (Z.of_int 64)) &&
          Uint64.test_bit w (integer_of_nat n);;

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
  k w = (if less_nat k (nat_of_integer (Z.of_int 64))
          then Uint64.shiftl w (integer_of_nat k) else Int64.zero);;

let rec drop_bit_uint64
  k w = (if less_nat k (nat_of_integer (Z.of_int 64))
          then Uint64.shiftr w (integer_of_nat k) else Int64.zero);;

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

let rec mask_uint64
  n = (if equal_nata n zero_nat then Int64.zero
        else Int64.logor (push_bit_uint64 (minus_nat n one_nata) Int64.one)
               (mask_uint64 (minus_nat n one_nata)));;

let rec take_bit_uint64 n a = Int64.logand a (mask_uint64 n);;

let rec modulo_uint64
  x y = (if (Int64.compare y Int64.zero = 0) then x else uint64_mod x y);;

let rec int_rotr_i64
  (I64_impl_abs x) (I64_impl_abs y) =
    I64_impl_abs
      (let n = nat_of_uint64 (modulo_uint64 y (uint64 (Z.of_int 64))) in
        Int64.logor (drop_bit_uint64 n x)
          (push_bit_uint64 (minus_nat (nat_of_integer (Z.of_int 64)) n)
            (take_bit_uint64 n x)));;

let rec int_rotl_i64
  (I64_impl_abs x) (I64_impl_abs y) =
    I64_impl_abs
      (let n = nat_of_uint64 (modulo_uint64 y (uint64 (Z.of_int 64))) in
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

let equal_literal = ({equal = (fun a b -> ((a : string) = b))} : string equal);;

type typerepa = Typerep of string * typerepa list;;

type sx = S | U;;

type binop_i = Add | Sub | Mul | Div of sx | Rem of sx | And | Or | Xor | Shl |
  Shr of sx | Rotl | Rotr;;

type binop_f = Addf | Subf | Mulf | Divf | Min | Max | Copysign;;

type binop = Binop_i of binop_i | Binop_f of binop_f;;

let rec typerep_binopa t = Typerep ("Wasm_Ast.binop", []);;

type 'a typerep = {typerep : 'a itself -> typerepa};;
let typerep _A = _A.typerep;;

let typerep_binop = ({typerep = typerep_binopa} : binop typerep);;

type cvtop = Convert | Reinterpret;;

let rec typerep_cvtopa t = Typerep ("Wasm_Ast.cvtop", []);;

let typerep_cvtop = ({typerep = typerep_cvtopa} : cvtop typerep);;

let rec equal_unita u v = true;;

let equal_unit = ({equal = equal_unita} : unit equal);;

type 'a inst_ext =
  Inst_ext of
    tf list * nat list * nat list * nat list * nat list * nat list * nat list *
      'a;;

type v_vec = ConstVec128 of V128Wrapper.t;;

type 'a limit_t_ext = Limit_t_ext of nat * nat option * 'a;;

type tab_t = T_tab of unit limit_t_ext * t_ref;;

type shape_vec_i = I8_16 | I16_8 | I32_4 | I64_2;;

type storeop_vec = Store_128 | Store_lane of shape_vec_i * nat;;

type tp_vec = Tp_v8_8 | Tp_v16_4 | Tp_v32_2;;

type loadop_vec = Load_128 | Load_packed_vec of tp_vec * sx | Load_32_zero |
  Load_64_zero | Load_splat of shape_vec_i;;

type shape_vec_f = F32_4 | F64_2;;

type shape_vec = Svi of shape_vec_i | Svf of shape_vec_f;;

type tp_num = Tp_i8 | Tp_i16 | Tp_i32;;

type testop = Eqz;;

type v_num = ConstInt32 of i32 | ConstInt64 of i64 |
  ConstFloat32 of F32Wrapper.t | ConstFloat64 of F64Wrapper.t;;

type relop_i = Eq | Ne | Lt of sx | Gt of sx | Le of sx | Ge of sx;;

type relop_f = Eqf | Nef | Ltf | Gtf | Lef | Gef;;

type relop = Relop_i of relop_i | Relop_f of relop_f;;

type unop_i = Clz | Ctz | Popcnt;;

type unop_f = Neg | Abs | Ceil | Floor | Trunc | Nearest | Sqrt;;

type unop = Unop_i of unop_i | Unop_f of unop_f | Extend_s of tp_num;;

type sat = Sat | Nonsat;;

type tb = Tbf of nat | Tbv of t option;;

type b_e = Unreachable | Nop | Drop | Select of t option |
  Block of tb * b_e list | Loop of tb * b_e list |
  If of tb * b_e list * b_e list | Br of nat | Br_if of nat |
  Br_table of nat list * nat | Return | Call of nat | Call_indirect of nat * nat
  | Local_get of nat | Local_set of nat | Local_tee of nat | Global_get of nat |
  Global_set of nat | Table_get of nat | Table_set of nat | Table_size of nat |
  Table_grow of nat | Load of t_num * (tp_num * sx) option * nat * nat |
  Store of t_num * tp_num option * nat * nat |
  Load_vec of loadop_vec * nat * nat |
  Load_lane_vec of shape_vec_i * nat * nat * nat |
  Store_vec of storeop_vec * nat * nat | Memory_size | Memory_grow |
  Memory_init of nat | Memory_fill | Memory_copy | Table_init of nat * nat |
  Table_copy of nat * nat | Table_fill of nat | Elem_drop of nat |
  Data_drop of nat | EConstNum of v_num | EConstVec of v_vec |
  Unop of t_num * unop | Binop of t_num * binop | Testop of t_num * testop |
  Relop of t_num * relop | Cvtop of t_num * cvtop * t_num * (sat * sx) option |
  Ref_null of t_ref | Ref_is_null | Ref_func of nat |
  Unop_vec of V128Wrapper.unop_vec_t | Binop_vec of V128Wrapper.binop_vec_t |
  Ternop_vec of V128Wrapper.ternop_vec_t | Test_vec of V128Wrapper.testop_vec_t
  | Shift_vec of V128Wrapper.shiftop_vec_t | Splat_vec of shape_vec |
  Extract_vec of shape_vec * sx * nat | Replace_vec of shape_vec * nat;;

type uint8 = Abs_uint8 of num1 bit0 bit0 bit0 word;;

type v = V_num of v_num | V_vec of v_vec | V_ref of v_ref
and 'a global_ext = Global_ext of mut * v * 'a
and 'a s_ext =
  S_ext of
    cl list * (tab_t * v_ref list) list * (unit limit_t_ext * Pbytes.pbt) list *
      unit global_ext list * (t_ref * v_ref list) list * (uint8 list) list * 'a
and host_func =
  Abs_host_func of (unit s_ext * v list -> (unit s_ext * v list) option)
and host = Host_func of host_func | Host_ref of int32
and cl = Func_native of unit inst_ext * tf * t list * b_e list |
  Func_host of tf * host
and v_ref = ConstNull of t_ref | ConstRefFunc of nat | ConstRefExtern of host;;

type 'a f_ext = F_ext of v list * unit inst_ext * 'a;;

type e = Basic of b_e | Trap | Invoke of nat | Label of nat * e list * e list |
  Frame of nat * unit f_ext * e list | Ref of v_ref;;

type 'a seq = Empty | Insert of 'a * 'a pred | Join of 'a pred * 'a seq
and 'a pred = Seq of (unit -> 'a seq);;

type v_ext = Ext_func of nat | Ext_tab of nat | Ext_mem of nat |
  Ext_glob of nat;;

type 'a tg_ext = Tg_ext of mut * t * 'a;;

type imp_desc = Imp_func of nat | Imp_tab of tab_t | Imp_mem of unit limit_t_ext
  | Imp_glob of unit tg_ext;;

type 'a module_import_ext =
  Module_import_ext of string * string * imp_desc * 'a;;

type 'a module_export_ext = Module_export_ext of string * v_ext * 'a;;

type 'a module_glob_ext = Module_glob_ext of unit tg_ext * b_e list * 'a;;

type elem_mode = Em_passive | Em_active of nat * b_e list | Em_declarative;;

type 'a module_elem_ext =
  Module_elem_ext of t_ref * (b_e list) list * elem_mode * 'a;;

type data_mode = Dm_passive | Dm_active of nat * b_e list;;

type 'a module_data_ext = Module_data_ext of uint8 list * data_mode * 'a;;

type 'a m_ext =
  M_ext of
    tf list * (nat * (t list * b_e list)) list * tab_t list *
      unit limit_t_ext list * unit module_glob_ext list *
      unit module_elem_ext list * unit module_data_ext list * nat option *
      unit module_import_ext list * unit module_export_ext list * 'a;;

type res_error = Error_invalid of string | Error_invariant of string |
  Error_exhaustion of string;;

type res = RCrash of res_error | RTrap of string | RValue of v list;;

type extern_t = Te_func of tf | Te_tab of tab_t | Te_mem of unit limit_t_ext |
  Te_glob of unit tg_ext;;

type redex = Redex of v list * e list * b_e list;;

type label_context = Label_context of v list * b_e list * nat * b_e list;;

type frame_context =
  Frame_context of redex * label_context list * nat * unit f_ext;;

type config = Config of nat * unit s_ext * frame_context * frame_context list;;

type reach = Reach | Unreach;;

type res_step = Res_crash of res_error | Res_trap of string | Step_normal;;

type res_inst = RI_crash of res_error | RI_trap of string |
  RI_res of unit inst_ext * unit module_export_ext list * e list;;

type 'a t_context_ext =
  T_context_ext of
    tf list * tf list * unit tg_ext list * t_ref list * unit list * tab_t list *
      unit limit_t_ext list * t list * (t list) list * (t list) option *
      nat list * 'a;;

let failwith_nth _ = failwith "OCaml_Printing.failwith_nth";;

let rec nth
  x0 n = match x0, n with [], n -> failwith_nth n
    | x :: xs, n ->
        (if equal_nata n zero_nat then x else nth xs (minus_nat n one_nata));;

let rec zip xs ys = match xs, ys with x :: xs, y :: ys -> (x, y) :: zip xs ys
              | xs, [] -> []
              | [], ys -> [];;

let rec drop
  n x1 = match n, x1 with n, [] -> []
    | n, x :: xs ->
        (if equal_nata n zero_nat then x :: xs
          else drop (minus_nat n one_nata) xs);;

let rec null = function [] -> true
               | x :: xs -> false;;

let rec last (x :: xs) = (if null xs then x else last xs);;

let rec maps f x1 = match f, x1 with f, [] -> []
               | f, x :: xs -> f x @ maps f xs;;

let rec take_tr
  n x1 acc_r = match n, x1, acc_r with n, [], acc_r -> rev acc_r
    | n, x :: xs, acc_r ->
        (if equal_nata n zero_nat then rev acc_r
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

let rec int_of_integer_symbolic x = Int_of_integer x;;

let rec uint8
  i = Abs_uint8
        (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
          (int_of_integer_symbolic i));;

let rec remdups _A
  = function [] -> []
    | x :: xs ->
        (if member _A xs x then remdups _A xs else x :: remdups _A xs);;

let rec distinct _A = function [] -> true
                      | x :: xs -> not (member _A xs x) && distinct _A xs;;

let ki64 : nat = nat_of_integer (Z.of_int 65536);;

let rec replicate_tr
  n x acc =
    (if equal_nata n zero_nat then acc
      else replicate_tr (minus_nat n one_nata) x (x :: acc));;

let rec replicate n x = replicate_tr n x [];;

let rec is_none = function Some x -> false
                  | None -> true;;

let rec bind (Seq g) f = Seq (fun _ -> apply f (g ()))
and apply f x1 = match f, x1 with f, Empty -> Empty
            | f, Insert (x, p) -> Join (f x, Join (bind p f, Empty))
            | f, Join (p, xq) -> Join (bind p f, apply f xq);;

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

let rec l_min (Limit_t_ext (l_min, l_max, more)) = l_min;;

let rec rep_uint8a (Abs_uint8 x) = x;;

let rec and_uint8
  p q = Abs_uint8
          (and_word (len_bit0 (len_bit0 (len_bit0 len_num1))) (rep_uint8a p)
            (rep_uint8a q));;

let rec bit_uint8
  w n = less_nat n (nat_of_integer (Z.of_int 8)) &&
          uint8_test_bit w (integer_of_nat n)
and uint8_test_bit
  w k = (if Z.lt k Z.zero || Z.leq (Z.of_int 8) k
          then failwith "undefined" bit_uint8 w k
          else bit_word (len_bit0 (len_bit0 (len_bit0 len_num1))) (rep_uint8a w)
                 (nat_of_integer k));;

let rec rep_uint8
  x = set_bits_word (len_bit0 (len_bit0 (len_bit0 len_num1))) (bit_uint8 x);;

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

let rec isabelle_byte_to_ocaml_char n = LibAux.char_of_z (integer_of_uint8 n);;

let rec nat_to_ocaml_int x = Z.to_int (integer_of_nat x);;

let zero_uint8 : uint8
  = Abs_uint8 (zero_worda (len_bit0 (len_bit0 (len_bit0 len_num1))));;

let zero_byte : uint8 = zero_uint8;;

let rec mem_rep_mk
  x = Pbytes.make  (nat_to_ocaml_int (times_nata x ki64))
        (isabelle_byte_to_ocaml_char zero_byte);;

let rec mem_mk lim = (lim, mem_rep_mk (l_min lim));;

let rec msbyte bs = last bs;;

let rec mems (S_ext (funcs, tabs, mems, globs, elems, datas, more)) = mems;;

let rec tabs (S_ext (funcs, tabs, mems, globs, elems, datas, more)) = tabs;;

let rec list_update
  x0 i y = match x0, i, y with [], i, y -> []
    | x :: xs, i, y ->
        (if equal_nata i zero_nat then y :: xs
          else x :: list_update xs (minus_nat i one_nata) y);;

let bot_pred : 'a pred = Seq (fun _ -> Empty);;

let rec single x = Seq (fun _ -> Insert (x, bot_pred));;

let rec dvd (_A1, _A2)
  a b = eq _A1
          (modulo
            _A2.semiring_modulo_trivial_semidom_modulo.semiring_modulo_semiring_modulo_trivial.modulo_semiring_modulo
            b a)
          (zero _A2.algebraic_semidom_semidom_modulo.semidom_divide_algebraic_semidom.semidom_semidom_divide.comm_semiring_1_cancel_semidom.comm_semiring_1_comm_semiring_1_cancel.semiring_1_comm_semiring_1.semiring_0_semiring_1.mult_zero_semiring_0.zero_mult_zero);;

let rec bin_split
  n w = (if equal_nata n zero_nat then (w, zero_inta)
          else (let (w1, w2) =
                  bin_split (minus_nat n one_nata)
                    (divide_inta w (Int_of_integer (Z.of_int 2)))
                  in
                 (w1, plus_inta
                        (of_bool zero_neq_one_int
                          (not (dvd (equal_int, semidom_modulo_int)
                                 (Int_of_integer (Z.of_int 2)) w)))
                        (times_inta (Int_of_integer (Z.of_int 2)) w2))));;

let rec abs_uint8
  x = uint8 (integer_of_int
              (the_int (len_bit0 (len_bit0 (len_bit0 len_num1))) x));;

let empty_frame : unit f_ext
  = F_ext ([], Inst_ext ([], [], [], [], [], [], [], ()), ());;

let rec typeof_vec v = (let ConstVec128 _ = v in T_v128);;

let rec typeof_ref
  v = (match v with ConstNull t_ref -> t_ref | ConstRefFunc _ -> T_func_ref
        | ConstRefExtern _ -> T_ext_ref);;

let rec typeof_num
  v = (match v with ConstInt32 _ -> T_i32 | ConstInt64 _ -> T_i64
        | ConstFloat32 _ -> T_f32 | ConstFloat64 _ -> T_f64);;

let rec typeof
  v = (match v with V_num v_n -> T_num (typeof_num v_n)
        | V_vec v_v -> T_vec (typeof_vec v_v)
        | V_ref v_r -> T_ref (typeof_ref v_r));;

let rec g_val (Global_ext (g_mut, g_val, more)) = g_val;;

let rec g_mut (Global_ext (g_mut, g_val, more)) = g_mut;;

let rec tg_mut (Tg_ext (tg_mut, tg_t, more)) = tg_mut;;

let rec tg_t (Tg_ext (tg_mut, tg_t, more)) = tg_t;;

let rec glob_typing
  g tg =
    equal_muta (tg_mut tg) (g_mut g) && equal_ta (tg_t tg) (typeof (g_val g));;

let rec l_max (Limit_t_ext (l_min, l_max, more)) = l_max;;

let rec mem_max m = l_max (fst m);;

let rec datas (S_ext (funcs, tabs, mems, globs, elems, datas, more)) = datas;;

let rec elems (S_ext (funcs, tabs, mems, globs, elems, datas, more)) = elems;;

let rec funcs (S_ext (funcs, tabs, mems, globs, elems, datas, more)) = funcs;;

let rec globs (S_ext (funcs, tabs, mems, globs, elems, datas, more)) = globs;;

let rec tab_max t = (let (T_tab (limits, _), _) = t in l_max limits);;

let rec signed_take_bit _A
  n a = (let l =
           take_bit _A.semiring_bit_operations_ring_bit_operations (suc n) a in
          (if bit _A.semiring_bit_operations_ring_bit_operations.semiring_bits_semiring_bit_operations
                l n
            then plus _A.ring_parity_ring_bit_operations.comm_ring_1_ring_parity.ring_1_comm_ring_1.neg_numeral_ring_1.numeral_neg_numeral.semigroup_add_numeral.plus_semigroup_add
                   l (push_bit _A.semiring_bit_operations_ring_bit_operations
                       (suc n)
                       (uminus
                         _A.ring_parity_ring_bit_operations.comm_ring_1_ring_parity.ring_1_comm_ring_1.neg_numeral_ring_1.group_add_neg_numeral.uminus_group_add
                         (one _A.ring_parity_ring_bit_operations.comm_ring_1_ring_parity.ring_1_comm_ring_1.neg_numeral_ring_1.numeral_neg_numeral.one_numeral)))
            else l));;

let rec the_signed_int _A
  w = signed_take_bit ring_bit_operations_int
        (minus_nat (len_of _A.len0_len Type) (suc zero_nat)) (the_int _A w);;

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

let rec f_inst (F_ext (f_locs, f_inst, more)) = f_inst;;

let rec f_locs (F_ext (f_locs, f_inst, more)) = f_locs;;

let rec msb_uint8 x = uint8_test_bit x (Z.of_int 7);;

let rec msb_byte x = msb_uint8 x;;

let rec list_all p x1 = match p, x1 with p, [] -> true
                   | p, x :: xs -> p x && list_all p xs;;

let rec nat_of_uint8 x = nat_of_integer (integer_of_uint8 x);;

let rec uint8_of_int i = uint8 (integer_of_int i);;

let rec uint8_of_nat x = comp uint8_of_int int_of_nat x;;

let rec memsa
  (Inst_ext (types, funcs, tabs, mems, globs, elems, datas, more)) = mems;;

let rec tabsa
  (Inst_ext (types, funcs, tabs, mems, globs, elems, datas, more)) = tabs;;

let rec tab_t_lim tt = (let T_tab (lim, _) = tt in lim);;

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

let rec is_ref_type
  t = (match t with T_num _ -> false | T_vec _ -> false | T_ref _ -> true
        | T_bot -> false);;

let rec push (ts, r) t = (t :: ts, r);;

let rec pop
  = function
    ([], r) ->
      (match r with Reach -> None | Unreach -> Some (T_bot, ([], Unreach)))
    | (t :: ts, r) -> Some (t, (ts, r));;

let rec type_update_ref_is_null
  ct = (match pop ct with None -> None
         | Some (t, cta) ->
           (if is_ref_type t || equal_ta t T_bot
             then Some (push cta (T_num T_i32)) else None));;

let rec push_rev_list (tsa, r) ts = (ts @ tsa, r);;

let rec produce ct ts = push_rev_list ct (rev ts);;

let rec t_subtyping t1 t2 = equal_ta t1 T_bot || equal_ta t1 t2;;

let rec pop_expect
  ct t =
    (match pop ct with None -> None
      | Some (ta, cta) -> (if t_subtyping ta t then Some cta else None));;

let rec pop_expect_list
  ct x1 = match ct, x1 with ct, [] -> Some ct
    | ct, t :: ts ->
        (match pop_expect ct t with None -> None
          | Some cta -> pop_expect_list cta ts);;

let rec consume ct ts = pop_expect_list ct (rev ts);;

let rec type_update
  ct cons prods = map_option (fun cta -> produce cta prods) (consume ct cons);;

let rec is_vec_type
  t = (match t with T_num _ -> false | T_vec _ -> true | T_ref _ -> false
        | T_bot -> false);;

let rec is_num_type
  t = (match t with T_num _ -> true | T_vec _ -> false | T_ref _ -> false
        | T_bot -> false);;

let rec type_update_select
  ct x1 = match ct, x1 with
    ct, None ->
      (match pop_expect ct (T_num T_i32) with None -> None
        | Some cta ->
          (match pop cta with None -> None
            | Some (t1, ctb) ->
              (match pop ctb with None -> None
                | Some (t2, ctc) ->
                  (if not ((is_num_type t1 || equal_ta t1 T_bot) &&
                             (is_num_type t2 || equal_ta t2 T_bot) ||
                            (is_vec_type t1 || equal_ta t1 T_bot) &&
                              (is_vec_type t2 || equal_ta t2 T_bot))
                    then None
                    else (if not (equal_ta t1 t2) &&
                               (not (equal_ta t1 T_bot) &&
                                 not (equal_ta t2 T_bot))
                           then None
                           else Some (push ctc
                                       (if equal_ta t1 T_bot then t2
 else t1)))))))
    | ct, Some t -> type_update ct [t; t; T_num T_i32] [t];;

let rec type_update_drop ct = map_option snd (pop ct);;

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

let rec power _A
  a n = (if equal_nata n zero_nat then one _A.one_power
          else times _A.times_power a (power _A a (minus_nat n one_nata)));;

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
      (types_t, func_t, global, elem, data, table, memory, local, label, return,
        refs, more))
    = T_context_ext
        (types_t, func_t, global, elem, data, table, memory, local,
          labela label, return, refs, more);;

let rec equal_sx x0 x1 = match x0, x1 with S, U -> false
                   | U, S -> false
                   | U, U -> true
                   | S, S -> true;;

let rec c_types_agree
  ct ts = (match consume ct ts with None -> false | Some (tsa, _) -> null tsa);;

let rec option_projl x = map_option fst x;;

let rec types_t
  (T_context_ext
    (types_t, func_t, global, elem, data, table, memory, local, label, return,
      refs, more))
    = types_t;;

let rec equal_bool p pa = match p, pa with p, true -> p
                     | p, false -> not p
                     | true, p -> p
                     | false, p -> not p;;

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
    (types_t, func_t, global, elem, data, table, memory, local, label, return,
      refs, more))
    = return;;

let rec memory
  (T_context_ext
    (types_t, func_t, global, elem, data, table, memory, local, label, return,
      refs, more))
    = memory;;

let rec global
  (T_context_ext
    (types_t, func_t, global, elem, data, table, memory, local, label, return,
      refs, more))
    = global;;

let rec func_t
  (T_context_ext
    (types_t, func_t, global, elem, data, table, memory, local, label, return,
      refs, more))
    = func_t;;

let rec table
  (T_context_ext
    (types_t, func_t, global, elem, data, table, memory, local, label, return,
      refs, more))
    = table;;

let rec local
  (T_context_ext
    (types_t, func_t, global, elem, data, table, memory, local, label, return,
      refs, more))
    = local;;

let rec label
  (T_context_ext
    (types_t, func_t, global, elem, data, table, memory, local, label, return,
      refs, more))
    = label;;

let rec refs
  (T_context_ext
    (types_t, func_t, global, elem, data, table, memory, local, label, return,
      refs, more))
    = refs;;

let rec elem
  (T_context_ext
    (types_t, func_t, global, elem, data, table, memory, local, label, return,
      refs, more))
    = elem;;

let rec data
  (T_context_ext
    (types_t, func_t, global, elem, data, table, memory, local, label, return,
      refs, more))
    = data;;

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

let rec tab_t_reftype tt = (let T_tab (_, t) = tt in t);;

let rec is_mut tg = equal_muta (tg_mut tg) T_mut;;

let rec min_t t1 t2 = (if equal_ta t1 t2 then t1 else T_bot);;

let rec min_ts
  ts1 ts2 =
    (if equal_nata (size_list ts1) (size_list ts2)
      then Some (map (fun (a, b) -> min_t a b) (zip ts1 ts2)) else None);;

let rec min_lab_h
  x0 uu ts = match x0, uu, ts with [], uu, ts -> Some ts
    | i :: is, lab_c, ts ->
        (if less_eq_nat (size_list lab_c) i then None
          else (match min_ts (nth lab_c i) ts with None -> None
                 | Some a -> min_lab_h is lab_c a));;

let rec min_lab
  x0 lab_c = match x0, lab_c with [], lab_c -> None
    | i :: is, lab_c ->
        (if less_eq_nat (size_list lab_c) i then None
          else min_lab_h is lab_c (nth lab_c i));;

let rec check
  c es ct =
    (match es with [] -> Some ct
      | e :: esa ->
        (match check_single c e ct with None -> None | Some a -> check c esa a))
and b_e_type_checker
  c es (Tf (tsa, ts)) =
    (match check c es (rev tsa, Reach) with None -> false
      | Some cts -> c_types_agree cts ts)
and check_single
  c x1 ts = match c, x1, ts with
    c, EConstNum v, ts -> type_update ts [] [T_num (typeof_num v)]
    | c, EConstVec v, ts -> type_update ts [] [T_vec (typeof_vec v)]
    | c, Unop (t, op), ts ->
        (if unop_t_num_agree op t then type_update ts [T_num t] [T_num t]
          else None)
    | c, Binop (t, op), ts ->
        (if binop_t_num_agree op t
          then type_update ts [T_num t; T_num t] [T_num t] else None)
    | c, Testop (t, uu), ts ->
        (if is_int_t_num t then type_update ts [T_num t] [T_num T_i32]
          else None)
    | c, Relop (t, op), ts ->
        (if relop_t_num_agree op t
          then type_update ts [T_num t; T_num t] [T_num T_i32] else None)
    | c, Unop_vec op, ts -> type_update ts [T_vec T_v128] [T_vec T_v128]
    | c, Binop_vec op, ts ->
        (if V128Wrapper.binop_vec_wf op
          then type_update ts [T_vec T_v128; T_vec T_v128] [T_vec T_v128]
          else None)
    | c, Ternop_vec op, ts ->
        type_update ts [T_vec T_v128; T_vec T_v128; T_vec T_v128] [T_vec T_v128]
    | c, Test_vec op, ts -> type_update ts [T_vec T_v128] [T_num T_i32]
    | c, Shift_vec op, ts ->
        type_update ts [T_vec T_v128; T_num T_i32] [T_vec T_v128]
    | c, Splat_vec sv, ts ->
        type_update ts [T_num (vec_lane_t sv)] [T_vec T_v128]
    | c, Extract_vec (sv, sx, i), ts ->
        (if less_nat i (vec_num sv) &&
              (equal_sx sx U ||
                less_eq_nat (vec_length sv) (nat_of_integer (Z.of_int 2)))
          then type_update ts [T_vec T_v128] [T_num (vec_lane_t sv)] else None)
    | c, Replace_vec (sv, i), ts ->
        (if less_nat i (vec_num sv)
          then type_update ts [T_vec T_v128; T_num (vec_lane_t sv)]
                 [T_vec T_v128]
          else None)
    | c, Ref_null t, ts -> type_update ts [] [T_ref t]
    | c, Ref_is_null, ts -> type_update_ref_is_null ts
    | c, Ref_func j, ts ->
        (if less_nat j (size_list (func_t c)) && member equal_nat (refs c) j
          then type_update ts [] [T_ref T_func_ref] else None)
    | c, Cvtop (t1, Convert, t2, sat_sx), ts ->
        (if convert_cond t1 t2 sat_sx then type_update ts [T_num t2] [T_num t1]
          else None)
    | c, Cvtop (t1, Reinterpret, t2, sx), ts ->
        (if not (equal_t_num t1 t2) &&
              (equal_nata (t_num_length t1) (t_num_length t2) && is_none sx)
          then type_update ts [T_num t2] [T_num t1] else None)
    | c, Unreachable, ts -> Some ([], Unreach)
    | c, Nop, ts -> Some ts
    | c, Drop, ts -> type_update_drop ts
    | c, Select t_tag, ts -> type_update_select ts t_tag
    | c, Block (tb, es), ts ->
        (match tb_tf_t c tb with None -> None
          | Some (Tf (tn, tm)) ->
            (if b_e_type_checker (label_update (fun _ -> [tm] @ label c) c) es
                  (Tf (tn, tm))
              then type_update ts tn tm else None))
    | c, Loop (tb, es), ts ->
        (match tb_tf_t c tb with None -> None
          | Some (Tf (tn, tm)) ->
            (if b_e_type_checker (label_update (fun _ -> [tn] @ label c) c) es
                  (Tf (tn, tm))
              then type_update ts tn tm else None))
    | c, If (tb, es1, es2), ts ->
        (match tb_tf_t c tb with None -> None
          | Some (Tf (tn, tm)) ->
            (if b_e_type_checker (label_update (fun _ -> [tm] @ label c) c) es1
                  (Tf (tn, tm)) &&
                  b_e_type_checker (label_update (fun _ -> [tm] @ label c) c)
                    es2 (Tf (tn, tm))
              then type_update ts (tn @ [T_num T_i32]) tm else None))
    | c, Br i, ts ->
        (if less_nat i (size_list (label c)) &&
              not (is_none (consume ts (nth (label c) i)))
          then Some ([], Unreach) else None)
    | c, Br_if i, ts ->
        (if less_nat i (size_list (label c))
          then type_update ts (nth (label c) i @ [T_num T_i32])
                 (nth (label c) i)
          else None)
    | c, Br_table (is, i), ts ->
        (match min_lab (is @ [i]) (label c) with None -> None
          | Some tls ->
            (if not (is_none (consume ts (tls @ [T_num T_i32])))
              then Some ([], Unreach) else None))
    | c, Return, ts ->
        (match return c with None -> None
          | Some tls ->
            (if not (is_none (consume ts tls)) then Some ([], Unreach)
              else None))
    | c, Call i, ts ->
        (if less_nat i (size_list (func_t c))
          then (let Tf (a, b) = nth (func_t c) i in type_update ts a b)
          else None)
    | c, Call_indirect (ti, i), ts ->
        (if less_nat i (size_list (types_t c)) &&
              less_nat ti (size_list (table c))
          then (match (nth (types_t c) i, nth (table c) ti)
                 with (Tf (tn, tm), T_tab (_, T_func_ref)) ->
                   type_update ts (tn @ [T_num T_i32]) tm
                 | (Tf (_, _), T_tab (_, T_ext_ref)) -> None)
          else None)
    | c, Local_get i, ts ->
        (if less_nat i (size_list (local c))
          then type_update ts [] [nth (local c) i] else None)
    | c, Local_set i, ts ->
        (if less_nat i (size_list (local c))
          then type_update ts [nth (local c) i] [] else None)
    | c, Local_tee i, ts ->
        (if less_nat i (size_list (local c))
          then type_update ts [nth (local c) i] [nth (local c) i] else None)
    | c, Global_get i, ts ->
        (if less_nat i (size_list (global c))
          then type_update ts [] [tg_t (nth (global c) i)] else None)
    | c, Global_set i, ts ->
        (if less_nat i (size_list (global c)) && is_mut (nth (global c) i)
          then type_update ts [tg_t (nth (global c) i)] [] else None)
    | c, Load (t, tp_sx, a, off), ts ->
        (if less_eq_nat one_nata (size_list (memory c)) &&
              load_store_t_bounds a (option_projl tp_sx) t
          then type_update ts [T_num T_i32] [T_num t] else None)
    | c, Store (t, tp, a, off), ts ->
        (if less_eq_nat one_nata (size_list (memory c)) &&
              load_store_t_bounds a tp t
          then type_update ts [T_num T_i32; T_num t] [] else None)
    | c, Load_vec (lv, a, off), ts ->
        (if less_eq_nat one_nata (size_list (memory c)) &&
              load_vec_t_bounds lv a
          then type_update ts [T_num T_i32] [T_vec T_v128] else None)
    | c, Load_lane_vec (svi, i, a, off), ts ->
        (if less_eq_nat one_nata (size_list (memory c)) &&
              (less_nat i (vec_i_num svi) &&
                less_eq_nat (power power_nat (nat_of_integer (Z.of_int 2)) a)
                  (vec_i_length svi))
          then type_update ts [T_num T_i32; T_vec T_v128] [T_vec T_v128]
          else None)
    | c, Store_vec (sv, a, off), ts ->
        (if less_eq_nat one_nata (size_list (memory c)) &&
              store_vec_t_bounds sv a
          then type_update ts [T_num T_i32; T_vec T_v128] [] else None)
    | c, Memory_size, ts ->
        (if less_eq_nat one_nata (size_list (memory c))
          then type_update ts [] [T_num T_i32] else None)
    | c, Memory_grow, ts ->
        (if less_eq_nat one_nata (size_list (memory c))
          then type_update ts [T_num T_i32] [T_num T_i32] else None)
    | c, Memory_init i, ts ->
        (if less_eq_nat one_nata (size_list (memory c)) &&
              less_nat i (size_list (data c))
          then type_update ts [T_num T_i32; T_num T_i32; T_num T_i32] []
          else None)
    | c, Memory_copy, ts ->
        (if less_eq_nat one_nata (size_list (memory c))
          then type_update ts [T_num T_i32; T_num T_i32; T_num T_i32] []
          else None)
    | c, Memory_fill, ts ->
        (if less_eq_nat one_nata (size_list (memory c))
          then type_update ts [T_num T_i32; T_num T_i32; T_num T_i32] []
          else None)
    | c, Table_set ti, ts ->
        (if less_nat ti (size_list (table c))
          then type_update ts
                 [T_num T_i32; T_ref (tab_t_reftype (nth (table c) ti))] []
          else None)
    | c, Table_get ti, ts ->
        (if less_nat ti (size_list (table c))
          then type_update ts [T_num T_i32]
                 [T_ref (tab_t_reftype (nth (table c) ti))]
          else None)
    | c, Table_size ti, ts ->
        (if less_nat ti (size_list (table c))
          then type_update ts [] [T_num T_i32] else None)
    | c, Table_grow ti, ts ->
        (if less_nat ti (size_list (table c))
          then type_update ts
                 [T_ref (tab_t_reftype (nth (table c) ti)); T_num T_i32]
                 [T_num T_i32]
          else None)
    | c, Table_init (x, y), ts ->
        (if less_nat x (size_list (table c)) &&
              (less_nat y (size_list (elem c)) &&
                equal_t_ref (tab_t_reftype (nth (table c) x)) (nth (elem c) y))
          then type_update ts [T_num T_i32; T_num T_i32; T_num T_i32] []
          else None)
    | c, Table_copy (x, y), ts ->
        (if less_nat x (size_list (table c)) &&
              (less_nat y (size_list (table c)) &&
                equal_t_ref (tab_t_reftype (nth (table c) x))
                  (tab_t_reftype (nth (table c) y)))
          then type_update ts [T_num T_i32; T_num T_i32; T_num T_i32] []
          else None)
    | c, Table_fill x, ts ->
        (if less_nat x (size_list (table c))
          then type_update ts
                 [T_num T_i32; T_ref (tab_t_reftype (nth (table c) x));
                   T_num T_i32]
                 []
          else None)
    | c, Elem_drop x, ts ->
        (if less_nat x (size_list (elem c)) then type_update ts [] [] else None)
    | c, Data_drop x, ts ->
        (if less_nat x (size_list (data c)) then type_update ts [] []
          else None);;

let rec eq_i_i _A
  xa xb =
    bind (single (xa, xb))
      (fun (x, xaa) -> (if eq _A x xaa then single () else bot_pred));;

let rec list_all2
  p xs ys = match p, xs, ys with
    p, x :: xs, y :: ys -> p x y && list_all2 p xs ys
    | p, xs, [] -> null xs
    | p, [], ys -> null ys;;

let rec datasa
  (Inst_ext (types, funcs, tabs, mems, globs, elems, datas, more)) = datas;;

let rec elemsa
  (Inst_ext (types, funcs, tabs, mems, globs, elems, datas, more)) = elems;;

let rec funcsa
  (Inst_ext (types, funcs, tabs, mems, globs, elems, datas, more)) = funcs;;

let rec globsa
  (Inst_ext (types, funcs, tabs, mems, globs, elems, datas, more)) = globs;;

let rec types
  (Inst_ext (types, funcs, tabs, mems, globs, elems, datas, more)) = types;;

let rec divide_nat
  m n = Nat (divide_integer (integer_of_nat m) (integer_of_nat n));;

let rec l_min_update
  l_mina (Limit_t_ext (l_min, l_max, more)) =
    Limit_t_ext (l_mina l_min, l_max, more);;

let rec mem_rep_append
  m x b =
    MemRepWrapper.memRepAppend m (nat_to_ocaml_int x)
      (isabelle_byte_to_ocaml_char b);;

let rec mem_append
  m n b =
    (l_min_update (fun _ -> plus_nat (l_min (fst m)) (divide_nat n ki64))
       (fst m),
      mem_rep_append (snd m) n b);;

let rec ocaml_int_to_nat x = nat_of_integer (Z.of_int x);;

let rec mem_rep_length m = ocaml_int_to_nat (Pbytes.length m);;

let rec mem_length m = mem_rep_length (snd m);;

let rec ocaml_char_to_isabelle_byte n = uint8 (LibAux.z_of_char n);;

let rec mem_rep_read_bytes
  m x y =
    map ocaml_char_to_isabelle_byte
      (MemRepWrapper.memRepReadBytes m (nat_to_ocaml_int x)
        (nat_to_ocaml_int y));;

let rec read_bytes m n l = mem_rep_read_bytes (snd m) n l;;

let rec load
  m n off l =
    (if less_eq_nat (plus_nat (plus_nat n off) l) (mem_length m)
      then Some (read_bytes m (plus_nat n off) l) else None);;

let rec byte_of_nat x = uint8_of_nat x;;

let rec nat_of_byte x = nat_of_uint8 x;;

let rec uminus_word _A a = of_int _A (uminus_inta (the_int _A a));;

let rec uminus_uint8
  p = Abs_uint8
        (uminus_word (len_bit0 (len_bit0 (len_bit0 len_num1))) (rep_uint8a p));;

let one_uint8 : uint8
  = Abs_uint8 (one_worda (len_bit0 (len_bit0 (len_bit0 len_num1))));;

let negone_byte : uint8 = uminus_uint8 one_uint8;;

let rec mem_rep_write_bytes
  m x bs =
    MemRepWrapper.memRepWriteBytes m (nat_to_ocaml_int x)
      (map isabelle_byte_to_ocaml_char bs);;

let rec write_bytes m n bs = (fst m, mem_rep_write_bytes (snd m) n bs);;

let rec takefill
  fill n xs =
    (if equal_nata n zero_nat then []
      else (match xs with [] -> fill :: takefill fill (minus_nat n one_nata) xs
             | y :: ys -> y :: takefill fill (minus_nat n one_nata) ys));;

let rec bytes_takefill x = takefill x;;

let rec store
  m n off bs l =
    (if less_eq_nat (plus_nat (plus_nat n off) l) (mem_length m)
      then Some (write_bytes m (plus_nat n off) (bytes_takefill zero_byte l bs))
      else None);;

let rec tb_tf
  inst tb =
    (match tb with Tbf a -> nth (types inst) a | Tbv None -> Tf ([], [])
      | Tbv (Some t) -> Tf ([], [t]));;

let rec m_mems
  (M_ext
    (m_types, m_funcs, m_tabs, m_mems, m_globs, m_elems, m_datas, m_start,
      m_imports, m_exports, more))
    = m_mems;;

let rec m_tabs
  (M_ext
    (m_types, m_funcs, m_tabs, m_mems, m_globs, m_elems, m_datas, m_start,
      m_imports, m_exports, more))
    = m_tabs;;

let rec stypes i j = nth (types i) j;;

let rec v_to_e
  ve = (match ve with V_num x -> Basic (EConstNum x)
         | V_vec v -> Basic (EConstVec v) | V_ref a -> Ref a);;

let rec typerep_of _A x = typerep _A Type;;

let rec name _A a = (let Typerep (s, _) = typerep_of _A a in s);;

let rec m_datas
  (M_ext
    (m_types, m_funcs, m_tabs, m_mems, m_globs, m_elems, m_datas, m_start,
      m_imports, m_exports, more))
    = m_datas;;

let rec m_elems
  (M_ext
    (m_types, m_funcs, m_tabs, m_mems, m_globs, m_elems, m_datas, m_start,
      m_imports, m_exports, more))
    = m_elems;;

let rec m_funcs
  (M_ext
    (m_types, m_funcs, m_tabs, m_mems, m_globs, m_elems, m_datas, m_start,
      m_imports, m_exports, more))
    = m_funcs;;

let rec m_globs
  (M_ext
    (m_types, m_funcs, m_tabs, m_mems, m_globs, m_elems, m_datas, m_start,
      m_imports, m_exports, more))
    = m_globs;;

let rec m_start
  (M_ext
    (m_types, m_funcs, m_tabs, m_mems, m_globs, m_elems, m_datas, m_start,
      m_imports, m_exports, more))
    = m_start;;

let rec m_types
  (M_ext
    (m_types, m_funcs, m_tabs, m_mems, m_globs, m_elems, m_datas, m_start,
      m_imports, m_exports, more))
    = m_types;;

let rec mems_update
  memsa (S_ext (funcs, tabs, mems, globs, elems, datas, more)) =
    S_ext (funcs, tabs, memsa mems, globs, elems, datas, more);;

let rec tabs_update
  tabsa (S_ext (funcs, tabs, mems, globs, elems, datas, more)) =
    S_ext (funcs, tabsa tabs, mems, globs, elems, datas, more);;

let rec bitzero_vec t = (let T_v128 = t in ConstVec128 V128Wrapper.zero);;

let rec bitzero_ref
  t = (match t with T_func_ref -> ConstNull T_func_ref
        | T_ext_ref -> ConstNull T_ext_ref);;

let rec bitzero_num
  t = (match t with T_i32 -> ConstInt32 zero_i32a
        | T_i64 -> ConstInt64 zero_i64a | T_f32 -> ConstFloat32 F32Wrapper.zero
        | T_f64 -> ConstFloat64 F64Wrapper.zero);;

let rec bitzero
  t = (match t with T_num t_n -> Some (V_num (bitzero_num t_n))
        | T_vec t_v -> Some (V_vec (bitzero_vec t_v))
        | T_ref t_r -> Some (V_ref (bitzero_ref t_r)) | T_bot -> None);;

let rec cl_type
  cl = (match cl with Func_native (_, tf, _, _) -> tf
         | Func_host (tf, _) -> tf);;

let rec n_zeros ts = those (map bitzero ts);;

let rec update_redex_return
  (Redex (v_sa, es, b_es)) v_s = Redex (v_s @ v_sa, es, b_es);;

let rec update_fc_return
  (Frame_context (rdx, lcs, nf, f)) v_s =
    Frame_context (update_redex_return rdx v_s, lcs, nf, f);;

let res_crash_fuel : res = RCrash (Error_invariant "fuel exhausted");;

let rec split_v_s_b_s_aux
  v_s x1 = match v_s, x1 with
    v_s, EConstNum n :: b_es -> split_v_s_b_s_aux (V_num n :: v_s) b_es
    | v_s, EConstVec v :: b_es -> split_v_s_b_s_aux (V_vec v :: v_s) b_es
    | v_s, [] -> (v_s, [])
    | v_s, Unreachable :: va -> (v_s, Unreachable :: va)
    | v_s, Nop :: va -> (v_s, Nop :: va)
    | v_s, Drop :: va -> (v_s, Drop :: va)
    | v_s, Select vb :: va -> (v_s, Select vb :: va)
    | v_s, Block (vb, vc) :: va -> (v_s, Block (vb, vc) :: va)
    | v_s, Loop (vb, vc) :: va -> (v_s, Loop (vb, vc) :: va)
    | v_s, If (vb, vc, vd) :: va -> (v_s, If (vb, vc, vd) :: va)
    | v_s, Br vb :: va -> (v_s, Br vb :: va)
    | v_s, Br_if vb :: va -> (v_s, Br_if vb :: va)
    | v_s, Br_table (vb, vc) :: va -> (v_s, Br_table (vb, vc) :: va)
    | v_s, Return :: va -> (v_s, Return :: va)
    | v_s, Call vb :: va -> (v_s, Call vb :: va)
    | v_s, Call_indirect (vb, vc) :: va -> (v_s, Call_indirect (vb, vc) :: va)
    | v_s, Local_get vb :: va -> (v_s, Local_get vb :: va)
    | v_s, Local_set vb :: va -> (v_s, Local_set vb :: va)
    | v_s, Local_tee vb :: va -> (v_s, Local_tee vb :: va)
    | v_s, Global_get vb :: va -> (v_s, Global_get vb :: va)
    | v_s, Global_set vb :: va -> (v_s, Global_set vb :: va)
    | v_s, Table_get vb :: va -> (v_s, Table_get vb :: va)
    | v_s, Table_set vb :: va -> (v_s, Table_set vb :: va)
    | v_s, Table_size vb :: va -> (v_s, Table_size vb :: va)
    | v_s, Table_grow vb :: va -> (v_s, Table_grow vb :: va)
    | v_s, Load (vb, vc, vd, ve) :: va -> (v_s, Load (vb, vc, vd, ve) :: va)
    | v_s, Store (vb, vc, vd, ve) :: va -> (v_s, Store (vb, vc, vd, ve) :: va)
    | v_s, Load_vec (vb, vc, vd) :: va -> (v_s, Load_vec (vb, vc, vd) :: va)
    | v_s, Load_lane_vec (vb, vc, vd, ve) :: va ->
        (v_s, Load_lane_vec (vb, vc, vd, ve) :: va)
    | v_s, Store_vec (vb, vc, vd) :: va -> (v_s, Store_vec (vb, vc, vd) :: va)
    | v_s, Memory_size :: va -> (v_s, Memory_size :: va)
    | v_s, Memory_grow :: va -> (v_s, Memory_grow :: va)
    | v_s, Memory_init vb :: va -> (v_s, Memory_init vb :: va)
    | v_s, Memory_fill :: va -> (v_s, Memory_fill :: va)
    | v_s, Memory_copy :: va -> (v_s, Memory_copy :: va)
    | v_s, Table_init (vb, vc) :: va -> (v_s, Table_init (vb, vc) :: va)
    | v_s, Table_copy (vb, vc) :: va -> (v_s, Table_copy (vb, vc) :: va)
    | v_s, Table_fill vb :: va -> (v_s, Table_fill vb :: va)
    | v_s, Elem_drop vb :: va -> (v_s, Elem_drop vb :: va)
    | v_s, Data_drop vb :: va -> (v_s, Data_drop vb :: va)
    | v_s, Unop (vb, vc) :: va -> (v_s, Unop (vb, vc) :: va)
    | v_s, Binop (vb, vc) :: va -> (v_s, Binop (vb, vc) :: va)
    | v_s, Testop (vb, vc) :: va -> (v_s, Testop (vb, vc) :: va)
    | v_s, Relop (vb, vc) :: va -> (v_s, Relop (vb, vc) :: va)
    | v_s, Cvtop (vb, vc, vd, ve) :: va -> (v_s, Cvtop (vb, vc, vd, ve) :: va)
    | v_s, Ref_null vb :: va -> (v_s, Ref_null vb :: va)
    | v_s, Ref_is_null :: va -> (v_s, Ref_is_null :: va)
    | v_s, Ref_func vb :: va -> (v_s, Ref_func vb :: va)
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

let rec split_v_s_es_aux
  v_s x1 = match v_s, x1 with
    v_s, Basic (EConstNum n) :: es -> split_v_s_es_aux (V_num n :: v_s) es
    | v_s, Basic (EConstVec v) :: es -> split_v_s_es_aux (V_vec v :: v_s) es
    | v_s, Ref r :: es -> split_v_s_es_aux (V_ref r :: v_s) es
    | v_s, [] -> (v_s, [])
    | v_s, Basic Unreachable :: va -> (v_s, Basic Unreachable :: va)
    | v_s, Basic Nop :: va -> (v_s, Basic Nop :: va)
    | v_s, Basic Drop :: va -> (v_s, Basic Drop :: va)
    | v_s, Basic (Select vc) :: va -> (v_s, Basic (Select vc) :: va)
    | v_s, Basic (Block (vc, vd)) :: va -> (v_s, Basic (Block (vc, vd)) :: va)
    | v_s, Basic (Loop (vc, vd)) :: va -> (v_s, Basic (Loop (vc, vd)) :: va)
    | v_s, Basic (If (vc, vd, ve)) :: va -> (v_s, Basic (If (vc, vd, ve)) :: va)
    | v_s, Basic (Br vc) :: va -> (v_s, Basic (Br vc) :: va)
    | v_s, Basic (Br_if vc) :: va -> (v_s, Basic (Br_if vc) :: va)
    | v_s, Basic (Br_table (vc, vd)) :: va ->
        (v_s, Basic (Br_table (vc, vd)) :: va)
    | v_s, Basic Return :: va -> (v_s, Basic Return :: va)
    | v_s, Basic (Call vc) :: va -> (v_s, Basic (Call vc) :: va)
    | v_s, Basic (Call_indirect (vc, vd)) :: va ->
        (v_s, Basic (Call_indirect (vc, vd)) :: va)
    | v_s, Basic (Local_get vc) :: va -> (v_s, Basic (Local_get vc) :: va)
    | v_s, Basic (Local_set vc) :: va -> (v_s, Basic (Local_set vc) :: va)
    | v_s, Basic (Local_tee vc) :: va -> (v_s, Basic (Local_tee vc) :: va)
    | v_s, Basic (Global_get vc) :: va -> (v_s, Basic (Global_get vc) :: va)
    | v_s, Basic (Global_set vc) :: va -> (v_s, Basic (Global_set vc) :: va)
    | v_s, Basic (Table_get vc) :: va -> (v_s, Basic (Table_get vc) :: va)
    | v_s, Basic (Table_set vc) :: va -> (v_s, Basic (Table_set vc) :: va)
    | v_s, Basic (Table_size vc) :: va -> (v_s, Basic (Table_size vc) :: va)
    | v_s, Basic (Table_grow vc) :: va -> (v_s, Basic (Table_grow vc) :: va)
    | v_s, Basic (Load (vc, vd, ve, vf)) :: va ->
        (v_s, Basic (Load (vc, vd, ve, vf)) :: va)
    | v_s, Basic (Store (vc, vd, ve, vf)) :: va ->
        (v_s, Basic (Store (vc, vd, ve, vf)) :: va)
    | v_s, Basic (Load_vec (vc, vd, ve)) :: va ->
        (v_s, Basic (Load_vec (vc, vd, ve)) :: va)
    | v_s, Basic (Load_lane_vec (vc, vd, ve, vf)) :: va ->
        (v_s, Basic (Load_lane_vec (vc, vd, ve, vf)) :: va)
    | v_s, Basic (Store_vec (vc, vd, ve)) :: va ->
        (v_s, Basic (Store_vec (vc, vd, ve)) :: va)
    | v_s, Basic Memory_size :: va -> (v_s, Basic Memory_size :: va)
    | v_s, Basic Memory_grow :: va -> (v_s, Basic Memory_grow :: va)
    | v_s, Basic (Memory_init vc) :: va -> (v_s, Basic (Memory_init vc) :: va)
    | v_s, Basic Memory_fill :: va -> (v_s, Basic Memory_fill :: va)
    | v_s, Basic Memory_copy :: va -> (v_s, Basic Memory_copy :: va)
    | v_s, Basic (Table_init (vc, vd)) :: va ->
        (v_s, Basic (Table_init (vc, vd)) :: va)
    | v_s, Basic (Table_copy (vc, vd)) :: va ->
        (v_s, Basic (Table_copy (vc, vd)) :: va)
    | v_s, Basic (Table_fill vc) :: va -> (v_s, Basic (Table_fill vc) :: va)
    | v_s, Basic (Elem_drop vc) :: va -> (v_s, Basic (Elem_drop vc) :: va)
    | v_s, Basic (Data_drop vc) :: va -> (v_s, Basic (Data_drop vc) :: va)
    | v_s, Basic (Unop (vc, vd)) :: va -> (v_s, Basic (Unop (vc, vd)) :: va)
    | v_s, Basic (Binop (vc, vd)) :: va -> (v_s, Basic (Binop (vc, vd)) :: va)
    | v_s, Basic (Testop (vc, vd)) :: va -> (v_s, Basic (Testop (vc, vd)) :: va)
    | v_s, Basic (Relop (vc, vd)) :: va -> (v_s, Basic (Relop (vc, vd)) :: va)
    | v_s, Basic (Cvtop (vc, vd, ve, vf)) :: va ->
        (v_s, Basic (Cvtop (vc, vd, ve, vf)) :: va)
    | v_s, Basic (Ref_null vc) :: va -> (v_s, Basic (Ref_null vc) :: va)
    | v_s, Basic Ref_is_null :: va -> (v_s, Basic Ref_is_null :: va)
    | v_s, Basic (Ref_func vc) :: va -> (v_s, Basic (Ref_func vc) :: va)
    | v_s, Basic (Unop_vec vc) :: va -> (v_s, Basic (Unop_vec vc) :: va)
    | v_s, Basic (Binop_vec vc) :: va -> (v_s, Basic (Binop_vec vc) :: va)
    | v_s, Basic (Ternop_vec vc) :: va -> (v_s, Basic (Ternop_vec vc) :: va)
    | v_s, Basic (Test_vec vc) :: va -> (v_s, Basic (Test_vec vc) :: va)
    | v_s, Basic (Shift_vec vc) :: va -> (v_s, Basic (Shift_vec vc) :: va)
    | v_s, Basic (Splat_vec vc) :: va -> (v_s, Basic (Splat_vec vc) :: va)
    | v_s, Basic (Extract_vec (vc, vd, ve)) :: va ->
        (v_s, Basic (Extract_vec (vc, vd, ve)) :: va)
    | v_s, Basic (Replace_vec (vc, vd)) :: va ->
        (v_s, Basic (Replace_vec (vc, vd)) :: va)
    | v_s, Trap :: va -> (v_s, Trap :: va)
    | v_s, Invoke vb :: va -> (v_s, Invoke vb :: va)
    | v_s, Label (vb, vc, vd) :: va -> (v_s, Label (vb, vc, vd) :: va)
    | v_s, Frame (vb, vc, vd) :: va -> (v_s, Frame (vb, vc, vd) :: va);;

let rec split_v_s_es es = split_v_s_es_aux [] es;;

let rec mem_rep_write_i32_of_i64
  m n vi64 =
    Pbytes.set_int32 m (nat_to_ocaml_int n)
      (isabelle_int32_to_ocaml_int32 (wasm_wrap vi64));;

let rec mem_rep_write_i32
  m n vala =
    Pbytes.set_int32 m (nat_to_ocaml_int n)
      (isabelle_int32_to_ocaml_int32 vala);;

let rec mem_rep_write_i32_of_i32 x = mem_rep_write_i32 x;;

let rec mem_rep_write_i16_of_i64
  m n vi64 =
    Pbytes.set_int16 m (nat_to_ocaml_int n)
      (Z.to_int (LibAux.z_of_uint64 (isabelle_int64_to_ocaml_int64 vi64)));;

let rec mem_rep_write_i16_of_i32
  m n vala =
    Pbytes.set_int16 m (nat_to_ocaml_int n)
      (Z.to_int (LibAux.z_of_uint32 (isabelle_int32_to_ocaml_int32 vala)));;

let rec mem_rep_write_i8_of_i64
  m n vi64 =
    Pbytes.set_int8 m (nat_to_ocaml_int n)
      (Z.to_int (LibAux.z_of_uint64 (isabelle_int64_to_ocaml_int64 vi64)));;

let rec mem_rep_write_i8_of_i32
  m n vala =
    Pbytes.set_int8 m (nat_to_ocaml_int n)
      (Z.to_int (LibAux.z_of_uint32 (isabelle_int32_to_ocaml_int32 vala)));;

let rec f64_serialise_isabelle_bytes
  f = map ocaml_char_to_isabelle_byte (ImplWrapper.serialise_f64 f);;

let rec serialise_f64 x = f64_serialise_isabelle_bytes x;;

let rec f32_serialise_isabelle_bytes
  f = map ocaml_char_to_isabelle_byte (ImplWrapper.serialise_f32 f);;

let rec serialise_f32 x = f32_serialise_isabelle_bytes x;;

let rec store_packed_v_numa
  m n off v tp =
    (if less_eq_nat (plus_nat (plus_nat n off) (tp_num_length tp))
          (mem_length m)
      then Some (fst m,
                  (match v
                    with ConstInt32 vala ->
                      (match tp
                        with Tp_i8 ->
                          mem_rep_write_i8_of_i32 (snd m) (plus_nat n off) vala
                        | Tp_i16 ->
                          mem_rep_write_i16_of_i32 (snd m) (plus_nat n off) vala
                        | Tp_i32 ->
                          mem_rep_write_i32_of_i32 (snd m) (plus_nat n off)
                            vala)
                    | ConstInt64 vala ->
                      (match tp
                        with Tp_i8 ->
                          mem_rep_write_i8_of_i64 (snd m) (plus_nat n off) vala
                        | Tp_i16 ->
                          mem_rep_write_i16_of_i64 (snd m) (plus_nat n off) vala
                        | Tp_i32 ->
                          mem_rep_write_i32_of_i64 (snd m) (plus_nat n off)
                            vala)
                    | ConstFloat32 vala ->
                      mem_rep_write_bytes (snd m) (plus_nat n off)
                        (bytes_takefill zero_byte (tp_num_length tp)
                          (serialise_f32 vala))
                    | ConstFloat64 vala ->
                      mem_rep_write_bytes (snd m) (plus_nat n off)
                        (bytes_takefill zero_byte (tp_num_length tp)
                          (serialise_f64 vala))))
      else None);;

let rec store_packed_v_num m n off v tp = store_packed_v_numa m n off v tp;;

let crash_invalid : res_step
  = Res_crash (Error_invalid "type system violation");;

let rec smem_ind i = (match memsa i with [] -> None | n :: _ -> Some n);;

let rec app_s_f_v_s_store_packed
  t tp off ms f v_s =
    (let i = f_inst f in
      (match v_s with [] -> (ms, (v_s, crash_invalid))
        | [V_num _] -> (ms, (v_s, crash_invalid))
        | V_num v :: V_num (ConstInt32 c) :: v_sa ->
          (if equal_t_num (typeof_num v) t
            then (match smem_ind i with None -> (ms, (v_s, crash_invalid))
                   | Some j ->
                     (match
                       store_packed_v_num (nth ms j) (nat_of_int_i32 c) off v tp
                       with None -> (ms, (v_sa, Res_trap "store"))
                       | Some a -> (list_update ms j a, (v_sa, Step_normal))))
            else (ms, (v_s, crash_invalid)))
        | V_num _ :: V_num (ConstInt64 _) :: _ -> (ms, (v_s, crash_invalid))
        | V_num _ :: V_num (ConstFloat32 _) :: _ -> (ms, (v_s, crash_invalid))
        | V_num _ :: V_num (ConstFloat64 _) :: _ -> (ms, (v_s, crash_invalid))
        | V_num _ :: V_vec _ :: _ -> (ms, (v_s, crash_invalid))
        | V_num _ :: V_ref _ :: _ -> (ms, (v_s, crash_invalid))
        | V_vec _ :: _ -> (ms, (v_s, crash_invalid))
        | V_ref _ :: _ -> (ms, (v_s, crash_invalid))));;

let rec mem_rep_write_i64
  m n vi64 =
    Pbytes.set_int64 m (nat_to_ocaml_int n)
      (isabelle_int64_to_ocaml_int64 vi64);;

let rec mem_rep_write_f64
  m n vf64 =
    Pbytes.set_int64 m (nat_to_ocaml_int n)
      (I64Wrapper_convert.reinterpret_of_f64 vf64);;

let rec mem_rep_write_f32
  m n vf32 =
    Pbytes.set_int32 m (nat_to_ocaml_int n)
      (I32Wrapper_convert.reinterpret_of_f32 vf32);;

let rec store_v_numa
  m n off vn =
    (let l = t_num_length (typeof_num vn) in
      (if less_eq_nat (plus_nat (plus_nat n off) l) (mem_length m)
        then (match vn
               with ConstInt32 vala ->
                 Some (fst m, mem_rep_write_i32 (snd m) (plus_nat n off) vala)
               | ConstInt64 vala ->
                 Some (fst m, mem_rep_write_i64 (snd m) (plus_nat n off) vala)
               | ConstFloat32 vala ->
                 Some (fst m, mem_rep_write_f32 (snd m) (plus_nat n off) vala)
               | ConstFloat64 vala ->
                 Some (fst m, mem_rep_write_f64 (snd m) (plus_nat n off) vala))
        else None));;

let rec store_v_num m n off v = store_v_numa m n off v;;

let rec app_s_f_v_s_store
  t off ms f v_s =
    (let i = f_inst f in
      (match v_s with [] -> (ms, (v_s, crash_invalid))
        | [V_num _] -> (ms, (v_s, crash_invalid))
        | V_num v :: V_num (ConstInt32 c) :: v_sa ->
          (if equal_t_num (typeof_num v) t
            then (match smem_ind i with None -> (ms, (v_s, crash_invalid))
                   | Some j ->
                     (match store_v_num (nth ms j) (nat_of_int_i32 c) off v
                       with None -> (ms, (v_sa, Res_trap "store"))
                       | Some a -> (list_update ms j a, (v_sa, Step_normal))))
            else (ms, (v_s, crash_invalid)))
        | V_num _ :: V_num (ConstInt64 _) :: _ -> (ms, (v_s, crash_invalid))
        | V_num _ :: V_num (ConstFloat32 _) :: _ -> (ms, (v_s, crash_invalid))
        | V_num _ :: V_num (ConstFloat64 _) :: _ -> (ms, (v_s, crash_invalid))
        | V_num _ :: V_vec _ :: _ -> (ms, (v_s, crash_invalid))
        | V_num _ :: V_ref _ :: _ -> (ms, (v_s, crash_invalid))
        | V_vec _ :: _ -> (ms, (v_s, crash_invalid))
        | V_ref _ :: _ -> (ms, (v_s, crash_invalid))));;

let rec app_s_f_v_s_store_maybe_packed
  t tp_opt off ms f v_s =
    (match tp_opt with None -> app_s_f_v_s_store t off ms f v_s
      | Some tp -> app_s_f_v_s_store_packed t tp off ms f v_s);;

let rec mem_rep_read_i64_of_u32
  m n = ocaml_int64_to_isabelle_int64
          (I64Wrapper_convert.extend_u_i32
            (Pbytes.get_int32 m (nat_to_ocaml_int n)));;

let rec mem_rep_read_i64_of_u16
  m n = ocaml_int64_to_isabelle_int64
          (I64Wrapper_convert.of_int_s
            (Pbytes.get_uint16 m (nat_to_ocaml_int n)));;

let rec mem_rep_read_i64_of_i32
  m n = ocaml_int64_to_isabelle_int64
          (I64Wrapper_convert.extend_s_i32
            (Pbytes.get_int32 m (nat_to_ocaml_int n)));;

let rec mem_rep_read_i64_of_i16
  m n = ocaml_int64_to_isabelle_int64
          (I64Wrapper_convert.of_int_s
            (Pbytes.get_int16 m (nat_to_ocaml_int n)));;

let rec mem_rep_read_i64_of_u8
  m n = ocaml_int64_to_isabelle_int64
          (I64Wrapper_convert.of_int_s
            (Pbytes.get_uint8 m (nat_to_ocaml_int n)));;

let rec mem_rep_read_i64_of_i8
  m n = ocaml_int64_to_isabelle_int64
          (I64Wrapper_convert.of_int_s
            (Pbytes.get_int8 m (nat_to_ocaml_int n)));;

let rec mem_rep_read_i64_packed
  m n sx tp =
    (match (sx, tp) with (S, Tp_i8) -> mem_rep_read_i64_of_i8 m n
      | (S, Tp_i16) -> mem_rep_read_i64_of_i16 m n
      | (S, Tp_i32) -> mem_rep_read_i64_of_i32 m n
      | (U, Tp_i8) -> mem_rep_read_i64_of_u8 m n
      | (U, Tp_i16) -> mem_rep_read_i64_of_u16 m n
      | (U, Tp_i32) -> mem_rep_read_i64_of_u32 m n);;

let rec mem_rep_read_i32_of_u32
  m n = ocaml_int32_to_isabelle_int32
          (Pbytes.get_int32 m (nat_to_ocaml_int n));;

let rec mem_rep_read_i32_of_u16
  m n = ocaml_int32_to_isabelle_int32
          (I32Wrapper_convert.of_int_s
            (Pbytes.get_uint16 m (nat_to_ocaml_int n)));;

let rec mem_rep_read_i32_of_i32
  m n = ocaml_int32_to_isabelle_int32
          (Pbytes.get_int32 m (nat_to_ocaml_int n));;

let rec mem_rep_read_i32_of_i16
  m n = ocaml_int32_to_isabelle_int32
          (I32Wrapper_convert.of_int_s
            (Pbytes.get_int16 m (nat_to_ocaml_int n)));;

let rec mem_rep_read_i32_of_u8
  m n = ocaml_int32_to_isabelle_int32
          (I32Wrapper_convert.of_int_s
            (Pbytes.get_uint8 m (nat_to_ocaml_int n)));;

let rec mem_rep_read_i32_of_i8
  m n = ocaml_int32_to_isabelle_int32
          (I32Wrapper_convert.of_int_s
            (Pbytes.get_int8 m (nat_to_ocaml_int n)));;

let rec mem_rep_read_i32_packed
  m n sx tp =
    (match (sx, tp) with (S, Tp_i8) -> mem_rep_read_i32_of_i8 m n
      | (S, Tp_i16) -> mem_rep_read_i32_of_i16 m n
      | (S, Tp_i32) -> mem_rep_read_i32_of_i32 m n
      | (U, Tp_i8) -> mem_rep_read_i32_of_u8 m n
      | (U, Tp_i16) -> mem_rep_read_i32_of_u16 m n
      | (U, Tp_i32) -> mem_rep_read_i32_of_u32 m n);;

let rec f64_deserialise_isabelle_bytes
  bs = ImplWrapper.deserialise_f64 (map isabelle_byte_to_ocaml_char bs);;

let rec deserialise_f64 x = f64_deserialise_isabelle_bytes x;;

let rec f32_deserialise_isabelle_bytes
  bs = ImplWrapper.deserialise_f32 (map isabelle_byte_to_ocaml_char bs);;

let rec deserialise_f32 x = f32_deserialise_isabelle_bytes x;;

let rec sign_extend
  sx l bytes =
    (let msb = msb_byte (msbyte bytes) in
     let byte =
       (match sx with S -> (if msb then negone_byte else zero_byte)
         | U -> zero_byte)
       in
      bytes_takefill byte l bytes);;

let rec load_packed_v_numa
  sx m n off t tp =
    (if less_eq_nat (plus_nat (plus_nat n off) (tp_num_length tp))
          (mem_length m)
      then (match t
             with T_i32 ->
               Some (ConstInt32
                      (mem_rep_read_i32_packed (snd m) (plus_nat n off) sx tp))
             | T_i64 ->
               Some (ConstInt64
                      (mem_rep_read_i64_packed (snd m) (plus_nat n off) sx tp))
             | T_f32 ->
               Some (ConstFloat32
                      (deserialise_f32
                        (sign_extend sx (t_num_length T_i32)
                          (mem_rep_read_bytes (snd m) (plus_nat n off)
                            (tp_num_length tp)))))
             | T_f64 ->
               Some (ConstFloat64
                      (deserialise_f64
                        (sign_extend sx (t_num_length T_i64)
                          (mem_rep_read_bytes (snd m) (plus_nat n off)
                            (tp_num_length tp))))))
      else None);;

let rec load_packed_v_num sx m n off t tp = load_packed_v_numa sx m n off t tp;;

let rec app_s_f_v_s_load_packed
  t tp sx off ms f v_s =
    (let i = f_inst f in
      (match v_s with [] -> (v_s, crash_invalid)
        | V_num (ConstInt32 c) :: v_sa ->
          (match smem_ind i with None -> (v_s, crash_invalid)
            | Some j ->
              (match load_packed_v_num sx (nth ms j) (nat_of_int_i32 c) off t tp
                with None -> (v_sa, Res_trap "load")
                | Some a -> (V_num a :: v_sa, Step_normal)))
        | V_num (ConstInt64 _) :: _ -> (v_s, crash_invalid)
        | V_num (ConstFloat32 _) :: _ -> (v_s, crash_invalid)
        | V_num (ConstFloat64 _) :: _ -> (v_s, crash_invalid)
        | V_vec _ :: _ -> (v_s, crash_invalid)
        | V_ref _ :: _ -> (v_s, crash_invalid)));;

let rec mem_rep_read_i64
  m n = ocaml_int64_to_isabelle_int64
          (Pbytes.get_int64 m (nat_to_ocaml_int n));;

let rec mem_rep_read_i32
  m n = ocaml_int32_to_isabelle_int32
          (Pbytes.get_int32 m (nat_to_ocaml_int n));;

let rec mem_rep_read_f64
  m n = I64Wrapper_convert.reinterpret_to_f64
          (Pbytes.get_int64 m (nat_to_ocaml_int n));;

let rec mem_rep_read_f32
  m n = I32Wrapper_convert.reinterpret_to_f32
          (Pbytes.get_int32 m (nat_to_ocaml_int n));;

let rec load_v_numa
  m n off t =
    (let l = t_num_length t in
      (if less_eq_nat (plus_nat (plus_nat n off) l) (mem_length m)
        then (match t
               with T_i32 ->
                 Some (ConstInt32 (mem_rep_read_i32 (snd m) (plus_nat n off)))
               | T_i64 ->
                 Some (ConstInt64 (mem_rep_read_i64 (snd m) (plus_nat n off)))
               | T_f32 ->
                 Some (ConstFloat32 (mem_rep_read_f32 (snd m) (plus_nat n off)))
               | T_f64 ->
                 Some (ConstFloat64
                        (mem_rep_read_f64 (snd m) (plus_nat n off))))
        else None));;

let rec load_v_num m n off t = load_v_numa m n off t;;

let rec app_s_f_v_s_load
  t off ms f v_s =
    (let i = f_inst f in
      (match v_s with [] -> (v_s, crash_invalid)
        | V_num (ConstInt32 c) :: v_sa ->
          (match smem_ind i with None -> (v_s, crash_invalid)
            | Some j ->
              (match load_v_num (nth ms j) (nat_of_int_i32 c) off t
                with None -> (v_sa, Res_trap "load")
                | Some a -> (V_num a :: v_sa, Step_normal)))
        | V_num (ConstInt64 _) :: _ -> (v_s, crash_invalid)
        | V_num (ConstFloat32 _) :: _ -> (v_s, crash_invalid)
        | V_num (ConstFloat64 _) :: _ -> (v_s, crash_invalid)
        | V_vec _ :: _ -> (v_s, crash_invalid)
        | V_ref _ :: _ -> (v_s, crash_invalid)));;

let rec app_s_f_v_s_load_maybe_packed
  t tp_sx off ms f v_s =
    (match tp_sx with None -> app_s_f_v_s_load t off ms f v_s
      | Some (tp, sx) -> app_s_f_v_s_load_packed t tp sx off ms f v_s);;

let rec insert_lane_vec_bs
  len_lane i bs_lane bs_vec =
    take (times_nata i len_lane) bs_vec @
      take len_lane bs_lane @
        drop (times_nata (plus_nat i one_nata) len_lane) bs_vec;;

let rec v128_deserialise_isabelle_bytes
  bs = ImplWrapper.deserialise_v128 (map isabelle_byte_to_ocaml_char bs);;

let rec deserialise_v128 x = v128_deserialise_isabelle_bytes x;;

let rec v128_serialise_isabelle_bytes
  v = map ocaml_char_to_isabelle_byte (ImplWrapper.serialise_v128 v);;

let rec serialise_v128 x = v128_serialise_isabelle_bytes x;;

let rec insert_lane_vec
  svi i bs v =
    (let bs_v = serialise_v128 v in
      deserialise_v128 (insert_lane_vec_bs (vec_i_length svi) i bs bs_v));;

let rec app_s_f_v_s_load_lane_vec
  svi i_n off ms f v_s =
    (let i = f_inst f in
      (match v_s with [] -> (v_s, crash_invalid)
        | V_num _ :: _ -> (v_s, crash_invalid)
        | [V_vec (ConstVec128 _)] -> (v_s, crash_invalid)
        | V_vec (ConstVec128 v) :: V_num (ConstInt32 c) :: v_sa ->
          (match smem_ind i with None -> (v_s, crash_invalid)
            | Some j ->
              (match load (nth ms j) (nat_of_int_i32 c) off (vec_i_length svi)
                with None -> (v_sa, Res_trap "load_lane_vec")
                | Some a ->
                  (V_vec (ConstVec128 (insert_lane_vec svi i_n a v)) :: v_sa,
                    Step_normal)))
        | V_vec (ConstVec128 _) :: V_num (ConstInt64 _) :: _ ->
          (v_s, crash_invalid)
        | V_vec (ConstVec128 _) :: V_num (ConstFloat32 _) :: _ ->
          (v_s, crash_invalid)
        | V_vec (ConstVec128 _) :: V_num (ConstFloat64 _) :: _ ->
          (v_s, crash_invalid)
        | V_vec (ConstVec128 _) :: V_vec _ :: _ -> (v_s, crash_invalid)
        | V_vec (ConstVec128 _) :: V_ref _ :: _ -> (v_s, crash_invalid)
        | V_ref _ :: _ -> (v_s, crash_invalid)));;

let rec tab_cl_ind
  st i j =
    (let stabinst = snd (nth st i) in
      (if less_nat j (size_list stabinst) then Some (nth stabinst j)
        else None));;

let rec app_s_f_v_s_call_indirect
  x y tinsts cls f v_s =
    (let i = f_inst f in
      (match v_s with [] -> (v_s, ([], crash_invalid))
        | V_num (ConstInt32 c) :: v_sa ->
          (if less_nat x (size_list (tabsa i))
            then (match tab_cl_ind tinsts (nth (tabsa i) x) (nat_of_int_i32 c)
                   with None -> (v_sa, ([], Res_trap "call_indirect"))
                   | Some (ConstNull _) ->
                     (v_sa, ([], Res_trap "call_indirect"))
                   | Some (ConstRefFunc a) ->
                     (if equal_tfa (stypes i y) (cl_type (nth cls a))
                       then (v_sa, ([Invoke a], Step_normal))
                       else (v_sa, ([], Res_trap "call_indirect")))
                   | Some (ConstRefExtern _) -> (v_s, ([], crash_invalid)))
            else (v_s, ([], crash_invalid)))
        | V_num (ConstInt64 _) :: _ -> (v_s, ([], crash_invalid))
        | V_num (ConstFloat32 _) :: _ -> (v_s, ([], crash_invalid))
        | V_num (ConstFloat64 _) :: _ -> (v_s, ([], crash_invalid))
        | V_vec _ :: _ -> (v_s, ([], crash_invalid))
        | V_ref _ :: _ -> (v_s, ([], crash_invalid))));;

let rec app_s_f_v_s_memory_init
  x meminsts datainsts f v_s =
    (match v_s with [] -> (v_s, ([], crash_invalid))
      | [V_num (ConstInt32 _)] -> (v_s, ([], crash_invalid))
      | [V_num (ConstInt32 _); V_num (ConstInt32 _)] ->
        (v_s, ([], crash_invalid))
      | V_num (ConstInt32 n) ::
          V_num (ConstInt32 src) :: V_num (ConstInt32 dest) :: v_sa
        -> (match smem_ind (f_inst f) with None -> (v_s, ([], crash_invalid))
             | Some ma ->
               (let ndest = nat_of_int_i32 dest in
                let nsrc = nat_of_int_i32 src in
                let nn = nat_of_int_i32 n in
                let m = nth meminsts ma in
                let da = nth (datasa (f_inst f)) x in
                let dat = nth datainsts da in
                 (if less_nat (size_list dat) (plus_nat nsrc nn) ||
                       less_nat (mem_length m) (plus_nat ndest nn)
                   then (v_sa, ([], Res_trap "memory_init"))
                   else (if equal_nata nn zero_nat
                          then (v_sa, ([], Step_normal))
                          else (let b = nat_of_uint8 (nth dat nsrc) in
                                 (v_sa,
                                   ([Basic (EConstNum
     (ConstInt32 (int_of_nat_i32 ndest)));
                                      Basic
(EConstNum (ConstInt32 (int_of_nat_i32 b)));
                                      Basic
(Store (T_i32, Some Tp_i8, zero_nat, zero_nat));
                                      Basic
(EConstNum (ConstInt32 (int_of_nat_i32 (plus_nat ndest one_nata))));
                                      Basic
(EConstNum (ConstInt32 (int_of_nat_i32 (plus_nat nsrc one_nata))));
                                      Basic
(EConstNum (ConstInt32 (int_of_nat_i32 (minus_nat nn one_nata))));
                                      Basic (Memory_init x)],
                                     Step_normal)))))))
      | V_num (ConstInt32 _) ::
          V_num (ConstInt32 _) :: V_num (ConstInt64 _) :: _
        -> (v_s, ([], crash_invalid))
      | V_num (ConstInt32 _) ::
          V_num (ConstInt32 _) :: V_num (ConstFloat32 _) :: _
        -> (v_s, ([], crash_invalid))
      | V_num (ConstInt32 _) ::
          V_num (ConstInt32 _) :: V_num (ConstFloat64 _) :: _
        -> (v_s, ([], crash_invalid))
      | V_num (ConstInt32 _) :: V_num (ConstInt32 _) :: V_vec _ :: _ ->
        (v_s, ([], crash_invalid))
      | V_num (ConstInt32 _) :: V_num (ConstInt32 _) :: V_ref _ :: _ ->
        (v_s, ([], crash_invalid))
      | V_num (ConstInt32 _) :: V_num (ConstInt64 _) :: _ ->
        (v_s, ([], crash_invalid))
      | V_num (ConstInt32 _) :: V_num (ConstFloat32 _) :: _ ->
        (v_s, ([], crash_invalid))
      | V_num (ConstInt32 _) :: V_num (ConstFloat64 _) :: _ ->
        (v_s, ([], crash_invalid))
      | V_num (ConstInt32 _) :: V_vec _ :: _ -> (v_s, ([], crash_invalid))
      | V_num (ConstInt32 _) :: V_ref _ :: _ -> (v_s, ([], crash_invalid))
      | V_num (ConstInt64 _) :: _ -> (v_s, ([], crash_invalid))
      | V_num (ConstFloat32 _) :: _ -> (v_s, ([], crash_invalid))
      | V_num (ConstFloat64 _) :: _ -> (v_s, ([], crash_invalid))
      | V_vec _ :: _ -> (v_s, ([], crash_invalid))
      | V_ref _ :: _ -> (v_s, ([], crash_invalid)));;

let rec app_s_f_v_s_memory_fill
  meminsts f v_s =
    (match v_s with [] -> (v_s, ([], crash_invalid))
      | [V_num (ConstInt32 _)] -> (v_s, ([], crash_invalid))
      | [V_num (ConstInt32 _); V_num (ConstInt32 _)] ->
        (v_s, ([], crash_invalid))
      | V_num (ConstInt32 n) ::
          V_num (ConstInt32 vala) :: V_num (ConstInt32 dest) :: v_sa
        -> (match smem_ind (f_inst f) with None -> (v_s, ([], crash_invalid))
             | Some ma ->
               (let m = nth meminsts ma in
                let ndest = nat_of_int_i32 dest in
                let nn = nat_of_int_i32 n in
                 (if less_nat (mem_length m) (plus_nat ndest nn)
                   then (v_sa, ([], Res_trap "memory_fill"))
                   else (if equal_nata nn zero_nat
                          then (v_sa, ([], Step_normal))
                          else (v_sa,
                                 ([Basic (EConstNum (ConstInt32 dest));
                                    Basic (EConstNum (ConstInt32 vala));
                                    Basic (Store
    (T_i32, Some Tp_i8, zero_nat, zero_nat));
                                    Basic (EConstNum
    (ConstInt32 (int_of_nat_i32 (plus_nat ndest one_nata))));
                                    Basic (EConstNum (ConstInt32 vala));
                                    Basic (EConstNum
    (ConstInt32 (int_of_nat_i32 (minus_nat nn one_nata))));
                                    Basic Memory_fill],
                                   Step_normal))))))
      | V_num (ConstInt32 _) ::
          V_num (ConstInt32 _) :: V_num (ConstInt64 _) :: _
        -> (v_s, ([], crash_invalid))
      | V_num (ConstInt32 _) ::
          V_num (ConstInt32 _) :: V_num (ConstFloat32 _) :: _
        -> (v_s, ([], crash_invalid))
      | V_num (ConstInt32 _) ::
          V_num (ConstInt32 _) :: V_num (ConstFloat64 _) :: _
        -> (v_s, ([], crash_invalid))
      | V_num (ConstInt32 _) :: V_num (ConstInt32 _) :: V_vec _ :: _ ->
        (v_s, ([], crash_invalid))
      | V_num (ConstInt32 _) :: V_num (ConstInt32 _) :: V_ref _ :: _ ->
        (v_s, ([], crash_invalid))
      | V_num (ConstInt32 _) :: V_num (ConstInt64 _) :: _ ->
        (v_s, ([], crash_invalid))
      | V_num (ConstInt32 _) :: V_num (ConstFloat32 _) :: _ ->
        (v_s, ([], crash_invalid))
      | V_num (ConstInt32 _) :: V_num (ConstFloat64 _) :: _ ->
        (v_s, ([], crash_invalid))
      | V_num (ConstInt32 _) :: V_vec _ :: _ -> (v_s, ([], crash_invalid))
      | V_num (ConstInt32 _) :: V_ref _ :: _ -> (v_s, ([], crash_invalid))
      | V_num (ConstInt64 _) :: _ -> (v_s, ([], crash_invalid))
      | V_num (ConstFloat32 _) :: _ -> (v_s, ([], crash_invalid))
      | V_num (ConstFloat64 _) :: _ -> (v_s, ([], crash_invalid))
      | V_vec _ :: _ -> (v_s, ([], crash_invalid))
      | V_ref _ :: _ -> (v_s, ([], crash_invalid)));;

let rec app_s_f_v_s_memory_copy
  meminsts f v_s =
    (match v_s with [] -> (v_s, ([], crash_invalid))
      | [V_num (ConstInt32 _)] -> (v_s, ([], crash_invalid))
      | [V_num (ConstInt32 _); V_num (ConstInt32 _)] ->
        (v_s, ([], crash_invalid))
      | V_num (ConstInt32 n) ::
          V_num (ConstInt32 src) :: V_num (ConstInt32 dest) :: v_sa
        -> (match smem_ind (f_inst f) with None -> (v_s, ([], crash_invalid))
             | Some ma ->
               (let ndest = nat_of_int_i32 dest in
                let nsrc = nat_of_int_i32 src in
                let nn = nat_of_int_i32 n in
                let m = nth meminsts ma in
                 (if less_nat (mem_length m) (plus_nat nsrc nn) ||
                       less_nat (mem_length m) (plus_nat ndest nn)
                   then (v_sa, ([], Res_trap "memory_copy"))
                   else (if equal_nata nn zero_nat
                          then (v_sa, ([], Step_normal))
                          else (if less_eq_nat ndest nsrc
                                 then (v_sa,
([Basic (EConstNum (ConstInt32 dest)); Basic (EConstNum (ConstInt32 src));
   Basic (Load (T_i32, Some (Tp_i8, U), zero_nat, zero_nat));
   Basic (Store (T_i32, Some Tp_i8, zero_nat, zero_nat));
   Basic (EConstNum (ConstInt32 (int_of_nat_i32 (plus_nat ndest one_nata))));
   Basic (EConstNum (ConstInt32 (int_of_nat_i32 (plus_nat nsrc one_nata))));
   Basic (EConstNum (ConstInt32 (int_of_nat_i32 (minus_nat nn one_nata))));
   Basic Memory_copy],
  Step_normal))
                                 else (v_sa,
([Basic (EConstNum
          (ConstInt32
            (int_of_nat_i32 (plus_nat ndest (minus_nat nn one_nata)))));
   Basic (EConstNum
           (ConstInt32
             (int_of_nat_i32 (plus_nat nsrc (minus_nat nn one_nata)))));
   Basic (Load (T_i32, Some (Tp_i8, U), zero_nat, zero_nat));
   Basic (Store (T_i32, Some Tp_i8, zero_nat, zero_nat));
   Basic (EConstNum (ConstInt32 dest)); Basic (EConstNum (ConstInt32 src));
   Basic (EConstNum (ConstInt32 (int_of_nat_i32 (minus_nat nn one_nata))));
   Basic Memory_copy],
  Step_normal)))))))
      | V_num (ConstInt32 _) ::
          V_num (ConstInt32 _) :: V_num (ConstInt64 _) :: _
        -> (v_s, ([], crash_invalid))
      | V_num (ConstInt32 _) ::
          V_num (ConstInt32 _) :: V_num (ConstFloat32 _) :: _
        -> (v_s, ([], crash_invalid))
      | V_num (ConstInt32 _) ::
          V_num (ConstInt32 _) :: V_num (ConstFloat64 _) :: _
        -> (v_s, ([], crash_invalid))
      | V_num (ConstInt32 _) :: V_num (ConstInt32 _) :: V_vec _ :: _ ->
        (v_s, ([], crash_invalid))
      | V_num (ConstInt32 _) :: V_num (ConstInt32 _) :: V_ref _ :: _ ->
        (v_s, ([], crash_invalid))
      | V_num (ConstInt32 _) :: V_num (ConstInt64 _) :: _ ->
        (v_s, ([], crash_invalid))
      | V_num (ConstInt32 _) :: V_num (ConstFloat32 _) :: _ ->
        (v_s, ([], crash_invalid))
      | V_num (ConstInt32 _) :: V_num (ConstFloat64 _) :: _ ->
        (v_s, ([], crash_invalid))
      | V_num (ConstInt32 _) :: V_vec _ :: _ -> (v_s, ([], crash_invalid))
      | V_num (ConstInt32 _) :: V_ref _ :: _ -> (v_s, ([], crash_invalid))
      | V_num (ConstInt64 _) :: _ -> (v_s, ([], crash_invalid))
      | V_num (ConstFloat32 _) :: _ -> (v_s, ([], crash_invalid))
      | V_num (ConstFloat64 _) :: _ -> (v_s, ([], crash_invalid))
      | V_vec _ :: _ -> (v_s, ([], crash_invalid))
      | V_ref _ :: _ -> (v_s, ([], crash_invalid)));;

let rec stab_ind
  i ti =
    (if less_nat ti (size_list (tabsa i)) then Some (nth (tabsa i) ti)
      else None);;

let rec app_s_f_v_s_table_size
  x tabinsts f v_s =
    (match stab_ind (f_inst f) x with None -> (v_s, crash_invalid)
      | Some a ->
        (V_num (ConstInt32
                 (int_of_nat_i32 (size_list (snd (nth tabinsts a))))) ::
           v_s,
          Step_normal));;

let rec app_s_f_v_s_table_init
  x y tabinsts eleminsts f v_s =
    (match v_s with [] -> (v_s, ([], crash_invalid))
      | [V_num (ConstInt32 _)] -> (v_s, ([], crash_invalid))
      | [V_num (ConstInt32 _); V_num (ConstInt32 _)] ->
        (v_s, ([], crash_invalid))
      | V_num (ConstInt32 n) ::
          V_num (ConstInt32 src) :: V_num (ConstInt32 dest) :: v_sa
        -> (match stab_ind (f_inst f) x with None -> (v_s, ([], crash_invalid))
             | Some ta ->
               (let ndest = nat_of_int_i32 dest in
                let nsrc = nat_of_int_i32 src in
                let nn = nat_of_int_i32 n in
                let tab = nth tabinsts ta in
                let ea = nth (elemsa (f_inst f)) y in
                let el = nth eleminsts ea in
                 (if less_nat (size_list (snd el)) (plus_nat nsrc nn) ||
                       less_nat (size_list (snd tab)) (plus_nat ndest nn)
                   then (v_sa, ([], Res_trap "table_init"))
                   else (if equal_nata nn zero_nat
                          then (v_sa, ([], Step_normal))
                          else (let vala = nth (snd el) nsrc in
                                 (v_sa,
                                   ([Basic (EConstNum (ConstInt32 dest));
                                      v_to_e (V_ref vala); Basic (Table_set x);
                                      Basic
(EConstNum (ConstInt32 (int_of_nat_i32 (plus_nat ndest one_nata))));
                                      Basic
(EConstNum (ConstInt32 (int_of_nat_i32 (plus_nat nsrc one_nata))));
                                      Basic
(EConstNum (ConstInt32 (int_of_nat_i32 (minus_nat nn one_nata))));
                                      Basic (Table_init (x, y))],
                                     Step_normal)))))))
      | V_num (ConstInt32 _) ::
          V_num (ConstInt32 _) :: V_num (ConstInt64 _) :: _
        -> (v_s, ([], crash_invalid))
      | V_num (ConstInt32 _) ::
          V_num (ConstInt32 _) :: V_num (ConstFloat32 _) :: _
        -> (v_s, ([], crash_invalid))
      | V_num (ConstInt32 _) ::
          V_num (ConstInt32 _) :: V_num (ConstFloat64 _) :: _
        -> (v_s, ([], crash_invalid))
      | V_num (ConstInt32 _) :: V_num (ConstInt32 _) :: V_vec _ :: _ ->
        (v_s, ([], crash_invalid))
      | V_num (ConstInt32 _) :: V_num (ConstInt32 _) :: V_ref _ :: _ ->
        (v_s, ([], crash_invalid))
      | V_num (ConstInt32 _) :: V_num (ConstInt64 _) :: _ ->
        (v_s, ([], crash_invalid))
      | V_num (ConstInt32 _) :: V_num (ConstFloat32 _) :: _ ->
        (v_s, ([], crash_invalid))
      | V_num (ConstInt32 _) :: V_num (ConstFloat64 _) :: _ ->
        (v_s, ([], crash_invalid))
      | V_num (ConstInt32 _) :: V_vec _ :: _ -> (v_s, ([], crash_invalid))
      | V_num (ConstInt32 _) :: V_ref _ :: _ -> (v_s, ([], crash_invalid))
      | V_num (ConstInt64 _) :: _ -> (v_s, ([], crash_invalid))
      | V_num (ConstFloat32 _) :: _ -> (v_s, ([], crash_invalid))
      | V_num (ConstFloat64 _) :: _ -> (v_s, ([], crash_invalid))
      | V_vec _ :: _ -> (v_s, ([], crash_invalid))
      | V_ref _ :: _ -> (v_s, ([], crash_invalid)));;

let int32_minus_one : i32 = I32_impl_abs (Int32.neg Int32.one);;

let rec pred_option p x1 = match p, x1 with p, Some a -> p a
                      | p, None -> true;;

let rec grow_tab
  t n vr =
    (let len = plus_nat (size_list (snd t)) n in
     let old_limits = tab_t_lim (fst t) in
     let limits = l_min_update (fun _ -> len) old_limits in
      (if less_nat len
            (power power_nat (nat_of_integer (Z.of_int 2))
              (nat_of_integer (Z.of_int 32))) &&
            pred_option (less_eq_nat len) (tab_max t)
        then Some (T_tab (limits, tab_t_reftype (fst t)),
                    snd t @ replicate n vr)
        else None));;

let rec app_s_f_v_s_table_grow
  ti tabinsts f v_s =
    (match v_s with [] -> (tabinsts, (v_s, crash_invalid))
      | [V_num (ConstInt32 _)] -> (tabinsts, (v_s, crash_invalid))
      | V_num (ConstInt32 _) :: V_num _ :: _ -> (tabinsts, (v_s, crash_invalid))
      | V_num (ConstInt32 _) :: V_vec _ :: _ -> (tabinsts, (v_s, crash_invalid))
      | V_num (ConstInt32 n) :: V_ref vr :: v_sa ->
        (match stab_ind (f_inst f) ti
          with None -> (tabinsts, (v_s, crash_invalid))
          | Some a ->
            (let tab = nth tabinsts a in
             let sz = size_list (snd tab) in
              (match grow_tab tab (nat_of_int_i32 n) vr
                with None ->
                  (tabinsts,
                    (V_num (ConstInt32 int32_minus_one) :: v_sa, Step_normal))
                | Some aa ->
                  (list_update tabinsts a aa,
                    (V_num (ConstInt32 (int_of_nat_i32 sz)) :: v_sa,
                      Step_normal)))))
      | V_num (ConstInt64 _) :: _ -> (tabinsts, (v_s, crash_invalid))
      | V_num (ConstFloat32 _) :: _ -> (tabinsts, (v_s, crash_invalid))
      | V_num (ConstFloat64 _) :: _ -> (tabinsts, (v_s, crash_invalid))
      | V_vec _ :: _ -> (tabinsts, (v_s, crash_invalid))
      | V_ref _ :: _ -> (tabinsts, (v_s, crash_invalid)));;

let rec app_s_f_v_s_table_fill
  x tabinsts f v_s =
    (match v_s with [] -> (v_s, ([], crash_invalid))
      | [V_num (ConstInt32 _)] -> (v_s, ([], crash_invalid))
      | V_num (ConstInt32 _) :: V_num _ :: _ -> (v_s, ([], crash_invalid))
      | V_num (ConstInt32 _) :: V_vec _ :: _ -> (v_s, ([], crash_invalid))
      | [V_num (ConstInt32 _); V_ref _] -> (v_s, ([], crash_invalid))
      | V_num (ConstInt32 n) :: V_ref vr :: V_num (ConstInt32 i) :: v_sa ->
        (match stab_ind (f_inst f) x with None -> (v_s, ([], crash_invalid))
          | Some ta ->
            (let ni = nat_of_int_i32 i in
             let nn = nat_of_int_i32 n in
             let tab = nth tabinsts ta in
              (if less_nat (size_list (snd tab)) (plus_nat ni nn)
                then (v_sa, ([], Res_trap "table_fill"))
                else (if equal_nata nn zero_nat then (v_sa, ([], Step_normal))
                       else (v_sa,
                              ([Basic (EConstNum (ConstInt32 i));
                                 v_to_e (V_ref vr); Basic (Table_set x);
                                 Basic (EConstNum
 (ConstInt32 (int_of_nat_i32 (plus_nat ni one_nata))));
                                 v_to_e (V_ref vr);
                                 Basic (EConstNum
 (ConstInt32 (int_of_nat_i32 (minus_nat nn one_nata))));
                                 Basic (Table_fill x)],
                                Step_normal))))))
      | V_num (ConstInt32 _) :: V_ref _ :: V_num (ConstInt64 _) :: _ ->
        (v_s, ([], crash_invalid))
      | V_num (ConstInt32 _) :: V_ref _ :: V_num (ConstFloat32 _) :: _ ->
        (v_s, ([], crash_invalid))
      | V_num (ConstInt32 _) :: V_ref _ :: V_num (ConstFloat64 _) :: _ ->
        (v_s, ([], crash_invalid))
      | V_num (ConstInt32 _) :: V_ref _ :: V_vec _ :: _ ->
        (v_s, ([], crash_invalid))
      | V_num (ConstInt32 _) :: V_ref _ :: V_ref _ :: _ ->
        (v_s, ([], crash_invalid))
      | V_num (ConstInt64 _) :: _ -> (v_s, ([], crash_invalid))
      | V_num (ConstFloat32 _) :: _ -> (v_s, ([], crash_invalid))
      | V_num (ConstFloat64 _) :: _ -> (v_s, ([], crash_invalid))
      | V_vec _ :: _ -> (v_s, ([], crash_invalid))
      | V_ref _ :: _ -> (v_s, ([], crash_invalid)));;

let rec app_s_f_v_s_table_copy
  x y tabinsts f v_s =
    (match v_s with [] -> (v_s, ([], crash_invalid))
      | [V_num (ConstInt32 _)] -> (v_s, ([], crash_invalid))
      | [V_num (ConstInt32 _); V_num (ConstInt32 _)] ->
        (v_s, ([], crash_invalid))
      | V_num (ConstInt32 n) ::
          V_num (ConstInt32 src) :: V_num (ConstInt32 dest) :: v_sa
        -> (match (stab_ind (f_inst f) x, stab_ind (f_inst f) y)
             with (None, _) -> (v_s, ([], crash_invalid))
             | (Some _, None) -> (v_s, ([], crash_invalid))
             | (Some tax, Some tay) ->
               (let ndest = nat_of_int_i32 dest in
                let nsrc = nat_of_int_i32 src in
                let nn = nat_of_int_i32 n in
                let tabx = nth tabinsts tax in
                let taby = nth tabinsts tay in
                 (if less_nat (size_list (snd tabx)) (plus_nat nsrc nn) ||
                       less_nat (size_list (snd taby)) (plus_nat ndest nn)
                   then (v_sa, ([], Res_trap "table_copy"))
                   else (if equal_nata nn zero_nat
                          then (v_sa, ([], Step_normal))
                          else (if less_eq_nat ndest nsrc
                                 then (v_sa,
([Basic (EConstNum (ConstInt32 dest)); Basic (EConstNum (ConstInt32 src));
   Basic (Table_get y); Basic (Table_set x);
   Basic (EConstNum (ConstInt32 (int_of_nat_i32 (plus_nat ndest one_nata))));
   Basic (EConstNum (ConstInt32 (int_of_nat_i32 (plus_nat nsrc one_nata))));
   Basic (EConstNum (ConstInt32 (int_of_nat_i32 (minus_nat nn one_nata))));
   Basic (Table_copy (x, y))],
  Step_normal))
                                 else (v_sa,
([Basic (EConstNum
          (ConstInt32
            (int_of_nat_i32 (plus_nat ndest (minus_nat nn one_nata)))));
   Basic (EConstNum
           (ConstInt32
             (int_of_nat_i32 (plus_nat nsrc (minus_nat nn one_nata)))));
   Basic (Table_get y); Basic (Table_set x);
   Basic (EConstNum (ConstInt32 dest)); Basic (EConstNum (ConstInt32 src));
   Basic (EConstNum (ConstInt32 (int_of_nat_i32 (minus_nat nn one_nata))));
   Basic (Table_copy (x, y))],
  Step_normal)))))))
      | V_num (ConstInt32 _) ::
          V_num (ConstInt32 _) :: V_num (ConstInt64 _) :: _
        -> (v_s, ([], crash_invalid))
      | V_num (ConstInt32 _) ::
          V_num (ConstInt32 _) :: V_num (ConstFloat32 _) :: _
        -> (v_s, ([], crash_invalid))
      | V_num (ConstInt32 _) ::
          V_num (ConstInt32 _) :: V_num (ConstFloat64 _) :: _
        -> (v_s, ([], crash_invalid))
      | V_num (ConstInt32 _) :: V_num (ConstInt32 _) :: V_vec _ :: _ ->
        (v_s, ([], crash_invalid))
      | V_num (ConstInt32 _) :: V_num (ConstInt32 _) :: V_ref _ :: _ ->
        (v_s, ([], crash_invalid))
      | V_num (ConstInt32 _) :: V_num (ConstInt64 _) :: _ ->
        (v_s, ([], crash_invalid))
      | V_num (ConstInt32 _) :: V_num (ConstFloat32 _) :: _ ->
        (v_s, ([], crash_invalid))
      | V_num (ConstInt32 _) :: V_num (ConstFloat64 _) :: _ ->
        (v_s, ([], crash_invalid))
      | V_num (ConstInt32 _) :: V_vec _ :: _ -> (v_s, ([], crash_invalid))
      | V_num (ConstInt32 _) :: V_ref _ :: _ -> (v_s, ([], crash_invalid))
      | V_num (ConstInt64 _) :: _ -> (v_s, ([], crash_invalid))
      | V_num (ConstFloat32 _) :: _ -> (v_s, ([], crash_invalid))
      | V_num (ConstFloat64 _) :: _ -> (v_s, ([], crash_invalid))
      | V_vec _ :: _ -> (v_s, ([], crash_invalid))
      | V_ref _ :: _ -> (v_s, ([], crash_invalid)));;

let rec g_val_update
  g_vala (Global_ext (g_mut, g_val, more)) =
    Global_ext (g_mut, g_vala g_val, more);;

let rec sglob_ind i j = nth (globsa i) j;;

let rec update_glob
  gs i j v =
    (let k = sglob_ind i j in
      list_update gs k (g_val_update (fun _ -> v) (nth gs k)));;

let rec app_s_f_v_s_global_set
  k gs f v_s =
    (match v_s with [] -> (gs, (v_s, crash_invalid))
      | v1 :: v_sa -> (update_glob gs (f_inst f) k v1, (v_sa, Step_normal)));;

let rec app_s_f_v_s_global_get
  k gs f v_s = (g_val (nth gs (sglob_ind (f_inst f) k)) :: v_s, Step_normal);;

let rec store_tab1
  tab n vr =
    (if less_nat n (size_list (snd tab))
      then Some (fst tab,
                  take n (snd tab) @
                    [vr] @ drop (plus_nat n one_nata) (snd tab))
      else None);;

let rec store_tabs1
  tables ti n vr =
    (match store_tab1 (nth tables ti) n vr with None -> None
      | Some tab ->
        Some (take ti tables @ [tab] @ drop (plus_nat ti one_nata) tables));;

let rec app_s_f_v_s_table_set
  x tabinsts f v_s =
    (let i = f_inst f in
      (match v_s with [] -> (tabinsts, (v_s, crash_invalid))
        | V_num _ :: _ -> (tabinsts, (v_s, crash_invalid))
        | V_vec _ :: _ -> (tabinsts, (v_s, crash_invalid))
        | [V_ref _] -> (tabinsts, (v_s, crash_invalid))
        | V_ref v_r :: V_num (ConstInt32 c) :: v_sa ->
          (match stab_ind i x with None -> (tabinsts, (v_s, crash_invalid))
            | Some a ->
              (match store_tabs1 tabinsts a (nat_of_int_i32 c) v_r
                with None -> (tabinsts, (v_sa, Res_trap "table_set"))
                | Some aa -> (aa, (v_sa, Step_normal))))
        | V_ref _ :: V_num (ConstInt64 _) :: _ ->
          (tabinsts, (v_s, crash_invalid))
        | V_ref _ :: V_num (ConstFloat32 _) :: _ ->
          (tabinsts, (v_s, crash_invalid))
        | V_ref _ :: V_num (ConstFloat64 _) :: _ ->
          (tabinsts, (v_s, crash_invalid))
        | V_ref _ :: V_vec _ :: _ -> (tabinsts, (v_s, crash_invalid))
        | V_ref _ :: V_ref _ :: _ -> (tabinsts, (v_s, crash_invalid))));;

let rec load_tabs1
  tables ti n =
    (if less_nat n (size_list (snd (nth tables ti)))
      then Some (nth (snd (nth tables ti)) n) else None);;

let rec app_s_f_v_s_table_get
  x tabinsts f v_s =
    (let i = f_inst f in
      (match v_s with [] -> (v_s, crash_invalid)
        | V_num (ConstInt32 c) :: v_sa ->
          (match stab_ind i x with None -> (v_s, crash_invalid)
            | Some a ->
              (match load_tabs1 tabinsts a (nat_of_int_i32 c)
                with None -> (v_sa, Res_trap "table_get")
                | Some aa -> (V_ref aa :: v_sa, Step_normal)))
        | V_num (ConstInt64 _) :: _ -> (v_s, crash_invalid)
        | V_num (ConstFloat32 _) :: _ -> (v_s, crash_invalid)
        | V_num (ConstFloat64 _) :: _ -> (v_s, crash_invalid)
        | V_vec _ :: _ -> (v_s, crash_invalid)
        | V_ref _ :: _ -> (v_s, crash_invalid)));;

let rec store_serialise_vec
  svop v =
    (match svop with Store_128 -> serialise_v128 v
      | Store_lane (svi, i) ->
        take (vec_i_length svi)
          (drop (times_nata i (vec_i_length svi)) (serialise_v128 v)));;

let rec app_s_f_v_s_store_vec
  sv off ms f v_s =
    (let i = f_inst f in
      (match v_s with [] -> (ms, (v_s, crash_invalid))
        | V_num _ :: _ -> (ms, (v_s, crash_invalid))
        | [V_vec (ConstVec128 _)] -> (ms, (v_s, crash_invalid))
        | V_vec (ConstVec128 v) :: V_num (ConstInt32 c) :: v_sa ->
          (match smem_ind i with None -> (ms, (v_s, crash_invalid))
            | Some j ->
              (let bs = store_serialise_vec sv v in
                (match store (nth ms j) (nat_of_int_i32 c) off bs (size_list bs)
                  with None -> (ms, (v_sa, Res_trap "store_vec"))
                  | Some a -> (list_update ms j a, (v_sa, Step_normal)))))
        | V_vec (ConstVec128 _) :: V_num (ConstInt64 _) :: _ ->
          (ms, (v_s, crash_invalid))
        | V_vec (ConstVec128 _) :: V_num (ConstFloat32 _) :: _ ->
          (ms, (v_s, crash_invalid))
        | V_vec (ConstVec128 _) :: V_num (ConstFloat64 _) :: _ ->
          (ms, (v_s, crash_invalid))
        | V_vec (ConstVec128 _) :: V_vec _ :: _ -> (ms, (v_s, crash_invalid))
        | V_vec (ConstVec128 _) :: V_ref _ :: _ -> (ms, (v_s, crash_invalid))
        | V_ref _ :: _ -> (ms, (v_s, crash_invalid))));;

let rec mem_size m = divide_nat (mem_length m) ki64;;

let rec app_s_f_v_s_mem_size
  ms f v_s =
    (let i = f_inst f in
      (match smem_ind i with None -> (v_s, crash_invalid)
        | Some j ->
          (V_num (ConstInt32 (int_of_nat_i32 (mem_size (nth ms j)))) :: v_s,
            Step_normal)));;

let rec mem_grow
  m n = (let len = plus_nat (mem_size m) n in
          (if less_eq_nat len
                (power power_nat (nat_of_integer (Z.of_int 2))
                  (nat_of_integer (Z.of_int 16))) &&
                pred_option (less_eq_nat len) (mem_max m)
            then Some (mem_append m (times_nata n ki64) zero_byte) else None));;

let rec app_s_f_v_s_mem_grow
  ms f v_s =
    (let i = f_inst f in
      (match v_s with [] -> (ms, (v_s, crash_invalid))
        | V_num (ConstInt32 c) :: v_sa ->
          (match smem_ind i with None -> (ms, (v_s, crash_invalid))
            | Some j ->
              (let l = mem_size (nth ms j) in
                (match mem_grow (nth ms j) (nat_of_int_i32 c)
                  with None ->
                    (ms, (V_num (ConstInt32 int32_minus_one) :: v_sa,
                           Step_normal))
                  | Some a ->
                    (list_update ms j a,
                      (V_num (ConstInt32 (int_of_nat_i32 l)) :: v_sa,
                        Step_normal)))))
        | V_num (ConstInt64 _) :: _ -> (ms, (v_s, crash_invalid))
        | V_num (ConstFloat32 _) :: _ -> (ms, (v_s, crash_invalid))
        | V_num (ConstFloat64 _) :: _ -> (ms, (v_s, crash_invalid))
        | V_vec _ :: _ -> (ms, (v_s, crash_invalid))
        | V_ref _ :: _ -> (ms, (v_s, crash_invalid))));;

let rec read_bytes_vec
  n len sx m ind =
    (if equal_nata n zero_nat then []
      else sign_extend sx (times_nata len (nat_of_integer (Z.of_int 2)))
             (read_bytes m ind len) @
             read_bytes_vec (minus_nat n one_nata) len sx m
               (plus_nat ind len));;

let rec load_packed_vec
  tp sx m n off =
    (if less_eq_nat
          (plus_nat (plus_nat n off)
            (times_nata (tp_vec_num tp) (tp_vec_length tp)))
          (mem_length m)
      then Some (read_bytes_vec (tp_vec_num tp) (tp_vec_length tp) sx m
                  (plus_nat n off))
      else None);;

let rec load_vec
  lvop m n off =
    (match lvop with Load_128 -> load m n off (t_vec_length T_v128)
      | Load_packed_vec (tp, sx) -> load_packed_vec tp sx m n off
      | Load_32_zero ->
        map_option (bytes_takefill zero_byte (t_vec_length T_v128))
          (load m n off (nat_of_integer (Z.of_int 4)))
      | Load_64_zero ->
        map_option (bytes_takefill zero_byte (t_vec_length T_v128))
          (load m n off (nat_of_integer (Z.of_int 8)))
      | Load_splat svi ->
        map_option (fun bs -> concat (replicate (vec_i_num svi) bs))
          (load m n off (vec_i_length svi)));;

let rec app_s_f_v_s_load_vec
  lv off ms f v_s =
    (let i = f_inst f in
      (match v_s with [] -> (v_s, crash_invalid)
        | V_num (ConstInt32 c) :: v_sa ->
          (match smem_ind i with None -> (v_s, crash_invalid)
            | Some j ->
              (match load_vec lv (nth ms j) (nat_of_int_i32 c) off
                with None -> (v_sa, Res_trap "load_vec")
                | Some a ->
                  (V_vec (ConstVec128 (deserialise_v128 a)) :: v_sa,
                    Step_normal)))
        | V_num (ConstInt64 _) :: _ -> (v_s, crash_invalid)
        | V_num (ConstFloat32 _) :: _ -> (v_s, crash_invalid)
        | V_num (ConstFloat64 _) :: _ -> (v_s, crash_invalid)
        | V_vec _ :: _ -> (v_s, crash_invalid)
        | V_ref _ :: _ -> (v_s, crash_invalid)));;

let rec bits_vec v = (let ConstVec128 a = v in serialise_v128 a);;

let rec bin_rsplit_rev
  n m c =
    (if equal_nata m zero_nat || equal_nata n zero_nat then []
      else (let (a, b) = bin_split n c in
             b :: bin_rsplit_rev n (minus_nat m n) a));;

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

let rec bits_num
  v = (match v with ConstInt32 a -> serialise_i32 a
        | ConstInt64 a -> serialise_i64 a | ConstFloat32 a -> serialise_f32 a
        | ConstFloat64 a -> serialise_f64 a);;

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
      | V_num _ :: V_ref _ :: _ -> (v_s, crash_invalid)
      | V_vec _ :: _ -> (v_s, crash_invalid)
      | V_ref _ :: _ -> (v_s, crash_invalid));;

let rec is_null_ref
  v = (match v with ConstNull _ -> true | ConstRefFunc _ -> false
        | ConstRefExtern _ -> false);;

let rec wasm_bool b = I32_impl_abs (if b then Int32.one else Int32.zero);;

let rec app_v_s_ref_is_null
  v_s = (match v_s with [] -> (v_s, crash_invalid)
          | V_num _ :: _ -> (v_s, crash_invalid)
          | V_vec _ :: _ -> (v_s, crash_invalid)
          | V_ref v_r :: v_sa ->
            (if is_null_ref v_r
              then (V_num (ConstInt32 (wasm_bool true)) :: v_sa, Step_normal)
              else (V_num (ConstInt32 (wasm_bool false)) :: v_sa,
                     Step_normal)));;

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
        (V_num (app_extract_vec sv sx i v1) :: v_sa, Step_normal)
      | V_ref _ :: _ -> (v_s, crash_invalid));;

let rec app_f_v_s_local_set
  k f v_s =
    (let locs = f_locs f in
      (match v_s with [] -> (f, (v_s, crash_invalid))
        | v1 :: v_sa ->
          (if less_nat k (size_list locs)
            then (F_ext (list_update locs k v1, f_inst f, ()),
                   (v_sa, Step_normal))
            else (f, (v_s, crash_invalid)))));;

let rec app_f_v_s_local_get
  k f v_s =
    (let locs = f_locs f in
      (if less_nat k (size_list locs) then (nth locs k :: v_s, Step_normal)
        else (v_s, crash_invalid)));;

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
        (V_vec (app_ternop_vec op v1 v2 v3) :: v_sa, Step_normal)
      | V_vec _ :: V_vec _ :: V_ref _ :: _ -> (v_s, crash_invalid)
      | V_vec _ :: V_ref _ :: _ -> (v_s, crash_invalid)
      | V_ref _ :: _ -> (v_s, crash_invalid));;

let rec app_f_v_s_ref_func
  x f v_s =
    (let fa = nth (funcsa (f_inst f)) x in
      (V_ref (ConstRefFunc fa) :: v_s, Step_normal));;

let rec app_splat_vec
  sv v =
    ConstVec128
      (deserialise_v128
        (concat (replicate (vec_num sv) (take (vec_length sv) (bits_num v)))));;

let rec app_v_s_splat_vec
  sv v_s =
    (match v_s with [] -> (v_s, crash_invalid)
      | V_num v1 :: v_sa -> (V_vec (app_splat_vec sv v1) :: v_sa, Step_normal)
      | V_vec _ :: _ -> (v_s, crash_invalid)
      | V_ref _ :: _ -> (v_s, crash_invalid));;

let rec app_shift_vec_v
  op2 v n = V128Wrapper.shift_vec op2 v (isabelle_int32_to_ocaml_int32 n);;

let rec app_shift_vec
  sop v cn =
    (let ConstVec128 cv = v in ConstVec128 (app_shift_vec_v sop cv cn));;

let rec app_v_s_shift_vec
  op v_s =
    (match v_s with [] -> (v_s, crash_invalid)
      | [V_num (ConstInt32 _)] -> (v_s, crash_invalid)
      | V_num (ConstInt32 _) :: V_num _ :: _ -> (v_s, crash_invalid)
      | V_num (ConstInt32 v2) :: V_vec v1 :: v_sa ->
        (V_vec (app_shift_vec op v1 v2) :: v_sa, Step_normal)
      | V_num (ConstInt32 _) :: V_ref _ :: _ -> (v_s, crash_invalid)
      | V_num (ConstInt64 _) :: _ -> (v_s, crash_invalid)
      | V_num (ConstFloat32 _) :: _ -> (v_s, crash_invalid)
      | V_num (ConstFloat64 _) :: _ -> (v_s, crash_invalid)
      | V_vec _ :: _ -> (v_s, crash_invalid)
      | V_ref _ :: _ -> (v_s, crash_invalid));;

let rec app_v_s_local_tee
  k v_s =
    (match v_s with [] -> (v_s, ([], crash_invalid))
      | v1 :: v_sa ->
        (v1 :: v1 :: v_sa, ([Basic (Local_set k)], Step_normal)));;

let rec app_binop_vec_v x = V128Wrapper.binop_vec x;;

let rec app_binop_vec
  bop v1 v2 =
    (let (ConstVec128 c1, ConstVec128 c2) = (v1, v2) in
      map_option (fun a -> ConstVec128 a) (app_binop_vec_v bop c1 c2));;

let rec app_v_s_binop_vec
  op v_s =
    (match v_s with [] -> (v_s, crash_invalid)
      | V_num _ :: _ -> (v_s, crash_invalid) | [V_vec _] -> (v_s, crash_invalid)
      | V_vec _ :: V_num _ :: _ -> (v_s, crash_invalid)
      | V_vec v2 :: V_vec v1 :: v_sa ->
        (match app_binop_vec op v1 v2 with None -> (v_sa, Res_trap "binop_vec")
          | Some a -> (V_vec a :: v_sa, Step_normal))
      | V_vec _ :: V_ref _ :: _ -> (v_s, crash_invalid)
      | V_ref _ :: _ -> (v_s, crash_invalid));;

let rec app_s_f_elem_drop
  x eleminsts f =
    (let a = nth (elemsa (f_inst f)) x in
      (list_update eleminsts a (fst (nth eleminsts a), []), Step_normal));;

let rec app_s_f_data_drop
  x datainsts f =
    (let a = nth (datasa (f_inst f)) x in
      (list_update datainsts a [], Step_normal));;

let rec app_unop_vec_v x = V128Wrapper.unop_vec x;;

let rec app_unop_vec
  uop v1 = (let ConstVec128 c = v1 in ConstVec128 (app_unop_vec_v uop c));;

let rec app_v_s_unop_vec
  op v_s =
    (match v_s with [] -> (v_s, crash_invalid)
      | V_num _ :: _ -> (v_s, crash_invalid)
      | V_vec v1 :: v_sa -> (V_vec (app_unop_vec op v1) :: v_sa, Step_normal)
      | V_ref _ :: _ -> (v_s, crash_invalid));;

let rec app_test_vec_v
  op1 v = ocaml_int32_to_isabelle_int32 (V128Wrapper.test_vec op1 v);;

let rec app_test_vec op v1 = (let ConstVec128 a = v1 in app_test_vec_v op a);;

let rec app_v_s_test_vec
  op v_s =
    (match v_s with [] -> (v_s, crash_invalid)
      | V_num _ :: _ -> (v_s, crash_invalid)
      | V_vec v1 :: v_sa ->
        (V_num (ConstInt32 (app_test_vec op v1)) :: v_sa, Step_normal)
      | V_ref _ :: _ -> (v_s, crash_invalid));;

let rec app_v_s_ref_null t v_s = (V_ref (ConstNull t) :: v_s, Step_normal);;

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
      | V_vec _ :: _ -> (v_s, ([], crash_invalid))
      | V_ref _ :: _ -> (v_s, ([], crash_invalid)));;

let crash_invariant : res_step
  = Res_crash (Error_invariant "interpreter invariant violation");;

let rec update_redex_step
  (Redex (v_sa, es, b_es)) v_s es_cont = Redex (v_s, es_cont @ es, b_es);;

let rec update_fc_step
  (Frame_context (rdx, lcs, nf, f)) v_s es_cont =
    Frame_context (update_redex_step rdx v_s es_cont, lcs, nf, f);;

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

let rec app_v_s_testop
  testop v_s =
    (match v_s with [] -> (v_s, crash_invalid)
      | V_num v1 :: v_sa -> (V_num (app_testop testop v1) :: v_sa, Step_normal)
      | V_vec _ :: _ -> (v_s, crash_invalid)
      | V_ref _ :: _ -> (v_s, crash_invalid));;

let rec select_types_agree
  x0 v1 v2 = match x0, v1, v2 with
    None, v1, v2 -> equal_ta (typeof v1) (typeof v2)
    | Some t, v1, v2 -> equal_ta (typeof v1) t && equal_ta (typeof v2) t;;

let rec app_v_s_select
  t_tag v_s =
    (match v_s with [] -> (v_s, crash_invalid)
      | [V_num (ConstInt32 _)] -> (v_s, crash_invalid)
      | [V_num (ConstInt32 _); _] -> (v_s, crash_invalid)
      | V_num (ConstInt32 c) :: v2 :: v1 :: v_sa ->
        (if select_types_agree t_tag v1 v2
          then (if int_eq_i32 c zero_i32a then (v2 :: v_sa, Step_normal)
                 else (v1 :: v_sa, Step_normal))
          else (v_s, crash_invalid))
      | V_num (ConstInt64 _) :: _ -> (v_s, crash_invalid)
      | V_num (ConstFloat32 _) :: _ -> (v_s, crash_invalid)
      | V_num (ConstFloat64 _) :: _ -> (v_s, crash_invalid)
      | V_vec _ :: _ -> (v_s, crash_invalid)
      | V_ref _ :: _ -> (v_s, crash_invalid));;

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

let rec app_v_s_relop
  relop v_s =
    (match v_s with [] -> (v_s, crash_invalid)
      | [V_num _] -> (v_s, crash_invalid)
      | V_num v2 :: V_num v1 :: v_sa ->
        (V_num (app_relop relop v1 v2) :: v_sa, Step_normal)
      | V_num _ :: V_vec _ :: _ -> (v_s, crash_invalid)
      | V_num _ :: V_ref _ :: _ -> (v_s, crash_invalid)
      | V_vec _ :: _ -> (v_s, crash_invalid)
      | V_ref _ :: _ -> (v_s, crash_invalid));;

let rec wasm_deserialise_num
  bs t =
    (match t with T_i32 -> ConstInt32 (deserialise_i32 bs)
      | T_i64 -> ConstInt64 (deserialise_i64 bs)
      | T_f32 -> ConstFloat32 (deserialise_f32 bs)
      | T_f64 -> ConstFloat64 (deserialise_f64 bs));;

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
      | V_vec _ :: _ -> (v_s, crash_invalid)
      | V_ref _ :: _ -> (v_s, crash_invalid));;

let rec app_v_s_br_if
  k v_s =
    (match v_s with [] -> (v_s, ([], crash_invalid))
      | V_num (ConstInt32 c) :: v_sa ->
        (if int_eq_i32 c zero_i32a then (v_sa, ([], Step_normal))
          else (v_sa, ([Basic (Br k)], Step_normal)))
      | V_num (ConstInt64 _) :: _ -> (v_s, ([], crash_invalid))
      | V_num (ConstFloat32 _) :: _ -> (v_s, ([], crash_invalid))
      | V_num (ConstFloat64 _) :: _ -> (v_s, ([], crash_invalid))
      | V_vec _ :: _ -> (v_s, ([], crash_invalid))
      | V_ref _ :: _ -> (v_s, ([], crash_invalid)));;

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

let rec app_v_s_binop
  binop v_s =
    (match v_s with [] -> (v_s, crash_invalid)
      | [V_num _] -> (v_s, crash_invalid)
      | V_num v2 :: V_num v1 :: v_sa ->
        (match app_binop binop v1 v2
          with None -> (v_sa, Res_trap (name typerep_binop binop))
          | Some a -> (V_num a :: v_sa, Step_normal))
      | V_num _ :: V_vec _ :: _ -> (v_s, crash_invalid)
      | V_num _ :: V_ref _ :: _ -> (v_s, crash_invalid)
      | V_vec _ :: _ -> (v_s, crash_invalid)
      | V_ref _ :: _ -> (v_s, crash_invalid));;

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

let rec app_v_s_unop
  unop v_s =
    (match v_s with [] -> (v_s, crash_invalid)
      | V_num v1 :: v_sa -> (V_num (app_unop unop v1) :: v_sa, Step_normal)
      | V_vec _ :: _ -> (v_s, crash_invalid)
      | V_ref _ :: _ -> (v_s, crash_invalid));;

let rec app_v_s_drop
  v_s = (match v_s with [] -> (v_s, crash_invalid)
          | _ :: v_sa -> (v_sa, Step_normal));;

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
      | V_vec _ :: _ -> (v_s, ([], crash_invalid))
      | V_ref _ :: _ -> (v_s, ([], crash_invalid)));;

let rec sfunc_ind i j = nth (funcsa i) j;;

let rec app_f_call k f = ([Invoke (sfunc_ind (f_inst f) k)], Step_normal);;

let rec split_n
  x0 n = match x0, n with [], n -> ([], [])
    | v :: va, n ->
        (if equal_nata n zero_nat then ([], v :: va)
          else (let (es, a) = split_n va (minus_nat n one_nata) in
                 (v :: es, a)));;

let rec globs_update
  globsa (S_ext (funcs, tabs, mems, globs, elems, datas, more)) =
    S_ext (funcs, tabs, mems, globsa globs, elems, datas, more);;

let rec elems_update
  elemsa (S_ext (funcs, tabs, mems, globs, elems, datas, more)) =
    S_ext (funcs, tabs, mems, globs, elemsa elems, datas, more);;

let rec datas_update
  datasa (S_ext (funcs, tabs, mems, globs, elems, datas, more)) =
    S_ext (funcs, tabs, mems, globs, elems, datasa datas, more);;

let rec run_step_b_e
  b_e (Config (d, s, fc, fcs)) =
    (let Frame_context (Redex (v_s, es, b_es), lcs, nf, f) = fc in
      (match b_e
        with Unreachable -> (Config (d, s, fc, fcs), Res_trap "unreachable")
        | Nop -> (Config (d, s, fc, fcs), Step_normal)
        | Drop ->
          (let (v_sa, a) = app_v_s_drop v_s in
            (Config (d, s, update_fc_step fc v_sa [], fcs), a))
        | Select t_tag ->
          (let (v_sa, a) = app_v_s_select t_tag v_s in
            (Config (d, s, update_fc_step fc v_sa [], fcs), a))
        | Block (tb, b_ebs) ->
          (if not (null es) then (Config (d, s, fc, fcs), crash_invariant)
            else (let Tf (t1s, t2s) = tb_tf (f_inst f) tb in
                  let n = size_list t1s in
                  let m = size_list t2s in
                   (if less_eq_nat n (size_list v_s)
                     then (let (v_bs, v_sa) = split_n v_s n in
                           let lc = Label_context (v_sa, b_es, m, []) in
                           let fca =
                             Frame_context
                               (Redex (v_bs, [], b_ebs), lc :: lcs, nf, f)
                             in
                            (Config (d, s, fca, fcs), Step_normal))
                     else (Config (d, s, fc, fcs), crash_invalid))))
        | Loop (tb, b_els) ->
          (if not (null es) then (Config (d, s, fc, fcs), crash_invariant)
            else (let Tf (t1s, t2s) = tb_tf (f_inst f) tb in
                  let n = size_list t1s in
                  let _ = size_list t2s in
                   (if less_eq_nat n (size_list v_s)
                     then (let (v_bs, v_sa) = split_n v_s n in
                           let lc =
                             Label_context (v_sa, b_es, n, [Loop (tb, b_els)])
                             in
                           let fca =
                             Frame_context
                               (Redex (v_bs, [], b_els), lc :: lcs, nf, f)
                             in
                            (Config (d, s, fca, fcs), Step_normal))
                     else (Config (d, s, fc, fcs), crash_invalid))))
        | If (tb, es1, es2) ->
          (let (v_sa, (es_cont, a)) = app_v_s_if tb es1 es2 v_s in
            (Config (d, s, update_fc_step fc v_sa es_cont, fcs), a))
        | Br k ->
          (if less_nat k (size_list lcs)
            then (let Label_context (v_ls, b_els, nl, b_ecls) = nth lcs k in
                   (if less_eq_nat nl (size_list v_s)
                     then (let v_sa = take nl v_s in
                           let fca =
                             Frame_context
                               (Redex (v_sa @ v_ls, [], b_ecls @ b_els),
                                 drop (suc k) lcs, nf, f)
                             in
                            (Config (d, s, fca, fcs), Step_normal))
                     else (Config (d, s, fc, fcs), crash_invalid)))
            else (Config (d, s, fc, fcs), crash_invalid))
        | Br_if k ->
          (let (v_sa, (es_cont, a)) = app_v_s_br_if k v_s in
            (Config (d, s, update_fc_step fc v_sa es_cont, fcs), a))
        | Br_table (ks, k) ->
          (let (v_sa, (es_cont, a)) = app_v_s_br_table ks k v_s in
            (Config (d, s, update_fc_step fc v_sa es_cont, fcs), a))
        | Return ->
          (match fcs with [] -> (Config (d, s, fc, fcs), crash_invalid)
            | fca :: fcsa ->
              (if less_eq_nat nf (size_list v_s)
                then (Config
                        (suc d, s, update_fc_return fca (take nf v_s), fcsa),
                       Step_normal)
                else (Config (d, s, fc, fcs), crash_invalid)))
        | Call k ->
          (let (es_cont, a) = app_f_call k f in
            (Config (d, s, update_fc_step fc v_s es_cont, fcs), a))
        | Call_indirect (x, y) ->
          (let (v_sa, (es_cont, a)) =
             app_s_f_v_s_call_indirect x y (tabs s) (funcs s) f v_s in
            (Config (d, s, update_fc_step fc v_sa es_cont, fcs), a))
        | Local_get k ->
          (let (v_sa, a) = app_f_v_s_local_get k f v_s in
            (Config (d, s, update_fc_step fc v_sa [], fcs), a))
        | Local_set k ->
          (let (fa, (v_sa, res)) = app_f_v_s_local_set k f v_s in
           let fca = Frame_context (Redex (v_sa, es, b_es), lcs, nf, fa) in
            (Config (d, s, fca, fcs), res))
        | Local_tee k ->
          (let (v_sa, (es_cont, a)) = app_v_s_local_tee k v_s in
            (Config (d, s, update_fc_step fc v_sa es_cont, fcs), a))
        | Global_get k ->
          (let (v_sa, a) = app_s_f_v_s_global_get k (globs s) f v_s in
            (Config (d, s, update_fc_step fc v_sa [], fcs), a))
        | Global_set k ->
          (let (gs, (v_sa, a)) = app_s_f_v_s_global_set k (globs s) f v_s in
            (Config
               (d, globs_update (fun _ -> gs) s, update_fc_step fc v_sa [],
                 fcs),
              a))
        | Table_get x ->
          (let (v_sa, a) = app_s_f_v_s_table_get x (tabs s) f v_s in
            (Config (d, s, update_fc_step fc v_sa [], fcs), a))
        | Table_set x ->
          (let (tabinsts, (v_sa, a)) = app_s_f_v_s_table_set x (tabs s) f v_s in
            (Config
               (d, tabs_update (fun _ -> tabinsts) s, update_fc_step fc v_sa [],
                 fcs),
              a))
        | Table_size x ->
          (let (v_sa, a) = app_s_f_v_s_table_size x (tabs s) f v_s in
            (Config (d, s, update_fc_step fc v_sa [], fcs), a))
        | Table_grow x ->
          (let (tabinsts, (v_sa, a)) = app_s_f_v_s_table_grow x (tabs s) f v_s
             in
            (Config
               (d, tabs_update (fun _ -> tabinsts) s, update_fc_step fc v_sa [],
                 fcs),
              a))
        | Load (t, tp_sx, _, off) ->
          (let (v_sa, a) =
             app_s_f_v_s_load_maybe_packed t tp_sx off (mems s) f v_s in
            (Config (d, s, update_fc_step fc v_sa [], fcs), a))
        | Store (t, tp, _, off) ->
          (let (ms, (v_sa, a)) =
             app_s_f_v_s_store_maybe_packed t tp off (mems s) f v_s in
            (Config
               (d, mems_update (fun _ -> ms) s, update_fc_step fc v_sa [], fcs),
              a))
        | Load_vec (lv, _, off) ->
          (let (v_sa, a) = app_s_f_v_s_load_vec lv off (mems s) f v_s in
            (Config (d, s, update_fc_step fc v_sa [], fcs), a))
        | Load_lane_vec (svi, i, _, off) ->
          (let (v_sa, a) = app_s_f_v_s_load_lane_vec svi i off (mems s) f v_s in
            (Config (d, s, update_fc_step fc v_sa [], fcs), a))
        | Store_vec (sv, _, off) ->
          (let (ms, (v_sa, a)) = app_s_f_v_s_store_vec sv off (mems s) f v_s in
            (Config
               (d, mems_update (fun _ -> ms) s, update_fc_step fc v_sa [], fcs),
              a))
        | Memory_size ->
          (let (v_sa, a) = app_s_f_v_s_mem_size (mems s) f v_s in
            (Config (d, s, update_fc_step fc v_sa [], fcs), a))
        | Memory_grow ->
          (let (ms, (v_sa, a)) = app_s_f_v_s_mem_grow (mems s) f v_s in
            (Config
               (d, mems_update (fun _ -> ms) s, update_fc_step fc v_sa [], fcs),
              a))
        | Memory_init x ->
          (let (v_sa, (esa, a)) =
             app_s_f_v_s_memory_init x (mems s) (datas s) f v_s in
            (Config (d, s, update_fc_step fc v_sa esa, fcs), a))
        | Memory_fill ->
          (let (v_sa, (esa, a)) = app_s_f_v_s_memory_fill (mems s) f v_s in
            (Config (d, s, update_fc_step fc v_sa esa, fcs), a))
        | Memory_copy ->
          (let (v_sa, (esa, a)) = app_s_f_v_s_memory_copy (mems s) f v_s in
            (Config (d, s, update_fc_step fc v_sa esa, fcs), a))
        | Table_init (x, y) ->
          (let (v_sa, (esa, a)) =
             app_s_f_v_s_table_init x y (tabs s) (elems s) f v_s in
            (Config (d, s, update_fc_step fc v_sa esa, fcs), a))
        | Table_copy (x, y) ->
          (let (v_sa, (esa, a)) = app_s_f_v_s_table_copy x y (tabs s) f v_s in
            (Config (d, s, update_fc_step fc v_sa esa, fcs), a))
        | Table_fill x ->
          (let (v_sa, (esa, a)) = app_s_f_v_s_table_fill x (tabs s) f v_s in
            (Config (d, s, update_fc_step fc v_sa esa, fcs), a))
        | Elem_drop x ->
          (let (eleminsts, a) = app_s_f_elem_drop x (elems s) f in
            (Config (d, elems_update (fun _ -> eleminsts) s, fc, fcs), a))
        | Data_drop x ->
          (let (datainsts, a) = app_s_f_data_drop x (datas s) f in
            (Config (d, datas_update (fun _ -> datainsts) s, fc, fcs), a))
        | EConstNum _ -> (Config (d, s, fc, fcs), crash_invariant)
        | EConstVec _ -> (Config (d, s, fc, fcs), crash_invariant)
        | Unop (_, op) ->
          (let (v_sa, a) = app_v_s_unop op v_s in
            (Config (d, s, update_fc_step fc v_sa [], fcs), a))
        | Binop (_, op) ->
          (let (v_sa, a) = app_v_s_binop op v_s in
            (Config (d, s, update_fc_step fc v_sa [], fcs), a))
        | Testop (_, op) ->
          (let (v_sa, a) = app_v_s_testop op v_s in
            (Config (d, s, update_fc_step fc v_sa [], fcs), a))
        | Relop (_, op) ->
          (let (v_sa, a) = app_v_s_relop op v_s in
            (Config (d, s, update_fc_step fc v_sa [], fcs), a))
        | Cvtop (t2, op, t1, tp_sx) ->
          (let (v_sa, a) = app_v_s_cvtop op t1 t2 tp_sx v_s in
            (Config (d, s, update_fc_step fc v_sa [], fcs), a))
        | Ref_null t ->
          (let (v_sa, a) = app_v_s_ref_null t v_s in
            (Config (d, s, update_fc_step fc v_sa [], fcs), a))
        | Ref_is_null ->
          (let (v_sa, a) = app_v_s_ref_is_null v_s in
            (Config (d, s, update_fc_step fc v_sa [], fcs), a))
        | Ref_func x ->
          (let (v_sa, a) = app_f_v_s_ref_func x f v_s in
            (Config (d, s, update_fc_step fc v_sa [], fcs), a))
        | Unop_vec op ->
          (let (v_sa, a) = app_v_s_unop_vec op v_s in
            (Config (d, s, update_fc_step fc v_sa [], fcs), a))
        | Binop_vec op ->
          (let (v_sa, a) = app_v_s_binop_vec op v_s in
            (Config (d, s, update_fc_step fc v_sa [], fcs), a))
        | Ternop_vec op ->
          (let (v_sa, a) = app_v_s_ternop_vec op v_s in
            (Config (d, s, update_fc_step fc v_sa [], fcs), a))
        | Test_vec op ->
          (let (v_sa, a) = app_v_s_test_vec op v_s in
            (Config (d, s, update_fc_step fc v_sa [], fcs), a))
        | Shift_vec vs ->
          (let (v_sa, a) = app_v_s_shift_vec vs v_s in
            (Config (d, s, update_fc_step fc v_sa [], fcs), a))
        | Splat_vec is ->
          (let (v_sa, a) = app_v_s_splat_vec is v_s in
            (Config (d, s, update_fc_step fc v_sa [], fcs), a))
        | Extract_vec (sv, sx, i) ->
          (let (v_sa, a) = app_v_s_extract_vec sv sx i v_s in
            (Config (d, s, update_fc_step fc v_sa [], fcs), a))
        | Replace_vec (sv, i) ->
          (let (v_sa, a) = app_v_s_replace_vec sv i v_s in
            (Config (d, s, update_fc_step fc v_sa [], fcs), a))));;

let rec rep_host_func (Abs_host_func x) = x;;

let rec host_func_apply_impl s tf h vs = rep_host_func h (s, vs);;

let crash_exhaustion : res_step
  = Res_crash (Error_exhaustion "call stack exhausted");;

let rec run_step_e
  e (Config (d, s, fc, fcs)) =
    (let Frame_context (Redex (v_s, es, b_es), lcs, nf, f) = fc in
      (match e with Basic b_e -> run_step_b_e b_e (Config (d, s, fc, fcs))
        | Trap -> (Config (d, s, fc, fcs), crash_invariant)
        | Invoke i_cl ->
          (match nth (funcs s) i_cl
            with Func_native (i, Tf (t1s, t2s), ts, es_f) ->
              (match n_zeros ts
                with None -> (Config (d, s, fc, fcs), crash_invalid)
                | Some zs ->
                  (if equal_nata d zero_nat
                    then (Config (d, s, fc, fcs), crash_exhaustion)
                    else (let n = size_list t1s in
                          let m = size_list t2s in
                           (if less_eq_nat n (size_list v_s)
                             then (let (v_fs, v_sa) = split_n v_s n in
                                   let fca =
                                     Frame_context
                                       (Redex (v_sa, es, b_es), lcs, nf, f)
                                     in
                                   let ff = F_ext (rev v_fs @ zs, i, ()) in
                                   let lc = Label_context ([], [], m, []) in
                                   let fcf =
                                     Frame_context
                                       (Redex ([], [], es_f), [lc], m, ff)
                                     in
                                    (Config
                                       (minus_nat d one_nata, s, fcf,
 fca :: fcs),
                                      Step_normal))
                             else (Config (d, s, fc, fcs), crash_invalid)))))
            | Func_host (Tf (t1s, t2s), Host_func hf) ->
              (let n = size_list t1s in
               let _ = size_list t2s in
                (if less_eq_nat n (size_list v_s)
                  then (let (v_fs, v_sa) = split_n v_s n in
                         (match
                           host_func_apply_impl s (Tf (t1s, t2s)) hf (rev v_fs)
                           with None ->
                             (Config
                                (d, s,
                                  Frame_context
                                    (Redex (v_sa, es, b_es), lcs, nf, f),
                                  fcs),
                               Res_trap "host_apply")
                           | Some (sa, rvs) ->
                             (if list_all2 (fun t v -> equal_ta (typeof v) t)
                                   t2s rvs
                               then (let fca =
                                       Frame_context
 (Redex (rev rvs @ v_sa, es, b_es), lcs, nf, f)
                                       in
                                      (Config (d, sa, fca, fcs), Step_normal))
                               else (Config (d, sa, fc, fcs), crash_invalid))))
                  else (Config (d, s, fc, fcs), crash_invalid)))
            | Func_host (Tf (_, _), Host_ref _) ->
              (Config (d, s, fc, fcs), crash_invariant))
        | Label (_, _, _) -> (Config (d, s, fc, fcs), crash_invariant)
        | Frame (_, _, _) -> (Config (d, s, fc, fcs), crash_invariant)
        | Ref _ -> (Config (d, s, fc, fcs), crash_invariant)));;

let rec run_iter
  n cfg =
    (if equal_nata n zero_nat then (cfg, res_crash_fuel)
      else (let Config
                  (d, s, Frame_context (Redex (v_s, es, b_es), lcs, nf, f), fcs)
              = cfg in
             (match split_v_s_es es
               with (v_sa, []) ->
                 (let v_sb = v_sa @ v_s in
                   (match b_es
                     with [] ->
                       (match lcs
                         with [] ->
                           (match fcs
                             with [] ->
                               (Config
                                  (d, s,
                                    Frame_context
                                      (Redex (v_sb, [], []), [], nf, f),
                                    []),
                                 RValue v_sb)
                             | fc :: fcsa ->
                               run_iter (minus_nat n one_nata)
                                 (Config
                                   (suc d, s, update_fc_return fc v_sb, fcsa)))
                         | Label_context (v_ls, b_els, _, _) :: lcsa ->
                           (let f_new =
                              Frame_context
                                (Redex (v_sb @ v_ls, [], b_els), lcsa, nf, f)
                              in
                             run_iter (minus_nat n one_nata)
                               (Config (d, s, f_new, fcs))))
                     | a :: lista ->
                       (match split_v_s_b_s (a :: lista)
                         with (v_saa, []) ->
                           run_iter (minus_nat n one_nata)
                             (Config
                               (d, s,
                                 Frame_context
                                   (Redex (v_saa @ v_sb, [], []), lcs, nf, f),
                                 fcs))
                         | (v_saa, b_e :: b_esa) ->
                           (match
                             run_step_b_e b_e
                               (Config
                                 (d, s,
                                   Frame_context
                                     (Redex (v_saa @ v_sb, [], b_esa), lcs, nf,
                                       f),
                                   fcs))
                             with (cfga, Res_crash str) -> (cfga, RCrash str)
                             | (cfga, Res_trap str) -> (cfga, RTrap str)
                             | (cfga, Step_normal) ->
                               run_iter (minus_nat n one_nata) cfga))))
               | (v_sa, e :: esa) ->
                 (let v_sb = v_sa @ v_s in
                   (match
                     run_step_e e
                       (Config
                         (d, s,
                           Frame_context (Redex (v_sb, esa, b_es), lcs, nf, f),
                           fcs))
                     with (cfga, Res_crash str) -> (cfga, RCrash str)
                     | (cfga, Res_trap str) -> (cfga, RTrap str)
                     | (cfga, Step_normal) ->
                       run_iter (minus_nat n one_nata) cfga)))));;

let rec run_v
  n d (s, (f, b_es)) =
    (let (Config (_, sa, _, _), res) =
       run_iter n
         (Config
           (d, s, Frame_context (Redex ([], [], b_es), [], zero_nat, f), []))
       in
      (sa, res));;

let rec const_expr_p
  xa xb =
    sup_pred
      (bind (single (xa, xb))
        (fun a ->
          (match a with (_, Unreachable) -> bot_pred | (_, Nop) -> bot_pred
            | (_, Drop) -> bot_pred | (_, Select _) -> bot_pred
            | (_, Block (_, _)) -> bot_pred | (_, Loop (_, _)) -> bot_pred
            | (_, If (_, _, _)) -> bot_pred | (_, Br _) -> bot_pred
            | (_, Br_if _) -> bot_pred | (_, Br_table (_, _)) -> bot_pred
            | (_, Return) -> bot_pred | (_, Call _) -> bot_pred
            | (_, Call_indirect (_, _)) -> bot_pred
            | (_, Local_get _) -> bot_pred | (_, Local_set _) -> bot_pred
            | (_, Local_tee _) -> bot_pred | (_, Global_get _) -> bot_pred
            | (_, Global_set _) -> bot_pred | (_, Table_get _) -> bot_pred
            | (_, Table_set _) -> bot_pred | (_, Table_size _) -> bot_pred
            | (_, Table_grow _) -> bot_pred | (_, Load (_, _, _, _)) -> bot_pred
            | (_, Store (_, _, _, _)) -> bot_pred
            | (_, Load_vec (_, _, _)) -> bot_pred
            | (_, Load_lane_vec (_, _, _, _)) -> bot_pred
            | (_, Store_vec (_, _, _)) -> bot_pred
            | (_, Memory_size) -> bot_pred | (_, Memory_grow) -> bot_pred
            | (_, Memory_init _) -> bot_pred | (_, Memory_fill) -> bot_pred
            | (_, Memory_copy) -> bot_pred | (_, Table_init (_, _)) -> bot_pred
            | (_, Table_copy (_, _)) -> bot_pred | (_, Table_fill _) -> bot_pred
            | (_, Elem_drop _) -> bot_pred | (_, Data_drop _) -> bot_pred
            | (_, EConstNum _) -> single () | (_, EConstVec _) -> bot_pred
            | (_, Unop (_, _)) -> bot_pred | (_, Binop (_, _)) -> bot_pred
            | (_, Testop (_, _)) -> bot_pred | (_, Relop (_, _)) -> bot_pred
            | (_, Cvtop (_, _, _, _)) -> bot_pred | (_, Ref_null _) -> bot_pred
            | (_, Ref_is_null) -> bot_pred | (_, Ref_func _) -> bot_pred
            | (_, Unop_vec _) -> bot_pred | (_, Binop_vec _) -> bot_pred
            | (_, Ternop_vec _) -> bot_pred | (_, Test_vec _) -> bot_pred
            | (_, Shift_vec _) -> bot_pred | (_, Splat_vec _) -> bot_pred
            | (_, Extract_vec (_, _, _)) -> bot_pred
            | (_, Replace_vec (_, _)) -> bot_pred)))
      (sup_pred
        (bind (single (xa, xb))
          (fun a ->
            (match a with (_, Unreachable) -> bot_pred | (_, Nop) -> bot_pred
              | (_, Drop) -> bot_pred | (_, Select _) -> bot_pred
              | (_, Block (_, _)) -> bot_pred | (_, Loop (_, _)) -> bot_pred
              | (_, If (_, _, _)) -> bot_pred | (_, Br _) -> bot_pred
              | (_, Br_if _) -> bot_pred | (_, Br_table (_, _)) -> bot_pred
              | (_, Return) -> bot_pred | (_, Call _) -> bot_pred
              | (_, Call_indirect (_, _)) -> bot_pred
              | (_, Local_get _) -> bot_pred | (_, Local_set _) -> bot_pred
              | (_, Local_tee _) -> bot_pred | (_, Global_get _) -> bot_pred
              | (_, Global_set _) -> bot_pred | (_, Table_get _) -> bot_pred
              | (_, Table_set _) -> bot_pred | (_, Table_size _) -> bot_pred
              | (_, Table_grow _) -> bot_pred
              | (_, Load (_, _, _, _)) -> bot_pred
              | (_, Store (_, _, _, _)) -> bot_pred
              | (_, Load_vec (_, _, _)) -> bot_pred
              | (_, Load_lane_vec (_, _, _, _)) -> bot_pred
              | (_, Store_vec (_, _, _)) -> bot_pred
              | (_, Memory_size) -> bot_pred | (_, Memory_grow) -> bot_pred
              | (_, Memory_init _) -> bot_pred | (_, Memory_fill) -> bot_pred
              | (_, Memory_copy) -> bot_pred
              | (_, Table_init (_, _)) -> bot_pred
              | (_, Table_copy (_, _)) -> bot_pred
              | (_, Table_fill _) -> bot_pred | (_, Elem_drop _) -> bot_pred
              | (_, Data_drop _) -> bot_pred | (_, EConstNum _) -> bot_pred
              | (_, EConstVec _) -> single () | (_, Unop (_, _)) -> bot_pred
              | (_, Binop (_, _)) -> bot_pred | (_, Testop (_, _)) -> bot_pred
              | (_, Relop (_, _)) -> bot_pred
              | (_, Cvtop (_, _, _, _)) -> bot_pred
              | (_, Ref_null _) -> bot_pred | (_, Ref_is_null) -> bot_pred
              | (_, Ref_func _) -> bot_pred | (_, Unop_vec _) -> bot_pred
              | (_, Binop_vec _) -> bot_pred | (_, Ternop_vec _) -> bot_pred
              | (_, Test_vec _) -> bot_pred | (_, Shift_vec _) -> bot_pred
              | (_, Splat_vec _) -> bot_pred
              | (_, Extract_vec (_, _, _)) -> bot_pred
              | (_, Replace_vec (_, _)) -> bot_pred)))
        (sup_pred
          (bind (single (xa, xb))
            (fun a ->
              (match a with (_, Unreachable) -> bot_pred | (_, Nop) -> bot_pred
                | (_, Drop) -> bot_pred | (_, Select _) -> bot_pred
                | (_, Block (_, _)) -> bot_pred | (_, Loop (_, _)) -> bot_pred
                | (_, If (_, _, _)) -> bot_pred | (_, Br _) -> bot_pred
                | (_, Br_if _) -> bot_pred | (_, Br_table (_, _)) -> bot_pred
                | (_, Return) -> bot_pred | (_, Call _) -> bot_pred
                | (_, Call_indirect (_, _)) -> bot_pred
                | (_, Local_get _) -> bot_pred | (_, Local_set _) -> bot_pred
                | (_, Local_tee _) -> bot_pred | (_, Global_get _) -> bot_pred
                | (_, Global_set _) -> bot_pred | (_, Table_get _) -> bot_pred
                | (_, Table_set _) -> bot_pred | (_, Table_size _) -> bot_pred
                | (_, Table_grow _) -> bot_pred
                | (_, Load (_, _, _, _)) -> bot_pred
                | (_, Store (_, _, _, _)) -> bot_pred
                | (_, Load_vec (_, _, _)) -> bot_pred
                | (_, Load_lane_vec (_, _, _, _)) -> bot_pred
                | (_, Store_vec (_, _, _)) -> bot_pred
                | (_, Memory_size) -> bot_pred | (_, Memory_grow) -> bot_pred
                | (_, Memory_init _) -> bot_pred | (_, Memory_fill) -> bot_pred
                | (_, Memory_copy) -> bot_pred
                | (_, Table_init (_, _)) -> bot_pred
                | (_, Table_copy (_, _)) -> bot_pred
                | (_, Table_fill _) -> bot_pred | (_, Elem_drop _) -> bot_pred
                | (_, Data_drop _) -> bot_pred | (_, EConstNum _) -> bot_pred
                | (_, EConstVec _) -> bot_pred | (_, Unop (_, _)) -> bot_pred
                | (_, Binop (_, _)) -> bot_pred | (_, Testop (_, _)) -> bot_pred
                | (_, Relop (_, _)) -> bot_pred
                | (_, Cvtop (_, _, _, _)) -> bot_pred
                | (_, Ref_null _) -> bot_pred | (_, Ref_is_null) -> bot_pred
                | (_, Ref_func _) -> single () | (_, Unop_vec _) -> bot_pred
                | (_, Binop_vec _) -> bot_pred | (_, Ternop_vec _) -> bot_pred
                | (_, Test_vec _) -> bot_pred | (_, Shift_vec _) -> bot_pred
                | (_, Splat_vec _) -> bot_pred
                | (_, Extract_vec (_, _, _)) -> bot_pred
                | (_, Replace_vec (_, _)) -> bot_pred)))
          (sup_pred
            (bind (single (xa, xb))
              (fun a ->
                (match a with (_, Unreachable) -> bot_pred
                  | (_, Nop) -> bot_pred | (_, Drop) -> bot_pred
                  | (_, Select _) -> bot_pred | (_, Block (_, _)) -> bot_pred
                  | (_, Loop (_, _)) -> bot_pred | (_, If (_, _, _)) -> bot_pred
                  | (_, Br _) -> bot_pred | (_, Br_if _) -> bot_pred
                  | (_, Br_table (_, _)) -> bot_pred | (_, Return) -> bot_pred
                  | (_, Call _) -> bot_pred
                  | (_, Call_indirect (_, _)) -> bot_pred
                  | (_, Local_get _) -> bot_pred | (_, Local_set _) -> bot_pred
                  | (_, Local_tee _) -> bot_pred | (_, Global_get _) -> bot_pred
                  | (_, Global_set _) -> bot_pred | (_, Table_get _) -> bot_pred
                  | (_, Table_set _) -> bot_pred | (_, Table_size _) -> bot_pred
                  | (_, Table_grow _) -> bot_pred
                  | (_, Load (_, _, _, _)) -> bot_pred
                  | (_, Store (_, _, _, _)) -> bot_pred
                  | (_, Load_vec (_, _, _)) -> bot_pred
                  | (_, Load_lane_vec (_, _, _, _)) -> bot_pred
                  | (_, Store_vec (_, _, _)) -> bot_pred
                  | (_, Memory_size) -> bot_pred | (_, Memory_grow) -> bot_pred
                  | (_, Memory_init _) -> bot_pred
                  | (_, Memory_fill) -> bot_pred | (_, Memory_copy) -> bot_pred
                  | (_, Table_init (_, _)) -> bot_pred
                  | (_, Table_copy (_, _)) -> bot_pred
                  | (_, Table_fill _) -> bot_pred | (_, Elem_drop _) -> bot_pred
                  | (_, Data_drop _) -> bot_pred | (_, EConstNum _) -> bot_pred
                  | (_, EConstVec _) -> bot_pred | (_, Unop (_, _)) -> bot_pred
                  | (_, Binop (_, _)) -> bot_pred
                  | (_, Testop (_, _)) -> bot_pred
                  | (_, Relop (_, _)) -> bot_pred
                  | (_, Cvtop (_, _, _, _)) -> bot_pred
                  | (_, Ref_null _) -> single () | (_, Ref_is_null) -> bot_pred
                  | (_, Ref_func _) -> bot_pred | (_, Unop_vec _) -> bot_pred
                  | (_, Binop_vec _) -> bot_pred | (_, Ternop_vec _) -> bot_pred
                  | (_, Test_vec _) -> bot_pred | (_, Shift_vec _) -> bot_pred
                  | (_, Splat_vec _) -> bot_pred
                  | (_, Extract_vec (_, _, _)) -> bot_pred
                  | (_, Replace_vec (_, _)) -> bot_pred)))
            (bind (single (xa, xb))
              (fun a ->
                (match a with (_, Unreachable) -> bot_pred
                  | (_, Nop) -> bot_pred | (_, Drop) -> bot_pred
                  | (_, Select _) -> bot_pred | (_, Block (_, _)) -> bot_pred
                  | (_, Loop (_, _)) -> bot_pred | (_, If (_, _, _)) -> bot_pred
                  | (_, Br _) -> bot_pred | (_, Br_if _) -> bot_pred
                  | (_, Br_table (_, _)) -> bot_pred | (_, Return) -> bot_pred
                  | (_, Call _) -> bot_pred
                  | (_, Call_indirect (_, _)) -> bot_pred
                  | (_, Local_get _) -> bot_pred | (_, Local_set _) -> bot_pred
                  | (_, Local_tee _) -> bot_pred
                  | (c, Global_get k) ->
                    bind (if_pred (less_nat k (size_list (global c))))
                      (fun () ->
                        bind (eq_i_i equal_mut (tg_mut (nth (global c) k))
                               T_immut)
                          (fun () -> single ()))
                  | (_, Global_set _) -> bot_pred | (_, Table_get _) -> bot_pred
                  | (_, Table_set _) -> bot_pred | (_, Table_size _) -> bot_pred
                  | (_, Table_grow _) -> bot_pred
                  | (_, Load (_, _, _, _)) -> bot_pred
                  | (_, Store (_, _, _, _)) -> bot_pred
                  | (_, Load_vec (_, _, _)) -> bot_pred
                  | (_, Load_lane_vec (_, _, _, _)) -> bot_pred
                  | (_, Store_vec (_, _, _)) -> bot_pred
                  | (_, Memory_size) -> bot_pred | (_, Memory_grow) -> bot_pred
                  | (_, Memory_init _) -> bot_pred
                  | (_, Memory_fill) -> bot_pred | (_, Memory_copy) -> bot_pred
                  | (_, Table_init (_, _)) -> bot_pred
                  | (_, Table_copy (_, _)) -> bot_pred
                  | (_, Table_fill _) -> bot_pred | (_, Elem_drop _) -> bot_pred
                  | (_, Data_drop _) -> bot_pred | (_, EConstNum _) -> bot_pred
                  | (_, EConstVec _) -> bot_pred | (_, Unop (_, _)) -> bot_pred
                  | (_, Binop (_, _)) -> bot_pred
                  | (_, Testop (_, _)) -> bot_pred
                  | (_, Relop (_, _)) -> bot_pred
                  | (_, Cvtop (_, _, _, _)) -> bot_pred
                  | (_, Ref_null _) -> bot_pred | (_, Ref_is_null) -> bot_pred
                  | (_, Ref_func _) -> bot_pred | (_, Unop_vec _) -> bot_pred
                  | (_, Binop_vec _) -> bot_pred | (_, Ternop_vec _) -> bot_pred
                  | (_, Test_vec _) -> bot_pred | (_, Shift_vec _) -> bot_pred
                  | (_, Splat_vec _) -> bot_pred
                  | (_, Extract_vec (_, _, _)) -> bot_pred
                  | (_, Replace_vec (_, _)) -> bot_pred))))));;

let rec const_expr x1 x2 = holds (const_expr_p x1 x2);;

let rec min _A a b = (if less_eq _A a b then a else b);;

let rec funcs_update
  funcsa (S_ext (funcs, tabs, mems, globs, elems, datas, more)) =
    S_ext (funcsa funcs, tabs, mems, globs, elems, datas, more);;

let rec m_exports
  (M_ext
    (m_types, m_funcs, m_tabs, m_mems, m_globs, m_elems, m_datas, m_start,
      m_imports, m_exports, more))
    = m_exports;;

let rec m_imports
  (M_ext
    (m_types, m_funcs, m_tabs, m_mems, m_globs, m_elems, m_datas, m_start,
      m_imports, m_exports, more))
    = m_imports;;

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

let rec alloc_Xs
  f s x2 = match f, s, x2 with f, s, [] -> (s, [])
    | f, s, m_X :: m_Xs ->
        (let (sa, i_X) = f s m_X in
         let (sb, i_Xs) = alloc_Xs f sa m_Xs in
          (sb, i_X :: i_Xs));;

let rec d_mode (Module_data_ext (d_init, d_mode, more)) = d_mode;;

let rec d_init (Module_data_ext (d_init, d_mode, more)) = d_init;;

let rec run_data
  m_d i =
    (match d_mode m_d with Dm_passive -> []
      | Dm_active (_, offset) ->
        offset @
          [EConstNum (ConstInt32 zero_i32a);
            EConstNum (ConstInt32 (int_of_nat_i32 (size_list (d_init m_d))));
            Memory_init i; Data_drop i]);;

let rec e_mode (Module_elem_ext (e_type, e_init, e_mode, more)) = e_mode;;

let rec e_init (Module_elem_ext (e_type, e_init, e_mode, more)) = e_init;;

let rec run_elem
  m_e i =
    (match e_mode m_e with Em_passive -> []
      | Em_active (x, offset) ->
        offset @
          [EConstNum (ConstInt32 zero_i32a);
            EConstNum (ConstInt32 (int_of_nat_i32 (size_list (e_init m_e))));
            Table_init (x, i); Elem_drop i]
      | Em_declarative -> [Elem_drop i]);;

let rec limits_compat
  lt1 lt2 =
    less_eq_nat (l_min lt2) (l_min lt1) &&
      pred_option
        (fun lt2_the ->
          (match l_max lt1 with None -> false
            | Some lt1_the -> less_eq_nat lt1_the lt2_the))
        (l_max lt2);;

let rec tab_subtyping
  t1 t2 =
    (let (T_tab (lims1, tr1), T_tab (lims2, tr2)) = (t1, t2) in
      limits_compat lims1 lims2 && equal_t_ref tr1 tr2);;

let rec mem_subtyping t1 t2 = limits_compat t1 t2;;

let rec external_checker
  x xa xb =
    sup_pred
      (bind (single (x, (xa, xb)))
        (fun a ->
          (match a
            with (s, (Ext_func i, Te_func tf)) ->
              bind (if_pred (less_nat i (size_list (funcs s))))
                (fun () ->
                  bind (eq_i_i equal_tf (cl_type (nth (funcs s) i)) tf)
                    (fun () -> single ()))
            | (_, (Ext_func _, Te_tab _)) -> bot_pred
            | (_, (Ext_func _, Te_mem _)) -> bot_pred
            | (_, (Ext_func _, Te_glob _)) -> bot_pred
            | (_, (Ext_tab _, _)) -> bot_pred | (_, (Ext_mem _, _)) -> bot_pred
            | (_, (Ext_glob _, _)) -> bot_pred)))
      (sup_pred
        (bind (single (x, (xa, xb)))
          (fun a ->
            (match a with (_, (Ext_func _, _)) -> bot_pred
              | (_, (Ext_tab _, Te_func _)) -> bot_pred
              | (s, (Ext_tab i, Te_tab tt)) ->
                bind (if_pred (less_nat i (size_list (tabs s))))
                  (fun () ->
                    bind (if_pred (tab_subtyping (fst (nth (tabs s) i)) tt))
                      (fun () -> single ()))
              | (_, (Ext_tab _, Te_mem _)) -> bot_pred
              | (_, (Ext_tab _, Te_glob _)) -> bot_pred
              | (_, (Ext_mem _, _)) -> bot_pred
              | (_, (Ext_glob _, _)) -> bot_pred)))
        (sup_pred
          (bind (single (x, (xa, xb)))
            (fun a ->
              (match a with (_, (Ext_func _, _)) -> bot_pred
                | (_, (Ext_tab _, _)) -> bot_pred
                | (_, (Ext_mem _, Te_func _)) -> bot_pred
                | (_, (Ext_mem _, Te_tab _)) -> bot_pred
                | (s, (Ext_mem i, Te_mem mt)) ->
                  bind (if_pred (less_nat i (size_list (mems s))))
                    (fun () ->
                      bind (if_pred (mem_subtyping (fst (nth (mems s) i)) mt))
                        (fun () -> single ()))
                | (_, (Ext_mem _, Te_glob _)) -> bot_pred
                | (_, (Ext_glob _, _)) -> bot_pred)))
          (bind (single (x, (xa, xb)))
            (fun a ->
              (match a with (_, (Ext_func _, _)) -> bot_pred
                | (_, (Ext_tab _, _)) -> bot_pred
                | (_, (Ext_mem _, _)) -> bot_pred
                | (_, (Ext_glob _, Te_func _)) -> bot_pred
                | (_, (Ext_glob _, Te_tab _)) -> bot_pred
                | (_, (Ext_glob _, Te_mem _)) -> bot_pred
                | (s, (Ext_glob i, Te_glob gt)) ->
                  bind (if_pred (less_nat i (size_list (globs s))))
                    (fun () ->
                      bind (if_pred (glob_typing (nth (globs s) i) gt))
                        (fun () -> single ())))))));;

let rec external_typing x1 x2 x3 = holds (external_checker x1 x2 x3);;

let rec typing x = b_e_type_checker x;;

let rec alloc_mem
  s m_m = (mems_update (fun _ -> mems s @ [mem_mk m_m]) s, size_list (mems s));;

let rec alloc_tab
  s t_t =
    (tabs_update
       (fun _ ->
         tabs s @
           [(t_t, replicate (l_min (tab_t_lim t_t))
                    (ConstNull (tab_t_reftype t_t)))])
       s,
      size_list (tabs s));;

let rec run_datas
  m_ds =
    map (fun a -> Basic a)
      (maps (fun (a, b) -> run_data a b)
        (zip m_ds (upt zero_nat (size_list m_ds))));;

let rec run_elems
  m_es =
    map (fun a -> Basic a)
      (maps (fun (a, b) -> run_elem a b)
        (zip m_es (upt zero_nat (size_list m_es))));;

let rec export_get_v_ext
  inst exp =
    (match exp with Ext_func i -> Ext_func (nth (funcsa inst) i)
      | Ext_tab i -> Ext_tab (nth (tabsa inst) i)
      | Ext_mem i -> Ext_mem (nth (memsa inst) i)
      | Ext_glob i -> Ext_glob (nth (globsa inst) i));;

let rec m_funcs_update
  m_funcsa
    (M_ext
      (m_types, m_funcs, m_tabs, m_mems, m_globs, m_elems, m_datas, m_start,
        m_imports, m_exports, more))
    = M_ext (m_types, m_funcsa m_funcs, m_tabs, m_mems, m_globs, m_elems,
              m_datas, m_start, m_imports, m_exports, more);;

let rec m_start_update
  m_starta
    (M_ext
      (m_types, m_funcs, m_tabs, m_mems, m_globs, m_elems, m_datas, m_start,
        m_imports, m_exports, more))
    = M_ext (m_types, m_funcs, m_tabs, m_mems, m_globs, m_elems, m_datas,
              m_starta m_start, m_imports, m_exports, more);;

let rec alloc_data
  s m_d =
    (datas_update (fun _ -> datas s @ [d_init m_d]) s, size_list (datas s));;

let rec e_type (Module_elem_ext (e_type, e_init, e_mode, more)) = e_type;;

let rec alloc_elem
  s m_el_v_rs =
    (let (m_el, v_rs) = m_el_v_rs in
      (elems_update (fun _ -> elems s @ [(e_type m_el, v_rs)]) s,
        size_list (elems s)));;

let rec alloc_func
  s m_f inst =
    (let (i_t, (loc_ts, b_es)) = m_f in
      (funcs_update
         (fun _ ->
           funcs s @ [Func_native (inst, nth (types inst) i_t, loc_ts, b_es)])
         s,
        size_list (funcs s)));;

let rec g_type (Module_glob_ext (g_type, g_init, more)) = g_type;;

let rec alloc_glob
  s m_g_v =
    (let (m_g, v) = m_g_v in
      (globs_update
         (fun _ -> globs s @ [Global_ext (tg_mut (g_type m_g), v, ())]) s,
        size_list (globs s)));;

let rec run_invoke_v
  n d (s, (vs, i)) =
    (let (Config (_, sa, _, _), res) =
       run_iter n
         (Config
           (d, s,
             Frame_context
               (Redex (rev vs, [Invoke i], []), [], zero_nat, empty_frame),
             []))
       in
      (sa, res));;

let rec run
  x = run_v (power power_nat (nat_of_integer (Z.of_int 2))
              (nat_of_integer (Z.of_int 63)))
        (nat_of_integer (Z.of_int 300)) x;;

let rec module_tab_type_checker_p
  x = bind (single x)
        (fun (T_tab (lims, _)) ->
          bind (limit_type_checker_p lims
                 (minus_nat
                   (power power_nat (nat_of_integer (Z.of_int 2))
                     (nat_of_integer (Z.of_int 32)))
                   one_nata))
            (fun () -> single ()));;

let rec module_tab_typing x1 = holds (module_tab_type_checker_p x1);;

let rec g_init (Module_glob_ext (g_type, g_init, more)) = g_init;;

let rec local_update
  locala
    (T_context_ext
      (types_t, func_t, global, elem, data, table, memory, local, label, return,
        refs, more))
    = T_context_ext
        (types_t, func_t, global, elem, data, table, memory, locala local,
          label, return, refs, more);;

let rec interp_get_v
  s inst b_es =
    (let (_, RValue [v]) =
       run_v (nat_of_integer (Z.of_int 2)) zero_nat
         (s, (F_ext ([], inst, ()), b_es))
       in
      v);;

let rec extract_funcidx_b_e = function Ref_func x -> Some x
                              | Unreachable -> None
                              | Nop -> None
                              | Drop -> None
                              | Select v -> None
                              | Block (v, va) -> None
                              | Loop (v, va) -> None
                              | If (v, va, vb) -> None
                              | Br v -> None
                              | Br_if v -> None
                              | Br_table (v, va) -> None
                              | Return -> None
                              | Call v -> None
                              | Call_indirect (v, va) -> None
                              | Local_get v -> None
                              | Local_set v -> None
                              | Local_tee v -> None
                              | Global_get v -> None
                              | Global_set v -> None
                              | Table_get v -> None
                              | Table_set v -> None
                              | Table_size v -> None
                              | Table_grow v -> None
                              | Load (v, va, vb, vc) -> None
                              | Store (v, va, vb, vc) -> None
                              | Load_vec (v, va, vb) -> None
                              | Load_lane_vec (v, va, vb, vc) -> None
                              | Store_vec (v, va, vb) -> None
                              | Memory_size -> None
                              | Memory_grow -> None
                              | Memory_init v -> None
                              | Memory_fill -> None
                              | Memory_copy -> None
                              | Table_init (v, va) -> None
                              | Table_copy (v, va) -> None
                              | Table_fill v -> None
                              | Elem_drop v -> None
                              | Data_drop v -> None
                              | EConstNum v -> None
                              | EConstVec v -> None
                              | Unop (v, va) -> None
                              | Binop (v, va) -> None
                              | Testop (v, va) -> None
                              | Relop (v, va) -> None
                              | Cvtop (v, va, vb, vc) -> None
                              | Ref_null v -> None
                              | Ref_is_null -> None
                              | Unop_vec v -> None
                              | Binop_vec v -> None
                              | Ternop_vec v -> None
                              | Test_vec v -> None
                              | Shift_vec v -> None
                              | Splat_vec v -> None
                              | Extract_vec (v, va, vb) -> None
                              | Replace_vec (v, va) -> None;;

let rec module_start_type_checker_p
  x xa =
    bind (single (x, xa))
      (fun (c, i) ->
        bind (if_pred (less_nat i (size_list (func_t c))))
          (fun () ->
            bind (eq_i_i equal_tf (nth (func_t c) i) (Tf ([], [])))
              (fun () -> single ())));;

let rec module_start_typing x1 x2 = holds (module_start_type_checker_p x1 x2);;

let rec global_update
  globala
    (T_context_ext
      (types_t, func_t, global, elem, data, table, memory, local, label, return,
        refs, more))
    = T_context_ext
        (types_t, func_t, globala global, elem, data, table, memory, local,
          label, return, refs, more);;

let rec return_update
  returna
    (T_context_ext
      (types_t, func_t, global, elem, data, table, memory, local, label, return,
        refs, more))
    = T_context_ext
        (types_t, func_t, global, elem, data, table, memory, local, label,
          returna return, refs, more);;

let rec run_instantiate
  n d (s, (inst, es)) =
    (let (Config (_, sa, _, _), res) =
       run_iter n
         (Config
           (d, s,
             Frame_context
               (Redex ([], es, []), [], zero_nat, F_ext ([], inst, ())),
             []))
       in
      (sa, res));;

let rec e_desc (Module_export_ext (e_name, e_desc, more)) = e_desc;;

let rec e_name (Module_export_ext (e_name, e_desc, more)) = e_name;;

let rec i_desc (Module_import_ext (i_module, i_name, i_desc, more)) = i_desc;;

let rec interp_get_v_ref
  s inst b_es = (let V_ref v = interp_get_v s inst b_es in v);;

let rec collect_funcidxs_module_import
  me = (match i_desc me with Imp_func i -> [i] | Imp_tab _ -> []
         | Imp_mem _ -> [] | Imp_glob _ -> []);;

let rec collect_funcidxs_module_export
  me = (match e_desc me with Ext_func i -> [i] | Ext_tab _ -> []
         | Ext_mem _ -> [] | Ext_glob _ -> []);;

let rec collect_funcidxs_module_glob
  glob = map_filter extract_funcidx_b_e (g_init glob);;

let rec collect_funcidxs_module_func
  (uu, (uv, es)) = map_filter extract_funcidx_b_e es;;

let rec collect_funcidxs_b_e_list es = map_filter extract_funcidx_b_e es;;

let rec collect_funcidxs_elem_mode
  = function Em_active (uu, es) -> collect_funcidxs_b_e_list es
    | Em_passive -> []
    | Em_declarative -> [];;

let rec collect_funcidxs_module_elem
  me = concat
         (collect_funcidxs_elem_mode (e_mode me) ::
           map collect_funcidxs_b_e_list (e_init me));;

let rec collect_funcidxs_module_data
  (Module_data_ext (es, dm, ())) =
    (match dm with Dm_passive -> []
      | Dm_active (_, a) -> collect_funcidxs_b_e_list a);;

let rec collect_funcidxs_module
  modulea =
    (let from_funcs = maps collect_funcidxs_module_func (m_funcs modulea) in
     let from_globs = maps collect_funcidxs_module_glob (m_globs modulea) in
     let from_start = (match m_start modulea with None -> [] | Some x -> [x]) in
     let from_elems = maps collect_funcidxs_module_elem (m_elems modulea) in
     let from_datas = maps collect_funcidxs_module_data (m_datas modulea) in
     let from_imports = maps collect_funcidxs_module_import (m_imports modulea)
       in
     let from_exports = maps collect_funcidxs_module_export (m_exports modulea)
       in
      remdups equal_nat
        (concat
          [from_funcs; from_globs; from_start; from_elems; from_datas;
            from_imports; from_exports]));;

let rec gather_m_f_type
  tfs m_f =
    (if less_nat (fst m_f) (size_list tfs) then Some (nth tfs (fst m_f))
      else None);;

let rec interp_get_v_refs s inst b_ess = map (interp_get_v_ref s inst) b_ess;;

let rec run_invoke
  x = run_invoke_v
        (power power_nat (nat_of_integer (Z.of_int 2))
          (nat_of_integer (Z.of_int 63)))
        (nat_of_integer (Z.of_int 300)) x;;

let rec module_glob_type_checker
  c (Module_glob_ext (tg, es, ())) =
    list_all (const_expr c) es && b_e_type_checker c es (Tf ([], [tg_t tg]));;

let rec module_func_type_checker
  c (i, (t_locs, b_es)) =
    less_nat i (size_list (types_t c)) &&
      (let Tf (tn, tm) = nth (types_t c) i in
        (if is_none (n_zeros t_locs) then false
          else b_e_type_checker
                 (return_update (fun _ -> Some tm)
                   (label_update (fun _ -> [tm] @ label c)
                     (local_update (fun _ -> tn @ t_locs) c)))
                 b_es (Tf ([], tm))));;

let rec elem_mode_type_checker
  c x1 tr = match c, x1, tr with
    c, Em_active (x, es), tr ->
      less_nat x (size_list (table c)) &&
        (equal_t_ref (tab_t_reftype (nth (table c) x)) tr &&
          (b_e_type_checker c es (Tf ([], [T_num T_i32])) &&
            list_all (const_expr c) es))
    | uu, Em_passive, uw -> true
    | uu, Em_declarative, uw -> true;;

let rec module_elem_type_checker
  c (Module_elem_ext (tra, ess, em, ())) tr =
    equal_t_ref tra tr &&
      (list_all (list_all (const_expr c)) ess &&
        (list_all (fun es -> b_e_type_checker c es (Tf ([], [T_ref tra])))
           ess &&
          elem_mode_type_checker c em tra));;

let rec data_mode_type_checker
  c x1 = match c, x1 with
    c, Dm_active (x, es) ->
      less_nat x (size_list (memory c)) &&
        (b_e_type_checker c es (Tf ([], [T_num T_i32])) &&
          list_all (const_expr c) es)
    | uu, Dm_passive -> true;;

let rec module_data_type_checker
  c (Module_data_ext (bs, dm, ())) = data_mode_type_checker c dm;;

let rec module_import_typer
  tfs x1 = match tfs, x1 with
    tfs, Imp_func i ->
      (if less_nat i (size_list tfs) then Some (Te_func (nth tfs i)) else None)
    | tfs, Imp_tab tt ->
        (if module_tab_typing tt then Some (Te_tab tt) else None)
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

let rec module_type_checker
  (M_ext (tfs, fs, ts, ms, gs, els, ds, i_opt, imps, exps, ())) =
    (match
      (those (map (gather_m_f_type tfs) fs),
        those (map (fun imp -> module_import_typer tfs (i_desc imp)) imps))
      with (None, _) -> None | (Some _, None) -> None
      | (Some fts, Some impts) ->
        (let modulea =
           M_ext (tfs, fs, ts, ms, gs, els, ds, i_opt, imps, exps, ()) in
         let ifts =
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
         let rts = map e_type els in
         let dts = replicate (size_list ds) () in
         let rfs =
           collect_funcidxs_module
             (m_start_update (fun _ -> None)
               (m_funcs_update (fun _ -> []) modulea))
           in
         let c =
           T_context_ext
             (tfs, ifts @ fts, igs @ gts, rts, dts, its @ ts, ims @ ms, [], [],
               None, rfs, ())
           in
         let ca = global_update (fun _ -> igs) c in
          (if list_all (module_func_type_checker c) fs &&
                (list_all module_tab_typing ts &&
                  (list_all
                     (fun t ->
                       limit_typing t
                         (power power_nat (nat_of_integer (Z.of_int 2))
                           (nat_of_integer (Z.of_int 16))))
                     ms &&
                    (list_all (module_glob_type_checker ca) gs &&
                      (list_all2 (module_elem_type_checker ca) els rts &&
                        (list_all (module_data_type_checker ca) ds &&
                          (pred_option (module_start_typing c) i_opt &&
                            (distinct equal_literal (map e_name exps) &&
                              less_eq_nat (size_list (ims @ ms)) one_nata)))))))
            then (match
                   those (map (fun exp -> module_export_typer c (e_desc exp))
                           exps)
                   with None -> None | Some expts -> Some (impts, expts))
            else None)));;

let rec interp_alloc_module
  s m imps gvs el_inits =
    (let i_fs =
       upt (size_list (funcs s))
         (plus_nat (size_list (funcs s)) (size_list (m_funcs m)))
       in
     let i_ts =
       upt (size_list (tabs s))
         (plus_nat (size_list (tabs s)) (size_list (m_tabs m)))
       in
     let i_ms =
       upt (size_list (mems s))
         (plus_nat (size_list (mems s)) (size_list (m_mems m)))
       in
     let i_gs =
       upt (size_list (globs s))
         (plus_nat (size_list (globs s))
           (min ord_nat (size_list (m_globs m)) (size_list gvs)))
       in
     let i_es =
       upt (size_list (elems s))
         (plus_nat (size_list (elems s))
           (min ord_nat (size_list (m_elems m)) (size_list el_inits)))
       in
     let i_ds =
       upt (size_list (datas s))
         (plus_nat (size_list (datas s)) (size_list (m_datas m)))
       in
     let inst =
       Inst_ext
         (m_types m,
           map_filter
             (fun a ->
               (match a with Ext_func aa -> Some aa | Ext_tab _ -> None
                 | Ext_mem _ -> None | Ext_glob _ -> None))
             imps @
             i_fs,
           map_filter
             (fun a ->
               (match a with Ext_func _ -> None | Ext_tab aa -> Some aa
                 | Ext_mem _ -> None | Ext_glob _ -> None))
             imps @
             i_ts,
           map_filter
             (fun a ->
               (match a with Ext_func _ -> None | Ext_tab _ -> None
                 | Ext_mem aa -> Some aa | Ext_glob _ -> None))
             imps @
             i_ms,
           map_filter
             (fun a ->
               (match a with Ext_func _ -> None | Ext_tab _ -> None
                 | Ext_mem _ -> None | Ext_glob aa -> Some aa))
             imps @
             i_gs,
           i_es, i_ds, ())
       in
     let (s1, _) = alloc_Xs (fun sa m_f -> alloc_func sa m_f inst) s (m_funcs m)
       in
     let (s2, _) = alloc_Xs alloc_tab s1 (m_tabs m) in
     let (s3, _) = alloc_Xs alloc_mem s2 (m_mems m) in
     let (s4, _) = alloc_Xs alloc_glob s3 (zip (m_globs m) gvs) in
     let (s5, _) = alloc_Xs alloc_elem s4 (zip (m_elems m) el_inits) in
     let (sa, _) = alloc_Xs alloc_data s5 (m_datas m) in
     let exps =
       map (fun m_exp ->
             Module_export_ext
               (e_name m_exp, export_get_v_ext inst (e_desc m_exp), ()))
         (m_exports m)
       in
      (sa, (inst, exps)));;

let rec interp_instantiate
  s m v_imps =
    (match module_type_checker m with None -> (s, RI_trap "invalid module")
      | Some (t_imps, _) ->
        (if list_all2 (external_typing s) v_imps t_imps
          then (let inst_init_funcs =
                  map_filter
                    (fun a ->
                      (match a with Ext_func aa -> Some aa | Ext_tab _ -> None
                        | Ext_mem _ -> None | Ext_glob _ -> None))
                    v_imps @
                    upt (size_list (funcs s))
                      (plus_nat (size_list (funcs s)) (size_list (m_funcs m)))
                  in
                let inst_init =
                  Inst_ext
                    ([], inst_init_funcs, [], [],
                      map_filter
                        (fun a ->
                          (match a with Ext_func _ -> None | Ext_tab _ -> None
                            | Ext_mem _ -> None | Ext_glob aa -> Some aa))
                        v_imps,
                      [], [], ())
                  in
                let g_inits =
                  map (fun g -> interp_get_v s inst_init (g_init g)) (m_globs m)
                  in
                let el_inits =
                  map (fun el -> interp_get_v_refs s inst_init (e_init el))
                    (m_elems m)
                  in
                let (sa, (inst, v_exps)) =
                  interp_alloc_module s m v_imps g_inits el_inits in
                let start =
                  (match m_start m with None -> []
                    | Some i_s -> [Invoke (nth (funcsa inst) i_s)])
                  in
                 (sa, RI_res
                        (inst, v_exps,
                          run_elems (m_elems m) @
                            run_datas (m_datas m) @ start)))
          else (s, RI_trap "invalid import")));;

let rec interp_instantiate_init
  s m v_imps =
    (match interp_instantiate s m v_imps
      with (sa, RI_crash res_error) -> (sa, RI_crash res_error)
      | (sa, RI_trap literal) -> (sa, RI_trap literal)
      | (sa, RI_res (inst, v_exps, init_es)) ->
        (match
          run_instantiate
            (power power_nat (nat_of_integer (Z.of_int 2))
              (nat_of_integer (Z.of_int 63)))
            (nat_of_integer (Z.of_int 300)) (sa, (inst, init_es))
          with (sb, RCrash r) -> (sb, RI_crash r)
          | (sb, RTrap r) -> (sb, RI_trap r)
          | (sb, RValue []) -> (sb, RI_res (inst, v_exps, []))
          | (sb, RValue (_ :: _)) ->
            (sb, RI_crash (Error_invalid "start function"))));;

end;; (*struct WasmRef_Isa*)
