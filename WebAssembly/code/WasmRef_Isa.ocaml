module WasmRef_Isa : sig
  type num = One | Bit0 of num | Bit1 of num
  val equal_num : num -> num -> bool
  type int = Zero_int | Pos of num | Nega of num
  val equal_inta : int -> int -> bool
  type 'a equal = {equal : 'a -> 'a -> bool}
  val equal : 'a equal -> 'a -> 'a -> bool
  val equal_int : int equal
  val plus_num : num -> num -> num
  val times_num : num -> num -> num
  val times_inta : int -> int -> int
  type 'a times = {times : 'a -> 'a -> 'a}
  val times : 'a times -> 'a -> 'a -> 'a
  type 'a dvd = {times_dvd : 'a times}
  val times_int : int times
  val dvd_int : int dvd
  val one_inta : int
  type 'a one = {one : 'a}
  val one : 'a one -> 'a
  val one_int : int one
  val uminus_inta : int -> int
  val bitM : num -> num
  val dup : int -> int
  val minus_inta : int -> int -> int
  val sub : num -> num -> int
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
  val less_eq_num : num -> num -> bool
  val less_num : num -> num -> bool
  val less_eq_int : int -> int -> bool
  val divmod_step_int : num -> int * int -> int * int
  val divmod_int : num -> num -> int * int
  val fst : 'a * 'b -> 'a
  type 'a zero_neq_one =
    {one_zero_neq_one : 'a one; zero_zero_neq_one : 'a zero}
  val of_bool : 'a zero_neq_one -> bool -> 'a
  val zero_neq_one_int : int zero_neq_one
  val adjust_div : int * int -> int
  val divide_inta : int -> int -> int
  type 'a divide = {divide : 'a -> 'a -> 'a}
  val divide : 'a divide -> 'a -> 'a -> 'a
  val divide_int : int divide
  val snd : 'a * 'b -> 'b
  val adjust_mod : int -> int -> int
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
  val eq : 'a equal -> 'a -> 'a -> bool
  type 'a semiring_no_zero_divisors_cancel =
    {semiring_no_zero_divisors_semiring_no_zero_divisors_cancel :
       'a semiring_no_zero_divisors}
  type 'a semidom_divide =
    {divide_semidom_divide : 'a divide; semidom_semidom_divide : 'a semidom;
      semiring_no_zero_divisors_cancel_semidom_divide :
        'a semiring_no_zero_divisors_cancel}
  type 'a algebraic_semidom =
    {semidom_divide_algebraic_semidom : 'a semidom_divide}
  type 'a semidom_modulo =
    {algebraic_semidom_semidom_modulo : 'a algebraic_semidom;
      semiring_modulo_semidom_modulo : 'a semiring_modulo}
  val dvd : 'a equal * 'a semidom_modulo -> 'a -> 'a -> bool
  val semiring_no_zero_divisors_cancel_int :
    int semiring_no_zero_divisors_cancel
  val semidom_divide_int : int semidom_divide
  val algebraic_semidom_int : int algebraic_semidom
  val semidom_modulo_int : int semidom_modulo
  val bit_int : int -> nat -> bool
  type 'a semiring_bits =
    {semiring_parity_semiring_bits : 'a semiring_parity;
      bit : 'a -> nat -> bool}
  val bit : 'a semiring_bits -> 'a -> nat -> bool
  val semiring_bits_int : int semiring_bits
  val take_bit_int : nat -> int -> int
  val push_bit_int : nat -> int -> int
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
  type 'a set = Set of 'a list | Coset of 'a list
  val bot_set : 'a set
  val membera : 'a equal -> 'a list -> 'a -> bool
  val member : 'a equal -> 'a -> 'a set -> bool
  val removeAll : 'a equal -> 'a -> 'a list -> 'a list
  val inserta : 'a equal -> 'a -> 'a list -> 'a list
  val insert : 'a equal -> 'a -> 'a set -> 'a set
  val and_int : int -> int -> int
  val not_int : int -> int
  val or_int : int -> int -> int
  val xor_int : int -> int -> int
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
  val one_nat : nat one
  val times_nata : nat -> nat -> nat
  val times_nat : nat times
  val power_nat : nat power
  val less_eq_nat : nat -> nat -> bool
  val less_nat : nat -> nat -> bool
  val ord_nat : nat ord
  type 'a itself = Type
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
  type t = T_i32 | T_i64 | T_f32 | T_f64
  val equal_ta : t -> t -> bool
  val equal_t : t equal
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
  type num1 = One_num1
  type 'a finite = unit
  type 'a bit0 = Abs_bit0 of int
  type i32 = Abs_i32 of num1 bit0 bit0 bit0 bit0 bit0 word
  val apsnd : ('a -> 'b) -> 'c * 'a -> 'c * 'b
  val divmod_integer : Z.t -> Z.t -> Z.t * Z.t
  val int_of_integer : Z.t -> int
  val int_of_nat : nat -> int
  val of_nat : 'a len -> nat -> 'a word
  val len_of_num1 : num1 itself -> nat
  val len0_num1 : num1 len0
  val len_num1 : num1 len
  val nat_of_integer : Z.t -> nat
  val len_of_bit0 : 'a len0 -> 'a bit0 itself -> nat
  val len0_bit0 : 'a len0 -> 'a bit0 len0
  val len_bit0 : 'a len -> 'a bit0 len
  val zero_i32a : i32
  val zero_i32 : i32 zero
  val len_of_i32 : i32 itself -> nat
  val len0_i32 : i32 len0
  val len_i32 : i32 len
  val less_int : int -> int -> bool
  val integer_of_int : int -> Z.t
  val nat : int -> nat
  val the_nat : 'a len -> 'a word -> nat
  val nat_of_int_i32 : i32 -> nat
  val plus_nat : nat -> nat -> nat
  val suc : nat -> nat
  val gen_length : nat -> 'a list -> nat
  val size_list : 'a list -> nat
  val map : ('a -> 'b) -> 'a list -> 'b list
  val upt : nat -> nat -> nat list
  val fold : ('a -> 'b -> 'b) -> 'a list -> 'b -> 'b
  val rev : 'a list -> 'a list
  val to_bl : 'a len -> 'a word -> bool list
  val filter : ('a -> bool) -> 'a list -> 'a list
  val id : 'a -> 'a
  val pop_count : 'a len -> 'a word -> nat
  val int_popcnt_i32 : i32 -> i32
  val int_of_nat_i32 : nat -> i32
  val shiftr : 'a semiring_bit_syntax -> 'a -> nat -> 'a
  val and_nat : nat -> nat -> nat
  val int_shr_u_i32 : i32 -> i32 -> i32
  val signed_take_bit : 'a ring_bit_operations -> nat -> 'a -> 'a
  val the_signed_int : 'a len -> 'a word -> int
  val signed_drop_bit : 'a len -> nat -> 'a word -> 'a word
  val sshiftr : 'a len -> 'a word -> nat -> 'a word
  val int_shr_s_i32 : i32 -> i32 -> i32
  val int_rem_u_i32 : i32 -> i32 -> i32 option
  val sgn_int : int -> int
  val abs_int : int -> int
  val signed_divide_int : int -> int -> int
  val signed_modulo_int : int -> int -> int
  val signed_modulo_word : 'a len -> 'a word -> 'a word -> 'a word
  val int_rem_s_i32 : i32 -> i32 -> i32 option
  val int_div_u_i32 : i32 -> i32 -> i32 option
  val signed_divide_word : 'a len -> 'a word -> 'a word -> 'a word
  val int_div_s_i32 : i32 -> i32 -> i32 option
  val modulo_integer : Z.t -> Z.t -> Z.t
  val modulo_nat : nat -> nat -> nat
  val concat_bit : nat -> int -> int -> int
  val word_rotr : 'a len -> nat -> 'a word -> 'a word
  val int_rotr_i32 : i32 -> i32 -> i32
  val word_rotl : 'a len -> nat -> 'a word -> 'a word
  val int_rotl_i32 : i32 -> i32 -> i32
  val less_word : 'a len -> 'a word -> 'a word -> bool
  val int_lt_u_i32 : i32 -> i32 -> bool
  val word_sless : 'a len -> 'a word -> 'a word -> bool
  val int_lt_s_i32 : i32 -> i32 -> bool
  val less_eq_word : 'a len -> 'a word -> 'a word -> bool
  val int_le_u_i32 : i32 -> i32 -> bool
  val word_sle : 'a len -> 'a word -> 'a word -> bool
  val int_le_s_i32 : i32 -> i32 -> bool
  val int_gt_u_i32 : i32 -> i32 -> bool
  val int_gt_s_i32 : i32 -> i32 -> bool
  val int_ge_u_i32 : i32 -> i32 -> bool
  val int_ge_s_i32 : i32 -> i32 -> bool
  val xor_word : 'a len -> 'a word -> 'a word -> 'a word
  val int_xor_i32 : i32 -> i32 -> i32
  val int_sub_i32 : i32 -> i32 -> i32
  val shiftl : 'a semiring_bit_syntax -> 'a -> nat -> 'a
  val int_shl_i32 : i32 -> i32 -> i32
  val int_mul_i32 : i32 -> i32 -> i32
  val int_eqz_i32 : i32 -> bool
  val takeWhile : ('a -> bool) -> 'a list -> 'a list
  val word_ctz : 'a len -> 'a word -> nat
  val int_ctz_i32 : i32 -> i32
  val word_clz : 'a len -> 'a word -> nat
  val int_clz_i32 : i32 -> i32
  val int_and_i32 : i32 -> i32 -> i32
  val int_add_i32 : i32 -> i32 -> i32
  val or_word : 'a len -> 'a word -> 'a word -> 'a word
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
  type i64 = Abs_i64 of num1 bit0 bit0 bit0 bit0 bit0 bit0 word
  val zero_i64a : i64
  val zero_i64 : i64 zero
  val len_of_i64 : i64 itself -> nat
  val len0_i64 : i64 len0
  val len_i64 : i64 len
  val nat_of_int_i64 : i64 -> nat
  val int_popcnt_i64 : i64 -> i64
  val int_of_nat_i64 : nat -> i64
  val int_shr_u_i64 : i64 -> i64 -> i64
  val int_shr_s_i64 : i64 -> i64 -> i64
  val int_rem_u_i64 : i64 -> i64 -> i64 option
  val int_rem_s_i64 : i64 -> i64 -> i64 option
  val int_div_u_i64 : i64 -> i64 -> i64 option
  val int_div_s_i64 : i64 -> i64 -> i64 option
  val int_rotr_i64 : i64 -> i64 -> i64
  val int_rotl_i64 : i64 -> i64 -> i64
  val int_lt_u_i64 : i64 -> i64 -> bool
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
    Inst_ext of tf list * nat list * nat list * nat list * nat list * 'a
  type v = ConstInt32 of i32 | ConstInt64 of i64 | ConstFloat32 of F32Wrapper.t
    | ConstFloat64 of F64Wrapper.t
  type 'a f_ext = F_ext of v list * unit inst_ext * 'a
  type testop = Eqz
  type relop_i = Eq | Ne | Lt of sx | Gt of sx | Le of sx | Ge of sx
  type relop_f = Eqf | Nef | Ltf | Gtf | Lef | Gef
  type relop = Relop_i of relop_i | Relop_f of relop_f
  type unop_i = Clz | Ctz | Popcnt
  type unop_f = Neg | Abs | Ceil | Floor | Trunc | Nearest | Sqrt
  type unop = Unop_i of unop_i | Unop_f of unop_f
  type tp = Tp_i8 | Tp_i16 | Tp_i32
  type b_e = Unreachable | Nop | Drop | Select | Block of tf * b_e list |
    Loop of tf * b_e list | If of tf * b_e list * b_e list | Br of nat |
    Br_if of nat | Br_table of nat list * nat | Return | Call of nat |
    Call_indirect of nat | Get_local of nat | Set_local of nat |
    Tee_local of nat | Get_global of nat | Set_global of nat |
    Load of t * (tp * sx) option * nat * nat |
    Store of t * tp option * nat * nat | Current_memory | Grow_memory |
    EConst of v | Unop of t * unop | Binop of t * binop | Testop of t * testop |
    Relop of t * relop | Cvtop of t * cvtop * t * sx option
  type e = Basic of b_e | Trap | Invoke of nat | Label of nat * e list * e list
    | Frame of nat * unit f_ext * e list
  type 'a global_ext = Global_ext of mut * v * 'a
  type byte = Abs_byte of num1 bit0 bit0 bit0 word
  type mem_rep = Abs_mem_rep of byte list
  type cl = Func_native of unit inst_ext * tf * t list * b_e list |
    Func_host of tf * host
  and 'a s_ext =
    S_ext of
      cl list * ((nat option) list * nat option) list *
        (mem_rep * nat option) list * unit global_ext list * 'a
  and host = Abs_host of (unit s_ext * v list -> (unit s_ext * v list) option)
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
  type 'a module_data_ext = Module_data_ext of nat * b_e list * byte list * 'a
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
  type label_context = Label_context of v list * b_e list * nat * b_e list
  type frame_context =
    Frame_context of redex * label_context list * nat * unit f_ext
  type config = Config of nat * unit s_ext * frame_context * frame_context list
  type res_step = Res_crash of res_error | Res_trap of string | Step_normal
  type checker_type = TopType of ct list | Typea of t list | Bot
  type 'a t_context_ext =
    T_context_ext of
      tf list * tf list * unit tg_ext list * unit limit_t_ext list *
        unit limit_t_ext list * t list * (t list) list * (t list) option * 'a
  val comp : ('a -> 'b) -> ('c -> 'a) -> 'c -> 'b
  val nth : 'a list -> nat -> 'a
  val zip : 'a list -> 'b list -> ('a * 'b) list
  val drop : nat -> 'a list -> 'a list
  val null : 'a list -> bool
  val last : 'a list -> 'a
  val take_tr : nat -> 'a list -> 'a list -> 'a list
  val take : nat -> 'a list -> 'a list
  val cast : 'b len -> 'a len -> 'b word -> 'a word
  val foldl : ('a -> 'b -> 'a) -> 'a -> 'b list -> 'a
  val foldr : ('a -> 'b -> 'b) -> 'a list -> 'b -> 'b
  val map_option : ('a -> 'b) -> 'a option -> 'b option
  val those : ('a option) list -> ('a list) option
  val distinct : 'a equal -> 'a list -> bool
  val ki64 : nat
  val replicate_tr : nat -> 'a -> 'a list -> 'a list
  val replicate : nat -> 'a -> 'a list
  val is_none : 'a option -> bool
  val bind : 'a pred -> ('a -> 'b pred) -> 'b pred
  val apply : ('a -> 'b pred) -> 'a seq -> 'b seq
  val map_filter : ('a -> 'b option) -> 'a list -> 'b list
  val eval : 'a equal -> 'a pred -> 'a -> bool
  val memberb : 'a equal -> 'a seq -> 'a -> bool
  val holds : unit pred -> bool
  val divide_integer : Z.t -> Z.t -> Z.t
  val divide_nat : nat -> nat -> nat
  val mem_rep_length : mem_rep -> nat
  val mem_length : mem_rep * nat option -> nat
  val mem_size : mem_rep * nat option -> nat
  val pred_option : ('a -> bool) -> 'a option -> bool
  val l_min : 'a limit_t_ext -> nat
  val l_max : 'a limit_t_ext -> nat option
  val limits_compat : 'a limit_t_ext -> 'b limit_t_ext -> bool
  val mem_max : mem_rep * nat option -> nat option
  val mem_typing : mem_rep * nat option -> 'a limit_t_ext -> bool
  val tab_typing : (nat option) list * nat option -> 'a limit_t_ext -> bool
  val bytes_replicate : nat -> byte -> byte list
  val zero_byte : byte
  val mem_rep_mk : nat -> mem_rep
  val mem_mk : unit limit_t_ext -> mem_rep * nat option
  val msbyte : byte list -> byte
  val mems : 'a s_ext -> (mem_rep * nat option) list
  val tabs : 'a s_ext -> ((nat option) list * nat option) list
  val list_update : 'a list -> nat -> 'a -> 'a list
  val bot_pred : 'a pred
  val single : 'a -> 'a pred
  val typeof : v -> t
  val g_val : 'a global_ext -> v
  val g_mut : 'a global_ext -> mut
  val tg_mut : 'a tg_ext -> mut
  val tg_t : 'a tg_ext -> t
  val glob_typing : 'a global_ext -> 'b tg_ext -> bool
  val funcs : 'a s_ext -> cl list
  val globs : 'a s_ext -> unit global_ext list
  val signed_cast : 'b len -> 'a len -> 'b word -> 'a word
  val bin_sign : int -> int
  val adjunct : 'a pred -> 'a seq -> 'a seq
  val sup_pred : 'a pred -> 'a pred -> 'a pred
  val if_pred : bool -> unit pred
  val f_inst : 'a f_ext -> unit inst_ext
  val f_locs : 'a f_ext -> v list
  val msb_word : 'a len -> 'a word -> bool
  val msb_byte : byte -> bool
  val bin_split : nat -> int -> int * int
  val list_all : ('a -> bool) -> 'a list -> bool
  val memsa : 'a inst_ext -> nat list
  val tabsa : 'a inst_ext -> nat list
  val ocaml_int64_to_isabelle_int64 : Int64.t -> i64
  val isabelle_i64_trunc_u_f64 : F64Wrapper.t -> i64 option
  val ui64_trunc_f64 : F64Wrapper.t -> i64 option
  val isabelle_i64_trunc_u_f32 : F32Wrapper.t -> i64 option
  val ui64_trunc_f32 : F32Wrapper.t -> i64 option
  val si64_trunc_f64 : F64Wrapper.t -> i64 option
  val si64_trunc_f32 : F32Wrapper.t -> i64 option
  val wasm_extend_u : i32 -> i64
  val wasm_extend_s : i32 -> i64
  val cvt_i64 : sx option -> v -> i64 option
  val ocaml_int32_to_isabelle_int32 : Int32.t -> i32
  val isabelle_i32_trunc_u_f64 : F64Wrapper.t -> i32 option
  val ui32_trunc_f64 : F64Wrapper.t -> i32 option
  val isabelle_i32_trunc_u_f32 : F32Wrapper.t -> i32 option
  val ui32_trunc_f32 : F32Wrapper.t -> i32 option
  val si32_trunc_f64 : F64Wrapper.t -> i32 option
  val si32_trunc_f32 : F32Wrapper.t -> i32 option
  val wasm_wrap : i64 -> i32
  val cvt_i32 : sx option -> v -> i32 option
  val isabelle_int64_to_ocaml_int64 : i64 -> Int64.t
  val f64_convert_u_isabelle_i64 : i64 -> F64Wrapper.t
  val f64_convert_ui64 : i64 -> F64Wrapper.t
  val isabelle_int32_to_ocaml_int32 : i32 -> Int32.t
  val f64_convert_u_isabelle_i32 : i32 -> F64Wrapper.t
  val f64_convert_ui32 : i32 -> F64Wrapper.t
  val f64_convert_s_isabelle_i64 : i64 -> F64Wrapper.t
  val f64_convert_si64 : i64 -> F64Wrapper.t
  val f64_convert_s_isabelle_i32 : i32 -> F64Wrapper.t
  val f64_convert_si32 : i32 -> F64Wrapper.t
  val cvt_f64 : sx option -> v -> F64Wrapper.t option
  val f32_convert_u_isabelle_i64 : i64 -> F32Wrapper.t
  val f32_convert_ui64 : i64 -> F32Wrapper.t
  val f32_convert_u_isabelle_i32 : i32 -> F32Wrapper.t
  val f32_convert_ui32 : i32 -> F32Wrapper.t
  val f32_convert_s_isabelle_i64 : i64 -> F32Wrapper.t
  val f32_convert_si64 : i64 -> F32Wrapper.t
  val f32_convert_s_isabelle_i32 : i32 -> F32Wrapper.t
  val f32_convert_si32 : i32 -> F32Wrapper.t
  val cvt_f32 : sx option -> v -> F32Wrapper.t option
  val cvt : t -> sx option -> v -> v option
  val select_return_top : ct list -> ct -> ct -> checker_type
  val to_ct_list : t list -> ct list
  val produce : checker_type -> checker_type -> checker_type
  val ct_compat : ct -> ct -> bool
  val ct_prefix : ct list -> ct list -> bool
  val ct_suffix : ct list -> ct list -> bool
  val consume : checker_type -> ct list -> checker_type
  val type_update : checker_type -> ct list -> checker_type -> checker_type
  val type_update_select : checker_type -> checker_type
  val tp_length : tp -> nat
  val t_length : t -> nat
  val is_int_t : t -> bool
  val load_store_t_bounds : nat -> tp option -> t -> bool
  val label_update :
    ((t list) list -> (t list) list) -> 'a t_context_ext -> 'a t_context_ext
  val c_types_agree : checker_type -> t list -> bool
  val is_float_t : t -> bool
  val relop_t_agree : relop -> t -> bool
  val binop_t_agree : binop -> t -> bool
  val unop_t_agree : unop -> t -> bool
  val option_projl : ('a * 'b) option -> 'a option
  val types_t : 'a t_context_ext -> tf list
  val equal_bool : bool -> bool -> bool
  val convert_cond : t -> t -> sx option -> bool
  val return : 'a t_context_ext -> (t list) option
  val memory : 'a t_context_ext -> unit limit_t_ext list
  val global : 'a t_context_ext -> unit tg_ext list
  val func_t : 'a t_context_ext -> tf list
  val table : 'a t_context_ext -> unit limit_t_ext list
  val local : 'a t_context_ext -> t list
  val label : 'a t_context_ext -> (t list) list
  val same_lab_h : nat list -> (t list) list -> t list -> (t list) option
  val same_lab : nat list -> (t list) list -> (t list) option
  val is_mut : unit tg_ext -> bool
  val check : unit t_context_ext -> b_e list -> checker_type -> checker_type
  val b_e_type_checker : unit t_context_ext -> b_e list -> tf -> bool
  val check_single : unit t_context_ext -> b_e -> checker_type -> checker_type
  val eq_i_i : 'a equal -> 'a -> 'a -> unit pred
  val list_all2 : ('a -> 'b -> bool) -> 'a list -> 'b list -> bool
  val funcsa : 'a inst_ext -> nat list
  val globsa : 'a inst_ext -> nat list
  val types : 'a inst_ext -> tf list
  val app_rev_tr : 'a list -> 'a list -> 'a list
  val mem_rep_append : mem_rep -> nat -> byte -> mem_rep
  val mem_append : mem_rep * nat option -> nat -> byte -> mem_rep * nat option
  val mem_rep_read_bytes : mem_rep -> nat -> nat -> byte list
  val read_bytes : mem_rep * nat option -> nat -> nat -> byte list
  val bin_rsplit_rev : nat -> nat -> int -> int list
  val word_rsplit_rev : 'a len -> 'b len -> 'a word -> 'b word list
  val serialise_i64 : i64 -> byte list
  val serialise_i32 : i32 -> byte list
  val byte_of_nat : nat -> byte
  val ocaml_char_to_isabelle_byte : Char.t -> byte
  val f64_serialise_isabelle_bytes : F64Wrapper.t -> byte list
  val serialise_f64 : F64Wrapper.t -> byte list
  val f32_serialise_isabelle_bytes : F32Wrapper.t -> byte list
  val serialise_f32 : F32Wrapper.t -> byte list
  val bits : v -> byte list
  val load : mem_rep * nat option -> nat -> nat -> nat -> (byte list) option
  val nat_of_byte : byte -> nat
  val uminus_word : 'a len -> 'a word -> 'a word
  val negone_byte : byte
  val mem_rep_write_bytes : mem_rep -> nat -> byte list -> mem_rep
  val write_bytes :
    mem_rep * nat option -> nat -> byte list -> mem_rep * nat option
  val takefill : 'a -> nat -> 'a list -> 'a list
  val bytes_takefill : byte -> nat -> byte list -> byte list
  val store :
    mem_rep * nat option ->
      nat -> nat -> byte list -> nat -> (mem_rep * nat option) option
  val m_data : 'a m_ext -> unit module_data_ext list
  val m_elem : 'a m_ext -> unit module_elem_ext list
  val m_mems : 'a m_ext -> unit limit_t_ext list
  val m_tabs : 'a m_ext -> unit limit_t_ext list
  val stypes : unit inst_ext -> nat -> tf
  val typerep_of : 'a typerep -> 'a -> typerepa
  val name : 'a typerep -> 'a -> string
  val m_funcs : 'a m_ext -> (nat * (t list * b_e list)) list
  val m_globs : 'a m_ext -> unit module_glob_ext list
  val m_start : 'a m_ext -> nat option
  val m_types : 'a m_ext -> tf list
  val rep_byte : byte -> num1 bit0 bit0 bit0 word
  val mems_update :
    ((mem_rep * nat option) list -> (mem_rep * nat option) list) ->
      'a s_ext -> 'a s_ext
  val tabs_update :
    (((nat option) list * nat option) list ->
      ((nat option) list * nat option) list) ->
      'a s_ext -> 'a s_ext
  val bitzero : t -> v
  val cl_type : cl -> tf
  val n_zeros : t list -> v list
  val update_redex_return : redex -> v list -> redex
  val update_fc_return : frame_context -> v list -> frame_context
  val res_crash_fuel : res
  val split_v_s_b_s_aux : v list -> b_e list -> v list * b_e list
  val split_v_s_b_s : b_e list -> v list * b_e list
  val crash_invalid : res_step
  val store_packed :
    mem_rep * nat option ->
      nat -> nat -> byte list -> nat -> (mem_rep * nat option) option
  val types_agree : t -> v -> bool
  val smem_ind : unit inst_ext -> nat option
  val app_s_f_v_s_store_packed :
    t -> tp -> nat ->
                 (mem_rep * nat option) list ->
                   unit f_ext ->
                     v list -> (mem_rep * nat option) list * (v list * res_step)
  val app_s_f_v_s_store :
    t -> nat ->
           (mem_rep * nat option) list ->
             unit f_ext ->
               v list -> (mem_rep * nat option) list * (v list * res_step)
  val app_s_f_v_s_store_maybe_packed :
    t -> tp option ->
           nat ->
             (mem_rep * nat option) list ->
               unit f_ext ->
                 v list -> (mem_rep * nat option) list * (v list * res_step)
  val horner_sum : 'b comm_semiring_0 -> ('a -> 'b) -> 'b -> 'a list -> 'b
  val word_rcat_rev : 'a len -> 'b len -> 'a word list -> 'b word
  val deserialise_i64_aux : num1 bit0 bit0 bit0 word list -> i64
  val deserialise_i64 : byte list -> i64
  val deserialise_i32_aux : num1 bit0 bit0 bit0 word list -> i32
  val deserialise_i32 : byte list -> i32
  val isabelle_byte_to_ocaml_char : byte -> Char.t
  val f64_deserialise_isabelle_bytes : byte list -> F64Wrapper.t
  val deserialise_f64 : byte list -> F64Wrapper.t
  val f32_deserialise_isabelle_bytes : byte list -> F32Wrapper.t
  val deserialise_f32 : byte list -> F32Wrapper.t
  val wasm_deserialise : byte list -> t -> v
  val sign_extend : sx -> nat -> byte list -> byte list
  val load_packed :
    sx -> mem_rep * nat option -> nat -> nat -> nat -> nat -> (byte list) option
  val app_s_f_v_s_load_packed :
    t -> tp -> sx -> nat ->
                       (mem_rep * nat option) list ->
                         unit f_ext -> v list -> v list * res_step
  val app_s_f_v_s_load :
    t -> nat ->
           (mem_rep * nat option) list ->
             unit f_ext -> v list -> v list * res_step
  val app_s_f_v_s_load_maybe_packed :
    t -> (tp * sx) option ->
           nat ->
             (mem_rep * nat option) list ->
               unit f_ext -> v list -> v list * res_step
  val tab_cl_ind :
    ((nat option) list * nat option) list -> nat -> nat -> nat option
  val app_s_f_v_s_call_indirect :
    nat ->
      ((nat option) list * nat option) list ->
        cl list -> unit f_ext -> v list -> v list * (e list * res_step)
  val g_val_update : (v -> v) -> 'a global_ext -> 'a global_ext
  val sglob_ind : unit inst_ext -> nat -> nat
  val update_glob :
    unit global_ext list -> unit inst_ext -> nat -> v -> unit global_ext list
  val app_s_f_v_s_set_global :
    nat ->
      unit global_ext list ->
        unit f_ext -> v list -> unit global_ext list * (v list * res_step)
  val app_s_f_v_s_get_global :
    nat -> unit global_ext list -> unit f_ext -> v list -> v list * res_step
  val app_s_f_v_s_mem_size :
    (mem_rep * nat option) list -> unit f_ext -> v list -> v list * res_step
  val int32_minus_one : i32
  val mem_grow : mem_rep * nat option -> nat -> (mem_rep * nat option) option
  val app_s_f_v_s_mem_grow :
    (mem_rep * nat option) list ->
      unit f_ext -> v list -> (mem_rep * nat option) list * (v list * res_step)
  val app_f_v_s_set_local :
    nat -> unit f_ext -> v list -> unit f_ext * (v list * res_step)
  val app_f_v_s_get_local : nat -> unit f_ext -> v list -> v list * res_step
  val app_v_s_tee_local : nat -> v list -> v list * (e list * res_step)
  val app_v_s_br_table :
    nat list -> nat -> v list -> v list * (e list * res_step)
  val crash_invariant : res_step
  val update_redex_step : redex -> v list -> e list -> redex
  val update_fc_step : frame_context -> v list -> e list -> frame_context
  val app_testop_i : 'a wasm_int -> testop -> 'a -> bool
  val wasm_bool : bool -> i32
  val app_testop : testop -> v -> v
  val app_v_s_testop : testop -> v list -> v list * res_step
  val app_v_s_select : v list -> v list * res_step
  val app_relop_i : 'a wasm_int -> relop_i -> 'a -> 'a -> bool
  val app_relop_i_v : relop_i -> v -> v -> v
  val app_relop_f : 'a wasm_float -> relop_f -> 'a -> 'a -> bool
  val app_relop_f_v : relop_f -> v -> v -> v
  val app_relop : relop -> v -> v -> v
  val app_v_s_relop : relop -> v list -> v list * res_step
  val app_v_s_cvtop :
    cvtop -> t -> t -> sx option -> v list -> v list * res_step
  val app_v_s_br_if : nat -> v list -> v list * (e list * res_step)
  val app_binop_i : 'a wasm_int -> binop_i -> 'a -> 'a -> 'a option
  val app_binop_i_v : binop_i -> v -> v -> v option
  val app_binop_f : 'a wasm_float -> binop_f -> 'a -> 'a -> 'a option
  val app_binop_f_v : binop_f -> v -> v -> v option
  val app_binop : binop -> v -> v -> v option
  val app_v_s_binop : binop -> v list -> v list * res_step
  val app_unop_i : 'a wasm_int -> unop_i -> 'a -> 'a
  val app_unop_i_v : unop_i -> v -> v
  val app_unop_f : 'a wasm_float -> unop_f -> 'a -> 'a
  val app_unop_f_v : unop_f -> v -> v
  val app_unop : unop -> v -> v
  val app_v_s_unop : unop -> v list -> v list * res_step
  val app_v_s_drop : v list -> v list * res_step
  val app_v_s_if :
    tf -> b_e list -> b_e list -> v list -> v list * (e list * res_step)
  val sfunc_ind : unit inst_ext -> nat -> nat
  val app_f_call : nat -> unit f_ext -> e list * res_step
  val split_n : v list -> nat -> v list * v list
  val globs_update :
    (unit global_ext list -> unit global_ext list) -> 'a s_ext -> 'a s_ext
  val run_step_b_e : b_e -> config -> config * res_step
  val crash_exhaustion : res_step
  val rep_host : host -> unit s_ext * v list -> (unit s_ext * v list) option
  val host_apply_impl :
    unit s_ext -> tf -> host -> v list -> (unit s_ext * v list) option
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
  val d_init : 'a module_data_ext -> byte list
  val d_data : 'a module_data_ext -> nat
  val init_mem :
    unit s_ext -> unit inst_ext -> nat -> unit module_data_ext -> unit s_ext
  val e_init : 'a module_elem_ext -> nat list
  val e_tab : 'a module_elem_ext -> nat
  val init_tab :
    unit s_ext -> unit inst_ext -> nat -> unit module_elem_ext -> unit s_ext
  val external_checker : unit s_ext -> v_ext -> extern_t -> unit pred
  val external_typing : unit s_ext -> v_ext -> extern_t -> bool
  val typing : unit t_context_ext -> b_e list -> tf -> bool
  val alloc_mem : unit s_ext -> unit limit_t_ext -> unit s_ext * nat
  val alloc_tab : unit s_ext -> unit limit_t_ext -> unit s_ext * nat
  val init_mems :
    unit s_ext ->
      unit inst_ext -> nat list -> unit module_data_ext list -> unit s_ext
  val init_tabs :
    unit s_ext ->
      unit inst_ext -> nat list -> unit module_elem_ext list -> unit s_ext
  val empty_frame : unit f_ext
  val export_get_v_ext : unit inst_ext -> v_ext -> v_ext
  val alloc_func :
    unit s_ext -> nat * (t list * b_e list) -> unit inst_ext -> unit s_ext * nat
  val g_type : 'a module_glob_ext -> unit tg_ext
  val alloc_glob : unit s_ext -> unit module_glob_ext * v -> unit s_ext * nat
  val run_invoke_v :
    nat -> nat -> unit s_ext * (v list * nat) -> unit s_ext * res
  val run : unit s_ext * (unit f_ext * b_e list) -> unit s_ext * res
  val d_off : 'a module_data_ext -> b_e list
  val e_off : 'a module_elem_ext -> b_e list
  val g_init : 'a module_glob_ext -> b_e list
  val local_update : (t list -> t list) -> 'a t_context_ext -> 'a t_context_ext
  val interp_get_v : unit s_ext -> unit inst_ext -> b_e list -> v
  val module_start_type_checker_p : unit t_context_ext -> nat -> unit pred
  val module_start_typing : unit t_context_ext -> nat -> bool
  val return_update :
    ((t list) option -> (t list) option) -> 'a t_context_ext -> 'a t_context_ext
  val e_desc : 'a module_export_ext -> v_ext
  val e_name : 'a module_export_ext -> string
  val i_desc : 'a module_import_ext -> imp_desc
  val interp_get_i32 : unit s_ext -> unit inst_ext -> b_e list -> i32
  val gather_m_f_type : tf list -> nat * (t list * b_e list) -> tf option
  val run_invoke : unit s_ext * (v list * nat) -> unit s_ext * res
  val module_glob_type_checker :
    unit t_context_ext -> unit module_glob_ext -> bool
  val module_func_type_checker :
    unit t_context_ext -> nat * (t list * b_e list) -> bool
  val module_elem_type_checker :
    unit t_context_ext -> unit module_elem_ext -> bool
  val module_data_type_checker :
    unit t_context_ext -> unit module_data_ext -> bool
  val module_import_typer : tf list -> imp_desc -> extern_t option
  val module_export_typer : unit t_context_ext -> v_ext -> extern_t option
  val module_type_checker : unit m_ext -> (extern_t list * extern_t list) option
  val interp_alloc_module :
    unit s_ext ->
      unit m_ext ->
        v_ext list ->
          v list -> unit s_ext * (unit inst_ext * unit module_export_ext list)
  val interp_instantiate :
    unit s_ext ->
      unit m_ext ->
        v_ext list ->
          ((unit s_ext * (unit inst_ext * unit module_export_ext list)) *
            nat option) option
end = struct

type num = One | Bit0 of num | Bit1 of num;;

let rec equal_num x0 x1 = match x0, x1 with Bit0 x2, Bit1 x3 -> false
                    | Bit1 x3, Bit0 x2 -> false
                    | One, Bit1 x3 -> false
                    | Bit1 x3, One -> false
                    | One, Bit0 x2 -> false
                    | Bit0 x2, One -> false
                    | Bit1 x3, Bit1 y3 -> equal_num x3 y3
                    | Bit0 x2, Bit0 y2 -> equal_num x2 y2
                    | One, One -> true;;

type int = Zero_int | Pos of num | Nega of num;;

let rec equal_inta x0 x1 = match x0, x1 with Nega k, Nega l -> equal_num k l
                     | Nega k, Pos l -> false
                     | Nega k, Zero_int -> false
                     | Pos k, Nega l -> false
                     | Pos k, Pos l -> equal_num k l
                     | Pos k, Zero_int -> false
                     | Zero_int, Nega l -> false
                     | Zero_int, Pos l -> false
                     | Zero_int, Zero_int -> true;;

type 'a equal = {equal : 'a -> 'a -> bool};;
let equal _A = _A.equal;;

let equal_int = ({equal = equal_inta} : int equal);;

let rec plus_num
  x0 x1 = match x0, x1 with Bit1 m, Bit1 n -> Bit0 (plus_num (plus_num m n) One)
    | Bit1 m, Bit0 n -> Bit1 (plus_num m n)
    | Bit1 m, One -> Bit0 (plus_num m One)
    | Bit0 m, Bit1 n -> Bit1 (plus_num m n)
    | Bit0 m, Bit0 n -> Bit0 (plus_num m n)
    | Bit0 m, One -> Bit1 m
    | One, Bit1 n -> Bit0 (plus_num n One)
    | One, Bit0 n -> Bit1 n
    | One, One -> Bit0 One;;

let rec times_num
  m n = match m, n with
    Bit1 m, Bit1 n -> Bit1 (plus_num (plus_num m n) (Bit0 (times_num m n)))
    | Bit1 m, Bit0 n -> Bit0 (times_num (Bit1 m) n)
    | Bit0 m, Bit1 n -> Bit0 (times_num m (Bit1 n))
    | Bit0 m, Bit0 n -> Bit0 (Bit0 (times_num m n))
    | One, n -> n
    | m, One -> m;;

let rec times_inta k l = match k, l with Nega m, Nega n -> Pos (times_num m n)
                     | Nega m, Pos n -> Nega (times_num m n)
                     | Pos m, Nega n -> Nega (times_num m n)
                     | Pos m, Pos n -> Pos (times_num m n)
                     | Zero_int, l -> Zero_int
                     | k, Zero_int -> Zero_int;;

type 'a times = {times : 'a -> 'a -> 'a};;
let times _A = _A.times;;

type 'a dvd = {times_dvd : 'a times};;

let times_int = ({times = times_inta} : int times);;

let dvd_int = ({times_dvd = times_int} : int dvd);;

let one_inta : int = Pos One;;

type 'a one = {one : 'a};;
let one _A = _A.one;;

let one_int = ({one = one_inta} : int one);;

let rec uminus_inta = function Nega m -> Pos m
                      | Pos m -> Nega m
                      | Zero_int -> Zero_int;;

let rec bitM = function One -> One
               | Bit0 n -> Bit1 (bitM n)
               | Bit1 n -> Bit1 (Bit0 n);;

let rec dup = function Nega n -> Nega (Bit0 n)
              | Pos n -> Pos (Bit0 n)
              | Zero_int -> Zero_int;;

let rec minus_inta k l = match k, l with Nega m, Nega n -> sub n m
                     | Nega m, Pos n -> Nega (plus_num m n)
                     | Pos m, Nega n -> Pos (plus_num m n)
                     | Pos m, Pos n -> sub m n
                     | Zero_int, l -> uminus_inta l
                     | k, Zero_int -> k
and sub
  x0 x1 = match x0, x1 with
    Bit0 m, Bit1 n -> minus_inta (dup (sub m n)) one_inta
    | Bit1 m, Bit0 n -> plus_inta (dup (sub m n)) one_inta
    | Bit1 m, Bit1 n -> dup (sub m n)
    | Bit0 m, Bit0 n -> dup (sub m n)
    | One, Bit1 n -> Nega (Bit0 n)
    | One, Bit0 n -> Nega (bitM n)
    | Bit1 m, One -> Pos (Bit0 m)
    | Bit0 m, One -> Pos (bitM m)
    | One, One -> Zero_int
and plus_inta k l = match k, l with Nega m, Nega n -> Nega (plus_num m n)
                | Nega m, Pos n -> sub n m
                | Pos m, Nega n -> sub m n
                | Pos m, Pos n -> Pos (plus_num m n)
                | Zero_int, l -> l
                | k, Zero_int -> k;;

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

let zero_int = ({zero = Zero_int} : int zero);;

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

let rec less_eq_num x0 n = match x0, n with Bit1 m, Bit0 n -> less_num m n
                      | Bit1 m, Bit1 n -> less_eq_num m n
                      | Bit0 m, Bit1 n -> less_eq_num m n
                      | Bit0 m, Bit0 n -> less_eq_num m n
                      | Bit1 m, One -> false
                      | Bit0 m, One -> false
                      | One, n -> true
and less_num m x1 = match m, x1 with Bit1 m, Bit0 n -> less_num m n
               | Bit1 m, Bit1 n -> less_num m n
               | Bit0 m, Bit1 n -> less_eq_num m n
               | Bit0 m, Bit0 n -> less_num m n
               | One, Bit1 n -> true
               | One, Bit0 n -> true
               | m, One -> false;;

let rec less_eq_int
  x0 x1 = match x0, x1 with Nega k, Nega l -> less_eq_num l k
    | Nega k, Pos l -> true
    | Nega k, Zero_int -> true
    | Pos k, Nega l -> false
    | Pos k, Pos l -> less_eq_num k l
    | Pos k, Zero_int -> false
    | Zero_int, Nega l -> false
    | Zero_int, Pos l -> true
    | Zero_int, Zero_int -> true;;

let rec divmod_step_int
  l (q, r) =
    (if less_eq_int (Pos l) r
      then (plus_inta (times_inta (Pos (Bit0 One)) q) one_inta,
             minus_inta r (Pos l))
      else (times_inta (Pos (Bit0 One)) q, r));;

let rec divmod_int
  m x1 = match m, x1 with
    Bit1 m, Bit1 n ->
      (if less_num m n then (Zero_int, Pos (Bit1 m))
        else divmod_step_int (Bit1 n) (divmod_int (Bit1 m) (Bit0 (Bit1 n))))
    | Bit0 m, Bit1 n ->
        (if less_eq_num m n then (Zero_int, Pos (Bit0 m))
          else divmod_step_int (Bit1 n) (divmod_int (Bit0 m) (Bit0 (Bit1 n))))
    | Bit1 m, Bit0 n ->
        (let (q, r) = divmod_int m n in
          (q, plus_inta (times_inta (Pos (Bit0 One)) r) one_inta))
    | Bit0 m, Bit0 n ->
        (let (q, r) = divmod_int m n in (q, times_inta (Pos (Bit0 One)) r))
    | One, Bit1 n -> (Zero_int, Pos One)
    | One, Bit0 n -> (Zero_int, Pos One)
    | m, One -> (Pos m, Zero_int);;

let rec fst (x1, x2) = x1;;

type 'a zero_neq_one =
  {one_zero_neq_one : 'a one; zero_zero_neq_one : 'a zero};;

let rec of_bool _A = function true -> one _A.one_zero_neq_one
                     | false -> zero _A.zero_zero_neq_one;;

let zero_neq_one_int =
  ({one_zero_neq_one = one_int; zero_zero_neq_one = zero_int} :
    int zero_neq_one);;

let rec adjust_div
  (q, r) =
    plus_inta q (of_bool zero_neq_one_int (not (equal_inta r Zero_int)));;

let rec divide_inta
  k ka = match k, ka with Nega m, Nega n -> fst (divmod_int m n)
    | Pos m, Nega n -> uminus_inta (adjust_div (divmod_int m n))
    | Nega m, Pos n -> uminus_inta (adjust_div (divmod_int m n))
    | Pos m, Pos n -> fst (divmod_int m n)
    | k, Nega One -> uminus_inta k
    | k, Pos One -> k
    | Zero_int, k -> Zero_int
    | k, Zero_int -> Zero_int;;

type 'a divide = {divide : 'a -> 'a -> 'a};;
let divide _A = _A.divide;;

let divide_int = ({divide = divide_inta} : int divide);;

let rec snd (x1, x2) = x2;;

let rec adjust_mod
  l r = (if equal_inta r Zero_int then Zero_int else minus_inta l r);;

let rec modulo_inta
  k ka = match k, ka with Nega m, Nega n -> uminus_inta (snd (divmod_int m n))
    | Pos m, Nega n -> uminus_inta (adjust_mod (Pos n) (snd (divmod_int m n)))
    | Nega m, Pos n -> adjust_mod (Pos n) (snd (divmod_int m n))
    | Pos m, Pos n -> snd (divmod_int m n)
    | k, Nega One -> Zero_int
    | k, Pos One -> Zero_int
    | Zero_int, k -> Zero_int
    | k, Zero_int -> k;;

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

let rec eq _A a b = equal _A a b;;

type 'a semiring_no_zero_divisors_cancel =
  {semiring_no_zero_divisors_semiring_no_zero_divisors_cancel :
     'a semiring_no_zero_divisors};;

type 'a semidom_divide =
  {divide_semidom_divide : 'a divide; semidom_semidom_divide : 'a semidom;
    semiring_no_zero_divisors_cancel_semidom_divide :
      'a semiring_no_zero_divisors_cancel};;

type 'a algebraic_semidom =
  {semidom_divide_algebraic_semidom : 'a semidom_divide};;

type 'a semidom_modulo =
  {algebraic_semidom_semidom_modulo : 'a algebraic_semidom;
    semiring_modulo_semidom_modulo : 'a semiring_modulo};;

let rec dvd (_A1, _A2)
  a b = eq _A1
          (modulo _A2.semiring_modulo_semidom_modulo.modulo_semiring_modulo b a)
          (zero _A2.algebraic_semidom_semidom_modulo.semidom_divide_algebraic_semidom.semidom_semidom_divide.comm_semiring_1_cancel_semidom.comm_semiring_1_comm_semiring_1_cancel.semiring_1_comm_semiring_1.semiring_0_semiring_1.mult_zero_semiring_0.zero_mult_zero);;

let semiring_no_zero_divisors_cancel_int =
  ({semiring_no_zero_divisors_semiring_no_zero_divisors_cancel =
      semiring_no_zero_divisors_int}
    : int semiring_no_zero_divisors_cancel);;

let semidom_divide_int =
  ({divide_semidom_divide = divide_int; semidom_semidom_divide = semidom_int;
     semiring_no_zero_divisors_cancel_semidom_divide =
       semiring_no_zero_divisors_cancel_int}
    : int semidom_divide);;

let algebraic_semidom_int =
  ({semidom_divide_algebraic_semidom = semidom_divide_int} :
    int algebraic_semidom);;

let semidom_modulo_int =
  ({algebraic_semidom_semidom_modulo = algebraic_semidom_int;
     semiring_modulo_semidom_modulo = semiring_modulo_int}
    : int semidom_modulo);;

let rec bit_int
  k n = not (dvd (equal_int, semidom_modulo_int) (Pos (Bit0 One))
              (divide_inta k (power power_int (Pos (Bit0 One)) n)));;

type 'a semiring_bits =
  {semiring_parity_semiring_bits : 'a semiring_parity;
    bit : 'a -> nat -> bool};;
let bit _A = _A.bit;;

let semiring_bits_int =
  ({semiring_parity_semiring_bits = semiring_parity_int; bit = bit_int} :
    int semiring_bits);;

let rec take_bit_int n k = modulo_inta k (power power_int (Pos (Bit0 One)) n);;

let rec push_bit_int n k = times_inta k (power power_int (Pos (Bit0 One)) n);;

let rec drop_bit_int n k = divide_inta k (power power_int (Pos (Bit0 One)) n);;

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

let rec mask_int n = minus_inta (power power_int (Pos (Bit0 One)) n) one_inta;;

type 'a set = Set of 'a list | Coset of 'a list;;

let bot_set : 'a set = Set [];;

let rec membera _A x0 y = match x0, y with [], y -> false
                     | x :: xs, y -> eq _A x y || membera _A xs y;;

let rec member _A
  x xa1 = match x, xa1 with x, Coset xs -> not (membera _A xs x)
    | x, Set xs -> membera _A xs x;;

let rec removeAll _A
  x xa1 = match x, xa1 with x, [] -> []
    | x, y :: xs ->
        (if eq _A x y then removeAll _A x xs else y :: removeAll _A x xs);;

let rec inserta _A x xs = (if membera _A xs x then xs else x :: xs);;

let rec insert _A
  x xa1 = match x, xa1 with x, Coset xs -> Coset (removeAll _A x xs)
    | x, Set xs -> Set (inserta _A x xs);;

let rec and_int
  k l = (if member equal_int k
              (insert equal_int Zero_int
                (insert equal_int (uminus_inta one_inta) bot_set)) &&
              member equal_int l
                (insert equal_int Zero_int
                  (insert equal_int (uminus_inta one_inta) bot_set))
          then uminus_inta
                 (of_bool zero_neq_one_int
                   (not (dvd (equal_int, semidom_modulo_int) (Pos (Bit0 One))
                          k) &&
                     not (dvd (equal_int, semidom_modulo_int) (Pos (Bit0 One))
                           l)))
          else plus_inta
                 (of_bool zero_neq_one_int
                   (not (dvd (equal_int, semidom_modulo_int) (Pos (Bit0 One))
                          k) &&
                     not (dvd (equal_int, semidom_modulo_int) (Pos (Bit0 One))
                           l)))
                 (times_inta (Pos (Bit0 One))
                   (and_int (divide_inta k (Pos (Bit0 One)))
                     (divide_inta l (Pos (Bit0 One))))));;

let rec not_int k = minus_inta (uminus_inta k) one_inta;;

let rec or_int k l = not_int (and_int (not_int k) (not_int l));;

let rec xor_int k l = or_int (and_int k (not_int l)) (and_int (not_int k) l);;

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

let one_nat = ({one = one_nata} : nat one);;

let rec times_nata m n = Nat (Z.mul (integer_of_nat m) (integer_of_nat n));;

let times_nat = ({times = times_nata} : nat times);;

let power_nat = ({one_power = one_nat; times_power = times_nat} : nat power);;

let rec less_eq_nat m n = Z.leq (integer_of_nat m) (integer_of_nat n);;

let rec less_nat m n = Z.lt (integer_of_nat m) (integer_of_nat n);;

let ord_nat = ({less_eq = less_eq_nat; less = less_nat} : nat ord);;

type 'a itself = Type;;

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

let rec zero_worda _A = Word Zero_int;;

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
          (power (power_word _A) (of_int _A (Pos (Bit0 One))) n);;

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

type t = T_i32 | T_i64 | T_f32 | T_f64;;

let rec equal_ta x0 x1 = match x0, x1 with T_f32, T_f64 -> false
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

let equal_t = ({equal = equal_ta} : t equal);;

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

type num1 = One_num1;;

type 'a finite = unit;;

type 'a bit0 = Abs_bit0 of int;;

type i32 = Abs_i32 of num1 bit0 bit0 bit0 bit0 bit0 word;;

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

let rec int_of_integer
  k = (if Z.lt k Z.zero then uminus_inta (int_of_integer (Z.neg k))
        else (if Z.equal k Z.zero then Zero_int
               else (let (l, j) = divmod_integer k (Z.of_int 2) in
                     let la = times_inta (Pos (Bit0 One)) (int_of_integer l) in
                      (if Z.equal j Z.zero then la
                        else plus_inta la one_inta))));;

let rec int_of_nat n = int_of_integer (integer_of_nat n);;

let rec of_nat _A
  n = Word (take_bit_int (len_of _A.len0_len Type) (int_of_nat n));;

let rec len_of_num1 uu = one_nata;;

let len0_num1 = ({len_of = len_of_num1} : num1 len0);;

let len_num1 = ({len0_len = len0_num1} : num1 len);;

let rec nat_of_integer k = Nat (max ord_integer Z.zero k);;

let rec len_of_bit0 _A
  uu = times_nata (nat_of_integer (Z.of_int 2)) (len_of _A Type);;

let rec len0_bit0 _A = ({len_of = len_of_bit0 _A} : 'a bit0 len0);;

let rec len_bit0 _A = ({len0_len = (len0_bit0 _A.len0_len)} : 'a bit0 len);;

let zero_i32a : i32
  = Abs_i32
      (of_nat (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
        zero_nat);;

let zero_i32 = ({zero = zero_i32a} : i32 zero);;

let rec len_of_i32 uu = nat_of_integer (Z.of_int 32);;

let len0_i32 = ({len_of = len_of_i32} : i32 len0);;

let len_i32 = ({len0_len = len0_i32} : i32 len);;

let rec less_int x0 x1 = match x0, x1 with Nega k, Nega l -> less_num l k
                   | Nega k, Pos l -> true
                   | Nega k, Zero_int -> true
                   | Pos k, Nega l -> false
                   | Pos k, Pos l -> less_num k l
                   | Pos k, Zero_int -> false
                   | Zero_int, Nega l -> false
                   | Zero_int, Pos l -> true
                   | Zero_int, Zero_int -> false;;

let rec integer_of_int
  k = (if less_int k Zero_int then Z.neg (integer_of_int (uminus_inta k))
        else (if equal_inta k Zero_int then Z.zero
               else (let l =
                       Z.mul (Z.of_int 2)
                         (integer_of_int (divide_inta k (Pos (Bit0 One))))
                       in
                     let j = modulo_inta k (Pos (Bit0 One)) in
                      (if equal_inta j Zero_int then l
                        else Z.add l (Z.of_int 1)))));;

let rec nat k = Nat (max ord_integer Z.zero (integer_of_int k));;

let rec the_nat _A w = nat (the_int _A w);;

let rec nat_of_int_i32
  (Abs_i32 x) =
    the_nat (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))) x;;

let rec plus_nat m n = Nat (Z.add (integer_of_nat m) (integer_of_nat n));;

let rec suc n = plus_nat n one_nata;;

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

let rec filter
  p x1 = match p, x1 with p, [] -> []
    | p, x :: xs -> (if p x then x :: filter p xs else filter p xs);;

let rec id x = (fun xa -> xa) x;;

let rec pop_count _A w = size_list (filter id (to_bl _A w));;

let rec int_popcnt_i32
  (Abs_i32 x) =
    Abs_i32
      (of_nat (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
        (pop_count
          (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))) x));;

let rec int_of_nat_i32
  x = Abs_i32
        (of_nat (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
          x);;

let rec shiftr _A
  a n = drop_bit _A.semiring_bit_shifts_semiring_bit_syntax n a;;

let rec and_nat m n = nat (and_int (int_of_nat m) (int_of_nat n));;

let rec int_shr_u_i32
  (Abs_i32 x) (Abs_i32 y) =
    Abs_i32
      (shiftr
        (semiring_bit_syntax_word
          (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
        x (and_nat
            (the_nat
              (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))) y)
            (nat_of_integer (Z.of_int 31))));;

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

let rec signed_drop_bit _A
  n w = Word (take_bit_int (len_of _A.len0_len Type)
               (drop_bit_int n (the_signed_int _A w)));;

let rec sshiftr _A w n = signed_drop_bit _A n w;;

let rec int_shr_s_i32
  (Abs_i32 x) (Abs_i32 y) =
    Abs_i32
      (sshiftr (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))) x
        (and_nat
          (the_nat
            (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))) y)
          (nat_of_integer (Z.of_int 31))));;

let rec int_rem_u_i32
  (Abs_i32 x) (Abs_i32 y) =
    (if equal_word
          (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))) y
          (zero_worda
            (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
      then None
      else Some (Abs_i32
                  (modulo_worda
                    (len_bit0
                      (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
                    x y)));;

let rec sgn_int
  i = (if equal_inta i Zero_int then Zero_int
        else (if less_int Zero_int i then one_inta else uminus_inta one_inta));;

let rec abs_int i = (if less_int i Zero_int then uminus_inta i else i);;

let rec signed_divide_int
  k l = times_inta (times_inta (sgn_int k) (sgn_int l))
          (divide_inta (abs_int k) (abs_int l));;

let rec signed_modulo_int
  k l = minus_inta k (times_inta (signed_divide_int k l) l);;

let rec signed_modulo_word _A
  v w = of_int _A
          (signed_modulo_int (the_signed_int _A v) (the_signed_int _A w));;

let rec int_rem_s_i32
  (Abs_i32 x) (Abs_i32 y) =
    (if equal_word
          (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))) y
          (zero_worda
            (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
      then None
      else Some (Abs_i32
                  (signed_modulo_word
                    (len_bit0
                      (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
                    x y)));;

let rec int_div_u_i32
  (Abs_i32 x) (Abs_i32 y) =
    (if equal_word
          (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))) y
          (zero_worda
            (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
      then None
      else Some (Abs_i32
                  (divide_worda
                    (len_bit0
                      (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
                    x y)));;

let rec signed_divide_word _A
  v w = of_int _A
          (signed_divide_int (the_signed_int _A v) (the_signed_int _A w));;

let rec int_div_s_i32
  (Abs_i32 x) (Abs_i32 y) =
    (if equal_word
          (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))) y
          (zero_worda
            (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))) ||
          equal_word
            (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))) x
            (of_int
              (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
              (uminus_inta
                (power power_int (Pos (Bit0 One))
                  (minus_nat (len_of_i32 Type) one_nata)))) &&
            equal_word
              (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))) y
              (of_int
                (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
                (uminus_inta one_inta))
      then None
      else Some (Abs_i32
                  (signed_divide_word
                    (len_bit0
                      (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
                    x y)));;

let rec modulo_integer k l = snd (divmod_integer k l);;

let rec modulo_nat
  m n = Nat (modulo_integer (integer_of_nat m) (integer_of_nat n));;

let rec concat_bit n k l = or_int (take_bit_int n k) (push_bit_int n l);;

let rec word_rotr _A
  n w = Word (concat_bit
               (minus_nat (len_of _A.len0_len Type)
                 (modulo_nat n (len_of _A.len0_len Type)))
               (drop_bit_int (modulo_nat n (len_of _A.len0_len Type))
                 (the_int _A w))
               (the_int _A
                 (take_bit_word _A (modulo_nat n (len_of _A.len0_len Type))
                   w)));;

let rec int_rotr_i32
  (Abs_i32 x) (Abs_i32 y) =
    Abs_i32
      (word_rotr (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
        (the_nat (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
          y)
        x);;

let rec word_rotl _A
  n = word_rotr _A
        (minus_nat (len_of _A.len0_len Type)
          (modulo_nat n (len_of _A.len0_len Type)));;

let rec int_rotl_i32
  (Abs_i32 x) (Abs_i32 y) =
    Abs_i32
      (word_rotl (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
        (the_nat (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
          y)
        x);;

let rec less_word _A a b = less_int (the_int _A a) (the_int _A b);;

let rec int_lt_u_i32
  (Abs_i32 x) (Abs_i32 y) =
    less_word (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))) x
      y;;

let rec word_sless _A
  a b = less_int (the_signed_int _A a) (the_signed_int _A b);;

let rec int_lt_s_i32
  (Abs_i32 x) (Abs_i32 y) =
    word_sless (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))) x
      y;;

let rec less_eq_word _A a b = less_eq_int (the_int _A a) (the_int _A b);;

let rec int_le_u_i32
  (Abs_i32 x) (Abs_i32 y) =
    less_eq_word (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
      x y;;

let rec word_sle _A
  a b = less_eq_int (the_signed_int _A a) (the_signed_int _A b);;

let rec int_le_s_i32
  (Abs_i32 x) (Abs_i32 y) =
    word_sle (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))) x
      y;;

let rec int_gt_u_i32
  (Abs_i32 x) (Abs_i32 y) =
    less_word (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))) y
      x;;

let rec int_gt_s_i32
  (Abs_i32 x) (Abs_i32 y) =
    word_sless (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))) y
      x;;

let rec int_ge_u_i32
  (Abs_i32 x) (Abs_i32 y) =
    less_eq_word (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
      y x;;

let rec int_ge_s_i32
  (Abs_i32 x) (Abs_i32 y) =
    word_sle (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))) y
      x;;

let rec xor_word _A v w = Word (xor_int (the_int _A v) (the_int _A w));;

let rec int_xor_i32
  (Abs_i32 x) (Abs_i32 y) =
    Abs_i32
      (xor_word (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
        x y);;

let rec int_sub_i32
  (Abs_i32 x) (Abs_i32 y) =
    Abs_i32
      (minus_worda
        (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))) x y);;

let rec shiftl _A
  a n = push_bit _A.semiring_bit_shifts_semiring_bit_syntax n a;;

let rec int_shl_i32
  (Abs_i32 x) (Abs_i32 y) =
    Abs_i32
      (shiftl
        (semiring_bit_syntax_word
          (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
        x (and_nat
            (the_nat
              (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))) y)
            (nat_of_integer (Z.of_int 31))));;

let rec int_mul_i32
  (Abs_i32 x) (Abs_i32 y) =
    Abs_i32
      (times_worda
        (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))) x y);;

let rec int_eqz_i32
  (Abs_i32 x) =
    equal_word (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))) x
      (zero_worda
        (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))));;

let rec takeWhile p x1 = match p, x1 with p, [] -> []
                    | p, x :: xs -> (if p x then x :: takeWhile p xs else []);;

let rec word_ctz _A w = size_list (takeWhile not (rev (to_bl _A w)));;

let rec int_ctz_i32
  (Abs_i32 x) =
    Abs_i32
      (of_nat (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
        (word_ctz
          (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))) x));;

let rec word_clz _A w = size_list (takeWhile not (to_bl _A w));;

let rec int_clz_i32
  (Abs_i32 x) =
    Abs_i32
      (of_nat (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
        (word_clz
          (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))) x));;

let rec int_and_i32
  (Abs_i32 x) (Abs_i32 y) =
    Abs_i32
      (and_word (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
        x y);;

let rec int_add_i32
  (Abs_i32 x) (Abs_i32 y) =
    Abs_i32
      (plus_worda
        (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))) x y);;

let rec or_word _A v w = Word (or_int (the_int _A v) (the_int _A w));;

let rec int_or_i32
  (Abs_i32 x) (Abs_i32 y) =
    Abs_i32
      (or_word (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))) x
        y);;

let rec int_eq_i32
  (Abs_i32 x) (Abs_i32 y) =
    equal_word (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))) x
      y;;

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

type i64 = Abs_i64 of num1 bit0 bit0 bit0 bit0 bit0 bit0 word;;

let zero_i64a : i64
  = Abs_i64
      (of_nat
        (len_bit0
          (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
        zero_nat);;

let zero_i64 = ({zero = zero_i64a} : i64 zero);;

let rec len_of_i64 uu = nat_of_integer (Z.of_int 64);;

let len0_i64 = ({len_of = len_of_i64} : i64 len0);;

let len_i64 = ({len0_len = len0_i64} : i64 len);;

let rec nat_of_int_i64
  (Abs_i64 x) =
    the_nat
      (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
      x;;

let rec int_popcnt_i64
  (Abs_i64 x) =
    Abs_i64
      (of_nat
        (len_bit0
          (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
        (pop_count
          (len_bit0
            (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
          x));;

let rec int_of_nat_i64
  x = Abs_i64
        (of_nat
          (len_bit0
            (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
          x);;

let rec int_shr_u_i64
  (Abs_i64 x) (Abs_i64 y) =
    Abs_i64
      (shiftr
        (semiring_bit_syntax_word
          (len_bit0
            (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))))
        x (and_nat
            (the_nat
              (len_bit0
                (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
              y)
            (nat_of_integer (Z.of_int 63))));;

let rec int_shr_s_i64
  (Abs_i64 x) (Abs_i64 y) =
    Abs_i64
      (sshiftr
        (len_bit0
          (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
        x (and_nat
            (the_nat
              (len_bit0
                (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
              y)
            (nat_of_integer (Z.of_int 63))));;

let rec int_rem_u_i64
  (Abs_i64 x) (Abs_i64 y) =
    (if equal_word
          (len_bit0
            (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
          y (zero_worda
              (len_bit0
                (len_bit0
                  (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))))
      then None
      else Some (Abs_i64
                  (modulo_worda
                    (len_bit0
                      (len_bit0
                        (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                    x y)));;

let rec int_rem_s_i64
  (Abs_i64 x) (Abs_i64 y) =
    (if equal_word
          (len_bit0
            (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
          y (zero_worda
              (len_bit0
                (len_bit0
                  (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))))
      then None
      else Some (Abs_i64
                  (signed_modulo_word
                    (len_bit0
                      (len_bit0
                        (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                    x y)));;

let rec int_div_u_i64
  (Abs_i64 x) (Abs_i64 y) =
    (if equal_word
          (len_bit0
            (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
          y (zero_worda
              (len_bit0
                (len_bit0
                  (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))))
      then None
      else Some (Abs_i64
                  (divide_worda
                    (len_bit0
                      (len_bit0
                        (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                    x y)));;

let rec int_div_s_i64
  (Abs_i64 x) (Abs_i64 y) =
    (if equal_word
          (len_bit0
            (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
          y (zero_worda
              (len_bit0
                (len_bit0
                  (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))) ||
          equal_word
            (len_bit0
              (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
            x (of_int
                (len_bit0
                  (len_bit0
                    (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                (uminus_inta
                  (power power_int (Pos (Bit0 One))
                    (minus_nat (len_of_i64 Type) one_nata)))) &&
            equal_word
              (len_bit0
                (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
              y (of_int
                  (len_bit0
                    (len_bit0
                      (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                  (uminus_inta one_inta))
      then None
      else Some (Abs_i64
                  (signed_divide_word
                    (len_bit0
                      (len_bit0
                        (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                    x y)));;

let rec int_rotr_i64
  (Abs_i64 x) (Abs_i64 y) =
    Abs_i64
      (word_rotr
        (len_bit0
          (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
        (the_nat
          (len_bit0
            (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
          y)
        x);;

let rec int_rotl_i64
  (Abs_i64 x) (Abs_i64 y) =
    Abs_i64
      (word_rotl
        (len_bit0
          (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
        (the_nat
          (len_bit0
            (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
          y)
        x);;

let rec int_lt_u_i64
  (Abs_i64 x) (Abs_i64 y) =
    less_word
      (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
      x y;;

let rec int_lt_s_i64
  (Abs_i64 x) (Abs_i64 y) =
    word_sless
      (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
      x y;;

let rec int_le_u_i64
  (Abs_i64 x) (Abs_i64 y) =
    less_eq_word
      (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
      x y;;

let rec int_le_s_i64
  (Abs_i64 x) (Abs_i64 y) =
    word_sle
      (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
      x y;;

let rec int_gt_u_i64
  (Abs_i64 x) (Abs_i64 y) =
    less_word
      (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
      y x;;

let rec int_gt_s_i64
  (Abs_i64 x) (Abs_i64 y) =
    word_sless
      (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
      y x;;

let rec int_ge_u_i64
  (Abs_i64 x) (Abs_i64 y) =
    less_eq_word
      (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
      y x;;

let rec int_ge_s_i64
  (Abs_i64 x) (Abs_i64 y) =
    word_sle
      (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
      y x;;

let rec int_xor_i64
  (Abs_i64 x) (Abs_i64 y) =
    Abs_i64
      (xor_word
        (len_bit0
          (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
        x y);;

let rec int_sub_i64
  (Abs_i64 x) (Abs_i64 y) =
    Abs_i64
      (minus_worda
        (len_bit0
          (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
        x y);;

let rec int_shl_i64
  (Abs_i64 x) (Abs_i64 y) =
    Abs_i64
      (shiftl
        (semiring_bit_syntax_word
          (len_bit0
            (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))))
        x (and_nat
            (the_nat
              (len_bit0
                (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
              y)
            (nat_of_integer (Z.of_int 63))));;

let rec int_mul_i64
  (Abs_i64 x) (Abs_i64 y) =
    Abs_i64
      (times_worda
        (len_bit0
          (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
        x y);;

let rec int_eqz_i64
  (Abs_i64 x) =
    equal_word
      (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
      x (zero_worda
          (len_bit0
            (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))));;

let rec int_ctz_i64
  (Abs_i64 x) =
    Abs_i64
      (of_nat
        (len_bit0
          (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
        (word_ctz
          (len_bit0
            (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
          x));;

let rec int_clz_i64
  (Abs_i64 x) =
    Abs_i64
      (of_nat
        (len_bit0
          (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
        (word_clz
          (len_bit0
            (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
          x));;

let rec int_and_i64
  (Abs_i64 x) (Abs_i64 y) =
    Abs_i64
      (and_word
        (len_bit0
          (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
        x y);;

let rec int_add_i64
  (Abs_i64 x) (Abs_i64 y) =
    Abs_i64
      (plus_worda
        (len_bit0
          (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
        x y);;

let rec int_or_i64
  (Abs_i64 x) (Abs_i64 y) =
    Abs_i64
      (or_word
        (len_bit0
          (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
        x y);;

let rec int_eq_i64
  (Abs_i64 x) (Abs_i64 y) =
    equal_word
      (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
      x y;;

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
  Inst_ext of tf list * nat list * nat list * nat list * nat list * 'a;;

type v = ConstInt32 of i32 | ConstInt64 of i64 | ConstFloat32 of F32Wrapper.t |
  ConstFloat64 of F64Wrapper.t;;

type 'a f_ext = F_ext of v list * unit inst_ext * 'a;;

type testop = Eqz;;

type relop_i = Eq | Ne | Lt of sx | Gt of sx | Le of sx | Ge of sx;;

type relop_f = Eqf | Nef | Ltf | Gtf | Lef | Gef;;

type relop = Relop_i of relop_i | Relop_f of relop_f;;

type unop_i = Clz | Ctz | Popcnt;;

type unop_f = Neg | Abs | Ceil | Floor | Trunc | Nearest | Sqrt;;

type unop = Unop_i of unop_i | Unop_f of unop_f;;

type tp = Tp_i8 | Tp_i16 | Tp_i32;;

type b_e = Unreachable | Nop | Drop | Select | Block of tf * b_e list |
  Loop of tf * b_e list | If of tf * b_e list * b_e list | Br of nat |
  Br_if of nat | Br_table of nat list * nat | Return | Call of nat |
  Call_indirect of nat | Get_local of nat | Set_local of nat | Tee_local of nat
  | Get_global of nat | Set_global of nat |
  Load of t * (tp * sx) option * nat * nat | Store of t * tp option * nat * nat
  | Current_memory | Grow_memory | EConst of v | Unop of t * unop |
  Binop of t * binop | Testop of t * testop | Relop of t * relop |
  Cvtop of t * cvtop * t * sx option;;

type e = Basic of b_e | Trap | Invoke of nat | Label of nat * e list * e list |
  Frame of nat * unit f_ext * e list;;

type 'a global_ext = Global_ext of mut * v * 'a;;

type byte = Abs_byte of num1 bit0 bit0 bit0 word;;

type mem_rep = Abs_mem_rep of byte list;;

type cl = Func_native of unit inst_ext * tf * t list * b_e list |
  Func_host of tf * host
and 'a s_ext =
  S_ext of
    cl list * ((nat option) list * nat option) list *
      (mem_rep * nat option) list * unit global_ext list * 'a
and host = Abs_host of (unit s_ext * v list -> (unit s_ext * v list) option);;

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

type 'a module_data_ext = Module_data_ext of nat * b_e list * byte list * 'a;;

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

type label_context = Label_context of v list * b_e list * nat * b_e list;;

type frame_context =
  Frame_context of redex * label_context list * nat * unit f_ext;;

type config = Config of nat * unit s_ext * frame_context * frame_context list;;

type res_step = Res_crash of res_error | Res_trap of string | Step_normal;;

type checker_type = TopType of ct list | Typea of t list | Bot;;

type 'a t_context_ext =
  T_context_ext of
    tf list * tf list * unit tg_ext list * unit limit_t_ext list *
      unit limit_t_ext list * t list * (t list) list * (t list) option * 'a;;

let rec comp f g = (fun x -> f (g x));;

let rec nth
  x0 n = match x0, n with [], n -> failwith "nth"
    | x :: xs, n ->
        (if equal_nat n zero_nat then x else nth xs (minus_nat n one_nata));;

let rec zip xs ys = match xs, ys with x :: xs, y :: ys -> (x, y) :: zip xs ys
              | xs, [] -> []
              | [], ys -> [];;

let rec drop
  n x1 = match n, x1 with n, [] -> []
    | n, x :: xs ->
        (if equal_nat n zero_nat then x :: xs
          else drop (minus_nat n one_nata) xs);;

let rec null = function [] -> true
               | x :: xs -> false;;

let rec last (x :: xs) = (if null xs then x else last xs);;

let rec take_tr
  n x1 acc_r = match n, x1, acc_r with n, [], acc_r -> rev acc_r
    | n, x :: xs, acc_r ->
        (if equal_nat n zero_nat then rev acc_r
          else take_tr (minus_nat n one_nata) xs (x :: acc_r));;

let rec take n xs = take_tr n xs [];;

let rec cast _B _A
  w = Word (take_bit_int (len_of _A.len0_len Type) (the_int _B w));;

let rec foldl f a x2 = match f, a, x2 with f, a, [] -> a
                | f, a, x :: xs -> foldl f (f a x) xs;;

let rec foldr f x1 = match f, x1 with f, [] -> id
                | f, x :: xs -> comp (f x) (foldr f xs);;

let rec map_option f x1 = match f, x1 with f, None -> None
                     | f, Some x2 -> Some (f x2);;

let rec those
  = function [] -> Some []
    | x :: xs ->
        (match x with None -> None
          | Some y -> map_option (fun a -> y :: a) (those xs));;

let rec distinct _A = function [] -> true
                      | x :: xs -> not (membera _A xs x) && distinct _A xs;;

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

let rec map_filter
  f x1 = match f, x1 with f, [] -> []
    | f, x :: xs ->
        (match f x with None -> map_filter f xs
          | Some y -> y :: map_filter f xs);;

let rec eval _A (Seq f) = memberb _A (f ())
and memberb _A xa0 x = match xa0, x with Empty, x -> false
                 | Insert (y, p), x -> eq _A x y || eval _A p x
                 | Join (p, xq), x -> eval _A p x || memberb _A xq x;;

let rec holds p = eval equal_unit p ();;

let rec divide_integer k l = fst (divmod_integer k l);;

let rec divide_nat
  m n = Nat (divide_integer (integer_of_nat m) (integer_of_nat n));;

let rec mem_rep_length (Abs_mem_rep x) = size_list x;;

let rec mem_length m = mem_rep_length (fst m);;

let rec mem_size m = divide_nat (mem_length m) ki64;;

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

let rec mem_max m = snd m;;

let rec mem_typing
  m mt = limits_compat (Limit_t_ext (mem_size m, mem_max m, ())) mt;;

let rec tab_typing
  t tt = limits_compat (Limit_t_ext (size_list (fst t), snd t, ())) tt;;

let rec bytes_replicate x = replicate x;;

let zero_byte : byte
  = Abs_byte (zero_worda (len_bit0 (len_bit0 (len_bit0 len_num1))));;

let rec mem_rep_mk
  x = Abs_mem_rep (bytes_replicate (times_nata x ki64) zero_byte);;

let rec mem_mk lim = (mem_rep_mk (l_min lim), l_max lim);;

let rec msbyte bs = last bs;;

let rec mems (S_ext (funcs, tabs, mems, globs, more)) = mems;;

let rec tabs (S_ext (funcs, tabs, mems, globs, more)) = tabs;;

let rec list_update
  x0 i y = match x0, i, y with [], i, y -> []
    | x :: xs, i, y ->
        (if equal_nat i zero_nat then y :: xs
          else x :: list_update xs (minus_nat i one_nata) y);;

let bot_pred : 'a pred = Seq (fun _ -> Empty);;

let rec single x = Seq (fun _ -> Insert (x, bot_pred));;

let rec typeof
  v = (match v with ConstInt32 _ -> T_i32 | ConstInt64 _ -> T_i64
        | ConstFloat32 _ -> T_f32 | ConstFloat64 _ -> T_f64);;

let rec g_val (Global_ext (g_mut, g_val, more)) = g_val;;

let rec g_mut (Global_ext (g_mut, g_val, more)) = g_mut;;

let rec tg_mut (Tg_ext (tg_mut, tg_t, more)) = tg_mut;;

let rec tg_t (Tg_ext (tg_mut, tg_t, more)) = tg_t;;

let rec glob_typing
  g tg =
    equal_muta (tg_mut tg) (g_mut g) && equal_ta (tg_t tg) (typeof (g_val g));;

let rec funcs (S_ext (funcs, tabs, mems, globs, more)) = funcs;;

let rec globs (S_ext (funcs, tabs, mems, globs, more)) = globs;;

let rec signed_cast _B _A
  w = Word (take_bit_int (len_of _A.len0_len Type) (the_signed_int _B w));;

let rec bin_sign
  k = (if less_eq_int Zero_int k then Zero_int else uminus_inta one_inta);;

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

let rec msb_word _A
  a = equal_inta
        (bin_sign
          (signed_take_bit ring_bit_operations_int
            (minus_nat (len_of _A.len0_len Type) one_nata) (the_int _A a)))
        (uminus_inta one_inta);;

let rec msb_byte
  (Abs_byte x) = msb_word (len_bit0 (len_bit0 (len_bit0 len_num1))) x;;

let rec bin_split
  n w = (if equal_nat n zero_nat then (w, Zero_int)
          else (let (w1, w2) =
                  bin_split (minus_nat n one_nata)
                    (divide_inta w (Pos (Bit0 One)))
                  in
                 (w1, plus_inta
                        (of_bool zero_neq_one_int
                          (not (dvd (equal_int, semidom_modulo_int)
                                 (Pos (Bit0 One)) w)))
                        (times_inta (Pos (Bit0 One)) w2))));;

let rec list_all p x1 = match p, x1 with p, [] -> true
                   | p, x :: xs -> p x && list_all p xs;;

let rec memsa (Inst_ext (types, funcs, tabs, mems, globs, more)) = mems;;

let rec tabsa (Inst_ext (types, funcs, tabs, mems, globs, more)) = tabs;;

let rec ocaml_int64_to_isabelle_int64
  n = int_of_nat_i64 (nat_of_integer (LibAux.z_of_uint64 n));;

let rec isabelle_i64_trunc_u_f64
  f = map_option ocaml_int64_to_isabelle_int64
        (I64Wrapper_convert.trunc_u_f64 f);;

let rec ui64_trunc_f64 x = isabelle_i64_trunc_u_f64 x;;

let rec isabelle_i64_trunc_u_f32
  f = map_option ocaml_int64_to_isabelle_int64
        (I64Wrapper_convert.trunc_u_f32 f);;

let rec ui64_trunc_f32 x = isabelle_i64_trunc_u_f32 x;;

let rec si64_trunc_f64 x = isabelle_i64_trunc_u_f64 x;;

let rec si64_trunc_f32 x = isabelle_i64_trunc_u_f32 x;;

let rec wasm_extend_u
  (Abs_i32 x) =
    Abs_i64
      (cast (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
        (len_bit0
          (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
        x);;

let rec wasm_extend_s
  (Abs_i32 x) =
    Abs_i64
      (signed_cast
        (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
        (len_bit0
          (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
        x);;

let rec cvt_i64
  sx v =
    (match v
      with ConstInt32 c ->
        (match sx with None -> None | Some S -> Some (wasm_extend_s c)
          | Some U -> Some (wasm_extend_u c))
      | ConstInt64 _ -> None
      | ConstFloat32 c ->
        (match sx with None -> None | Some S -> si64_trunc_f32 c
          | Some U -> ui64_trunc_f32 c)
      | ConstFloat64 c ->
        (match sx with None -> None | Some S -> si64_trunc_f64 c
          | Some U -> ui64_trunc_f64 c));;

let rec ocaml_int32_to_isabelle_int32
  n = int_of_nat_i32 (nat_of_integer (LibAux.z_of_uint32 n));;

let rec isabelle_i32_trunc_u_f64
  f = map_option ocaml_int32_to_isabelle_int32
        (I32Wrapper_convert.trunc_u_f64 f);;

let rec ui32_trunc_f64 x = isabelle_i32_trunc_u_f64 x;;

let rec isabelle_i32_trunc_u_f32
  f = map_option ocaml_int32_to_isabelle_int32
        (I32Wrapper_convert.trunc_u_f32 f);;

let rec ui32_trunc_f32 x = isabelle_i32_trunc_u_f32 x;;

let rec si32_trunc_f64 x = isabelle_i32_trunc_u_f64 x;;

let rec si32_trunc_f32 x = isabelle_i32_trunc_u_f32 x;;

let rec wasm_wrap
  (Abs_i64 x) =
    Abs_i32
      (cast (len_bit0
              (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
        (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))) x);;

let rec cvt_i32
  sx v =
    (match v with ConstInt32 _ -> None | ConstInt64 c -> Some (wasm_wrap c)
      | ConstFloat32 c ->
        (match sx with None -> None | Some S -> si32_trunc_f32 c
          | Some U -> ui32_trunc_f32 c)
      | ConstFloat64 c ->
        (match sx with None -> None | Some S -> si32_trunc_f64 c
          | Some U -> ui32_trunc_f64 c));;

let rec isabelle_int64_to_ocaml_int64
  n = LibAux.uint64_of_z (integer_of_nat (nat_of_int_i64 n));;

let rec f64_convert_u_isabelle_i64
  i = F64Wrapper_convert.convert_u_i64 (isabelle_int64_to_ocaml_int64 i);;

let rec f64_convert_ui64 x = f64_convert_u_isabelle_i64 x;;

let rec isabelle_int32_to_ocaml_int32
  n = LibAux.uint32_of_z (integer_of_nat (nat_of_int_i32 n));;

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
  sx v =
    (match v
      with ConstInt32 c ->
        (match sx with None -> None | Some S -> Some (f64_convert_si32 c)
          | Some U -> Some (f64_convert_ui32 c))
      | ConstInt64 c ->
        (match sx with None -> None | Some S -> Some (f64_convert_si64 c)
          | Some U -> Some (f64_convert_ui64 c))
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
  sx v =
    (match v
      with ConstInt32 c ->
        (match sx with None -> None | Some S -> Some (f32_convert_si32 c)
          | Some U -> Some (f32_convert_ui32 c))
      | ConstInt64 c ->
        (match sx with None -> None | Some S -> Some (f32_convert_si64 c)
          | Some U -> Some (f32_convert_ui64 c))
      | ConstFloat32 _ -> None
      | ConstFloat64 c -> Some ((F32Wrapper_convert.demote_f64) c));;

let rec cvt
  t sx v =
    (match t
      with T_i32 ->
        (match cvt_i32 sx v with None -> None | Some c -> Some (ConstInt32 c))
      | T_i64 ->
        (match cvt_i64 sx v with None -> None | Some c -> Some (ConstInt64 c))
      | T_f32 ->
        (match cvt_f32 sx v with None -> None | Some c -> Some (ConstFloat32 c))
      | T_f64 ->
        (match cvt_f64 sx v with None -> None
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
        then consume (Typea ts) [TAny; TSome T_i32] else Bot)
    | TopType ts ->
        (if equal_nat (size_list ts) zero_nat then TopType [TAny]
          else (if equal_nat (minus_nat (size_list ts) one_nata) zero_nat
                 then type_update (TopType ts) [TSome T_i32] (TopType [TAny])
                 else (if equal_nat
                            (minus_nat (minus_nat (size_list ts) one_nata)
                              one_nata)
                            zero_nat
                        then consume (TopType ts) [TSome T_i32]
                        else type_update (TopType ts) [TAny; TAny; TSome T_i32]
                               (select_return_top ts
                                 (nth ts
                                   (minus_nat (size_list ts)
                                     (nat_of_integer (Z.of_int 2))))
                                 (nth ts
                                   (minus_nat (size_list ts)
                                     (nat_of_integer (Z.of_int 3))))))))
    | Bot -> Bot;;

let rec tp_length
  tp = (match tp with Tp_i8 -> one_nata | Tp_i16 -> nat_of_integer (Z.of_int 2)
         | Tp_i32 -> nat_of_integer (Z.of_int 4));;

let rec t_length
  t = (match t with T_i32 -> nat_of_integer (Z.of_int 4)
        | T_i64 -> nat_of_integer (Z.of_int 8)
        | T_f32 -> nat_of_integer (Z.of_int 4)
        | T_f64 -> nat_of_integer (Z.of_int 8));;

let rec is_int_t
  t = (match t with T_i32 -> true | T_i64 -> true | T_f32 -> false
        | T_f64 -> false);;

let rec load_store_t_bounds
  a tp t =
    (match tp
      with None ->
        less_eq_nat (power power_nat (nat_of_integer (Z.of_int 2)) a)
          (t_length t)
      | Some tpa ->
        less_eq_nat (power power_nat (nat_of_integer (Z.of_int 2)) a)
          (tp_length tpa) &&
          (less_nat (tp_length tpa) (t_length t) && is_int_t t));;

let rec label_update
  labela
    (T_context_ext
      (types_t, func_t, global, table, memory, local, label, return, more))
    = T_context_ext
        (types_t, func_t, global, table, memory, local, labela label, return,
          more);;

let rec c_types_agree
  x0 ts = match x0, ts with Typea tsa, ts -> equal_list equal_t tsa ts
    | TopType tsa, ts -> ct_suffix tsa (to_ct_list ts)
    | Bot, uu -> false;;

let rec is_float_t
  t = (match t with T_i32 -> false | T_i64 -> false | T_f32 -> true
        | T_f64 -> true);;

let rec relop_t_agree
  relop t =
    (match relop with Relop_i _ -> is_int_t t | Relop_f _ -> is_float_t t);;

let rec binop_t_agree
  binop t =
    (match binop with Binop_i _ -> is_int_t t | Binop_f _ -> is_float_t t);;

let rec unop_t_agree
  unop t = (match unop with Unop_i _ -> is_int_t t | Unop_f _ -> is_float_t t);;

let rec option_projl x = map_option fst x;;

let rec types_t
  (T_context_ext
    (types_t, func_t, global, table, memory, local, label, return, more))
    = types_t;;

let rec equal_bool p pa = match p, pa with p, true -> p
                     | p, false -> not p
                     | true, p -> p
                     | false, p -> not p;;

let rec convert_cond
  t1 t2 sx =
    not (equal_ta t1 t2) &&
      equal_bool (is_none sx)
        (is_float_t t1 && is_float_t t2 ||
          is_int_t t1 &&
            (is_int_t t2 && less_nat (t_length t1) (t_length t2)));;

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
        (if unop_t_agree op t then type_update ts [TSome t] (Typea [t])
          else Bot)
    | c, Binop (t, op), ts ->
        (if binop_t_agree op t
          then type_update ts [TSome t; TSome t] (Typea [t]) else Bot)
    | c, Testop (t, uu), ts ->
        (if is_int_t t then type_update ts [TSome t] (Typea [T_i32]) else Bot)
    | c, Relop (t, op), ts ->
        (if relop_t_agree op t
          then type_update ts [TSome t; TSome t] (Typea [T_i32]) else Bot)
    | c, Cvtop (t1, Convert, t2, sx), ts ->
        (if convert_cond t1 t2 sx then type_update ts [TSome t2] (Typea [t1])
          else Bot)
    | c, Cvtop (t1, Reinterpret, t2, sx), ts ->
        (if not (equal_ta t1 t2) &&
              (equal_nat (t_length t1) (t_length t2) && is_none sx)
          then type_update ts [TSome t2] (Typea [t1]) else Bot)
    | c, Unreachable, ts -> type_update ts [] (TopType [])
    | c, Nop, ts -> ts
    | c, Drop, ts -> type_update ts [TAny] (Typea [])
    | c, Select, ts -> type_update_select ts
    | c, Block (Tf (tn, tm), es), ts ->
        (if b_e_type_checker (label_update (fun _ -> [tm] @ label c) c) es
              (Tf (tn, tm))
          then type_update ts (to_ct_list tn) (Typea tm) else Bot)
    | c, Loop (Tf (tn, tm), es), ts ->
        (if b_e_type_checker (label_update (fun _ -> [tn] @ label c) c) es
              (Tf (tn, tm))
          then type_update ts (to_ct_list tn) (Typea tm) else Bot)
    | c, If (Tf (tn, tm), es1, es2), ts ->
        (if b_e_type_checker (label_update (fun _ -> [tm] @ label c) c) es1
              (Tf (tn, tm)) &&
              b_e_type_checker (label_update (fun _ -> [tm] @ label c) c) es2
                (Tf (tn, tm))
          then type_update ts (to_ct_list (tn @ [T_i32])) (Typea tm) else Bot)
    | c, Br i, ts ->
        (if less_nat i (size_list (label c))
          then type_update ts (to_ct_list (nth (label c) i)) (TopType [])
          else Bot)
    | c, Br_if i, ts ->
        (if less_nat i (size_list (label c))
          then type_update ts (to_ct_list (nth (label c) i @ [T_i32]))
                 (Typea (nth (label c) i))
          else Bot)
    | c, Br_table (is, i), ts ->
        (match same_lab (is @ [i]) (label c) with None -> Bot
          | Some tls ->
            type_update ts (to_ct_list (tls @ [T_i32])) (TopType []))
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
                 type_update ts (to_ct_list (tn @ [T_i32])) (Typea tm))
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
          then type_update ts [TSome T_i32] (Typea [t]) else Bot)
    | c, Store (t, tp, a, off), ts ->
        (if less_eq_nat one_nata (size_list (memory c)) &&
              load_store_t_bounds a tp t
          then type_update ts [TSome T_i32; TSome t] (Typea []) else Bot)
    | c, Current_memory, ts ->
        (if less_eq_nat one_nata (size_list (memory c))
          then type_update ts [] (Typea [T_i32]) else Bot)
    | c, Grow_memory, ts ->
        (if less_eq_nat one_nata (size_list (memory c))
          then type_update ts [TSome T_i32] (Typea [T_i32]) else Bot);;

let rec eq_i_i _A
  xa xb =
    bind (single (xa, xb))
      (fun (x, xaa) -> (if eq _A x xaa then single () else bot_pred));;

let rec list_all2
  p xs ys = match p, xs, ys with
    p, x :: xs, y :: ys -> p x y && list_all2 p xs ys
    | p, xs, [] -> null xs
    | p, [], ys -> null ys;;

let rec funcsa (Inst_ext (types, funcs, tabs, mems, globs, more)) = funcs;;

let rec globsa (Inst_ext (types, funcs, tabs, mems, globs, more)) = globs;;

let rec types (Inst_ext (types, funcs, tabs, mems, globs, more)) = types;;

let rec app_rev_tr x0 ys = match x0, ys with [], ys -> ys
                     | x :: xs, ys -> app_rev_tr xs (x :: ys);;

let rec mem_rep_append
  (Abs_mem_rep m) n b = Abs_mem_rep (app_rev_tr (rev m) (replicate n b));;

let rec mem_append m n b = (mem_rep_append (fst m) n b, snd m);;

let rec mem_rep_read_bytes (Abs_mem_rep x) = (fun n l -> take l (drop n x));;

let rec read_bytes m n l = mem_rep_read_bytes (fst m) n l;;

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
  (Abs_i64 x) =
    map (fun a -> Abs_byte a)
      (word_rsplit_rev
        (len_bit0
          (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
        (len_bit0 (len_bit0 (len_bit0 len_num1))) x);;

let rec serialise_i32
  (Abs_i32 x) =
    map (fun a -> Abs_byte a)
      (word_rsplit_rev
        (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
        (len_bit0 (len_bit0 (len_bit0 len_num1))) x);;

let rec byte_of_nat
  x = Abs_byte (of_nat (len_bit0 (len_bit0 (len_bit0 len_num1))) x);;

let rec ocaml_char_to_isabelle_byte
  n = byte_of_nat (nat_of_integer (LibAux.z_of_char n));;

let rec f64_serialise_isabelle_bytes
  f = map ocaml_char_to_isabelle_byte (ImplWrapper.serialise_f64 f);;

let rec serialise_f64 x = f64_serialise_isabelle_bytes x;;

let rec f32_serialise_isabelle_bytes
  f = map ocaml_char_to_isabelle_byte (ImplWrapper.serialise_f32 f);;

let rec serialise_f32 x = f32_serialise_isabelle_bytes x;;

let rec bits
  v = (match v with ConstInt32 a -> serialise_i32 a
        | ConstInt64 a -> serialise_i64 a | ConstFloat32 a -> serialise_f32 a
        | ConstFloat64 a -> serialise_f64 a);;

let rec load
  m n off l =
    (if less_eq_nat (plus_nat (plus_nat n off) l) (mem_length m)
      then Some (read_bytes m (plus_nat n off) l) else None);;

let rec nat_of_byte
  (Abs_byte x) = the_nat (len_bit0 (len_bit0 (len_bit0 len_num1))) x;;

let rec uminus_word _A a = of_int _A (uminus_inta (the_int _A a));;

let negone_byte : byte
  = Abs_byte
      (uminus_word (len_bit0 (len_bit0 (len_bit0 len_num1)))
        (one_worda (len_bit0 (len_bit0 (len_bit0 len_num1)))));;

let rec mem_rep_write_bytes
  (Abs_mem_rep xb) xa x =
    Abs_mem_rep (take xa xb @ x @ drop (plus_nat xa (size_list x)) xb);;

let rec write_bytes m n bs = (mem_rep_write_bytes (fst m) n bs, snd m);;

let rec takefill
  fill n xs =
    (if equal_nat n zero_nat then []
      else (match xs with [] -> fill :: takefill fill (minus_nat n one_nata) xs
             | y :: ys -> y :: takefill fill (minus_nat n one_nata) ys));;

let rec bytes_takefill x = takefill x;;

let rec store
  m n off bs l =
    (if less_eq_nat (plus_nat (plus_nat n off) l) (mem_length m)
      then Some (write_bytes m (plus_nat n off) (bytes_takefill zero_byte l bs))
      else None);;

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

let rec stypes i j = nth (types i) j;;

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

let rec rep_byte (Abs_byte y) = y;;

let rec mems_update
  memsa (S_ext (funcs, tabs, mems, globs, more)) =
    S_ext (funcs, tabs, memsa mems, globs, more);;

let rec tabs_update
  tabsa (S_ext (funcs, tabs, mems, globs, more)) =
    S_ext (funcs, tabsa tabs, mems, globs, more);;

let rec bitzero
  t = (match t with T_i32 -> ConstInt32 zero_i32a
        | T_i64 -> ConstInt64 zero_i64a | T_f32 -> ConstFloat32 F32Wrapper.zero
        | T_f64 -> ConstFloat64 F64Wrapper.zero);;

let rec cl_type
  cl = (match cl with Func_native (_, tf, _, _) -> tf
         | Func_host (tf, _) -> tf);;

let rec n_zeros ts = map bitzero ts;;

let rec update_redex_return
  (Redex (v_sa, es, b_es)) v_s = Redex (v_s @ v_sa, es, b_es);;

let rec update_fc_return
  (Frame_context (rdx, lcs, nf, f)) v_s =
    Frame_context (update_redex_return rdx v_s, lcs, nf, f);;

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
    | v_s, Current_memory :: va -> (v_s, Current_memory :: va)
    | v_s, Grow_memory :: va -> (v_s, Grow_memory :: va)
    | v_s, Unop (vb, vc) :: va -> (v_s, Unop (vb, vc) :: va)
    | v_s, Binop (vb, vc) :: va -> (v_s, Binop (vb, vc) :: va)
    | v_s, Testop (vb, vc) :: va -> (v_s, Testop (vb, vc) :: va)
    | v_s, Relop (vb, vc) :: va -> (v_s, Relop (vb, vc) :: va)
    | v_s, Cvtop (vb, vc, vd, ve) :: va -> (v_s, Cvtop (vb, vc, vd, ve) :: va);;

let rec split_v_s_b_s es = split_v_s_b_s_aux [] es;;

let crash_invalid : res_step
  = Res_crash (Error_invalid "type system violation");;

let rec store_packed x = store x;;

let rec types_agree t v = equal_ta (typeof v) t;;

let rec smem_ind i = (match memsa i with [] -> None | n :: _ -> Some n);;

let rec app_s_f_v_s_store_packed
  t tp off ms f v_s =
    (let i = f_inst f in
      (match v_s with [] -> (ms, (v_s, crash_invalid))
        | [_] -> (ms, (v_s, crash_invalid))
        | v :: ConstInt32 c :: v_sa ->
          (if types_agree t v
            then (match smem_ind i with None -> (ms, (v_s, crash_invalid))
                   | Some j ->
                     (match
                       store_packed (nth ms j) (nat_of_int_i32 c) off (bits v)
                         (tp_length tp)
                       with None -> (ms, (v_sa, Res_trap "store"))
                       | Some a -> (list_update ms j a, (v_sa, Step_normal))))
            else (ms, (v_s, crash_invalid)))
        | _ :: ConstInt64 _ :: _ -> (ms, (v_s, crash_invalid))
        | _ :: ConstFloat32 _ :: _ -> (ms, (v_s, crash_invalid))
        | _ :: ConstFloat64 _ :: _ -> (ms, (v_s, crash_invalid))));;

let rec app_s_f_v_s_store
  t off ms f v_s =
    (let i = f_inst f in
      (match v_s with [] -> (ms, (v_s, crash_invalid))
        | [_] -> (ms, (v_s, crash_invalid))
        | v :: ConstInt32 c :: v_sa ->
          (if types_agree t v
            then (match smem_ind i with None -> (ms, (v_s, crash_invalid))
                   | Some j ->
                     (match
                       store (nth ms j) (nat_of_int_i32 c) off (bits v)
                         (t_length t)
                       with None -> (ms, (v_sa, Res_trap "store"))
                       | Some a -> (list_update ms j a, (v_sa, Step_normal))))
            else (ms, (v_s, crash_invalid)))
        | _ :: ConstInt64 _ :: _ -> (ms, (v_s, crash_invalid))
        | _ :: ConstFloat32 _ :: _ -> (ms, (v_s, crash_invalid))
        | _ :: ConstFloat64 _ :: _ -> (ms, (v_s, crash_invalid))));;

let rec app_s_f_v_s_store_maybe_packed
  t tp_opt off ms f v_s =
    (match tp_opt with None -> app_s_f_v_s_store t off ms f v_s
      | Some tp -> app_s_f_v_s_store_packed t tp off ms f v_s);;

let rec horner_sum _B
  f a xs =
    foldr (fun x b ->
            plus _B.semiring_0_comm_semiring_0.comm_monoid_add_semiring_0.monoid_add_comm_monoid_add.semigroup_add_monoid_add.plus_semigroup_add
              (f x)
              (times
                _B.semiring_0_comm_semiring_0.mult_zero_semiring_0.times_mult_zero
                a b))
      xs (zero _B.semiring_0_comm_semiring_0.mult_zero_semiring_0.zero_mult_zero);;

let rec word_rcat_rev _A _B
  = comp (of_int _B)
      (horner_sum comm_semiring_0_int (the_int _A)
        (power power_int (Pos (Bit0 One)) (len_of _A.len0_len Type)));;

let rec deserialise_i64_aux
  x = Abs_i64
        (word_rcat_rev (len_bit0 (len_bit0 (len_bit0 len_num1)))
          (len_bit0
            (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
          x);;

let rec deserialise_i64 xa = deserialise_i64_aux (map rep_byte xa);;

let rec deserialise_i32_aux
  x = Abs_i32
        (word_rcat_rev (len_bit0 (len_bit0 (len_bit0 len_num1)))
          (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))) x);;

let rec deserialise_i32 xa = deserialise_i32_aux (map rep_byte xa);;

let rec isabelle_byte_to_ocaml_char
  n = LibAux.char_of_z (integer_of_nat (nat_of_byte n));;

let rec f64_deserialise_isabelle_bytes
  bs = ImplWrapper.deserialise_f64 (map isabelle_byte_to_ocaml_char bs);;

let rec deserialise_f64 x = f64_deserialise_isabelle_bytes x;;

let rec f32_deserialise_isabelle_bytes
  bs = ImplWrapper.deserialise_f32 (map isabelle_byte_to_ocaml_char bs);;

let rec deserialise_f32 x = f32_deserialise_isabelle_bytes x;;

let rec wasm_deserialise
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

let rec load_packed
  sx m n off lp l = map_option (sign_extend sx l) (load m n off lp);;

let rec app_s_f_v_s_load_packed
  t tp sx off ms f v_s =
    (let i = f_inst f in
      (match v_s with [] -> (v_s, crash_invalid)
        | ConstInt32 c :: v_sa ->
          (match smem_ind i with None -> (v_s, crash_invalid)
            | Some j ->
              (match
                load_packed sx (nth ms j) (nat_of_int_i32 c) off (tp_length tp)
                  (t_length t)
                with None -> (v_sa, Res_trap "load")
                | Some a -> (wasm_deserialise a t :: v_sa, Step_normal)))
        | ConstInt64 _ :: _ -> (v_s, crash_invalid)
        | ConstFloat32 _ :: _ -> (v_s, crash_invalid)
        | ConstFloat64 _ :: _ -> (v_s, crash_invalid)));;

let rec app_s_f_v_s_load
  t off ms f v_s =
    (let i = f_inst f in
      (match v_s with [] -> (v_s, crash_invalid)
        | ConstInt32 c :: v_sa ->
          (match smem_ind i with None -> (v_s, crash_invalid)
            | Some j ->
              (match load (nth ms j) (nat_of_int_i32 c) off (t_length t)
                with None -> (v_sa, Res_trap "load")
                | Some a -> (wasm_deserialise a t :: v_sa, Step_normal)))
        | ConstInt64 _ :: _ -> (v_s, crash_invalid)
        | ConstFloat32 _ :: _ -> (v_s, crash_invalid)
        | ConstFloat64 _ :: _ -> (v_s, crash_invalid)));;

let rec app_s_f_v_s_load_maybe_packed
  t tp_sx off ms f v_s =
    (match tp_sx with None -> app_s_f_v_s_load t off ms f v_s
      | Some (tp, sx) -> app_s_f_v_s_load_packed t tp sx off ms f v_s);;

let rec tab_cl_ind
  st i j =
    (let stabinst = fst (nth st i) in
      (if less_nat j (size_list stabinst) then nth stabinst j else None));;

let rec app_s_f_v_s_call_indirect
  k tinsts cls f v_s =
    (let i = f_inst f in
      (match v_s with [] -> (v_s, ([], crash_invalid))
        | ConstInt32 c :: v_sa ->
          (match tabsa i with [] -> (v_s, ([], crash_invalid))
            | j :: _ ->
              (match tab_cl_ind tinsts j (nat_of_int_i32 c)
                with None -> (v_sa, ([], Res_trap "call_indirect"))
                | Some i_cl ->
                  (if equal_tfa (stypes i k) (cl_type (nth cls i_cl))
                    then (v_sa, ([Invoke i_cl], Step_normal))
                    else (v_sa, ([], Res_trap "call_indirect")))))
        | ConstInt64 _ :: _ -> (v_s, ([], crash_invalid))
        | ConstFloat32 _ :: _ -> (v_s, ([], crash_invalid))
        | ConstFloat64 _ :: _ -> (v_s, ([], crash_invalid))));;

let rec g_val_update
  g_vala (Global_ext (g_mut, g_val, more)) =
    Global_ext (g_mut, g_vala g_val, more);;

let rec sglob_ind i j = nth (globsa i) j;;

let rec update_glob
  gs i j v =
    (let k = sglob_ind i j in
      list_update gs k (g_val_update (fun _ -> v) (nth gs k)));;

let rec app_s_f_v_s_set_global
  k gs f v_s =
    (match v_s with [] -> (gs, (v_s, crash_invalid))
      | v1 :: v_sa -> (update_glob gs (f_inst f) k v1, (v_sa, Step_normal)));;

let rec app_s_f_v_s_get_global
  k gs f v_s = (g_val (nth gs (sglob_ind (f_inst f) k)) :: v_s, Step_normal);;

let rec app_s_f_v_s_mem_size
  ms f v_s =
    (let i = f_inst f in
      (match smem_ind i with None -> (v_s, crash_invalid)
        | Some j ->
          (ConstInt32 (int_of_nat_i32 (mem_size (nth ms j))) :: v_s,
            Step_normal)));;

let int32_minus_one : i32
  = Abs_i32
      (uminus_word
        (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
        (one_worda
          (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))));;

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
        | ConstInt32 c :: v_sa ->
          (match smem_ind i with None -> (ms, (v_s, crash_invalid))
            | Some j ->
              (let l = mem_size (nth ms j) in
                (match mem_grow (nth ms j) (nat_of_int_i32 c)
                  with None ->
                    (ms, (ConstInt32 int32_minus_one :: v_sa, Step_normal))
                  | Some a ->
                    (list_update ms j a,
                      (ConstInt32 (int_of_nat_i32 l) :: v_sa, Step_normal)))))
        | ConstInt64 _ :: _ -> (ms, (v_s, crash_invalid))
        | ConstFloat32 _ :: _ -> (ms, (v_s, crash_invalid))
        | ConstFloat64 _ :: _ -> (ms, (v_s, crash_invalid))));;

let rec app_f_v_s_set_local
  k f v_s =
    (let locs = f_locs f in
      (match v_s with [] -> (f, (v_s, crash_invalid))
        | v1 :: v_sa ->
          (if less_nat k (size_list locs)
            then (F_ext (list_update locs k v1, f_inst f, ()),
                   (v_sa, Step_normal))
            else (f, (v_s, crash_invalid)))));;

let rec app_f_v_s_get_local
  k f v_s =
    (let locs = f_locs f in
      (if less_nat k (size_list locs) then (nth locs k :: v_s, Step_normal)
        else (v_s, crash_invalid)));;

let rec app_v_s_tee_local
  k v_s =
    (match v_s with [] -> (v_s, ([], crash_invalid))
      | v1 :: v_sa ->
        (v1 :: v1 :: v_sa, ([Basic (Set_local k)], Step_normal)));;

let rec app_v_s_br_table
  ks k v_s =
    (match v_s with [] -> (v_s, ([], crash_invalid))
      | ConstInt32 c :: v_sa ->
        (let j = nat_of_int_i32 c in
          (if less_nat j (size_list ks)
            then (v_sa, ([Basic (Br (nth ks j))], Step_normal))
            else (v_sa, ([Basic (Br k)], Step_normal))))
      | ConstInt64 _ :: _ -> (v_s, ([], crash_invalid))
      | ConstFloat32 _ :: _ -> (v_s, ([], crash_invalid))
      | ConstFloat64 _ :: _ -> (v_s, ([], crash_invalid)));;

let crash_invariant : res_step
  = Res_crash (Error_invariant "interpreter invariant violation");;

let rec update_redex_step
  (Redex (v_sa, es, b_es)) v_s es_cont = Redex (v_s, es_cont @ es, b_es);;

let rec update_fc_step
  (Frame_context (rdx, lcs, nf, f)) v_s es_cont =
    Frame_context (update_redex_step rdx v_s es_cont, lcs, nf, f);;

let rec app_testop_i _A
  testop c = (let Eqz = testop in int_eqz _A.wasm_int_ops_wasm_int c);;

let rec wasm_bool
  x = Abs_i32
        (if x then one_worda
                     (len_bit0
                       (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
          else zero_worda
                 (len_bit0
                   (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))));;

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
      | v1 :: v_sa -> (app_testop testop v1 :: v_sa, Step_normal));;

let rec app_v_s_select
  v_s = (match v_s with [] -> (v_s, crash_invalid)
          | [ConstInt32 _] -> (v_s, crash_invalid)
          | [ConstInt32 _; _] -> (v_s, crash_invalid)
          | ConstInt32 c :: v2 :: v1 :: v_sa ->
            (if int_eq_i32 c zero_i32a then (v2 :: v_sa, Step_normal)
              else (v1 :: v_sa, Step_normal))
          | ConstInt64 _ :: _ -> (v_s, crash_invalid)
          | ConstFloat32 _ :: _ -> (v_s, crash_invalid)
          | ConstFloat64 _ :: _ -> (v_s, crash_invalid));;

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
    (match v_s with [] -> (v_s, crash_invalid) | [_] -> (v_s, crash_invalid)
      | v2 :: v1 :: v_sa -> (app_relop relop v1 v2 :: v_sa, Step_normal));;

let rec app_v_s_cvtop
  cvtop t1 t2 sx v_s =
    (match v_s with [] -> (v_s, crash_invalid)
      | v1 :: v_sa ->
        (if types_agree t1 v1
          then (match cvtop
                 with Convert ->
                   (match cvt t2 sx v1
                     with None -> (v_sa, Res_trap (name typerep_cvtop cvtop))
                     | Some a -> (a :: v_sa, Step_normal))
                 | Reinterpret ->
                   (if is_none sx
                     then (wasm_deserialise (bits v1) t2 :: v_sa, Step_normal)
                     else (v_s, crash_invalid)))
          else (v_s, crash_invalid)));;

let rec app_v_s_br_if
  k v_s =
    (match v_s with [] -> (v_s, ([], crash_invalid))
      | ConstInt32 c :: v_sa ->
        (if int_eq_i32 c zero_i32a then (v_sa, ([], Step_normal))
          else (v_sa, ([Basic (Br k)], Step_normal)))
      | ConstInt64 _ :: _ -> (v_s, ([], crash_invalid))
      | ConstFloat32 _ :: _ -> (v_s, ([], crash_invalid))
      | ConstFloat64 _ :: _ -> (v_s, ([], crash_invalid)));;

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
    (match v_s with [] -> (v_s, crash_invalid) | [_] -> (v_s, crash_invalid)
      | v2 :: v1 :: v_sa ->
        (match app_binop binop v1 v2
          with None -> (v_sa, Res_trap (name typerep_binop binop))
          | Some a -> (a :: v_sa, Step_normal)));;

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

let rec app_unop
  uop v =
    (match uop with Unop_i iop -> app_unop_i_v iop v
      | Unop_f fop -> app_unop_f_v fop v);;

let rec app_v_s_unop
  unop v_s =
    (match v_s with [] -> (v_s, crash_invalid)
      | v1 :: v_sa -> (app_unop unop v1 :: v_sa, Step_normal));;

let rec app_v_s_drop
  v_s = (match v_s with [] -> (v_s, crash_invalid)
          | _ :: v_sa -> (v_sa, Step_normal));;

let rec app_v_s_if
  tf es1 es2 v_s =
    (match v_s with [] -> (v_s, ([], crash_invalid))
      | ConstInt32 c :: v_sa ->
        (if int_eq_i32 c zero_i32a
          then (v_sa, ([Basic (Block (tf, es2))], Step_normal))
          else (v_sa, ([Basic (Block (tf, es1))], Step_normal)))
      | ConstInt64 _ :: _ -> (v_s, ([], crash_invalid))
      | ConstFloat32 _ :: _ -> (v_s, ([], crash_invalid))
      | ConstFloat64 _ :: _ -> (v_s, ([], crash_invalid)));;

let rec sfunc_ind i j = nth (funcsa i) j;;

let rec app_f_call k f = ([Invoke (sfunc_ind (f_inst f) k)], Step_normal);;

let rec split_n
  x0 n = match x0, n with [], n -> ([], [])
    | v :: va, n ->
        (if equal_nat n zero_nat then ([], v :: va)
          else (let a = split_n va (minus_nat n one_nata) in
                let (es, aa) = a in
                 (v :: es, aa)));;

let rec globs_update
  globsa (S_ext (funcs, tabs, mems, globs, more)) =
    S_ext (funcs, tabs, mems, globsa globs, more);;

let rec run_step_b_e
  b_e (Config (d, s, fc, fcs)) =
    (let Frame_context (Redex (v_s, es, b_es), lcs, nf, f) = fc in
      (match b_e
        with Unreachable -> (Config (d, s, fc, fcs), Res_trap "unreachable")
        | Nop -> (Config (d, s, fc, fcs), Step_normal)
        | Drop ->
          (let a = app_v_s_drop v_s in
           let (v_sa, aa) = a in
            (Config (d, s, update_fc_step fc v_sa [], fcs), aa))
        | Select ->
          (let a = app_v_s_select v_s in
           let (v_sa, aa) = a in
            (Config (d, s, update_fc_step fc v_sa [], fcs), aa))
        | Block (Tf (t1s, t2s), b_ebs) ->
          (if not (null es) then (Config (d, s, fc, fcs), crash_invariant)
            else (let n = size_list t1s in
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
        | Loop (Tf (t1s, t2s), b_els) ->
          (if not (null es) then (Config (d, s, fc, fcs), crash_invariant)
            else (let n = size_list t1s in
                  let _ = size_list t2s in
                   (if less_eq_nat n (size_list v_s)
                     then (let (v_bs, v_sa) = split_n v_s n in
                           let lc =
                             Label_context
                               (v_sa, b_es, n, [Loop (Tf (t1s, t2s), b_els)])
                             in
                           let fca =
                             Frame_context
                               (Redex (v_bs, [], b_els), lc :: lcs, nf, f)
                             in
                            (Config (d, s, fca, fcs), Step_normal))
                     else (Config (d, s, fc, fcs), crash_invalid))))
        | If (tf, es1, es2) ->
          (let a = app_v_s_if tf es1 es2 v_s in
           let (v_sa, aa) = a in
           let (es_cont, ab) = aa in
            (Config (d, s, update_fc_step fc v_sa es_cont, fcs), ab))
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
          (let a = app_v_s_br_if k v_s in
           let (v_sa, aa) = a in
           let (es_cont, ab) = aa in
            (Config (d, s, update_fc_step fc v_sa es_cont, fcs), ab))
        | Br_table (ks, k) ->
          (let a = app_v_s_br_table ks k v_s in
           let (v_sa, aa) = a in
           let (es_cont, ab) = aa in
            (Config (d, s, update_fc_step fc v_sa es_cont, fcs), ab))
        | Return ->
          (match fcs with [] -> (Config (d, s, fc, fcs), crash_invalid)
            | fca :: fcsa ->
              (if less_eq_nat nf (size_list v_s)
                then (Config
                        (suc d, s, update_fc_return fca (take nf v_s), fcsa),
                       Step_normal)
                else (Config (d, s, fc, fcs), crash_invalid)))
        | Call k ->
          (let a = app_f_call k f in
           let (es_cont, aa) = a in
            (Config (d, s, update_fc_step fc v_s es_cont, fcs), aa))
        | Call_indirect k ->
          (let a = app_s_f_v_s_call_indirect k (tabs s) (funcs s) f v_s in
           let (v_sa, aa) = a in
           let (es_cont, ab) = aa in
            (Config (d, s, update_fc_step fc v_sa es_cont, fcs), ab))
        | Get_local k ->
          (let a = app_f_v_s_get_local k f v_s in
           let (v_sa, aa) = a in
            (Config (d, s, update_fc_step fc v_sa [], fcs), aa))
        | Set_local k ->
          (let (fa, (v_sa, res)) = app_f_v_s_set_local k f v_s in
           let fca = Frame_context (Redex (v_sa, es, b_es), lcs, nf, fa) in
            (Config (d, s, fca, fcs), res))
        | Tee_local k ->
          (let a = app_v_s_tee_local k v_s in
           let (v_sa, aa) = a in
           let (es_cont, ab) = aa in
            (Config (d, s, update_fc_step fc v_sa es_cont, fcs), ab))
        | Get_global k ->
          (let a = app_s_f_v_s_get_global k (globs s) f v_s in
           let (v_sa, aa) = a in
            (Config (d, s, update_fc_step fc v_sa [], fcs), aa))
        | Set_global k ->
          (let a = app_s_f_v_s_set_global k (globs s) f v_s in
           let (gs, aa) = a in
           let (v_sa, ab) = aa in
            (Config
               (d, globs_update (fun _ -> gs) s, update_fc_step fc v_sa [],
                 fcs),
              ab))
        | Load (t, tp_sx, _, off) ->
          (let a = app_s_f_v_s_load_maybe_packed t tp_sx off (mems s) f v_s in
           let (v_sa, aa) = a in
            (Config (d, s, update_fc_step fc v_sa [], fcs), aa))
        | Store (t, tp, _, off) ->
          (let a = app_s_f_v_s_store_maybe_packed t tp off (mems s) f v_s in
           let (ms, aa) = a in
           let (v_sa, ab) = aa in
            (Config
               (d, mems_update (fun _ -> ms) s, update_fc_step fc v_sa [], fcs),
              ab))
        | Current_memory ->
          (let a = app_s_f_v_s_mem_size (mems s) f v_s in
           let (v_sa, aa) = a in
            (Config (d, s, update_fc_step fc v_sa [], fcs), aa))
        | Grow_memory ->
          (let a = app_s_f_v_s_mem_grow (mems s) f v_s in
           let (ms, aa) = a in
           let (v_sa, ab) = aa in
            (Config
               (d, mems_update (fun _ -> ms) s, update_fc_step fc v_sa [], fcs),
              ab))
        | EConst _ -> (Config (d, s, fc, fcs), crash_invariant)
        | Unop (_, op) ->
          (let a = app_v_s_unop op v_s in
           let (v_sa, aa) = a in
            (Config (d, s, update_fc_step fc v_sa [], fcs), aa))
        | Binop (_, op) ->
          (let a = app_v_s_binop op v_s in
           let (v_sa, aa) = a in
            (Config (d, s, update_fc_step fc v_sa [], fcs), aa))
        | Testop (_, op) ->
          (let a = app_v_s_testop op v_s in
           let (v_sa, aa) = a in
            (Config (d, s, update_fc_step fc v_sa [], fcs), aa))
        | Relop (_, op) ->
          (let a = app_v_s_relop op v_s in
           let (v_sa, aa) = a in
            (Config (d, s, update_fc_step fc v_sa [], fcs), aa))
        | Cvtop (t2, op, t1, sx) ->
          (let a = app_v_s_cvtop op t1 t2 sx v_s in
           let (v_sa, aa) = a in
            (Config (d, s, update_fc_step fc v_sa [], fcs), aa))));;

let crash_exhaustion : res_step
  = Res_crash (Error_exhaustion "call stack exhausted");;

let rec rep_host (Abs_host x) = x;;

let rec host_apply_impl s tf h vs = rep_host h (s, vs);;

let rec run_step_e
  e (Config (d, s, fc, fcs)) =
    (let Frame_context (Redex (v_s, es, b_es), lcs, nf, f) = fc in
      (match e with Basic b_e -> run_step_b_e b_e (Config (d, s, fc, fcs))
        | Trap -> (Config (d, s, fc, fcs), crash_invariant)
        | Invoke i_cl ->
          (match nth (funcs s) i_cl
            with Func_native (i, Tf (t1s, t2s), ts, es_f) ->
              (if equal_nat d zero_nat
                then (Config (d, s, fc, fcs), crash_exhaustion)
                else (let n = size_list t1s in
                      let m = size_list t2s in
                       (if less_eq_nat n (size_list v_s)
                         then (let (v_fs, v_sa) = split_n v_s n in
                               let fca =
                                 Frame_context
                                   (Redex (v_sa, es, b_es), lcs, nf, f)
                                 in
                               let zs = n_zeros ts in
                               let ff = F_ext (rev v_fs @ zs, i, ()) in
                               let fcf =
                                 Frame_context
                                   (Redex ([], [],
    [Block (Tf ([], t2s), es_f)]),
                                     [], m, ff)
                                 in
                                (Config
                                   (minus_nat d one_nata, s, fcf, fca :: fcs),
                                  Step_normal))
                         else (Config (d, s, fc, fcs), crash_invalid))))
            | Func_host (Tf (t1s, t2s), h) ->
              (let n = size_list t1s in
               let _ = size_list t2s in
                (if less_eq_nat n (size_list v_s)
                  then (let (v_fs, v_sa) = split_n v_s n in
                         (match host_apply_impl s (Tf (t1s, t2s)) h (rev v_fs)
                           with None ->
                             (Config
                                (d, s,
                                  Frame_context
                                    (Redex (v_sa, es, b_es), lcs, nf, f),
                                  fcs),
                               Res_trap "host_apply")
                           | Some (sa, rvs) ->
                             (if list_all2 types_agree t2s rvs
                               then (let fca =
                                       Frame_context
 (Redex (rev rvs @ v_sa, es, b_es), lcs, nf, f)
                                       in
                                      (Config (d, sa, fca, fcs), Step_normal))
                               else (Config (d, sa, fc, fcs), crash_invalid))))
                  else (Config (d, s, fc, fcs), crash_invalid))))
        | Label (_, _, _) -> (Config (d, s, fc, fcs), crash_invariant)
        | Frame (_, _, _) -> (Config (d, s, fc, fcs), crash_invariant)));;

let rec run_iter
  n cfg =
    (if equal_nat n zero_nat then (cfg, res_crash_fuel)
      else (let Config
                  (d, s, Frame_context (Redex (v_s, es, b_es), lcs, nf, f), fcs)
              = cfg in
             (match es
               with [] ->
                 (match b_es
                   with [] ->
                     (match lcs
                       with [] ->
                         (match fcs
                           with [] ->
                             (Config
                                (d, s,
                                  Frame_context
                                    (Redex (v_s, [], []), [], nf, f),
                                  []),
                               RValue v_s)
                           | fc :: fcsa ->
                             run_iter (minus_nat n one_nata)
                               (Config
                                 (suc d, s, update_fc_return fc v_s, fcsa)))
                       | Label_context (v_ls, b_els, _, _) :: lcsa ->
                         (let f_new =
                            Frame_context
                              (Redex (v_s @ v_ls, [], b_els), lcsa, nf, f)
                            in
                           run_iter (minus_nat n one_nata)
                             (Config (d, s, f_new, fcs))))
                   | a :: lista ->
                     (match split_v_s_b_s (a :: lista)
                       with (v_sa, []) ->
                         run_iter (minus_nat n one_nata)
                           (Config
                             (d, s,
                               Frame_context
                                 (Redex (v_sa @ v_s, [], []), lcs, nf, f),
                               fcs))
                       | (v_sa, b_e :: b_esa) ->
                         (match
                           run_step_b_e b_e
                             (Config
                               (d, s,
                                 Frame_context
                                   (Redex (v_sa @ v_s, [], b_esa), lcs, nf, f),
                                 fcs))
                           with (cfga, Res_crash str) -> (cfga, RCrash str)
                           | (cfga, Res_trap str) -> (cfga, RTrap str)
                           | (cfga, Step_normal) ->
                             run_iter (minus_nat n one_nata) cfga)))
               | e :: esa ->
                 (match
                   run_step_e e
                     (Config
                       (d, s,
                         Frame_context (Redex (v_s, esa, b_es), lcs, nf, f),
                         fcs))
                   with (cfga, Res_crash str) -> (cfga, RCrash str)
                   | (cfga, Res_trap str) -> (cfga, RTrap str)
                   | (cfga, Step_normal) ->
                     run_iter (minus_nat n one_nata) cfga))));;

let rec run_v
  n d (s, (f, b_es)) =
    (let (Config (_, sa, _, _), res) =
       run_iter n
         (Config
           (d, s, Frame_context (Redex ([], [], b_es), [], zero_nat, f), []))
       in
      (sa, res));;

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
            | (_, Current_memory) -> bot_pred | (_, Grow_memory) -> bot_pred
            | (_, EConst _) -> single () | (_, Unop (_, _)) -> bot_pred
            | (_, Binop (_, _)) -> bot_pred | (_, Testop (_, _)) -> bot_pred
            | (_, Relop (_, _)) -> bot_pred
            | (_, Cvtop (_, _, _, _)) -> bot_pred)))
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
            | (_, Current_memory) -> bot_pred | (_, Grow_memory) -> bot_pred
            | (_, EConst _) -> bot_pred | (_, Unop (_, _)) -> bot_pred
            | (_, Binop (_, _)) -> bot_pred | (_, Testop (_, _)) -> bot_pred
            | (_, Relop (_, _)) -> bot_pred
            | (_, Cvtop (_, _, _, _)) -> bot_pred)));;

let rec const_expr x1 x2 = holds (const_expr_p x1 x2);;

let rec min _A a b = (if less_eq _A a b then a else b);;

let rec funcs_update
  funcsa (S_ext (funcs, tabs, mems, globs, more)) =
    S_ext (funcsa funcs, tabs, mems, globs, more);;

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

let rec d_init (Module_data_ext (d_data, d_off, d_init, more)) = d_init;;

let rec d_data (Module_data_ext (d_data, d_off, d_init, more)) = d_data;;

let rec init_mem
  s inst d_ind d =
    (let m_ind = nth (memsa inst) (d_data d) in
     let mem = nth (mems s) m_ind in
     let mema = write_bytes mem d_ind (d_init d) in
      mems_update (fun _ -> list_update (mems s) m_ind mema) s);;

let rec e_init (Module_elem_ext (e_tab, e_off, e_init, more)) = e_init;;

let rec e_tab (Module_elem_ext (e_tab, e_off, e_init, more)) = e_tab;;

let rec init_tab
  s inst e_ind e =
    (let t_ind = nth (tabsa inst) (e_tab e) in
     let (tab_e, max) = nth (tabs s) t_ind in
     let e_pay = map (fun i -> Some (nth (funcsa inst) i)) (e_init e) in
     let tab_ea =
       take e_ind tab_e @ e_pay @ drop (plus_nat e_ind (size_list e_pay)) tab_e
       in
      tabs_update (fun _ -> list_update (tabs s) t_ind (tab_ea, max)) s);;

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
                    bind (if_pred (tab_typing (nth (tabs s) i) tt))
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
                      bind (if_pred (mem_typing (nth (mems s) i) mt))
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
  s m_t =
    (tabs_update (fun _ -> tabs s @ [(replicate (l_min m_t) None, l_max m_t)])
       s,
      size_list (tabs s));;

let rec init_mems
  s inst d_inds ds =
    foldl (fun sa (a, b) -> init_mem sa inst a b) s (zip d_inds ds);;

let rec init_tabs
  s inst e_inds es =
    foldl (fun sa (a, b) -> init_tab sa inst a b) s (zip e_inds es);;

let empty_frame : unit f_ext
  = F_ext ([], Inst_ext ([], [], [], [], [], ()), ());;

let rec export_get_v_ext
  inst exp =
    (match exp with Ext_func i -> Ext_func (nth (funcsa inst) i)
      | Ext_tab i -> Ext_tab (nth (tabsa inst) i)
      | Ext_mem i -> Ext_mem (nth (memsa inst) i)
      | Ext_glob i -> Ext_glob (nth (globsa inst) i));;

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

let rec d_off (Module_data_ext (d_data, d_off, d_init, more)) = d_off;;

let rec e_off (Module_elem_ext (e_tab, e_off, e_init, more)) = e_off;;

let rec g_init (Module_glob_ext (g_type, g_init, more)) = g_init;;

let rec local_update
  locala
    (T_context_ext
      (types_t, func_t, global, table, memory, local, label, return, more))
    = T_context_ext
        (types_t, func_t, global, table, memory, locala local, label, return,
          more);;

let rec interp_get_v
  s inst b_es =
    (let (_, RValue [v]) =
       run_v (nat_of_integer (Z.of_int 2)) zero_nat
         (s, (F_ext ([], inst, ()), b_es))
       in
      v);;

let rec module_start_type_checker_p
  x xa =
    bind (single (x, xa))
      (fun (c, i) ->
        bind (if_pred (less_nat i (size_list (func_t c))))
          (fun () ->
            bind (eq_i_i equal_tf (nth (func_t c) i) (Tf ([], [])))
              (fun () -> single ())));;

let rec module_start_typing x1 x2 = holds (module_start_type_checker_p x1 x2);;

let rec return_update
  returna
    (T_context_ext
      (types_t, func_t, global, table, memory, local, label, return, more))
    = T_context_ext
        (types_t, func_t, global, table, memory, local, label, returna return,
          more);;

let rec e_desc (Module_export_ext (e_name, e_desc, more)) = e_desc;;

let rec e_name (Module_export_ext (e_name, e_desc, more)) = e_name;;

let rec i_desc (Module_import_ext (i_module, i_name, i_desc, more)) = i_desc;;

let rec interp_get_i32
  s inst b_es =
    (match interp_get_v s inst b_es with ConstInt32 c -> c
      | ConstInt64 _ -> zero_i32a | ConstFloat32 _ -> zero_i32a
      | ConstFloat64 _ -> zero_i32a);;

let rec gather_m_f_type
  tfs m_f =
    (if less_nat (fst m_f) (size_list tfs) then Some (nth tfs (fst m_f))
      else None);;

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
        b_e_type_checker
          (return_update (fun _ -> Some tm)
            (label_update (fun _ -> [tm] @ label c)
              (local_update (fun _ -> tn @ t_locs) c)))
          b_es (Tf ([], tm)));;

let rec module_elem_type_checker
  c (Module_elem_ext (t, es, is, ())) =
    list_all (const_expr c) es &&
      (b_e_type_checker c es (Tf ([], [T_i32])) &&
        (less_nat t (size_list (table c)) &&
          list_all (fun i -> less_nat i (size_list (func_t c))) is));;

let rec module_data_type_checker
  c (Module_data_ext (d, es, bs, ())) =
    list_all (const_expr c) es &&
      (b_e_type_checker c es (Tf ([], [T_i32])) &&
        less_nat d (size_list (memory c)));;

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
          (if list_all (fun (Tf (_, tm)) -> less_eq_nat (size_list tm) one_nata)
                tfs &&
                (list_all (module_func_type_checker c) fs &&
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
                                    one_nata)))))))))
            then (match
                   those (map (fun exp -> module_export_typer c (e_desc exp))
                           exps)
                   with None -> None | Some expts -> Some (impts, expts))
            else None)));;

let rec interp_alloc_module
  s m imps gvs =
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
           ())
       in
     let (s1, _) = alloc_Xs (fun sa m_f -> alloc_func sa m_f inst) s (m_funcs m)
       in
     let (s2, _) = alloc_Xs alloc_tab s1 (m_tabs m) in
     let (s3, _) = alloc_Xs alloc_mem s2 (m_mems m) in
     let (sa, _) = alloc_Xs alloc_glob s3 (zip (m_globs m) gvs) in
     let exps =
       map (fun m_exp ->
             Module_export_ext
               (e_name m_exp, export_get_v_ext inst (e_desc m_exp), ()))
         (m_exports m)
       in
      (sa, (inst, exps)));;

let rec interp_instantiate
  s m v_imps =
    (match module_type_checker m with None -> None
      | Some (t_imps, _) ->
        (if list_all2 (external_typing s) v_imps t_imps
          then (let g_inits =
                  map (fun g ->
                        interp_get_v s
                          (Inst_ext
                            ([], [], [], [],
                              map_filter
                                (fun a ->
                                  (match a with Ext_func _ -> None
                                    | Ext_tab _ -> None | Ext_mem _ -> None
                                    | Ext_glob aa -> Some aa))
                                v_imps,
                              ()))
                          (g_init g))
                    (m_globs m)
                  in
                let (sa, (inst, v_exps)) =
                  interp_alloc_module s m v_imps g_inits in
                let e_offs =
                  map (fun e -> interp_get_i32 sa inst (e_off e)) (m_elem m) in
                let d_offs =
                  map (fun d -> interp_get_i32 sa inst (d_off d)) (m_data m) in
                 (if list_all2
                       (fun e_offa e ->
                         less_eq_nat
                           (plus_nat (nat_of_int_i32 e_offa)
                             (size_list (e_init e)))
                           (size_list
                             (fst (nth (tabs sa)
                                    (nth (tabsa inst) (e_tab e))))))
                       e_offs (m_elem m) &&
                       list_all2
                         (fun d_offa d ->
                           less_eq_nat
                             (plus_nat (nat_of_int_i32 d_offa)
                               (size_list (d_init d)))
                             (mem_length
                               (nth (mems sa) (nth (memsa inst) (d_data d)))))
                         d_offs (m_data m)
                   then (let start = map_option (nth (funcsa inst)) (m_start m)
                           in
                         let sb =
                           init_tabs sa inst (map nat_of_int_i32 e_offs)
                             (m_elem m)
                           in
                         let s_end =
                           init_mems sb inst (map nat_of_int_i32 d_offs)
                             (m_data m)
                           in
                          Some ((s_end, (inst, v_exps)), start))
                   else None))
          else None));;

end;; (*struct WasmRef_Isa*)
