theory Code_Target_Byte_Array imports Byte_Array begin

(* code generation setup *)

definition "new_zeroed_byte_array' (n::integer) = new_zeroed_byte_array (nat_of_integer n)"

lemma[code]: "new_zeroed_byte_array n = new_zeroed_byte_array' (integer_of_nat n)"
  unfolding new_zeroed_byte_array'_def
  by simp

definition "len_byte_array' ba = map_Heap integer_of_nat (len_byte_array ba)"

lemma[code]: "len_byte_array ba = map_Heap nat_of_integer (len_byte_array' ba)"
  using Heap.map
  unfolding len_byte_array'_def
  apply (cases "(len_byte_array ba)")
  apply (cases "(map_Heap integer_of_nat
            (len_byte_array ba))")
  apply (auto simp add: map_prod_def comp_def map_option_case split: prod.splits option.splits)
  done

definition "blit_byte_array' ba (si::integer) ba' (di::integer) (li::integer) = blit_byte_array ba (nat_of_integer si) ba' (nat_of_integer di) (nat_of_integer li)"

lemma[code]: "blit_byte_array ba sn ba' dn ln = blit_byte_array' ba (integer_of_nat sn) ba' (integer_of_nat dn) (integer_of_nat ln)"
  unfolding blit_byte_array'_def
  by simp

lemma Uint8_integer_of_uint8:"Uint8\<circ>integer_of_uint8 = id"
proof -
  have "(\<lambda>x. Abs_uint8 (word_of_int (int_of_uint8 x))) = id"
    using Rep_uint8_inverse int_of_uint8.rep_eq
    by auto
  thus ?thesis
    unfolding Uint8_def map_fun_def integer_of_uint8_def comp_def
    by simp
qed

(* TODO: if extraction of wider accesses is implemented correctly, raw byte accesses should never be used *)

definition "load_uint8' ba (i::integer) = map_Heap integer_of_uint8 (load_uint8 ba (nat_of_integer i))"

lemma[code]: "load_uint8 ba n = map_Heap Uint8 (load_uint8' ba (integer_of_nat n))"
  unfolding load_uint8'_def
  by (simp add: Heap.map_comp Heap.map_id Uint8_integer_of_uint8)

definition "store_uint8' ba i bi = store_uint8 ba (nat_of_integer i) (Uint8 bi)"

lemma[code]: "store_uint8 ba n b = store_uint8' ba (integer_of_nat n) (integer_of_uint8 b)"
  by (simp add: Uint8_integer_of_uint8 pointfree_idE store_uint8'_def)

(* direct heap accesses of different widths *)
(* i32 *)
definition "load_uint32_of_uint8' ba i = load_uint32_of_uint8 ba (nat_of_integer i)"
definition "load_uint32_of_sint8' ba i = load_uint32_of_sint8 ba (nat_of_integer i)"
definition "load_uint32_of_uint16' ba i = load_uint32_of_uint16 ba (nat_of_integer i)"
definition "load_uint32_of_sint16' ba i = load_uint32_of_sint16 ba (nat_of_integer i)"
definition "load_uint32' ba i = load_uint32 ba (nat_of_integer i)"

lemma[code]: "load_uint32_of_uint8 ba n = load_uint32_of_uint8' ba (integer_of_nat n)"
             "load_uint32_of_sint8 ba n = load_uint32_of_sint8' ba (integer_of_nat n)"
             "load_uint32_of_uint16 ba n = load_uint32_of_uint16' ba (integer_of_nat n)"
             "load_uint32_of_sint16 ba n = load_uint32_of_sint16' ba (integer_of_nat n)"
             "load_uint32 ba n = load_uint32' ba (integer_of_nat n)"
  unfolding load_uint32_of_uint8'_def
            load_uint32_of_sint8'_def
            load_uint32_of_uint16'_def
            load_uint32_of_sint16'_def
            load_uint32'_def
  by simp_all

definition "store_uint8_of_uint32' a i v \<equiv> store_uint8_of_uint32 a (nat_of_integer i) v"
definition "store_uint16_of_uint32' a i v \<equiv> store_uint16_of_uint32 a (nat_of_integer i) v"
definition "store_uint32' a i v \<equiv> store_uint32 a (nat_of_integer i) v"

lemma[code]: "store_uint8_of_uint32 ba n v = store_uint8_of_uint32' ba (integer_of_nat n) v"
             "store_uint16_of_uint32 ba n v = store_uint16_of_uint32' ba (integer_of_nat n) v"
             "store_uint32 ba n v = store_uint32' ba (integer_of_nat n) v"
  unfolding store_uint8_of_uint32'_def
            store_uint16_of_uint32'_def
            store_uint32'_def
  by simp_all

(* i64 *)
definition "load_uint64_of_uint8' ba i = load_uint64_of_uint8 ba (nat_of_integer i)"
definition "load_uint64_of_sint8' ba i = load_uint64_of_sint8 ba (nat_of_integer i)"
definition "load_uint64_of_uint16' ba i = load_uint64_of_uint16 ba (nat_of_integer i)"
definition "load_uint64_of_sint16' ba i = load_uint64_of_sint16 ba (nat_of_integer i)"
definition "load_uint64_of_uint32' ba i = load_uint64_of_uint32 ba (nat_of_integer i)"
definition "load_uint64_of_sint32' ba i = load_uint64_of_sint32 ba (nat_of_integer i)"
definition "load_uint64' ba i = load_uint64 ba (nat_of_integer i)"

lemma[code]: "load_uint64_of_uint8 ba n = load_uint64_of_uint8' ba (integer_of_nat n)"
             "load_uint64_of_sint8 ba n = load_uint64_of_sint8' ba (integer_of_nat n)"
             "load_uint64_of_uint16 ba n = load_uint64_of_uint16' ba (integer_of_nat n)"
             "load_uint64_of_sint16 ba n = load_uint64_of_sint16' ba (integer_of_nat n)"
             "load_uint64_of_uint32 ba n = load_uint64_of_uint32' ba (integer_of_nat n)"
             "load_uint64_of_sint32 ba n = load_uint64_of_sint32' ba (integer_of_nat n)"
             "load_uint64 ba n = load_uint64' ba (integer_of_nat n)"
  unfolding load_uint64_of_uint8'_def
  unfolding load_uint64_of_sint8'_def
  unfolding load_uint64_of_uint16'_def
  unfolding load_uint64_of_sint16'_def
  unfolding load_uint64_of_uint32'_def
  unfolding load_uint64_of_sint32'_def
  unfolding load_uint64'_def
  by simp_all

definition "store_uint8_of_uint64' a i v \<equiv> store_uint8_of_uint64 a (nat_of_integer i) v"
definition "store_uint16_of_uint64' a i v \<equiv> store_uint16_of_uint64 a (nat_of_integer i) v"
definition "store_uint32_of_uint64' a i v \<equiv> store_uint32_of_uint64 a (nat_of_integer i) v"
definition "store_uint64' a i v \<equiv> store_uint64 a (nat_of_integer i) v"

lemma[code]: "store_uint8_of_uint64 ba n v = store_uint8_of_uint64' ba (integer_of_nat n) v"
             "store_uint16_of_uint64 ba n v = store_uint16_of_uint64' ba (integer_of_nat n) v"
             "store_uint32_of_uint64 ba n v = store_uint32_of_uint64' ba (integer_of_nat n) v"
             "store_uint64 ba n v = store_uint64' ba (integer_of_nat n) v"
  unfolding store_uint8_of_uint64'_def
            store_uint16_of_uint64'_def
            store_uint32_of_uint64'_def
            store_uint64'_def
  by simp_all

(* TODO: why is this not a thing already? *)
declare [[code drop: map_Heap]]
lemma[code]:
  "map_Heap f M = do { a \<leftarrow> M; return (f a) }"
  apply (cases M)
  apply (simp add: bind_def map_conv_bind_option fun_eq_iff execute_return split: option.splits)
  done

(* requires OCaml 4.08 or above *)
(* assumes sizeof(int) \<ge> 8 *)
code_printing
  type_constructor byte_array \<rightharpoonup> (OCaml) "Bytes.t"

code_printing
  constant new_zeroed_byte_array' \<rightharpoonup> (OCaml) "(fun/ ()/ -> /Bytes.make (Z.to'_int _) (Char.chr 0))"
| constant len_byte_array' \<rightharpoonup> (OCaml) "(fun/ ()/ -> /Z.of'_int (Bytes.length _))"
| constant blit_byte_array' \<rightharpoonup> (OCaml) "(fun/ ()/ -> /Bytes.blit _ (Z.to'_int _) _ (Z.to'_int _) (Z.to'_int _))"
(* raw byte accesses *)
| constant load_uint8' \<rightharpoonup> (OCaml) "(fun/ ()/ -> /Z.of'_int (Bytes.get'_uint8 _ (Z.to'_int _)))"
| constant store_uint8' \<rightharpoonup> (OCaml) "(fun/ ()/ -> /Bytes.set'_uint8 _ (Z.to'_int _) (Z.to'_int _))"

(* i32 loads *)
| constant load_uint32_of_uint8' \<rightharpoonup> (OCaml) "(fun/ ()/ -> /Int32.of'_int (Bytes.get'_uint8 _ (Z.to'_int _)))"
| constant load_uint32_of_sint8' \<rightharpoonup> (OCaml) "(fun/ ()/ -> /Int32.of'_int (Bytes.get'_int8 _ (Z.to'_int _)))"
| constant load_uint32_of_uint16' \<rightharpoonup> (OCaml) "(fun/ ()/ -> /Int32.of'_int (Bytes.get'_uint16'_le _ (Z.to'_int _)))"
| constant load_uint32_of_sint16' \<rightharpoonup> (OCaml) "(fun/ ()/ -> /Int32.of'_int (Bytes.get'_int16'_le _ (Z.to'_int _)))"
| constant load_uint32' \<rightharpoonup> (OCaml) "(fun/ ()/ -> /Bytes.get'_int32'_le _ (Z.to'_int _))"
(* i32 stores *)
| constant store_uint8_of_uint32' \<rightharpoonup> (OCaml) "(fun/ ()/ -> /Bytes.set'_uint8 _ (Z.to'_int _) (Int32.to'_int _))"
| constant store_uint16_of_uint32' \<rightharpoonup> (OCaml) "(fun/ ()/ -> /Bytes.set'_uint16'_le _ (Z.to'_int _) (Int32.to'_int _))"
| constant store_uint32' \<rightharpoonup> (OCaml) "(fun/ ()/ -> /Bytes.set'_int32'_le _ (Z.to'_int _) _)"

(* i64 loads *)
| constant load_uint64_of_uint8' \<rightharpoonup> (OCaml) "(fun/ ()/ -> /Int64.of'_int (Bytes.get'_uint8 _ (Z.to'_int _)))"
| constant load_uint64_of_sint8' \<rightharpoonup> (OCaml) "(fun/ ()/ -> /Int64.of'_int (Bytes.get'_int8 _ (Z.to'_int _)))"
| constant load_uint64_of_uint16' \<rightharpoonup> (OCaml) "(fun/ ()/ -> /Int64.of'_int (Bytes.get'_uint16'_le _ (Z.to'_int _)))"
| constant load_uint64_of_sint16' \<rightharpoonup> (OCaml) "(fun/ ()/ -> /Int64.of'_int (Bytes.get'_int16'_le _ (Z.to'_int _)))"
| constant load_uint64_of_uint32' \<rightharpoonup> (OCaml) "(fun/ ()/ -> /Int64.of'_int (Int32.unsigned'_to'_int (Bytes.get'_int32'_le _ (Z.to'_int _))))"
| constant load_uint64_of_sint32' \<rightharpoonup> (OCaml) "(fun/ ()/ -> /Int64.of'_int32 (Bytes.get'_int32'_le _ (Z.to'_int _)))"
| constant load_uint64' \<rightharpoonup> (OCaml) "(fun/ ()/ -> /Bytes.get'_int64'_le _ (Z.to'_int _))"
(* i64 stores *)
| constant store_uint8_of_uint64' \<rightharpoonup> (OCaml) "(fun/ ()/ -> /Bytes.set'_uint8 _ (Z.to'_int _) (Int64.to'_int _))"
| constant store_uint16_of_uint64' \<rightharpoonup> (OCaml) "(fun/ ()/ -> /Bytes.set'_uint16'_le _ (Z.to'_int _) (Int64.to'_int _))"
| constant store_uint32_of_uint64' \<rightharpoonup> (OCaml) "(fun/ ()/ -> /Bytes.set'_int32'_le _ (Z.to'_int _) (Int64.to'_int32 _))"
| constant store_uint64' \<rightharpoonup> (OCaml) "(fun/ ()/ -> /Bytes.set'_int64'_le _ (Z.to'_int _) _)"

end