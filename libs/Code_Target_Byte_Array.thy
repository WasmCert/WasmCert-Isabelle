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

(* TODO: instead of deferring to bytewise accesses, target all heap accesses directly *)

definition "load_uint8' ba (i::integer) = map_Heap integer_of_uint8 (load_uint8 ba (nat_of_integer i))"

lemma Uint8_integer_of_uint8:"Uint8\<circ>integer_of_uint8 = id"
proof -
  have "(\<lambda>x. Abs_uint8 (word_of_int (int_of_uint8 x))) = id"
    using Rep_uint8_inverse int_of_uint8.rep_eq
    by auto
  thus ?thesis
    unfolding Uint8_def map_fun_def integer_of_uint8_def comp_def
    by simp
qed

lemma[code]: "load_uint8 ba n = map_Heap Uint8 (load_uint8' ba (integer_of_nat n))"
  unfolding load_uint8'_def
  by (simp add: Heap.map_comp Heap.map_id Uint8_integer_of_uint8)

definition "store_uint8' ba i bi = store_uint8 ba (nat_of_integer i) (Uint8 bi)"

lemma[code]: "store_uint8 ba n b = store_uint8' ba (integer_of_nat n) (integer_of_uint8 b)"
  by (simp add: Uint8_integer_of_uint8 pointfree_idE store_uint8'_def)

code_printing
  type_constructor byte_array \<rightharpoonup> (OCaml) "Bytes.t"

code_printing
  constant new_zeroed_byte_array' \<rightharpoonup> (OCaml) "(fun/ ()/ -> /Bytes.make _ 0)"
| constant len_byte_array' \<rightharpoonup> (OCaml) "(fun/ ()/ -> /Bytes.length _)"
| constant blit_byte_array' \<rightharpoonup> (OCaml) "(fun/ ()/ -> /Bytes.blit _ _ _ _ _)"
| constant load_uint8' \<rightharpoonup> (OCaml) "(fun/ ()/ -> /Bytes.get'_uint8 _ _)"
| constant store_uint8' \<rightharpoonup> (OCaml) "(fun/ ()/ -> /Bytes.set'_uint8 _ _ _)"

end