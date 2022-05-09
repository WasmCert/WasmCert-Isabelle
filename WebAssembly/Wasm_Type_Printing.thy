theory Wasm_Type_Printing imports Wasm_Native_Word_Entry begin
(* Maps types to Andreas' Ocaml implementation - a thin wrapper over Ocaml ints/floats for the most part. *)

code_printing
(*  type_constructor i32 \<rightharpoonup> (OCaml) "I32Wrapper.t" *)
(*| type_constructor i64 \<rightharpoonup> (OCaml) "I64Wrapper.t" *)
  type_constructor f32 \<rightharpoonup> (OCaml) "F32Wrapper.t"
| type_constructor f64 \<rightharpoonup> (OCaml) "F64Wrapper.t"

(* zero consts *)
code_printing
(*  constant zero_i32_inst.zero_i32 \<rightharpoonup> (OCaml) "I32Wrapper.zero"
| constant zero_i64_inst.zero_i64 \<rightharpoonup> (OCaml) "I64Wrapper.zero" *)
  constant zero_f32_inst.zero_f32 \<rightharpoonup> (OCaml) "F32Wrapper.zero"
| constant zero_f64_inst.zero_f64 \<rightharpoonup> (OCaml) "F64Wrapper.zero"

(* intra-{int,float} conversions *)
code_printing
(*  constant wasm_wrap \<rightharpoonup> (OCaml) "(I32Wrapper'_convert.wrap'_i64)"
| constant wasm_extend_u \<rightharpoonup> (OCaml) "(I64Wrapper'_convert.extend'_u'_i32)"
| constant wasm_extend_s \<rightharpoonup> (OCaml) "(I64Wrapper'_convert.extend'_s'_i32)" *)
  constant wasm_demote \<rightharpoonup> (OCaml) "(F32Wrapper'_convert.demote'_f64)"
| constant wasm_promote \<rightharpoonup> (OCaml) "(F64Wrapper'_convert.promote'_f32)"

text\<open>use Native Word library for integer implementations\<close>

code_datatype i32_impl_abs
code_datatype i64_impl_abs

lemma[code]:
  "i32_impl_rep (i32_impl_abs x) = x"
  unfolding i32_impl_rep_def i32_impl_abs_def
  by (simp add: I32.rep_abs Rep_uint32_inverse)

lemma[code]:
  "i64_impl_rep (i64_impl_abs x) = x"
  unfolding i64_impl_rep_def i64_impl_abs_def
  by (simp add: I64.rep_abs Rep_uint64_inverse)

(* TODO: avoid rep round-trip *)
lemma[code]: "wasm_wrap (i64_impl_abs x) = i32_impl_abs (Abs_uint32' (Word.ucast (Rep_uint64' x)))"
  by (simp add: wasm_wrap_def i32_impl_abs_def Abs_uint32'.rep_eq i64_impl_abs.rep_eq)

(* TODO: avoid rep round-trip *)
lemma[code]: "wasm_extend_u (i32_impl_abs x) = i64_impl_abs (Abs_uint64' (Word.ucast (Rep_uint32' x)))"
  by (simp add: wasm_extend_u_def i32_impl_abs_def I32.rep_abs  Abs_uint64'.abs_eq i64_impl_abs.abs_eq)

(* TODO: avoid rep round-trip *)
lemma[code]: "wasm_extend_s (i32_impl_abs x) = i64_impl_abs (Abs_uint64' (Word.scast (Rep_uint32' x)))"
  by (simp add: wasm_extend_s_def i32_impl_abs_def I32.rep_abs Abs_uint64'.abs_eq i64_impl_abs.abs_eq)


(* i32 *)

lemma[code]: "(0::i32) = i32_impl_abs 0"
  by (simp add: zero_i32.abs_eq zero_uint32.rep_eq i32_impl_abs_def)

lemma[code]: "(Wasm_Type_Abs.int_of_nat::(nat\<Rightarrow>i32)) n = i32_impl_abs (uint32_of_nat n)"
  by (simp add: i32_impl_abs_def uint32_of_nat_def uint32_of_int_def int_of_nat_i32.abs_eq Abs_uint32_inverse)

lemma[code]: "nat_of_int (i32_impl_abs x) = nat_of_uint32 x"
  by transfer fastforce

lemma[code]: "wasm_bool b = i32_impl_abs (if b then 1 else 0)"
  by transfer fastforce

lemma[code]: "int32_minus_one = i32_impl_abs (-1 :: uint32)"
  by transfer fastforce

lemma[code]: "deserialise_i32 bs = i32_impl_abs (Abs_uint32' (word_rcat_rev (map Rep_uint8' bs)))"
  by transfer fastforce

lemma[code]: "serialise_i32 (i32_impl_abs x) = map Abs_uint8' (word_rsplit_rev (Rep_uint32' x))"
  by (simp add: serialise_i32_def i32_impl_abs_def I32.rep_abs Abs_uint8'.abs_eq)

(* TODO: avoid rep round-trip *)
lemma[code]: "int_clz (i32_impl_abs x) = i32_impl_abs (Abs_uint32' (Word.of_nat (word_clz (Rep_uint32' x))))"
  by (simp add: i32_impl_abs_def Abs_uint32'.rep_eq I32.int_clz_def int_clz_i32.abs_eq)

(* TODO: avoid rep round-trip *)
lemma[code]: "int_ctz (i32_impl_abs x) = i32_impl_abs (Abs_uint32' (Word.of_nat (word_ctz (Rep_uint32' x))))"
  by (simp add: i32_impl_abs_def Abs_uint32'.rep_eq I32.int_ctz_def int_ctz_i32.abs_eq)

(* TODO: avoid rep round-trip *)
lemma[code]: "int_popcnt (i32_impl_abs x) = i32_impl_abs (Abs_uint32' (Word.of_nat (pop_count (Rep_uint32' x))))"
  by (simp add: i32_impl_abs_def Abs_uint32'.rep_eq I32.int_popcnt_def int_popcnt_i32.abs_eq)

lemma[code]: "int_add (i32_impl_abs x) (i32_impl_abs y) = i32_impl_abs (x + y)"
  by (simp add: i32_impl_abs_def I32.int_add_def int_add_i32.abs_eq plus_uint32.rep_eq)

lemma[code]: "int_sub (i32_impl_abs x) (i32_impl_abs y) = i32_impl_abs (x - y)"
  by (simp add: I32.int_sub_def i32_impl_abs_def int_sub_i32.abs_eq minus_uint32.rep_eq)

lemma[code]: "int_mul (i32_impl_abs x) (i32_impl_abs y) = i32_impl_abs (x * y)"
  by (simp add: i32_impl_abs_def I32.int_mul_def int_mul_i32.abs_eq times_uint32.rep_eq)

lemma[code]: "int_div_u (i32_impl_abs x) (i32_impl_abs y) = (if y = 0 then None else Some (i32_impl_abs (uint32_div x y)))"
  apply (simp add: i32_impl_abs_def I32.int_div_u_def int_div_u_i32.abs_eq split: if_splits)
  apply (metis Rep_uint32_inject div_uint32_code divide_uint32.rep_eq zero_uint32.rep_eq)
  done

lemma[code]: "int_div_s (i32_impl_abs x) (i32_impl_abs y) = (if y = 0 \<or> (x = -2147483648 \<and> y = -1) then None else Some (i32_impl_abs (uint32_sdiv x y)))"
  apply (cases "y = 0 \<or> (x = -2147483648 \<and> y = -1)")
  apply (simp_all add: i32_impl_abs_def uint32_sdiv_code I32.int_div_s_def int_div_s_i32.abs_eq)
  apply (metis Rep_uint32_neg_numeral one_uint32.rep_eq uminus_uint32.rep_eq zero_uint32.rep_eq)
  apply (metis Rep_uint32_inject Rep_uint32_neg_numeral one_uint32.rep_eq uminus_uint32.rep_eq zero_uint32.rep_eq)
  done

lemma[code]: "int_rem_u (i32_impl_abs x) (i32_impl_abs y) = (if y = 0 then None else Some (i32_impl_abs (uint32_mod x y)))"
  apply (simp add: i32_impl_abs_def I32.int_rem_u_def int_rem_u_i32.abs_eq split: if_splits)
  apply (metis Rep_uint32_inject mod_uint32_code modulo_uint32.rep_eq zero_uint32.rep_eq)
  done

(* TODO: avoid rep round-trip *)
lemma[code]: "int_rem_s (i32_impl_abs x) (i32_impl_abs y) = (if y = 0 then None else Some (i32_impl_abs (Abs_uint32' ((Rep_uint32' x) smod (Rep_uint32' y)))))"
  apply (simp_all add: i32_impl_abs_def I32.int_rem_s_def int_rem_s_i32.abs_eq split: if_splits)
  apply (metis Abs_uint32'.rep_eq Rep_uint32_inverse zero_uint32.abs_eq)
  done

lemma[code]: "int_and (i32_impl_abs x) (i32_impl_abs y) = i32_impl_abs (and x y)"
  by (simp add: i32_impl_abs_def I32.int_and_def int_and_i32.abs_eq and_uint32.rep_eq)

lemma[code]: "int_or (i32_impl_abs x) (i32_impl_abs y) = i32_impl_abs (or x y)"
  by (simp add: i32_impl_abs_def I32.int_or_def int_or_i32.abs_eq or_uint32.rep_eq)

lemma[code]: "int_xor (i32_impl_abs x) (i32_impl_abs y) = i32_impl_abs (xor x y)"
  by (simp add: i32_impl_abs_def I32.int_xor_def int_xor_i32.abs_eq xor_uint32.rep_eq)

lemma[code]: "int_shl (i32_impl_abs x) (i32_impl_abs y) = i32_impl_abs (uint32_shiftl x ((integer_of_uint32 y) mod 32))"
proof -
  have 1:"\<not>(integer_of_uint32 y mod 32 < 0 \<or> 32 \<le> integer_of_uint32 y mod 32)"
    by (meson unique_euclidean_semiring_numeral_class.pos_mod_bound unique_euclidean_semiring_numeral_class.pos_mod_sign verit_comp_simplify1(3) zero_less_numeral)
  have 2:"(Rep_uint32 (x << (nat_of_integer (integer_of_uint32 y mod 32)))) =
            ((Rep_uint32 x) << (unat (Rep_uint32 y) mod 32))"
    unfolding integer_of_uint32_def nat_of_integer_def
    apply transfer
    apply transfer
    apply (simp add: take_bit_eq_mod nat_mod_distrib)
    done
  thus ?thesis
    using 1
    unfolding i32_impl_abs_def uint32_shiftl_def
    by (simp add: shiftl_eq_push_bit I32.int_shl_def int_shl_i32.abs_eq)
qed

lemma[code]: "int_shr_u (i32_impl_abs x) (i32_impl_abs y) = i32_impl_abs (uint32_shiftr x ((integer_of_uint32 y) mod 32))"
proof -
  have 1:"\<not>(integer_of_uint32 y mod 32 < 0 \<or> 32 \<le> integer_of_uint32 y mod 32)"
    by (meson unique_euclidean_semiring_numeral_class.pos_mod_bound unique_euclidean_semiring_numeral_class.pos_mod_sign verit_comp_simplify1(3) zero_less_numeral)
  have 2:"(Rep_uint32 (shiftr x (nat_of_integer ((integer_of_uint32 y) mod 32)))) =
            (shiftr (Rep_uint32 x) ((unat (Rep_uint32 y)) mod 32))"
    unfolding integer_of_uint32_def nat_of_integer_def
    apply transfer
    apply transfer
    apply (simp add: take_bit_eq_mod nat_mod_distrib)
    done
  thus ?thesis
    using 1
    unfolding i32_impl_abs_def uint32_shiftr_def
    by (simp add: shiftr_eq_drop_bit I32.int_shr_u_def int_shr_u_i32.abs_eq)
qed

lemma[code]: "int_shr_s (i32_impl_abs x) (i32_impl_abs y) = i32_impl_abs (uint32_sshiftr x ((integer_of_uint32 y) mod 32))"
proof -
  have 1:"\<not>(integer_of_uint32 y mod 32 < 0 \<or> 32 \<le> integer_of_uint32 y mod 32)"
    by (meson unique_euclidean_semiring_numeral_class.pos_mod_bound unique_euclidean_semiring_numeral_class.pos_mod_sign verit_comp_simplify1(3) zero_less_numeral)
  have 2:"(Rep_uint32 (sshiftr_uint32 x (nat_of_integer ((integer_of_uint32 y) mod 32)))) =
            (sshiftr (Rep_uint32 x) ((unat (Rep_uint32 y)) mod 32))"
    unfolding integer_of_uint32_def nat_of_integer_def
    apply transfer
    apply transfer
    apply (simp add: take_bit_eq_mod nat_mod_distrib)
    done
  thus ?thesis
    using 1
    unfolding i32_impl_abs_def uint32_sshiftr_def
    by (simp add: I32.int_shr_s_def int_shr_s_i32.abs_eq)
qed

(* TODO: avoid rep round-trip *)
lemma[code]: "int_rotl (i32_impl_abs x) (i32_impl_abs y) = i32_impl_abs (Abs_uint32' (word_rotl (nat_of_uint32 y) (Rep_uint32' x)))"
  by (simp add: i32_impl_abs_def Abs_uint32'.rep_eq I32.int_rotl_def int_rotl_i32.abs_eq nat_of_uint32_def)

(* TODO: avoid rep round-trip *)
lemma[code]: "int_rotr (i32_impl_abs x) (i32_impl_abs y) = i32_impl_abs (Abs_uint32' (word_rotr (nat_of_uint32 y) (Rep_uint32' x)))"
  by (simp add: i32_impl_abs_def Abs_uint32'.rep_eq I32.int_rotr_def int_rotr_i32.abs_eq nat_of_uint32_def)

lemma[code]: "int_eqz (i32_impl_abs x) = (x = 0)"
  apply (simp add: i32_impl_abs_def I32.int_eqz_def int_eqz_i32.abs_eq)
  apply (metis I32.rep_0 I32.rep_abs Rep_uint32_inverse zero_i32.abs_eq zero_uint32.rep_eq)
  done

lemma[code]: "int_eq (i32_impl_abs x) (i32_impl_abs y) = (x = y)"
  by transfer (simp add: I32.int_eq_def)

lemma[code]: "int_lt_u (i32_impl_abs x) (i32_impl_abs y) = (x < y)"
  by (simp add: i32_impl_abs_def I32.int_lt_u_def int_lt_u_i32.abs_eq less_uint32.rep_eq)

lemma[code]: "int_lt_s (i32_impl_abs x) (i32_impl_abs y) = ((msb y \<longrightarrow> msb x) \<and> (msb x \<and> \<not> msb y \<or> x < y))"
  by (simp add: i32_impl_abs_def I32.int_lt_s_def int_lt_s_i32.abs_eq word_sless_msb_less less_uint32.rep_eq msb_uint32.rep_eq)

lemma[code]: "int_gt_u (i32_impl_abs x) (i32_impl_abs y) = (x > y)"
  by (simp add: i32_impl_abs_def I32.int_gt_u_def int_gt_u_i32.abs_eq less_uint32.rep_eq)

lemma[code]: "int_gt_s (i32_impl_abs x) (i32_impl_abs y) = ((msb x \<longrightarrow> msb y) \<and> (msb y \<and> \<not> msb x \<or> y < x))"
  by (simp add: i32_impl_abs_def I32.int_gt_s_def int_gt_s_i32.abs_eq less_uint32.rep_eq msb_uint32.rep_eq word_sless_msb_less)

lemma[code]: "int_le_u (i32_impl_abs x) (i32_impl_abs y) = (x \<le> y)"
  by (simp add: i32_impl_abs_def I32.int_le_u_def int_le_u_i32.abs_eq less_eq_uint32.rep_eq)

lemma[code]: "int_le_s (i32_impl_abs x) (i32_impl_abs y) = ((msb y \<longrightarrow> msb x) \<and> (msb x \<and> \<not> msb y \<or> x \<le> y))"
  by (simp add: i32_impl_abs_def I32.int_le_s_def int_le_s_i32.abs_eq less_eq_uint32.rep_eq msb_uint32.rep_eq word_sle_msb_le)

lemma[code]: "int_ge_u (i32_impl_abs x) (i32_impl_abs y) = (x \<ge> y)"
  by (simp add: i32_impl_abs_def I32.int_ge_u_def int_ge_u_i32.abs_eq less_eq_uint32.rep_eq)

lemma[code]: "int_ge_s (i32_impl_abs x) (i32_impl_abs y) =  ((msb x \<longrightarrow> msb y) \<and> (msb y \<and> \<not> msb x \<or> y \<le> x))"
  by (simp add: i32_impl_abs_def I32.int_ge_s_def int_ge_s_i32.abs_eq less_eq_uint32.rep_eq msb_uint32.rep_eq word_sle_msb_le)

(* i64 *)

lemma[code]: "(0::i64) = i64_impl_abs 0"
  by (simp add: zero_i64.abs_eq zero_uint64.rep_eq i64_impl_abs_def)

lemma[code]: "(Wasm_Type_Abs.int_of_nat::(nat\<Rightarrow>i64)) n = i64_impl_abs (uint64_of_nat n)"
  by (simp add: i64_impl_abs_def uint64_of_nat_def uint64_of_int_def int_of_nat_i64.abs_eq Abs_uint64_inverse)

lemma[code]: "nat_of_int (i64_impl_abs x) = nat_of_uint64 x"
  by transfer fastforce

lemma[code]: "deserialise_i64 bs = i64_impl_abs (Abs_uint64' (word_rcat_rev (map Rep_uint8' bs)))"
  by transfer fastforce

(* TODO: avoid rep round-trip *)
lemma[code]: "serialise_i64 (i64_impl_abs x) = map Abs_uint8' (word_rsplit_rev (Rep_uint64' x))"
  by (simp add: serialise_i64_def i64_impl_abs_def I64.rep_abs Abs_uint8'.abs_eq)

(* TODO: avoid rep round-trip *)
lemma[code]: "int_clz (i64_impl_abs x) = i64_impl_abs (Abs_uint64' (Word.of_nat (word_clz (Rep_uint64' x))))"
  by (simp add: i64_impl_abs_def Abs_uint64'.rep_eq I64.int_clz_def int_clz_i64.abs_eq)

(* TODO: avoid rep round-trip *)
lemma[code]: "int_ctz (i64_impl_abs x) = i64_impl_abs (Abs_uint64' (Word.of_nat (word_ctz (Rep_uint64' x))))"
  by (simp add: i64_impl_abs_def Abs_uint64'.rep_eq I64.int_ctz_def int_ctz_i64.abs_eq)

(* TODO: avoid rep round-trip *)
lemma[code]: "int_popcnt (i64_impl_abs x) = i64_impl_abs (Abs_uint64' (Word.of_nat (pop_count (Rep_uint64' x))))"
  by (simp add: i64_impl_abs_def Abs_uint64'.rep_eq I64.int_popcnt_def int_popcnt_i64.abs_eq)

lemma[code]: "int_add (i64_impl_abs x) (i64_impl_abs y) = i64_impl_abs (x + y)"
  by (simp add: i64_impl_abs_def I64.int_add_def int_add_i64.abs_eq plus_uint64.rep_eq)

lemma[code]: "int_sub (i64_impl_abs x) (i64_impl_abs y) = i64_impl_abs (x - y)"
  by (simp add: I64.int_sub_def i64_impl_abs_def int_sub_i64.abs_eq minus_uint64.rep_eq)

lemma[code]: "int_mul (i64_impl_abs x) (i64_impl_abs y) = i64_impl_abs (x * y)"
  by (simp add: i64_impl_abs_def I64.int_mul_def int_mul_i64.abs_eq times_uint64.rep_eq)

lemma[code]: "int_div_u (i64_impl_abs x) (i64_impl_abs y) = (if y = 0 then None else Some (i64_impl_abs (uint64_div x y)))"
  apply (simp add: i64_impl_abs_def I64.int_div_u_def int_div_u_i64.abs_eq split: if_splits)
  apply (metis Rep_uint64_inject div_uint64_code divide_uint64.rep_eq zero_uint64.rep_eq)
  done

lemma[code]: "int_div_s (i64_impl_abs x) (i64_impl_abs y) = (if y = 0 \<or> (x = -9223372036854775808 \<and> y = -1) then None else Some (i64_impl_abs (uint64_sdiv x y)))"
  apply (cases "y = 0 \<or> (x = -9223372036854775808 \<and> y = -1)")
  apply (simp_all add: i64_impl_abs_def uint64_sdiv_code I64.int_div_s_def int_div_s_i64.abs_eq)
  apply (metis Rep_uint64_neg_numeral one_uint64.rep_eq uminus_uint64.rep_eq zero_uint64.rep_eq)
  apply (metis Rep_uint64_inject Rep_uint64_neg_numeral one_uint64.rep_eq uminus_uint64.rep_eq zero_uint64.rep_eq)
  done

lemma[code]: "int_rem_u (i64_impl_abs x) (i64_impl_abs y) = (if y = 0 then None else Some (i64_impl_abs (uint64_mod x y)))"
  apply (simp add: i64_impl_abs_def I64.int_rem_u_def int_rem_u_i64.abs_eq split: if_splits)
  apply (metis Rep_uint64_inject mod_uint64_code modulo_uint64.rep_eq zero_uint64.rep_eq)
  done

(* TODO: avoid rep round-trip *)
lemma[code]: "int_rem_s (i64_impl_abs x) (i64_impl_abs y) = (if y = 0 then None else Some (i64_impl_abs (Abs_uint64' ((Rep_uint64' x) smod (Rep_uint64' y)))))"
  apply (simp_all add: i64_impl_abs_def I64.int_rem_s_def int_rem_s_i64.abs_eq split: if_splits)
  apply (metis Abs_uint64'.rep_eq Rep_uint64_inverse zero_uint64.abs_eq)
  done

lemma[code]: "int_and (i64_impl_abs x) (i64_impl_abs y) = i64_impl_abs (and x y)"
  by (simp add: i64_impl_abs_def I64.int_and_def int_and_i64.abs_eq and_uint64.rep_eq)

lemma[code]: "int_or (i64_impl_abs x) (i64_impl_abs y) = i64_impl_abs (or x y)"
  by (simp add: i64_impl_abs_def I64.int_or_def int_or_i64.abs_eq or_uint64.rep_eq)

lemma[code]: "int_xor (i64_impl_abs x) (i64_impl_abs y) = i64_impl_abs (xor x y)"
  by (simp add: i64_impl_abs_def I64.int_xor_def int_xor_i64.abs_eq xor_uint64.rep_eq)

lemma[code]: "int_shl (i64_impl_abs x) (i64_impl_abs y) = i64_impl_abs (uint64_shiftl x ((integer_of_uint64 y) mod 64))"
proof -
  have 1:"\<not>(integer_of_uint64 y mod 64 < 0 \<or> 64 \<le> integer_of_uint64 y mod 64)"
    by (meson unique_euclidean_semiring_numeral_class.pos_mod_bound unique_euclidean_semiring_numeral_class.pos_mod_sign verit_comp_simplify1(3) zero_less_numeral)
  have 2:"(Rep_uint64 (x << (nat_of_integer (integer_of_uint64 y mod 64)))) =
            ((Rep_uint64 x) << (unat (Rep_uint64 y) mod 64))"
    unfolding integer_of_uint64_def nat_of_integer_def
    apply transfer
    apply transfer
    apply (simp add: take_bit_eq_mod nat_mod_distrib)
    done
  thus ?thesis
    using 1
    unfolding i64_impl_abs_def uint64_shiftl_def
    by (simp add: shiftl_eq_push_bit I64.int_shl_def int_shl_i64.abs_eq)
qed

lemma[code]: "int_shr_u (i64_impl_abs x) (i64_impl_abs y) = i64_impl_abs (uint64_shiftr x ((integer_of_uint64 y) mod 64))"
proof -
  have 1:"\<not>(integer_of_uint64 y mod 64 < 0 \<or> 64 \<le> integer_of_uint64 y mod 64)"
    by (meson unique_euclidean_semiring_numeral_class.pos_mod_bound unique_euclidean_semiring_numeral_class.pos_mod_sign verit_comp_simplify1(3) zero_less_numeral)
  have 2:"(Rep_uint64 (shiftr x (nat_of_integer ((integer_of_uint64 y) mod 64)))) =
            (shiftr (Rep_uint64 x) ((unat (Rep_uint64 y)) mod 64))"
    unfolding integer_of_uint64_def nat_of_integer_def
    apply transfer
    apply transfer
    apply (simp add: take_bit_eq_mod nat_mod_distrib)
    done
  thus ?thesis
    using 1
    unfolding i64_impl_abs_def uint64_shiftr_def
    by (simp add: shiftr_eq_drop_bit I64.int_shr_u_def int_shr_u_i64.abs_eq)
qed

lemma[code]: "int_shr_s (i64_impl_abs x) (i64_impl_abs y) = i64_impl_abs (uint64_sshiftr x ((integer_of_uint64 y) mod 64))"
proof -
  have 1:"\<not>(integer_of_uint64 y mod 64 < 0 \<or> 64 \<le> integer_of_uint64 y mod 64)"
    by (meson unique_euclidean_semiring_numeral_class.pos_mod_bound unique_euclidean_semiring_numeral_class.pos_mod_sign verit_comp_simplify1(3) zero_less_numeral)
  have 2:"(Rep_uint64 (sshiftr_uint64 x (nat_of_integer ((integer_of_uint64 y) mod 64)))) =
            (sshiftr (Rep_uint64 x) ((unat (Rep_uint64 y)) mod 64))"
    unfolding integer_of_uint64_def nat_of_integer_def
    apply transfer
    apply transfer
    apply (simp add: take_bit_eq_mod nat_mod_distrib)
    done
  thus ?thesis
    using 1
    unfolding i64_impl_abs_def uint64_sshiftr_def
    by (simp add: I64.int_shr_s_def int_shr_s_i64.abs_eq)
qed

(* TODO: avoid rep round-trip *)
lemma[code]: "int_rotl (i64_impl_abs x) (i64_impl_abs y) = i64_impl_abs (Abs_uint64' (word_rotl (nat_of_uint64 y) (Rep_uint64' x)))"
  by (simp add: i64_impl_abs_def Abs_uint64'.rep_eq I64.int_rotl_def int_rotl_i64.abs_eq nat_of_uint64_def)

(* TODO: avoid rep round-trip *)
lemma[code]: "int_rotr (i64_impl_abs x) (i64_impl_abs y) = i64_impl_abs (Abs_uint64' (word_rotr (nat_of_uint64 y) (Rep_uint64' x)))"
  by (simp add: i64_impl_abs_def Abs_uint64'.rep_eq I64.int_rotr_def int_rotr_i64.abs_eq nat_of_uint64_def)

lemma[code]: "int_eqz (i64_impl_abs x) = (x = 0)"
  apply (simp add: i64_impl_abs_def I64.int_eqz_def int_eqz_i64.abs_eq)
  apply (metis I64.rep_0 I64.rep_abs Rep_uint64_inverse zero_i64.abs_eq zero_uint64.rep_eq)
  done

lemma[code]: "int_eq (i64_impl_abs x) (i64_impl_abs y) = (x = y)"
  by transfer (simp add: I64.int_eq_def)

lemma[code]: "int_lt_u (i64_impl_abs x) (i64_impl_abs y) = (x < y)"
  by (simp add: i64_impl_abs_def I64.int_lt_u_def int_lt_u_i64.abs_eq less_uint64.rep_eq)

lemma[code]: "int_lt_s (i64_impl_abs x) (i64_impl_abs y) = ((msb y \<longrightarrow> msb x) \<and> (msb x \<and> \<not> msb y \<or> x < y))"
  by (simp add: i64_impl_abs_def I64.int_lt_s_def int_lt_s_i64.abs_eq less_uint64.rep_eq msb_uint64.rep_eq word_sless_msb_less)

lemma[code]: "int_gt_u (i64_impl_abs x) (i64_impl_abs y) = (x > y)"
  by (simp add: i64_impl_abs_def I64.int_gt_u_def int_gt_u_i64.abs_eq less_uint64.rep_eq)

lemma[code]: "int_gt_s (i64_impl_abs x) (i64_impl_abs y) = ((msb x \<longrightarrow> msb y) \<and> (msb y \<and> \<not> msb x \<or> y < x))"
  by (simp add: i64_impl_abs_def I64.int_gt_s_def int_gt_s_i64.abs_eq less_uint64.rep_eq msb_uint64.rep_eq word_sless_msb_less)

lemma[code]: "int_le_u (i64_impl_abs x) (i64_impl_abs y) = (x \<le> y)"
  by (simp add: i64_impl_abs_def I64.int_le_u_def int_le_u_i64.abs_eq less_eq_uint64.rep_eq)

lemma[code]: "int_le_s (i64_impl_abs x) (i64_impl_abs y) = ((msb y \<longrightarrow> msb x) \<and> (msb x \<and> \<not> msb y \<or> x \<le> y))"
  by (simp add: i64_impl_abs_def I64.int_le_s_def int_le_s_i64.abs_eq less_eq_uint64.rep_eq msb_uint64.rep_eq word_sle_msb_le)

lemma[code]: "int_ge_u (i64_impl_abs x) (i64_impl_abs y) = (x \<ge> y)"
  by (simp add: i64_impl_abs_def I64.int_ge_u_def int_ge_u_i64.abs_eq less_eq_uint64.rep_eq)

lemma[code]: "int_ge_s (i64_impl_abs x) (i64_impl_abs y) = ((msb x \<longrightarrow> msb y) \<and> (msb y \<and> \<not> msb x \<or> y \<le> x))"
  by (simp add: i64_impl_abs_def I64.int_ge_s_def int_ge_s_i64.abs_eq less_eq_uint64.rep_eq msb_uint64.rep_eq word_sle_msb_le)

(* Sometimes to implement conversions we need to indirect through OCaml int types *)
typedecl ocaml_i32
typedecl ocaml_i64
typedecl ocaml_char

code_printing
  type_constructor ocaml_i32 \<rightharpoonup> (OCaml) "Int32.t"
| type_constructor ocaml_i64 \<rightharpoonup> (OCaml) "Int64.t"
| type_constructor ocaml_char \<rightharpoonup> (OCaml) "Char.t"

axiomatization
  ocaml_i32_to_integer :: "ocaml_i32 \<Rightarrow> integer" and
  integer_to_ocaml_i32 :: "integer \<Rightarrow> ocaml_i32" and
  ocaml_i64_to_integer :: "ocaml_i64 \<Rightarrow> integer" and
  integer_to_ocaml_i64 :: "integer \<Rightarrow> ocaml_i64" and
  ocaml_char_to_integer :: "ocaml_char \<Rightarrow> integer" and
  integer_to_ocaml_char :: "integer \<Rightarrow> ocaml_char"

code_printing
  constant ocaml_i32_to_integer \<rightharpoonup> (OCaml) "LibAux.z'_of'_uint32"
| constant integer_to_ocaml_i32 \<rightharpoonup> (OCaml) "LibAux.uint32'_of'_z"
| constant ocaml_i64_to_integer \<rightharpoonup> (OCaml) "LibAux.z'_of'_uint64"
| constant integer_to_ocaml_i64 \<rightharpoonup> (OCaml) "LibAux.uint64'_of'_z"
| constant ocaml_char_to_integer \<rightharpoonup> (OCaml) "LibAux.z'_of'_char"
| constant integer_to_ocaml_char \<rightharpoonup> (OCaml) "LibAux.char'_of'_z"

definition ocaml_int32_to_isabelle_int32 :: "ocaml_i32 \<Rightarrow> i32" where
  "ocaml_int32_to_isabelle_int32 n \<equiv> i32_impl_abs (Uint32 (ocaml_i32_to_integer n))"

definition isabelle_int32_to_ocaml_int32 :: "i32 \<Rightarrow> ocaml_i32" where
  "isabelle_int32_to_ocaml_int32 n \<equiv> integer_to_ocaml_i32 (integer_of_uint32 (i32_impl_rep n))"

definition ocaml_int64_to_isabelle_int64 :: "ocaml_i64 \<Rightarrow> i64" where
  "ocaml_int64_to_isabelle_int64 n \<equiv> i64_impl_abs (Uint64 (ocaml_i64_to_integer n))"

definition isabelle_int64_to_ocaml_int64 :: "i64 \<Rightarrow> ocaml_i64" where
  "isabelle_int64_to_ocaml_int64 n \<equiv> integer_to_ocaml_i64 (integer_of_uint64 (i64_impl_rep n))"

definition ocaml_char_to_isabelle_byte :: "ocaml_char \<Rightarrow> byte" where
  "ocaml_char_to_isabelle_byte n \<equiv> Uint8 (ocaml_char_to_integer n)"

definition isabelle_byte_to_ocaml_char :: "byte \<Rightarrow> ocaml_char" where
  "isabelle_byte_to_ocaml_char n \<equiv> integer_to_ocaml_char (integer_of_uint8 n)"

(* axiomatise the existence of conversions between floats and OCaml ints/char lists *)
axiomatization
  f32_convert_u_ocaml_i32 :: "ocaml_i32 \<Rightarrow> f32" and
  f32_convert_s_ocaml_i32 :: "ocaml_i32 \<Rightarrow> f32" and
  f32_convert_u_ocaml_i64 :: "ocaml_i64 \<Rightarrow> f32" and
  f32_convert_s_ocaml_i64 :: "ocaml_i64 \<Rightarrow> f32" and
  f64_convert_u_ocaml_i32 :: "ocaml_i32 \<Rightarrow> f64" and
  f64_convert_s_ocaml_i32 :: "ocaml_i32 \<Rightarrow> f64" and
  f64_convert_u_ocaml_i64 :: "ocaml_i64 \<Rightarrow> f64" and
  f64_convert_s_ocaml_i64 :: "ocaml_i64 \<Rightarrow> f64" and

  ocaml_i32_trunc_u_f32 :: "f32 \<Rightarrow> ocaml_i32 option" and
  ocaml_i32_trunc_s_f32 :: "f32 \<Rightarrow> ocaml_i32 option" and
  ocaml_i32_trunc_u_f64 :: "f64 \<Rightarrow> ocaml_i32 option" and
  ocaml_i32_trunc_s_f64 :: "f64 \<Rightarrow> ocaml_i32 option" and
  ocaml_i64_trunc_u_f32 :: "f32 \<Rightarrow> ocaml_i64 option" and
  ocaml_i64_trunc_s_f32 :: "f32 \<Rightarrow> ocaml_i64 option" and
  ocaml_i64_trunc_u_f64 :: "f64 \<Rightarrow> ocaml_i64 option" and
  ocaml_i64_trunc_s_f64 :: "f64 \<Rightarrow> ocaml_i64 option" and
  ocaml_i32_trunc_sat_u_f32 :: "f32 \<Rightarrow> ocaml_i32" and
  ocaml_i32_trunc_sat_s_f32 :: "f32 \<Rightarrow> ocaml_i32" and
  ocaml_i32_trunc_sat_u_f64 :: "f64 \<Rightarrow> ocaml_i32" and
  ocaml_i32_trunc_sat_s_f64 :: "f64 \<Rightarrow> ocaml_i32" and
  ocaml_i64_trunc_sat_u_f32 :: "f32 \<Rightarrow> ocaml_i64" and
  ocaml_i64_trunc_sat_s_f32 :: "f32 \<Rightarrow> ocaml_i64" and
  ocaml_i64_trunc_sat_u_f64 :: "f64 \<Rightarrow> ocaml_i64" and
  ocaml_i64_trunc_sat_s_f64 :: "f64 \<Rightarrow> ocaml_i64" and

  f32_serialise_ocaml_char :: "f32 \<Rightarrow> ocaml_char list" and
  f64_serialise_ocaml_char :: "f64 \<Rightarrow> ocaml_char list" and
  f32_deserialise_ocaml_char :: "ocaml_char list \<Rightarrow> f32" and
  f64_deserialise_ocaml_char :: "ocaml_char list \<Rightarrow> f64" and

  ocaml_i32_reinterpret_f32 :: "f32 \<Rightarrow> ocaml_i32" and
  ocaml_i64_reinterpret_f64 :: "f64 \<Rightarrow> ocaml_i64" and
  ocaml_f32_reinterpret_i32 :: "ocaml_i32 \<Rightarrow> f32" and
  ocaml_f64_reinterpret_i64 :: "ocaml_i64 \<Rightarrow> f64"

code_printing
  constant f32_convert_u_ocaml_i32 \<rightharpoonup> (OCaml) "F32Wrapper'_convert.convert'_u'_i32"
| constant f32_convert_s_ocaml_i32 \<rightharpoonup> (OCaml) "F32Wrapper'_convert.convert'_s'_i32"
| constant f32_convert_u_ocaml_i64 \<rightharpoonup> (OCaml) "F32Wrapper'_convert.convert'_u'_i64"
| constant f32_convert_s_ocaml_i64 \<rightharpoonup> (OCaml) "F32Wrapper'_convert.convert'_s'_i64"
| constant f64_convert_u_ocaml_i32 \<rightharpoonup> (OCaml) "F64Wrapper'_convert.convert'_u'_i32"
| constant f64_convert_s_ocaml_i32 \<rightharpoonup> (OCaml) "F64Wrapper'_convert.convert'_s'_i32"
| constant f64_convert_u_ocaml_i64 \<rightharpoonup> (OCaml) "F64Wrapper'_convert.convert'_u'_i64"
| constant f64_convert_s_ocaml_i64 \<rightharpoonup> (OCaml) "F64Wrapper'_convert.convert'_s'_i64"

| constant ocaml_i32_trunc_u_f32 \<rightharpoonup> (OCaml) "I32Wrapper'_convert.trunc'_u'_f32"
| constant ocaml_i32_trunc_s_f32 \<rightharpoonup> (OCaml) "I32Wrapper'_convert.trunc'_s'_f32"
| constant ocaml_i32_trunc_u_f64 \<rightharpoonup> (OCaml) "I32Wrapper'_convert.trunc'_u'_f64"
| constant ocaml_i32_trunc_s_f64 \<rightharpoonup> (OCaml) "I32Wrapper'_convert.trunc'_s'_f64"
| constant ocaml_i64_trunc_u_f32 \<rightharpoonup> (OCaml) "I64Wrapper'_convert.trunc'_u'_f32"
| constant ocaml_i64_trunc_s_f32 \<rightharpoonup> (OCaml) "I64Wrapper'_convert.trunc'_s'_f32"
| constant ocaml_i64_trunc_u_f64 \<rightharpoonup> (OCaml) "I64Wrapper'_convert.trunc'_u'_f64"
| constant ocaml_i64_trunc_s_f64 \<rightharpoonup> (OCaml) "I64Wrapper'_convert.trunc'_s'_f64"
| constant ocaml_i32_trunc_sat_u_f32 \<rightharpoonup> (OCaml) "I32Wrapper'_convert.trunc'_sat'_u'_f32"
| constant ocaml_i32_trunc_sat_s_f32 \<rightharpoonup> (OCaml) "I32Wrapper'_convert.trunc'_sat'_s'_f32"
| constant ocaml_i32_trunc_sat_u_f64 \<rightharpoonup> (OCaml) "I32Wrapper'_convert.trunc'_sat'_u'_f64"
| constant ocaml_i32_trunc_sat_s_f64 \<rightharpoonup> (OCaml) "I32Wrapper'_convert.trunc'_sat'_s'_f64"
| constant ocaml_i64_trunc_sat_u_f32 \<rightharpoonup> (OCaml) "I64Wrapper'_convert.trunc'_sat'_u'_f32"
| constant ocaml_i64_trunc_sat_s_f32 \<rightharpoonup> (OCaml) "I64Wrapper'_convert.trunc'_sat'_s'_f32"
| constant ocaml_i64_trunc_sat_u_f64 \<rightharpoonup> (OCaml) "I64Wrapper'_convert.trunc'_sat'_u'_f64"
| constant ocaml_i64_trunc_sat_s_f64 \<rightharpoonup> (OCaml) "I64Wrapper'_convert.trunc'_sat'_s'_f64"

| constant f32_serialise_ocaml_char \<rightharpoonup> (OCaml) "ImplWrapper.serialise'_f32"
| constant f64_serialise_ocaml_char \<rightharpoonup> (OCaml) "ImplWrapper.serialise'_f64"
| constant f32_deserialise_ocaml_char \<rightharpoonup> (OCaml) "ImplWrapper.deserialise'_f32"
| constant f64_deserialise_ocaml_char \<rightharpoonup> (OCaml) "ImplWrapper.deserialise'_f64"

| constant ocaml_i32_reinterpret_f32 \<rightharpoonup> (OCaml) "I32Wrapper'_convert.reinterpret'_of'_f32"
| constant ocaml_i64_reinterpret_f64 \<rightharpoonup> (OCaml) "I64Wrapper'_convert.reinterpret'_of'_f64"
| constant ocaml_f32_reinterpret_i32 \<rightharpoonup> (OCaml) "I32Wrapper'_convert.reinterpret'_to'_f32"
| constant ocaml_f64_reinterpret_i64 \<rightharpoonup> (OCaml) "I64Wrapper'_convert.reinterpret'_to'_f64"

definition f32_convert_u_isabelle_i32 :: "i32 \<Rightarrow> f32" where
  "f32_convert_u_isabelle_i32 i = f32_convert_u_ocaml_i32 (isabelle_int32_to_ocaml_int32 i)"

definition f32_convert_s_isabelle_i32 :: "i32 \<Rightarrow> f32" where
  "f32_convert_s_isabelle_i32 i = f32_convert_s_ocaml_i32 (isabelle_int32_to_ocaml_int32 i)"

definition f32_convert_u_isabelle_i64 :: "i64 \<Rightarrow> f32" where
  "f32_convert_u_isabelle_i64 i = f32_convert_u_ocaml_i64 (isabelle_int64_to_ocaml_int64 i)"

definition f32_convert_s_isabelle_i64 :: "i64 \<Rightarrow> f32" where
  "f32_convert_s_isabelle_i64 i = f32_convert_s_ocaml_i64 (isabelle_int64_to_ocaml_int64 i)"

definition f64_convert_u_isabelle_i32 :: "i32 \<Rightarrow> f64" where
  "f64_convert_u_isabelle_i32 i = f64_convert_u_ocaml_i32 (isabelle_int32_to_ocaml_int32 i)"

definition f64_convert_s_isabelle_i32 :: "i32 \<Rightarrow> f64" where
  "f64_convert_s_isabelle_i32 i = f64_convert_s_ocaml_i32 (isabelle_int32_to_ocaml_int32 i)"

definition f64_convert_u_isabelle_i64 :: "i64 \<Rightarrow> f64" where
  "f64_convert_u_isabelle_i64 i = f64_convert_u_ocaml_i64 (isabelle_int64_to_ocaml_int64 i)"

definition f64_convert_s_isabelle_i64 :: "i64 \<Rightarrow> f64" where
  "f64_convert_s_isabelle_i64 i = f64_convert_s_ocaml_i64 (isabelle_int64_to_ocaml_int64 i)"

definition isabelle_i32_trunc_u_f32 :: "f32 \<Rightarrow>i32 option" where
  "isabelle_i32_trunc_u_f32 f = map_option ocaml_int32_to_isabelle_int32 (ocaml_i32_trunc_u_f32 f)"

definition isabelle_i32_trunc_s_f32 :: "f32 \<Rightarrow>i32 option" where
  "isabelle_i32_trunc_s_f32 f = map_option ocaml_int32_to_isabelle_int32 (ocaml_i32_trunc_s_f32 f)"

definition isabelle_i32_trunc_u_f64 :: "f64 \<Rightarrow>i32 option" where
  "isabelle_i32_trunc_u_f64 f = map_option ocaml_int32_to_isabelle_int32 (ocaml_i32_trunc_u_f64 f)"

definition isabelle_i32_trunc_s_f64 :: "f64 \<Rightarrow>i32 option" where
  "isabelle_i32_trunc_s_f64 f = map_option ocaml_int32_to_isabelle_int32 (ocaml_i32_trunc_s_f64 f)"

definition isabelle_i64_trunc_u_f32 :: "f32 \<Rightarrow>i64 option" where
  "isabelle_i64_trunc_u_f32 f = map_option ocaml_int64_to_isabelle_int64 (ocaml_i64_trunc_u_f32 f)"

definition isabelle_i64_trunc_s_f32 :: "f32 \<Rightarrow>i64 option" where
  "isabelle_i64_trunc_s_f32 f = map_option ocaml_int64_to_isabelle_int64 (ocaml_i64_trunc_s_f32 f)"

definition isabelle_i64_trunc_u_f64 :: "f64 \<Rightarrow>i64 option" where
  "isabelle_i64_trunc_u_f64 f = map_option ocaml_int64_to_isabelle_int64 (ocaml_i64_trunc_u_f64 f)"

definition isabelle_i64_trunc_s_f64 :: "f64 \<Rightarrow>i64 option" where
  "isabelle_i64_trunc_s_f64 f = map_option ocaml_int64_to_isabelle_int64 (ocaml_i64_trunc_s_f64 f)"

definition isabelle_i32_trunc_sat_u_f32 :: "f32 \<Rightarrow>i32" where
  "isabelle_i32_trunc_sat_u_f32 f = ocaml_int32_to_isabelle_int32 (ocaml_i32_trunc_sat_u_f32 f)"

definition isabelle_i32_trunc_sat_s_f32 :: "f32 \<Rightarrow>i32" where
  "isabelle_i32_trunc_sat_s_f32 f = ocaml_int32_to_isabelle_int32 (ocaml_i32_trunc_sat_s_f32 f)"

definition isabelle_i32_trunc_sat_u_f64 :: "f64 \<Rightarrow>i32" where
  "isabelle_i32_trunc_sat_u_f64 f = ocaml_int32_to_isabelle_int32 (ocaml_i32_trunc_sat_u_f64 f)"

definition isabelle_i32_trunc_sat_s_f64 :: "f64 \<Rightarrow>i32" where
  "isabelle_i32_trunc_sat_s_f64 f = ocaml_int32_to_isabelle_int32 (ocaml_i32_trunc_sat_s_f64 f)"

definition isabelle_i64_trunc_sat_u_f32 :: "f32 \<Rightarrow>i64" where
  "isabelle_i64_trunc_sat_u_f32 f = ocaml_int64_to_isabelle_int64 (ocaml_i64_trunc_sat_u_f32 f)"

definition isabelle_i64_trunc_sat_s_f32 :: "f32 \<Rightarrow>i64" where
  "isabelle_i64_trunc_sat_s_f32 f = ocaml_int64_to_isabelle_int64 (ocaml_i64_trunc_sat_s_f32 f)"

definition isabelle_i64_trunc_sat_u_f64 :: "f64 \<Rightarrow>i64" where
  "isabelle_i64_trunc_sat_u_f64 f = ocaml_int64_to_isabelle_int64 (ocaml_i64_trunc_sat_u_f64 f)"

definition isabelle_i64_trunc_sat_s_f64 :: "f64 \<Rightarrow>i64" where
  "isabelle_i64_trunc_sat_s_f64 f = ocaml_int64_to_isabelle_int64 (ocaml_i64_trunc_sat_s_f64 f)"

definition f32_serialise_isabelle_bytes :: "f32 \<Rightarrow> bytes" where
  "f32_serialise_isabelle_bytes f = List.map ocaml_char_to_isabelle_byte (f32_serialise_ocaml_char f)"

definition f64_serialise_isabelle_bytes :: "f64 \<Rightarrow> bytes" where
  "f64_serialise_isabelle_bytes f = List.map ocaml_char_to_isabelle_byte (f64_serialise_ocaml_char f)"

definition f32_deserialise_isabelle_bytes :: "bytes \<Rightarrow> f32" where
  "f32_deserialise_isabelle_bytes bs = f32_deserialise_ocaml_char (List.map isabelle_byte_to_ocaml_char bs)"

definition f64_deserialise_isabelle_bytes :: "bytes \<Rightarrow> f64" where
  "f64_deserialise_isabelle_bytes bs = f64_deserialise_ocaml_char (List.map isabelle_byte_to_ocaml_char bs)"

axiomatization where
  f32_convert_ui32_is[code]: "f32_convert_ui32 \<equiv> f32_convert_u_isabelle_i32" and
  f32_convert_si32_is[code]: "f32_convert_si32 \<equiv> f32_convert_s_isabelle_i32" and
  f32_convert_ui64_is[code]: "f32_convert_ui64 \<equiv> f32_convert_u_isabelle_i64" and
  f32_convert_si64_is[code]: "f32_convert_si64 \<equiv> f32_convert_s_isabelle_i64" and
  f64_convert_ui32_is[code]: "f64_convert_ui32 \<equiv> f64_convert_u_isabelle_i32" and
  f64_convert_si32_is[code]: "f64_convert_si32 \<equiv> f64_convert_s_isabelle_i32" and
  f64_convert_ui64_is[code]: "f64_convert_ui64 \<equiv> f64_convert_u_isabelle_i64" and
  f64_convert_si64_is[code]: "f64_convert_si64 \<equiv> f64_convert_s_isabelle_i64" and

  ui32_trunc_f32_is[code]: "ui32_trunc_f32 \<equiv> isabelle_i32_trunc_u_f32" and
  si32_trunc_f32_is[code]: "si32_trunc_f32 \<equiv> isabelle_i32_trunc_s_f32" and
  ui32_trunc_f64_is[code]: "ui32_trunc_f64 \<equiv> isabelle_i32_trunc_u_f64" and
  si32_trunc_f64_is[code]: "si32_trunc_f64 \<equiv> isabelle_i32_trunc_s_f64" and
  ui64_trunc_f32_is[code]: "ui64_trunc_f32 \<equiv> isabelle_i64_trunc_u_f32" and
  si64_trunc_f32_is[code]: "si64_trunc_f32 \<equiv> isabelle_i64_trunc_s_f32" and
  ui64_trunc_f64_is[code]: "ui64_trunc_f64 \<equiv> isabelle_i64_trunc_u_f64" and
  si64_trunc_f64_is[code]: "si64_trunc_f64 \<equiv> isabelle_i64_trunc_s_f64" and
  ui32_trunc_sat_f32_is[code]: "ui32_trunc_sat_f32 \<equiv> isabelle_i32_trunc_sat_u_f32" and
  si32_trunc_sat_f32_is[code]: "si32_trunc_sat_f32 \<equiv> isabelle_i32_trunc_sat_s_f32" and
  ui32_trunc_sat_f64_is[code]: "ui32_trunc_sat_f64 \<equiv> isabelle_i32_trunc_sat_u_f64" and
  si32_trunc_sat_f64_is[code]: "si32_trunc_sat_f64 \<equiv> isabelle_i32_trunc_sat_s_f64" and
  ui64_trunc_sat_f32_is[code]: "ui64_trunc_sat_f32 \<equiv> isabelle_i64_trunc_sat_u_f32" and
  si64_trunc_sat_f32_is[code]: "si64_trunc_sat_f32 \<equiv> isabelle_i64_trunc_sat_s_f32" and
  ui64_trunc_sat_f64_is[code]: "ui64_trunc_sat_f64 \<equiv> isabelle_i64_trunc_sat_u_f64" and
  si64_trunc_sat_f64_is[code]: "si64_trunc_sat_f64 \<equiv> isabelle_i64_trunc_sat_s_f64" and

  serialise_f32_is[code]: "serialise_f32 \<equiv> f32_serialise_isabelle_bytes" and
  serialise_f64_is[code]: "serialise_f64 \<equiv> f64_serialise_isabelle_bytes" and
  deserialise_f32_is[code]: "deserialise_f32 \<equiv> f32_deserialise_isabelle_bytes" and
  deserialise_f64_is[code]: "deserialise_f64 \<equiv> f64_deserialise_isabelle_bytes" and

  ocaml_i32_reinterpret_f32_is: "ocaml_int32_to_isabelle_int32 (ocaml_i32_reinterpret_f32 f32) \<equiv> deserialise_i32 (serialise_f32 f32)" and
  ocaml_f32_reinterpret_i32_is: "(ocaml_f32_reinterpret_i32 (isabelle_int32_to_ocaml_int32 i32)) \<equiv> deserialise_f32 (serialise_i32 i32)" and
  ocaml_i64_reinterpret_f64_is: "ocaml_int64_to_isabelle_int64 (ocaml_i64_reinterpret_f64 f64) \<equiv> deserialise_i64 (serialise_f64 f64)" and
  ocaml_f64_reinterpret_i64_is: "(ocaml_f64_reinterpret_i64 (isabelle_int64_to_ocaml_int64 i64)) \<equiv> deserialise_f64 (serialise_i64 i64)"

lemma wasm_reinterpret_is[code]:
  "wasm_reinterpret t v =
     (case (t,v) of
       (T_f32, ConstInt32 c) \<Rightarrow> ConstFloat32 (ocaml_f32_reinterpret_i32 (isabelle_int32_to_ocaml_int32 c))
     | (T_f64, ConstInt64 c) \<Rightarrow> ConstFloat64 (ocaml_f64_reinterpret_i64 (isabelle_int64_to_ocaml_int64 c))
     | (T_i32, ConstFloat32 c) \<Rightarrow> ConstInt32 (ocaml_int32_to_isabelle_int32 (ocaml_i32_reinterpret_f32 c))
     | (T_i64, ConstFloat64 c) \<Rightarrow> ConstInt64 (ocaml_int64_to_isabelle_int64 (ocaml_i64_reinterpret_f64 c))
     | _ \<Rightarrow> (wasm_deserialise_num (bits_num v) t))"
  apply (cases t; cases v)
  apply (simp_all add: wasm_deserialise_num_def bits_num_def wasm_reinterpret_def ocaml_i32_reinterpret_f32_is ocaml_f32_reinterpret_i32_is ocaml_i64_reinterpret_f64_is ocaml_f64_reinterpret_i64_is)
  done

(* 1.1 vector ops *)
code_printing
  type_constructor v128 \<rightharpoonup> (OCaml) "V128Wrapper.t"
  | constant zero_v128_inst.zero_v128 \<rightharpoonup> (OCaml) "V128Wrapper.zero"
  | constant binop_vec_wf \<rightharpoonup> (OCaml) "V128Wrapper.binop'_vec'_wf"

consts
  v128_serialise_ocaml_char :: "v128 \<Rightarrow> ocaml_char list"
  v128_deserialise_ocaml_char :: "ocaml_char list \<Rightarrow> v128"

code_printing
  constant v128_serialise_ocaml_char \<rightharpoonup> (OCaml) "ImplWrapper.serialise'_v128"
| constant v128_deserialise_ocaml_char  \<rightharpoonup> (OCaml) "ImplWrapper.deserialise'_v128"

definition v128_serialise_isabelle_bytes :: "v128 \<Rightarrow> bytes" where
  "v128_serialise_isabelle_bytes v = List.map ocaml_char_to_isabelle_byte (v128_serialise_ocaml_char v)"

definition v128_deserialise_isabelle_bytes :: "bytes \<Rightarrow> v128" where
  "v128_deserialise_isabelle_bytes bs = v128_deserialise_ocaml_char (List.map isabelle_byte_to_ocaml_char bs)"

axiomatization where
  serialise_v128_is[code]: "serialise_v128 \<equiv> v128_serialise_isabelle_bytes" and
  deserialise_v128_is[code]: "deserialise_v128 \<equiv> v128_deserialise_isabelle_bytes"

code_printing
  type_constructor unop_vec \<rightharpoonup> (OCaml) "V128Wrapper.unop'_vec'_t"
| type_constructor binop_vec \<rightharpoonup> (OCaml) "V128Wrapper.binop'_vec'_t"
| type_constructor ternop_vec \<rightharpoonup> (OCaml) "V128Wrapper.ternop'_vec'_t"
| type_constructor testop_vec \<rightharpoonup> (OCaml) "V128Wrapper.testop'_vec'_t"
| type_constructor shiftop_vec \<rightharpoonup> (OCaml) "V128Wrapper.shiftop'_vec'_t"

consts
  ocaml_app_unop_vec_v :: "unop_vec \<Rightarrow> v128 \<Rightarrow> v128"
  ocaml_app_binop_vec_v :: "binop_vec \<Rightarrow> v128 \<Rightarrow> v128 \<Rightarrow> v128 option"
  ocaml_app_ternop_vec_v :: "ternop_vec \<Rightarrow> v128 \<Rightarrow> v128 \<Rightarrow> v128 \<Rightarrow> v128"
  ocaml_app_test_vec_v :: "testop_vec \<Rightarrow> v128 \<Rightarrow> ocaml_i32"
  ocaml_app_shift_vec_v :: "shiftop_vec \<Rightarrow> v128 \<Rightarrow> ocaml_i32 \<Rightarrow> v128"

code_printing
  constant ocaml_app_unop_vec_v \<rightharpoonup> (OCaml) "V128Wrapper.unop'_vec"
| constant ocaml_app_binop_vec_v \<rightharpoonup> (OCaml) "V128Wrapper.binop'_vec"
| constant ocaml_app_ternop_vec_v \<rightharpoonup> (OCaml) "V128Wrapper.ternop'_vec"
| constant ocaml_app_test_vec_v \<rightharpoonup> (OCaml) "V128Wrapper.test'_vec"
| constant ocaml_app_shift_vec_v \<rightharpoonup> (OCaml) "V128Wrapper.shift'_vec"

(* 1.1 vector ops *)
axiomatization where
  app_unop_vec_v_is[code]: "app_unop_vec_v \<equiv> ocaml_app_unop_vec_v" and
  app_binop_vec_v_is[code]: "app_binop_vec_v \<equiv> ocaml_app_binop_vec_v" and
  app_ternop_vec_v_is[code]: "app_ternop_vec_v \<equiv> ocaml_app_ternop_vec_v" and
  app_test_vec_v_is[code]: "app_test_vec_v op1 v \<equiv> ocaml_int32_to_isabelle_int32 (ocaml_app_test_vec_v op1 v)" and
  app_shift_vec_v_is[code]: "app_shift_vec_v op2 v n \<equiv> ocaml_app_shift_vec_v op2 v (isabelle_int32_to_ocaml_int32 n)"

(* arithmetic *)
code_printing
(* INT32 *)
  (* UNOPS *)
(*  constant wasm_int_ops_i32_inst.int_clz_i32 \<rightharpoonup> (OCaml) "I32Wrapper.clz"
| constant wasm_int_ops_i32_inst.int_ctz_i32 \<rightharpoonup> (OCaml) "I32Wrapper.ctz"
| constant wasm_int_ops_i32_inst.int_popcnt_i32 \<rightharpoonup> (OCaml) "I32Wrapper.popcnt"
  (* BINOPS - wrap *)
| constant wasm_int_ops_i32_inst.int_add_i32 \<rightharpoonup> (OCaml) "I32Wrapper.add"
| constant wasm_int_ops_i32_inst.int_sub_i32 \<rightharpoonup> (OCaml) "I32Wrapper.sub"
| constant wasm_int_ops_i32_inst.int_mul_i32 \<rightharpoonup> (OCaml) "I32Wrapper.mul"
| constant wasm_int_ops_i32_inst.int_div_u_i32 \<rightharpoonup> (OCaml) "I32Wrapper.div'_u"
| constant wasm_int_ops_i32_inst.int_div_s_i32 \<rightharpoonup> (OCaml) "I32Wrapper.div'_s"
| constant wasm_int_ops_i32_inst.int_rem_u_i32 \<rightharpoonup> (OCaml) "I32Wrapper.rem'_u"
| constant wasm_int_ops_i32_inst.int_rem_s_i32 \<rightharpoonup> (OCaml) "I32Wrapper.rem'_s"
| constant wasm_int_ops_i32_inst.int_and_i32 \<rightharpoonup> (OCaml) "I32Wrapper.and'_"
| constant wasm_int_ops_i32_inst.int_or_i32 \<rightharpoonup> (OCaml) "I32Wrapper.or'_"
| constant wasm_int_ops_i32_inst.int_xor_i32 \<rightharpoonup> (OCaml) "I32Wrapper.xor"
| constant wasm_int_ops_i32_inst.int_shl_i32 \<rightharpoonup> (OCaml) "I32Wrapper.shl"
| constant wasm_int_ops_i32_inst.int_shr_u_i32 \<rightharpoonup> (OCaml) "I32Wrapper.shr'_u"
| constant wasm_int_ops_i32_inst.int_shr_s_i32 \<rightharpoonup> (OCaml) "I32Wrapper.shr'_s"
| constant wasm_int_ops_i32_inst.int_rotl_i32 \<rightharpoonup> (OCaml) "I32Wrapper.rotl"
| constant wasm_int_ops_i32_inst.int_rotr_i32 \<rightharpoonup> (OCaml) "I32Wrapper.rotr"
  (* TESTOPS *)
| constant wasm_int_ops_i32_inst.int_eqz_i32 \<rightharpoonup> (OCaml) "I32Wrapper.eqz"
  (* RELOPS *)
| constant wasm_int_ops_i32_inst.int_eq_i32 \<rightharpoonup> (OCaml) "I32Wrapper.eq"
| constant wasm_int_ops_i32_inst.int_lt_u_i32 \<rightharpoonup> (OCaml) "I32Wrapper.lt'_u"
| constant wasm_int_ops_i32_inst.int_lt_s_i32 \<rightharpoonup> (OCaml) "I32Wrapper.lt'_s"
| constant wasm_int_ops_i32_inst.int_gt_u_i32 \<rightharpoonup> (OCaml) "I32Wrapper.gt'_u"
| constant wasm_int_ops_i32_inst.int_gt_s_i32 \<rightharpoonup> (OCaml) "I32Wrapper.gt'_s"
| constant wasm_int_ops_i32_inst.int_le_u_i32 \<rightharpoonup> (OCaml) "I32Wrapper.le'_u"
| constant wasm_int_ops_i32_inst.int_le_s_i32 \<rightharpoonup> (OCaml) "I32Wrapper.le'_s"
| constant wasm_int_ops_i32_inst.int_ge_u_i32 \<rightharpoonup> (OCaml) "I32Wrapper.ge'_u"
| constant wasm_int_ops_i32_inst.int_ge_s_i32 \<rightharpoonup> (OCaml) "I32Wrapper.ge'_s" *)
  (* CONVERSIONS *)
(*
  constant f32_convert_ui32 \<rightharpoonup> (OCaml) "F32Wrapper'_convert.convert'_u'_i32"
| constant f32_convert_si32 \<rightharpoonup> (OCaml) "F32Wrapper'_convert.convert'_s'_i32"
| constant f64_convert_ui32 \<rightharpoonup> (OCaml) "F64Wrapper'_convert.convert'_u'_i32"
| constant f64_convert_si32 \<rightharpoonup> (OCaml) "F64Wrapper'_convert.convert'_s'_i32"
*)
  (* VALUE CONVERSIONS - wrap *)
(* | constant wasm_int_ops_i32_inst.int_of_nat_i32 \<rightharpoonup> (OCaml) "I32Wrapper.int'_of'_z (integer'_of'_nat _)"
| constant wasm_int_ops_i32_inst.nat_of_int_i32 \<rightharpoonup> (OCaml) "Nat (I32Wrapper.z'_of'_int _)" *)
  (* SIGN EXTENDING DESERIALISATION TODO *)

(* INT64 *)
  (* UNOPS *)
(*| constant wasm_int_ops_i64_inst.int_clz_i64 \<rightharpoonup> (OCaml) "I64Wrapper.clz"
| constant wasm_int_ops_i64_inst.int_ctz_i64 \<rightharpoonup> (OCaml) "I64Wrapper.ctz"
| constant wasm_int_ops_i64_inst.int_popcnt_i64 \<rightharpoonup> (OCaml) "I64Wrapper.popcnt"
  (* BINOPS - wrap *)
| constant wasm_int_ops_i64_inst.int_add_i64 \<rightharpoonup> (OCaml) "I64Wrapper.add"
| constant wasm_int_ops_i64_inst.int_sub_i64 \<rightharpoonup> (OCaml) "I64Wrapper.sub"
| constant wasm_int_ops_i64_inst.int_mul_i64 \<rightharpoonup> (OCaml) "I64Wrapper.mul"
| constant wasm_int_ops_i64_inst.int_div_u_i64 \<rightharpoonup> (OCaml) "I64Wrapper.div'_u"
| constant wasm_int_ops_i64_inst.int_div_s_i64 \<rightharpoonup> (OCaml) "I64Wrapper.div'_s"
| constant wasm_int_ops_i64_inst.int_rem_u_i64 \<rightharpoonup> (OCaml) "I64Wrapper.rem'_u"
| constant wasm_int_ops_i64_inst.int_rem_s_i64 \<rightharpoonup> (OCaml) "I64Wrapper.rem'_s"
| constant wasm_int_ops_i64_inst.int_and_i64 \<rightharpoonup> (OCaml) "I64Wrapper.and'_"
| constant wasm_int_ops_i64_inst.int_or_i64 \<rightharpoonup> (OCaml) "I64Wrapper.or'_"
| constant wasm_int_ops_i64_inst.int_xor_i64 \<rightharpoonup> (OCaml) "I64Wrapper.xor"
| constant wasm_int_ops_i64_inst.int_shl_i64 \<rightharpoonup> (OCaml) "I64Wrapper.shl"
| constant wasm_int_ops_i64_inst.int_shr_u_i64 \<rightharpoonup> (OCaml) "I64Wrapper.shr'_u"
| constant wasm_int_ops_i64_inst.int_shr_s_i64 \<rightharpoonup> (OCaml) "I64Wrapper.shr'_s"
| constant wasm_int_ops_i64_inst.int_rotl_i64 \<rightharpoonup> (OCaml) "I64Wrapper.rotl"
| constant wasm_int_ops_i64_inst.int_rotr_i64 \<rightharpoonup> (OCaml) "I64Wrapper.rotr"
  (* TESTOPS *)
| constant wasm_int_ops_i64_inst.int_eqz_i64 \<rightharpoonup> (OCaml) "I64Wrapper.eqz"
  (* RELOPS *)
| constant wasm_int_ops_i64_inst.int_eq_i64 \<rightharpoonup> (OCaml) "I64Wrapper.eq"
| constant wasm_int_ops_i64_inst.int_lt_u_i64 \<rightharpoonup> (OCaml) "I64Wrapper.lt'_u"
| constant wasm_int_ops_i64_inst.int_lt_s_i64 \<rightharpoonup> (OCaml) "I64Wrapper.lt'_s"
| constant wasm_int_ops_i64_inst.int_gt_u_i64 \<rightharpoonup> (OCaml) "I64Wrapper.gt'_u"
| constant wasm_int_ops_i64_inst.int_gt_s_i64 \<rightharpoonup> (OCaml) "I64Wrapper.gt'_s"
| constant wasm_int_ops_i64_inst.int_le_u_i64 \<rightharpoonup> (OCaml) "I64Wrapper.le'_u"
| constant wasm_int_ops_i64_inst.int_le_s_i64 \<rightharpoonup> (OCaml) "I64Wrapper.le'_s"
| constant wasm_int_ops_i64_inst.int_ge_u_i64 \<rightharpoonup> (OCaml) "I64Wrapper.ge'_u"
| constant wasm_int_ops_i64_inst.int_ge_s_i64 \<rightharpoonup> (OCaml) "I64Wrapper.ge'_s" *)
  (* CONVERSIONS *)
(*
| constant f32_convert_ui64 \<rightharpoonup> (OCaml) "F32Wrapper'_convert.convert'_u'_i64"
| constant f32_convert_si64 \<rightharpoonup> (OCaml) "F32Wrapper'_convert.convert'_s'_i64"
| constant f64_convert_ui64 \<rightharpoonup> (OCaml) "F64Wrapper'_convert.convert'_u'_i64"
| constant f64_convert_si64 \<rightharpoonup> (OCaml) "F64Wrapper'_convert.convert'_s'_i64"
*)
  (* VALUE CONVERSIONS - wrap *)
(*| constant wasm_int_ops_i64_inst.int_of_nat_i64 \<rightharpoonup> (OCaml) "I64Wrapper.int'_of'_z (integer'_of'_nat _)"
| constant wasm_int_ops_i64_inst.nat_of_int_i64 \<rightharpoonup> (OCaml) "Nat (I64Wrapper.z'_of'_int _)" *)
(* FLOAT32 *)
  (* UNOPS *)
  constant wasm_float_f32_inst.float_neg_f32 \<rightharpoonup> (OCaml) "F32Wrapper.neg"
| constant wasm_float_f32_inst.float_abs_f32 \<rightharpoonup> (OCaml) "F32Wrapper.abs"
| constant wasm_float_f32_inst.float_ceil_f32 \<rightharpoonup> (OCaml) "F32Wrapper.ceil"
| constant wasm_float_f32_inst.float_floor_f32 \<rightharpoonup> (OCaml) "F32Wrapper.floor"
| constant wasm_float_f32_inst.float_trunc_f32 \<rightharpoonup> (OCaml) "F32Wrapper.trunc"
| constant wasm_float_f32_inst.float_nearest_f32 \<rightharpoonup> (OCaml) "F32Wrapper.nearest"
| constant wasm_float_f32_inst.float_sqrt_f32 \<rightharpoonup> (OCaml) "F32Wrapper.sqrt"
  (* BINOPS *)
| constant wasm_float_f32_inst.float_add_f32 \<rightharpoonup> (OCaml) "F32Wrapper.add"
| constant wasm_float_f32_inst.float_sub_f32 \<rightharpoonup> (OCaml) "F32Wrapper.sub"
| constant wasm_float_f32_inst.float_mul_f32 \<rightharpoonup> (OCaml) "F32Wrapper.mul"
| constant wasm_float_f32_inst.float_div_f32 \<rightharpoonup> (OCaml) "F32Wrapper.div"
| constant wasm_float_f32_inst.float_min_f32 \<rightharpoonup> (OCaml) "F32Wrapper.min"
| constant wasm_float_f32_inst.float_max_f32 \<rightharpoonup> (OCaml) "F32Wrapper.max"
| constant wasm_float_f32_inst.float_copysign_f32 \<rightharpoonup> (OCaml) "F32Wrapper.copysign"
  (* RELOPS *)
| constant wasm_float_f32_inst.float_eq_f32 \<rightharpoonup> (OCaml) "F32Wrapper.eq"
(* | constant wasm_float_f32_inst.float_ne_f32 \<rightharpoonup> (OCaml) "F32Wrapper.ne" *)
| constant wasm_float_f32_inst.float_lt_f32 \<rightharpoonup> (OCaml) "F32Wrapper.lt"
| constant wasm_float_f32_inst.float_gt_f32 \<rightharpoonup> (OCaml) "F32Wrapper.gt"
| constant wasm_float_f32_inst.float_le_f32 \<rightharpoonup> (OCaml) "F32Wrapper.le"
| constant wasm_float_f32_inst.float_ge_f32 \<rightharpoonup> (OCaml) "F32Wrapper.ge"
  (* CONVERSIONS *)
(*
| constant ui32_trunc_f32 \<rightharpoonup> (OCaml) "I32Wrapper'_convert.trunc'_u'_f32"
| constant si32_trunc_f32 \<rightharpoonup> (OCaml) "I32Wrapper'_convert.trunc'_s'_f32"
| constant ui64_trunc_f32 \<rightharpoonup> (OCaml) "I64Wrapper'_convert.trunc'_u'_f32"
| constant si64_trunc_f32 \<rightharpoonup> (OCaml) "I64Wrapper'_convert.trunc'_s'_f32"
*)
(* FLOAT64 *)
  (* UNOPS *)
| constant wasm_float_f64_inst.float_neg_f64 \<rightharpoonup> (OCaml) "F64Wrapper.neg"
| constant wasm_float_f64_inst.float_abs_f64 \<rightharpoonup> (OCaml) "F64Wrapper.abs"
| constant wasm_float_f64_inst.float_ceil_f64 \<rightharpoonup> (OCaml) "F64Wrapper.ceil"
| constant wasm_float_f64_inst.float_floor_f64 \<rightharpoonup> (OCaml) "F64Wrapper.floor"
| constant wasm_float_f64_inst.float_trunc_f64 \<rightharpoonup> (OCaml) "F64Wrapper.trunc"
| constant wasm_float_f64_inst.float_nearest_f64 \<rightharpoonup> (OCaml) "F64Wrapper.nearest"
| constant wasm_float_f64_inst.float_sqrt_f64 \<rightharpoonup> (OCaml) "F64Wrapper.sqrt"
  (* BINOPS *)
| constant wasm_float_f64_inst.float_add_f64 \<rightharpoonup> (OCaml) "F64Wrapper.add"
| constant wasm_float_f64_inst.float_sub_f64 \<rightharpoonup> (OCaml) "F64Wrapper.sub"
| constant wasm_float_f64_inst.float_mul_f64 \<rightharpoonup> (OCaml) "F64Wrapper.mul"
| constant wasm_float_f64_inst.float_div_f64 \<rightharpoonup> (OCaml) "F64Wrapper.div"
| constant wasm_float_f64_inst.float_min_f64 \<rightharpoonup> (OCaml) "F64Wrapper.min"
| constant wasm_float_f64_inst.float_max_f64 \<rightharpoonup> (OCaml) "F64Wrapper.max"
| constant wasm_float_f64_inst.float_copysign_f64 \<rightharpoonup> (OCaml) "F64Wrapper.copysign"
  (* RELOPS *)
| constant wasm_float_f64_inst.float_eq_f64 \<rightharpoonup> (OCaml) "F64Wrapper.eq"
(* | constant wasm_float_f64_inst.float_ne_f64 \<rightharpoonup> (OCaml) "F64Wrapper.ne" *)
| constant wasm_float_f64_inst.float_lt_f64 \<rightharpoonup> (OCaml) "F64Wrapper.lt"
| constant wasm_float_f64_inst.float_gt_f64 \<rightharpoonup> (OCaml) "F64Wrapper.gt"
| constant wasm_float_f64_inst.float_le_f64 \<rightharpoonup> (OCaml) "F64Wrapper.le"
| constant wasm_float_f64_inst.float_ge_f64 \<rightharpoonup> (OCaml) "F64Wrapper.ge"
  (* CONVERSIONS *)
(*
| constant ui32_trunc_f64 \<rightharpoonup> (OCaml) "I32Wrapper'_convert.trunc'_u'_f64"
| constant si32_trunc_f64 \<rightharpoonup> (OCaml) "I32Wrapper'_convert.trunc'_s'_f64"
| constant ui64_trunc_f64 \<rightharpoonup> (OCaml) "I64Wrapper'_convert.trunc'_u'_f64"
| constant si64_trunc_f64 \<rightharpoonup> (OCaml) "I64Wrapper'_convert.trunc'_s'_f64"
*)
(*
code_printing
  constant serialise_i32 \<rightharpoonup> (OCaml) "ImplWrapper.serialise'_i32"
| constant serialise_i64 \<rightharpoonup> (OCaml) "ImplWrapper.serialise'_i64"
| constant serialise_f32 \<rightharpoonup> (OCaml) "ImplWrapper.serialise'_f32"
| constant serialise_f64 \<rightharpoonup> (OCaml) "ImplWrapper.serialise'_f64"
| constant deserialise_i32 \<rightharpoonup> (OCaml) "ImplWrapper.deserialise'_i32"
| constant deserialise_i64 \<rightharpoonup> (OCaml) "ImplWrapper.deserialise'_i64"
| constant deserialise_f32 \<rightharpoonup> (OCaml) "ImplWrapper.deserialise'_f32"
| constant deserialise_f64 \<rightharpoonup> (OCaml) "ImplWrapper.deserialise'_f64"
| constant wasm_bool \<rightharpoonup> (OCaml) "ImplWrapper.bool"
| constant int32_minus_one \<rightharpoonup> (OCaml) "I32Wrapper.minus'_one" *)

end