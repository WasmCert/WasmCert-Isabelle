theory Wasm_Type_Printing imports Wasm_Base_Defs begin
(* Maps types to Andreas' Ocaml implementation - a thin wrapper over Ocaml ints/floats for the most part. *)

code_printing
  type_constructor i32 \<rightharpoonup> (OCaml) "I32Wrapper.t"
| type_constructor i64 \<rightharpoonup> (OCaml) "I64Wrapper.t"
| type_constructor f32 \<rightharpoonup> (OCaml) "F32Wrapper.t"
| type_constructor f64 \<rightharpoonup> (OCaml) "F64Wrapper.t"

(* zero consts *)
code_printing
  constant zero_i32_inst.zero_i32 \<rightharpoonup> (OCaml) "I32Wrapper.zero"
| constant zero_i64_inst.zero_i64 \<rightharpoonup> (OCaml) "I64Wrapper.zero"
| constant zero_f32_inst.zero_f32 \<rightharpoonup> (OCaml) "F32Wrapper.zero"
| constant zero_f64_inst.zero_f64 \<rightharpoonup> (OCaml) "F64Wrapper.zero"

(* intra-{int,float} conversions *)
code_printing
  constant wasm_wrap \<rightharpoonup> (OCaml) "(I32Wrapper'_convert.wrap'_i64)"
| constant wasm_extend_u \<rightharpoonup> (OCaml) "(I64Wrapper'_convert.extend'_u'_i32)"
| constant wasm_extend_s \<rightharpoonup> (OCaml) "(I64Wrapper'_convert.extend'_s'_i32)"
| constant wasm_demote \<rightharpoonup> (OCaml) "(F32Wrapper'_convert.demote'_f64)"
| constant wasm_promote \<rightharpoonup> (OCaml) "(F64Wrapper'_convert.promote'_f32)"

text\<open>
Repeat all code equations explicitly again because the ones like @{const I32.int_clz} do not work
in export_code. Most of these are simply the original definitions, but we can also do some minor
optimizations like in @{const int_shl} and others below.
\<close>
lemma[code]: "int_clz (Abs_i32 x) = Abs_i32 (of_nat (word_clz x))"
  by (simp add: I32.int_clz_def int_clz_i32.abs_eq)
lemma[code]: "int_ctz (Abs_i32 x) = Abs_i32 (of_nat (word_ctz x))"
  by (simp add: I32.int_ctz_def int_ctz_i32.abs_eq)
lemma[code]: "int_popcnt (Abs_i32 x) = Abs_i32 (of_nat (pop_count x))"
  by (simp add: I32.int_popcnt_def int_popcnt_i32.abs_eq)
lemma[code]: "int_add (Abs_i32 x) (Abs_i32 y) = Abs_i32 (x + y)"
  by (simp add: I32.int_add_def int_add_i32.abs_eq)
lemma[code]: "int_sub (Abs_i32 x) (Abs_i32 y) = Abs_i32 (x - y)"
  by (simp add: I32.int_sub_def int_sub_i32.abs_eq)
lemma[code]: "int_mul (Abs_i32 x) (Abs_i32 y) = Abs_i32 (x * y)"
  by (simp add: I32.int_mul_def int_mul_i32.abs_eq)
lemma[code]: "int_div_u (Abs_i32 x) (Abs_i32 y) =
  (if y = 0 then None else Some (Abs_i32 (x div y)))"
  by (simp add: int_div_u_i32.abs_eq I32.int_div_u_def)
lemma[code]: "int_div_s (Abs_i32 x) (Abs_i32 y) =
  (if y = 0 \<or> (x = of_int (-(2^(LENGTH(i32) - 1))) \<and> y = of_int (-1))
  then None else Some (Abs_i32 (x sdiv y)))"
  by (simp add: int_div_s_i32.abs_eq I32.int_div_s_def)
lemma[code]: "int_rem_u (Abs_i32 x) (Abs_i32 y) =
  (if y = 0 then None else Some (Abs_i32 (x mod y)))"
  by (simp add: int_rem_u_i32.abs_eq I32.int_rem_u_def)
lemma[code]: "int_rem_s (Abs_i32 x) (Abs_i32 y) =
  (if y = 0 then None else Some (Abs_i32 (x smod y)))"
  by (simp add: int_rem_s_i32.abs_eq I32.int_rem_s_def)
lemma[code]: "int_and (Abs_i32 x) (Abs_i32 y) = Abs_i32 (x AND y)"
  by (simp add: I32.int_and_def int_and_i32.abs_eq)
lemma[code]: "int_or (Abs_i32 x) (Abs_i32 y) = Abs_i32 (x OR y)"
  by (simp add: I32.int_or_def int_or_i32.abs_eq)
lemma[code]: "int_xor (Abs_i32 x) (Abs_i32 y) = Abs_i32 (x XOR y)"
  by (simp add: I32.int_xor_def int_xor_i32.abs_eq)
lemma mod_i32: "x AND 31 = x mod LENGTH(i32)"
proof -
  have int: "int x mod (int LENGTH(i32)) = int x AND 31" using AND_mod[of "int x" 5] by simp
  thus ?thesis by (simp add: int int_ops(3) nat_int.Rep_eqD of_nat_and_eq zmod_int)
qed
lemma[code]: "int_shl (Abs_i32 x) (Abs_i32 y) = Abs_i32 (x << (unat y AND 31))"
  by (simp add: I32.int_shl_def int_shl_i32.abs_eq mod_i32)
lemma[code]: "int_shr_u (Abs_i32 x) (Abs_i32 y) = Abs_i32 (x >> (unat y AND 31))"
  by (simp add: I32.int_shr_u_def int_shr_u_i32.abs_eq mod_i32)
lemma[code]: "int_shr_s (Abs_i32 x) (Abs_i32 y) = Abs_i32 (x >>> (unat y AND 31))"
  by (simp add: I32.int_shr_s_def int_shr_s_i32.abs_eq mod_i32)
lemma[code]: "int_rotl (Abs_i32 x) (Abs_i32 y) = Abs_i32 (word_rotl (unat y) x)"
  by (simp add: I32.int_rotl_def int_rotl_i32.abs_eq)
lemma[code]: "int_rotr (Abs_i32 x) (Abs_i32 y) = Abs_i32 (word_rotr (unat y) x)"
  by (simp add: I32.int_rotr_def int_rotr_i32.abs_eq)
lemma[code]: "int_eqz (Abs_i32 x) \<longleftrightarrow> x = 0"
proof -
  have "x = 0 \<longleftrightarrow> Abs_i32 x = 0"
    unfolding zero_i32_def
    by (metis Abs_fnat_hom_0 I32.rep_abs)
  thus ?thesis using I32.int_eqz_def int_eqz_i32.rep_eq by presburger
qed
lemma[code]: "int_eq (Abs_i32 x) (Abs_i32 y) \<longleftrightarrow> x = y"
  by (simp add: I32.int_eq_def int_eq_i32.abs_eq)
lemma[code]: "int_lt_u (Abs_i32 x) (Abs_i32 y) \<longleftrightarrow> x < y"
  by (simp add: I32.int_lt_u_def int_lt_u_i32.abs_eq)
lemma[code]: "int_lt_s (Abs_i32 x) (Abs_i32 y) \<longleftrightarrow> x <s y"
  by (simp add: I32.int_lt_s_def int_lt_s_i32.abs_eq)
lemma[code]: "int_gt_u (Abs_i32 x) (Abs_i32 y) \<longleftrightarrow> x > y"
  by (simp add: I32.int_gt_u_def int_gt_u_i32.abs_eq)
lemma[code]: "int_gt_s (Abs_i32 x) (Abs_i32 y) \<longleftrightarrow> signed.greater x y"
  by (simp add: I32.int_gt_s_def int_gt_s_i32.abs_eq)
lemma[code]: "int_le_u (Abs_i32 x) (Abs_i32 y) \<longleftrightarrow> x \<le> y"
  by (simp add: I32.int_le_u_def int_le_u_i32.abs_eq)
lemma[code]: "int_le_s (Abs_i32 x) (Abs_i32 y) \<longleftrightarrow> x \<le>s y"
  by (simp add: I32.int_le_s_def int_le_s_i32.abs_eq)
lemma[code]: "int_ge_u (Abs_i32 x) (Abs_i32 y) \<longleftrightarrow> x \<ge> y"
  by (simp add: I32.int_ge_u_def int_ge_u_i32.abs_eq)
lemma[code]: "int_ge_s (Abs_i32 x) (Abs_i32 y) \<longleftrightarrow> signed.greater_eq x y"
  by (simp add: I32.int_ge_s_def int_ge_s_i32.abs_eq)

lemma[code]: "int_clz (Abs_i64 x) = Abs_i64 (of_nat (word_clz x))"
  by (simp add: I64.int_clz_def int_clz_i64.abs_eq)
lemma[code]: "int_ctz (Abs_i64 x) = Abs_i64 (of_nat (word_ctz x))"
  by (simp add: I64.int_ctz_def int_ctz_i64.abs_eq)
lemma[code]: "int_popcnt (Abs_i64 x) = Abs_i64 (of_nat (pop_count x))"
  by (simp add: I64.int_popcnt_def int_popcnt_i64.abs_eq)
lemma[code]: "int_add (Abs_i64 x) (Abs_i64 y) = Abs_i64 (x + y)"
  by (simp add: I64.int_add_def int_add_i64.abs_eq)
lemma[code]: "int_sub (Abs_i64 x) (Abs_i64 y) = Abs_i64 (x - y)"
  by (simp add: I64.int_sub_def int_sub_i64.abs_eq)
lemma[code]: "int_mul (Abs_i64 x) (Abs_i64 y) = Abs_i64 (x * y)"
  by (simp add: I64.int_mul_def int_mul_i64.abs_eq)
lemma[code]: "int_div_u (Abs_i64 x) (Abs_i64 y) =
  (if y = 0 then None else Some (Abs_i64 (x div y)))"
  by (simp add: int_div_u_i64.abs_eq I64.int_div_u_def)
lemma[code]: "int_div_s (Abs_i64 x) (Abs_i64 y) =
  (if y = 0 \<or> (x = of_int (-(2^(LENGTH(i64) - 1))) \<and> y = of_int (-1))
  then None else Some (Abs_i64 (x sdiv y)))"
  by (simp add: int_div_s_i64.abs_eq I64.int_div_s_def)
lemma[code]: "int_rem_u (Abs_i64 x) (Abs_i64 y) =
  (if y = 0 then None else Some (Abs_i64 (x mod y)))"
  by (simp add: int_rem_u_i64.abs_eq I64.int_rem_u_def)
lemma[code]: "int_rem_s (Abs_i64 x) (Abs_i64 y) =
  (if y = 0 then None else Some (Abs_i64 (x smod y)))"
  by (simp add: int_rem_s_i64.abs_eq I64.int_rem_s_def)
lemma[code]: "int_and (Abs_i64 x) (Abs_i64 y) = Abs_i64 (x AND y)"
  by (simp add: I64.int_and_def int_and_i64.abs_eq)
lemma[code]: "int_or (Abs_i64 x) (Abs_i64 y) = Abs_i64 (x OR y)"
  by (simp add: I64.int_or_def int_or_i64.abs_eq)
lemma[code]: "int_xor (Abs_i64 x) (Abs_i64 y) = Abs_i64 (x XOR y)"
  by (simp add: I64.int_xor_def int_xor_i64.abs_eq)
lemma mod_i64: "x AND 63 = x mod LENGTH(i64)"
proof -
  have int: "int x mod (int LENGTH(i64)) = int x AND 63" using AND_mod[of "int x" 6] by simp
  thus ?thesis by (simp add: int int_ops(3) nat_int.Rep_eqD of_nat_and_eq zmod_int)
qed
lemma[code]: "int_shl (Abs_i64 x) (Abs_i64 y) = Abs_i64 (x << (unat y AND 63))"
  by (simp add: I64.int_shl_def int_shl_i64.abs_eq mod_i64)
lemma[code]: "int_shr_u (Abs_i64 x) (Abs_i64 y) = Abs_i64 (x >> (unat y AND 63))"
  by (simp add: I64.int_shr_u_def int_shr_u_i64.abs_eq mod_i64)
lemma[code]: "int_shr_s (Abs_i64 x) (Abs_i64 y) = Abs_i64 (x >>> (unat y AND 63))"
  by (simp add: I64.int_shr_s_def int_shr_s_i64.abs_eq mod_i64)
lemma[code]: "int_rotl (Abs_i64 x) (Abs_i64 y) = Abs_i64 (word_rotl (unat y) x)"
  by (simp add: I64.int_rotl_def int_rotl_i64.abs_eq)
lemma[code]: "int_rotr (Abs_i64 x) (Abs_i64 y) = Abs_i64 (word_rotr (unat y) x)"
  by (simp add: I64.int_rotr_def int_rotr_i64.abs_eq)
lemma[code]: "int_eqz (Abs_i64 x) \<longleftrightarrow> x = 0"
proof -
  have "x = 0 \<longleftrightarrow> Abs_i64 x = 0"
    unfolding zero_i64_def
    by (metis Abs_fnat_hom_0 I64.rep_abs)
  thus ?thesis using I64.int_eqz_def int_eqz_i64.rep_eq by presburger
qed
lemma[code]: "int_eq (Abs_i64 x) (Abs_i64 y) \<longleftrightarrow> x = y"
  by (simp add: I64.int_eq_def int_eq_i64.abs_eq)
lemma[code]: "int_lt_u (Abs_i64 x) (Abs_i64 y) \<longleftrightarrow> x < y"
  by (simp add: I64.int_lt_u_def int_lt_u_i64.abs_eq)
lemma[code]: "int_lt_s (Abs_i64 x) (Abs_i64 y) \<longleftrightarrow> x <s y"
  by (simp add: I64.int_lt_s_def int_lt_s_i64.abs_eq)
lemma[code]: "int_gt_u (Abs_i64 x) (Abs_i64 y) \<longleftrightarrow> x > y"
  by (simp add: I64.int_gt_u_def int_gt_u_i64.abs_eq)
lemma[code]: "int_gt_s (Abs_i64 x) (Abs_i64 y) \<longleftrightarrow> signed.greater x y"
  by (simp add: I64.int_gt_s_def int_gt_s_i64.abs_eq)
lemma[code]: "int_le_u (Abs_i64 x) (Abs_i64 y) \<longleftrightarrow> x \<le> y"
  by (simp add: I64.int_le_u_def int_le_u_i64.abs_eq)
lemma[code]: "int_le_s (Abs_i64 x) (Abs_i64 y) \<longleftrightarrow> x \<le>s y"
  by (simp add: I64.int_le_s_def int_le_s_i64.abs_eq)
lemma[code]: "int_ge_u (Abs_i64 x) (Abs_i64 y) \<longleftrightarrow> x \<ge> y"
  by (simp add: I64.int_ge_u_def int_ge_u_i64.abs_eq)
lemma[code]: "int_ge_s (Abs_i64 x) (Abs_i64 y) \<longleftrightarrow> signed.greater_eq x y"
  by (simp add: I64.int_ge_s_def int_ge_s_i64.abs_eq)

(* arithmetic *)
code_printing
(* INT32 *)
  (* UNOPS *)
  constant wasm_int_ops_i32_inst.int_clz_i32 \<rightharpoonup> (OCaml) "I32Wrapper.clz"
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
| constant wasm_int_ops_i32_inst.int_ge_s_i32 \<rightharpoonup> (OCaml) "I32Wrapper.ge'_s"
  (* CONVERSIONS *)
| constant f32_convert_ui32 \<rightharpoonup> (OCaml) "F32Wrapper'_convert.convert'_u'_i32"
| constant f32_convert_si32 \<rightharpoonup> (OCaml) "F32Wrapper'_convert.convert'_s'_i32"
| constant f64_convert_ui32 \<rightharpoonup> (OCaml) "F64Wrapper'_convert.convert'_u'_i32"
| constant f64_convert_si32 \<rightharpoonup> (OCaml) "F64Wrapper'_convert.convert'_s'_i32"
  (* VALUE CONVERSIONS - wrap *)
| constant wasm_int_ops_i32_inst.int_of_nat_i32 \<rightharpoonup> (OCaml) "I32Wrapper.int'_of'_z (integer'_of'_nat _)"
| constant wasm_int_ops_i32_inst.nat_of_int_i32 \<rightharpoonup> (OCaml) "Nat (I32Wrapper.z'_of'_int _)"
  (* SIGN EXTENDING DESERIALISATION TODO *)

(* INT64 *)
  (* UNOPS *)
| constant wasm_int_ops_i64_inst.int_clz_i64 \<rightharpoonup> (OCaml) "I64Wrapper.clz"
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
| constant wasm_int_ops_i64_inst.int_ge_s_i64 \<rightharpoonup> (OCaml) "I64Wrapper.ge'_s"
  (* CONVERSIONS *)
| constant f32_convert_ui64 \<rightharpoonup> (OCaml) "F32Wrapper'_convert.convert'_u'_i64"
| constant f32_convert_si64 \<rightharpoonup> (OCaml) "F32Wrapper'_convert.convert'_s'_i64"
| constant f64_convert_ui64 \<rightharpoonup> (OCaml) "F64Wrapper'_convert.convert'_u'_i64"
| constant f64_convert_si64 \<rightharpoonup> (OCaml) "F64Wrapper'_convert.convert'_s'_i64"
  (* VALUE CONVERSIONS - wrap *)
| constant wasm_int_ops_i64_inst.int_of_nat_i64 \<rightharpoonup> (OCaml) "I64Wrapper.int'_of'_z (integer'_of'_nat _)"
| constant wasm_int_ops_i64_inst.nat_of_int_i64 \<rightharpoonup> (OCaml) "Nat (I64Wrapper.z'_of'_int _)"
(* FLOAT32 *)
  (* UNOPS *)
| constant wasm_float_f32_inst.float_neg_f32 \<rightharpoonup> (OCaml) "F32Wrapper.neg"
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
| constant ui32_trunc_f32 \<rightharpoonup> (OCaml) "I32Wrapper'_convert.trunc'_u'_f32"
| constant si32_trunc_f32 \<rightharpoonup> (OCaml) "I32Wrapper'_convert.trunc'_s'_f32"
| constant ui64_trunc_f32 \<rightharpoonup> (OCaml) "I64Wrapper'_convert.trunc'_u'_f32"
| constant si64_trunc_f32 \<rightharpoonup> (OCaml) "I64Wrapper'_convert.trunc'_s'_f32"
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
| constant ui32_trunc_f64 \<rightharpoonup> (OCaml) "I32Wrapper'_convert.trunc'_u'_f64"
| constant si32_trunc_f64 \<rightharpoonup> (OCaml) "I32Wrapper'_convert.trunc'_s'_f64"
| constant ui64_trunc_f64 \<rightharpoonup> (OCaml) "I64Wrapper'_convert.trunc'_u'_f64"
| constant si64_trunc_f64 \<rightharpoonup> (OCaml) "I64Wrapper'_convert.trunc'_s'_f64"

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
| constant int32_minus_one \<rightharpoonup> (OCaml) "I32Wrapper.minus'_one"

end