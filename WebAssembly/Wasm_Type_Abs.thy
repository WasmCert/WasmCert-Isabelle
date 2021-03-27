section {* Syntactic Typeclasses *}

theory Wasm_Type_Abs imports
  Main
  "HOL-Library.Type_Length"
  HOL.Rat
begin

class wasm_base = zero

class wasm_int_ops = wasm_base + len +
  (* unops*)
  fixes int_clz :: "'a \<Rightarrow> 'a"
  fixes int_ctz :: "'a \<Rightarrow> 'a"
  fixes int_popcnt :: "'a \<Rightarrow> 'a"
  (* binops *)
  fixes int_add :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  fixes int_sub :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  fixes int_mul :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  fixes int_div_u :: "'a \<Rightarrow> 'a \<Rightarrow> 'a option"
  fixes int_div_s :: "'a \<Rightarrow> 'a \<Rightarrow> 'a option"
  fixes int_rem_u :: "'a \<Rightarrow> 'a \<Rightarrow> 'a option"
  fixes int_rem_s :: "'a \<Rightarrow> 'a \<Rightarrow> 'a option"
  fixes int_and :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  fixes int_or :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  fixes int_xor :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  fixes int_shl :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  fixes int_shr_u :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  fixes int_shr_s :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  fixes int_rotl :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  fixes int_rotr :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  (* testops *)
  fixes int_eqz :: "'a \<Rightarrow> bool"
  (* relops *)
  fixes int_eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  fixes int_lt_u :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  fixes int_lt_s :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  fixes int_gt_u :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  fixes int_gt_s :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  fixes int_le_u :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  fixes int_le_s :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  fixes int_ge_u :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  fixes int_ge_s :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  (* value conversions *)
  fixes int_of_nat :: "nat \<Rightarrow> 'a"
  fixes nat_of_int :: "'a \<Rightarrow> nat"
begin
  abbreviation (input)
  int_ne where
    "int_ne x y \<equiv> \<not> (int_eq x y)"

  text\<open>
  Convert a concrete wasm_int (usually a word) to its "abstract" integer representation,
  as used in the Wasm specs, where the whole integer domain is considered.
  \<close>
  abbreviation abs_int :: "'a \<Rightarrow> int"
    where "abs_int a \<equiv> int (nat_of_int a)"

  abbreviation rep_int :: "int \<Rightarrow> 'a"
    where "rep_int a \<equiv> int_of_nat (nat a)"
end

(* https://webassembly.github.io/spec/core/exec/numerics.html *)

definition trunc :: "rat \<Rightarrow> int" where
  "trunc q \<equiv>
    if 0 \<le> q
    then int (THE i::nat. q - 1 < rat_of_nat i \<and> rat_of_nat i \<le> q)
    else - int (THE i::nat. \<bar>q\<bar> - 1 < rat_of_nat i \<and> rat_of_nat i \<le> \<bar>q\<bar>)"

lemma trunc_exists1:
  assumes "0 \<le> q"
  shows "\<exists>!i. q - 1 < rat_of_nat i \<and> rat_of_nat i \<le> q"
proof -
  let ?F = "\<lambda>z. rat_of_int z \<le> q \<and> q < rat_of_int (z + 1)"
  let ?T = "\<lambda>i. q - 1 < rat_of_nat i \<and> rat_of_nat i \<le> q"
  obtain z where z: "?F z" "\<And>z'. ?F z' \<Longrightarrow> ?F z" using floor_exists1[of q] ..
  hence "q - 1 < rat_of_int z" by linarith
  moreover have "rat_of_int z \<le> q" using z(1) by blast
  moreover have "z \<ge> 0" using assms z(1) by linarith
  ultimately have "?T (nat z)" "\<And>i'. ?T i' \<Longrightarrow> i' = (nat z)" using z by auto
  thus ?thesis by blast
qed

lemma trunc: "trunc q = (if 0 \<le> q then \<lfloor>q\<rfloor> else -\<lfloor>-q\<rfloor>)"
proof -
  {
    fix q :: rat assume q: "0 \<le> q"
    have "(THE i::nat. q - 1 < rat_of_nat i \<and> rat_of_nat i \<le> q) = nat \<lfloor>q\<rfloor>"
      apply (rule the1_equality[OF trunc_exists1[OF q]])
      using q floor_less_cancel by force
  }
  thus ?thesis unfolding trunc_def by auto
qed

class wasm_int = wasm_int_ops +
  assumes zero: "nat_of_int (0::'a) = 0"
  assumes add: "int_add (a::'a) b =
    rep_int ((abs_int a + abs_int b) mod (2^LENGTH('a)))"
  assumes sub: "int_sub (a::'a) b =
    rep_int ((abs_int a - abs_int b + (2^LENGTH('a))) mod (2^LENGTH('a)))"
  assumes mul: "int_mul (a::'a) b =
    rep_int ((abs_int a * abs_int b) mod (2^LENGTH('a)))"
  assumes div_u_0: "b = 0 \<Longrightarrow> int_div_u (a::'a) b = None"
  assumes div_u_n0: "b \<noteq> 0 \<Longrightarrow> int_div_u (a::'a) b =
    Some (rep_int (trunc (of_int (abs_int a) / of_int (abs_int b))))"

class wasm_float = wasm_base +
  (* unops *)
  fixes float_neg     :: "'a \<Rightarrow> 'a"
  fixes float_abs     :: "'a \<Rightarrow> 'a"
  fixes float_ceil    :: "'a \<Rightarrow> 'a"
  fixes float_floor   :: "'a \<Rightarrow> 'a"
  fixes float_trunc   :: "'a \<Rightarrow> 'a"
  fixes float_nearest :: "'a \<Rightarrow> 'a"
  fixes float_sqrt    :: "'a \<Rightarrow> 'a"
  (* binops *)
  fixes float_add :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  fixes float_sub :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  fixes float_mul :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  fixes float_div :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  fixes float_min :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  fixes float_max :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  fixes float_copysign :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  (* relops *)
  fixes float_eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  fixes float_lt :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  fixes float_gt :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  fixes float_le :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  fixes float_ge :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
begin
  abbreviation (input)
  float_ne where
    "float_ne x y \<equiv> \<not> (float_eq x y)"
end
end