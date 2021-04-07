section {* Syntactic Typeclasses *}

theory Wasm_Type_Abs imports
  Main
  "HOL-Library.Type_Length"
  HOL.Rat
begin

(* https://webassembly.github.io/spec/core/exec/numerics.html *)

context len
begin

lemma half_power:
  "2 ^ LENGTH('a) = 2 * 2 ^ (LENGTH('a) - 1)"
  using power_Suc[of 2 "LENGTH('a) - 1"] by simp

text\<open>Interpret an unsigned number i obtained from a word of size N as signed.\<close>
definition signed :: "'a itself \<Rightarrow> int \<Rightarrow> int" where
  "signed _ i \<equiv>
    if 0 \<le> i \<and> i < (2^(LENGTH('a)-1)) then i
    else if 2^(LENGTH('a)-1) \<le> i \<and> i < 2^LENGTH('a) then i - (2^LENGTH('a))
    else 0"

text\<open>Inverse of signed, refined below.\<close>
definition signed_inv :: "'a itself \<Rightarrow> int \<Rightarrow> int" where
  "signed_inv N \<equiv> the_inv_into {0 ..< 2^LENGTH('a)} (signed N)"

lemma signed_inj: "inj_on (signed (N::'a itself)) {0 ..< 2^LENGTH('a)}"
proof (rule inj_onI, goal_cases)
  case (1 x y)
  thus ?case unfolding signed_def
  apply (cases "x < (2^(LENGTH('a)-1))")
    subgoal
      apply (cases "y < (2^(LENGTH('a)-1))")
      using atLeastLessThan_iff by simp_all
    apply (cases "y < (2^(LENGTH('a)-1))")
    using atLeastLessThan_iff by simp_all
qed

lemma signed_inv_id:
  assumes "0 \<le> y" "y < 2 ^ (LENGTH('a) - 1)"
  shows "signed N y = y"
  unfolding signed_def half_power using assms by simp

lemma signed_inv_neg:
  assumes "- (2 ^ (LENGTH('a) - 1)) \<le> y" "y < 0"
  shows "signed N (y + (2 ^ LENGTH('a))) = y"
proof -
  let ?x = "y + (2 ^ LENGTH('a))"
  have "(2^(LENGTH('a)-1)) \<le> ?x " using assms(1) unfolding half_power by simp
  moreover have "2^(LENGTH('a)-1) \<le> ?x \<and> ?x < 2^LENGTH('a)"
    using assms(2) calculation by force
  ultimately show ?thesis unfolding signed_def by simp
qed

lemma signed_image: "signed N ` {0 ..< 2^LENGTH('a)} = {-(2^(LENGTH('a)-1)) ..< 2^(LENGTH('a)-1)}"
unfolding image_def proof (intro Set.equalityI Set.subsetI, goal_cases)
  case (1 y)
  then obtain x where x: "x\<in>{0..<2 ^ LENGTH('a)}" "y = signed N x" by blast
  hence xb: "0 \<le> x" "x < 2 ^ LENGTH('a)" by auto
  {
    assume nx: "\<not>x < 2 ^ (LENGTH('a) - 1)"
    hence "2 ^ (LENGTH('a) - 1) \<le> x \<and> x < 2 ^ LENGTH('a)" using xb(2) by fastforce
    hence signed: "signed N x = x - 2 ^ LENGTH('a)" unfolding signed_def using nx by simp
    have "- (2 ^ (LENGTH('a) - 1)) \<le> signed N x"
    proof -
      have "0 \<le> x - 2 * (2 ^ (LENGTH('a) - 1)) + (2 ^ (LENGTH('a) - 1))"
        using nx by linarith
      hence "0 \<le> x - 2 ^ LENGTH('a) + (2 ^ (LENGTH('a) - 1))"
        unfolding half_power .
      hence "- (2 ^ (LENGTH('a) - 1)) \<le> x - 2 ^ LENGTH('a)" by simp
      thus ?thesis by (subst signed)
    qed
    moreover from nx have "signed N x < 2 ^ (LENGTH('a) - 1)"
      using calculation signed xb(2) by force
    ultimately have "signed N x \<in> {- (2 ^ (LENGTH('a) - 1))..<2 ^ (LENGTH('a) - 1)}" by simp
  }
  then show ?case unfolding x(2) signed_def using x(1)
    by (cases "x < 2 ^ (LENGTH('a) - 1)") auto
next
  case (2 y)
  show ?case
  proof (cases "0 \<le> y")
    case True
    have "signed N y = y"
      apply (rule signed_inv_id[OF True])
      using 2 by auto
    moreover have "y < 2 ^ LENGTH('a)" unfolding half_power using "2" by force
    ultimately show ?thesis using True by force
  next
    case False
    have eq: "signed N (y + (2 ^ LENGTH('a))) = y"
      apply (rule signed_inv_neg)
      subgoal using "2" atLeastLessThan_iff by blast
      using False by simp
    have lt: "y + (2 ^ LENGTH('a)) < 2 ^ LENGTH('a)" unfolding half_power using False by auto
    have ge: "0 \<le> y + 2 ^ LENGTH('a)" unfolding half_power using "2" by auto
    show ?thesis
      apply (intro CollectI bexI[where x="y + 2 ^ LENGTH('a)"])
      subgoal using eq[THEN sym] .
      unfolding atLeastLessThan_iff
      using lt ge by blast
  qed
qed

lemma signed_bij:
  "bij_betw (signed N) {0 ..< 2^LENGTH('a)} {-(2^(LENGTH('a)-1)) ..< 2^(LENGTH('a)-1)}"
  by (rule bij_betw_imageI[OF signed_inj signed_image])

lemma signed_inv:
  assumes "- (2^(LENGTH('a)-1)) \<le> i" "i < 2^(LENGTH('a)-1)"
  shows "signed_inv N i = (if 0 \<le> i then i else i + (2^LENGTH('a)))"
proof (cases "0 \<le> i")
  case True
  note val = signed_inv_id[OF True assms(2)]
  show ?thesis unfolding signed_inv_def the_inv_into_def
  proof (rule the_equality, goal_cases)
    case 1
    then show ?case using val unfolding half_power using assms(2) True by auto
  next
    case (2 y)
    hence other: "signed N y = signed N i" using val by simp
    show ?case using inj_onD[OF signed_inj other 2[THEN conjunct1]]
      unfolding half_power using True assms(2) by auto
  qed
next
  case False
  hence False: "i < 0" by simp
  note val = signed_inv_neg[OF assms(1) False]
  show ?thesis unfolding signed_inv_def the_inv_into_def
  proof (rule the_equality, goal_cases)
    case 1
    then show ?case using val unfolding half_power using assms(1) False by auto
  next
    case (2 y)
    hence other: "signed N y = signed N (i + 2 ^ LENGTH('a))" using val by simp
    show ?case using inj_onD[OF signed_inj other 2[THEN conjunct1]]
      unfolding half_power using False assms(1) by auto
  qed
qed

lemma signed_inv_nneg:
  assumes "- (2^(LENGTH('a)-1)) \<le> i" "i < 2^(LENGTH('a)-1)"
  shows "0 \<le> signed_inv N i"
  using signed_inv[OF assms, unfolded half_power]
  apply (cases "0 \<le> i")
  apply presburger
  using assms(1) by force

end

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

abbreviation (in wasm_int_ops) abs_int_s :: "'a \<Rightarrow> int"
  where "abs_int_s a \<equiv> signed TYPE('a) (abs_int a)"

abbreviation (in wasm_int_ops) rep_int_s :: "int \<Rightarrow> 'a"
  where "rep_int_s a \<equiv> rep_int (signed_inv TYPE('a) a)"

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
  assumes add: "int_add (i\<^sub>1::'a) i\<^sub>2 =
    rep_int ((abs_int i\<^sub>1 + abs_int i\<^sub>2) mod (2^LENGTH('a)))"
  assumes sub: "int_sub (i\<^sub>1::'a) i\<^sub>2 =
    rep_int ((abs_int i\<^sub>1 - abs_int i\<^sub>2 + (2^LENGTH('a))) mod (2^LENGTH('a)))"
  assumes mul: "int_mul (i\<^sub>1::'a) i\<^sub>2 =
    rep_int ((abs_int i\<^sub>1 * abs_int i\<^sub>2) mod (2^LENGTH('a)))"
  assumes div_u_0: "i\<^sub>2 = 0 \<Longrightarrow> int_div_u (i\<^sub>1::'a) i\<^sub>2 = None"
  assumes div_u: "i\<^sub>2 \<noteq> 0 \<Longrightarrow> int_div_u (i\<^sub>1::'a) i\<^sub>2 =
    Some (rep_int (trunc (of_int (abs_int i\<^sub>1) / of_int (abs_int i\<^sub>2))))"
  assumes div_s_0: "i\<^sub>2 = 0 \<Longrightarrow> int_div_s (i\<^sub>1::'a) i\<^sub>2 = None"
  assumes div_s_nrep:
    "i\<^sub>2 \<noteq> 0
    \<Longrightarrow> rat_of_int (abs_int_s i\<^sub>1) / of_int (abs_int_s i\<^sub>2) = 2^(LENGTH('a)-1)
    \<Longrightarrow> int_div_s (i\<^sub>1::'a) i\<^sub>2 = None"
  assumes div_s:
    "i\<^sub>2 \<noteq> 0
    \<Longrightarrow> rat_of_int (abs_int_s i\<^sub>1) / of_int (abs_int_s i\<^sub>2) \<noteq> 2^(LENGTH('a)-1)
    \<Longrightarrow> int_div_s (i\<^sub>1::'a) i\<^sub>2 =
            Some (rep_int_s (trunc (of_int (abs_int_s i\<^sub>1) / of_int (abs_int_s i\<^sub>2))))"
  assumes rem_u_0: "i\<^sub>2 = 0 \<Longrightarrow> int_rem_u (i\<^sub>1::'a) i\<^sub>2 = None"
  assumes rem_u: "i\<^sub>2 \<noteq> 0 \<Longrightarrow> int_rem_u (i\<^sub>1::'a) i\<^sub>2 =
    Some (rep_int (abs_int i\<^sub>1 - abs_int i\<^sub>2 * trunc (of_int (abs_int i\<^sub>1) / of_int (abs_int i\<^sub>2))))"
  assumes rem_s_0: "i\<^sub>2 = 0 \<Longrightarrow> int_rem_s (i\<^sub>1::'a) i\<^sub>2 = None"
  assumes rem_s: "i\<^sub>2 \<noteq> 0 \<Longrightarrow> int_rem_s (i\<^sub>1::'a) i\<^sub>2 = Some (rep_int_s (
      abs_int_s i\<^sub>1 - abs_int_s i\<^sub>2 * trunc (of_int (abs_int_s i\<^sub>1) / of_int (abs_int_s i\<^sub>2))))"

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