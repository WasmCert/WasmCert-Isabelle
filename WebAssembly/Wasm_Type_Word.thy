theory Wasm_Type_Word
  imports
    Wasm_Ast (* TODO: remove *)
    Wasm_Type_Abs
    "Word_Lib.Signed_Division_Word"
    "Word_Lib.More_Word_Operations"
    Sshiftr
begin

lemma mult_inv_le: "(a::int) < 0 \<Longrightarrow> b \<ge> 0 \<Longrightarrow> a * b \<le> -b"
  by (metis add.inverse_inverse mult.commute mult.right_neutral
      mult_minus_right neg_0_less_iff_less neg_le_iff_le pos_mult_pos_ge)

text\<open>
Special non-representable case in signed division apart from division by 0:
-(2^(LENGTH('a)-1)) div -1 = 2^(LENGTH('a)-1 and these operands are unique for this result.
\<close>
lemma sdiv_nrep: "(i\<^sub>1::'a::len word) = of_int (-(2^(LENGTH('a)-1))) \<and> i\<^sub>2 = of_int (-1)
  \<longleftrightarrow> rat_of_int (sint i\<^sub>1) / of_int (sint i\<^sub>2) = 2^(LENGTH('a)-1)"
proof (rule iffI, goal_cases)
  case 1
  thus ?case by (simp add: sint_int_min)
next
  case 2
  {
    assume i2: "i\<^sub>2 \<noteq> 0"
    hence nz: "rat_of_int (sint i\<^sub>1) \<noteq> 0" using signed_eq_0_iff 2 by force
    from 2 this i2 have "rat_of_int (sint i\<^sub>1) = rat_of_int (sint i\<^sub>2) * 2 ^ (LENGTH('a) - 1)"
      by (metis Word.of_int_sint nonzero_mult_div_cancel_left signed_eq_0_iff times_divide_eq_right)
    hence mul: "sint i\<^sub>1 = sint i\<^sub>2 * (2 ^ (LENGTH('a) - 1))"
      by (subst of_int_eq_iff[THEN sym], subst of_int_mult) simp
    have "sint i\<^sub>1 = - (2 ^ (LENGTH('a) - 1))"
    proof (rule ccontr)
      assume "sint i\<^sub>1 \<noteq> - (2 ^ (LENGTH('a) - 1))"
      hence gt: "sint i\<^sub>1 > - (2 ^ (LENGTH('a) - 1))" using sint_ge[of i\<^sub>1] by linarith
      have "sint i\<^sub>1 \<ge> 0"
      proof (rule ccontr)
        assume "\<not>sint i\<^sub>1 \<ge> 0"
        hence i1_lt_0: "sint i\<^sub>1 < 0" by simp
        have "sint i\<^sub>2 \<noteq> 0" apply (rule ccontr) using mul i1_lt_0 by simp
        {
          assume "sint i\<^sub>2 > 0"
          hence "sint i\<^sub>2 * (2 ^ (LENGTH('a) - 1)) \<ge> (2 ^ (LENGTH('a) - 1))"
            by force
          hence False using gt i1_lt_0 local.mul by linarith
        }
        {
          assume "sint i\<^sub>2 < 0"
          have "sint i\<^sub>2 * (2 ^ (LENGTH('a) - 1)) \<le> -(2 ^ (LENGTH('a) - 1))"
            by (rule mult_inv_le) (simp_all add: \<open>sint i\<^sub>2 < 0\<close>)
          hence False using mul gt by linarith
        }
        then show False using \<open>0 < sint i\<^sub>2 \<Longrightarrow> False\<close> \<open>sint i\<^sub>2 \<noteq> 0\<close> by fastforce
      qed
      hence "sint i\<^sub>1 \<ge> (2 ^ (LENGTH('a) - 1))" using mul
        by (metis div_pos_pos_trivial i2 mult.commute nonzero_mult_div_cancel_left
            of_int_0 sint_lt word_sint.Rep_inverse)
      thus False by (smt (z3) sint_lt)
    qed
    hence "sint i\<^sub>1 = - (2 ^ (LENGTH('a) - 1)) \<and> sint i\<^sub>2 = - 1" using mul
      by (smt (z3) mult_cancel_right1 mult_minus_left
          semiring_1_no_zero_divisors_class.power_not_zero)
  }
  thus ?case
    apply (cases "i\<^sub>2 \<noteq> 0")
      apply (subst word_sint.Rep_inverse[THEN sym])
    using 2 by simp_all
qed

locale Wasm_Int_Word =
  fixes rep :: "'a :: {len, wasm_base} \<Rightarrow> 'n :: len word"
  fixes abs :: "'n word \<Rightarrow> 'a"
  assumes length: "LENGTH('a) = LENGTH('n)"
  and abs_rep: "\<And>x. abs (rep x) = x"
  and rep_abs: "\<And>x. rep (abs x) = x"
begin

definition int_clz :: "'n word \<Rightarrow> 'n word" where "int_clz \<equiv> of_nat \<circ> word_clz"
definition int_ctz :: "'n word \<Rightarrow> 'n word" where "int_ctz \<equiv> of_nat \<circ> word_ctz"
definition int_popcnt :: "'n word \<Rightarrow> 'n word" where "int_popcnt \<equiv> of_nat \<circ> pop_count"
definition int_add :: "'n word \<Rightarrow> 'n word \<Rightarrow> 'n word" where "int_add \<equiv> (+)"
definition int_sub :: "'n word \<Rightarrow> 'n word \<Rightarrow> 'n word" where "int_sub \<equiv> (-)"
definition int_mul :: "'n word \<Rightarrow> 'n word \<Rightarrow> 'n word" where "int_mul \<equiv> (*)"
definition int_div_u :: "'n word \<Rightarrow> 'n word \<Rightarrow> 'n word option" where
  "int_div_u i\<^sub>1 i\<^sub>2 \<equiv> if i\<^sub>2 = 0 then None else Some (i\<^sub>1 div i\<^sub>2)"
definition int_div_s :: "'n word \<Rightarrow> 'n word \<Rightarrow> 'n word option" where
  "int_div_s i\<^sub>1 i\<^sub>2 \<equiv>
    if i\<^sub>2 = 0 \<or> (i\<^sub>1 = of_int (-(2^31)) \<and> i\<^sub>2 = of_int (-1))
    then None
    else Some (i\<^sub>1 sdiv i\<^sub>2)"
definition int_rem_u :: "'n word \<Rightarrow> 'n word \<Rightarrow> 'n word option" where
  "int_rem_u i\<^sub>1 i\<^sub>2 \<equiv> if i\<^sub>2 = 0 then None else Some (i\<^sub>1 mod i\<^sub>2)"
definition int_rem_s :: "'n word \<Rightarrow> 'n word \<Rightarrow> 'n word option" where
  "int_rem_s i\<^sub>1 i\<^sub>2 \<equiv> if i\<^sub>2 = 0 then None else Some (i\<^sub>1 smod i\<^sub>2)"
definition int_and :: "'n word \<Rightarrow> 'n word \<Rightarrow> 'n word" where "int_and \<equiv> and"
definition int_or :: "'n word \<Rightarrow> 'n word \<Rightarrow> 'n word" where "int_or \<equiv> or"
definition int_xor :: "'n word \<Rightarrow> 'n word \<Rightarrow> 'n word" where "int_xor \<equiv> xor"
definition int_shl :: "'n word \<Rightarrow> 'n word \<Rightarrow> 'n word" where
  "int_shl i\<^sub>1 i\<^sub>2 \<equiv> i\<^sub>1 << (unat i\<^sub>2 mod LENGTH('n))"
definition int_shr_u :: "'n word \<Rightarrow> 'n word \<Rightarrow> 'n word" where
  "int_shr_u i\<^sub>1 i\<^sub>2 \<equiv> i\<^sub>1 >> (unat i\<^sub>2 mod LENGTH('n))"
definition int_shr_s :: "'n word \<Rightarrow> 'n word \<Rightarrow> 'n word" where
  "int_shr_s i\<^sub>1 i\<^sub>2 \<equiv> i\<^sub>1 >>> (unat i\<^sub>2 mod LENGTH('n))"
definition int_rotl :: "'n word \<Rightarrow> 'n word \<Rightarrow> 'n word" where
  "int_rotl i\<^sub>1 i\<^sub>2 \<equiv> word_rotl (unat i\<^sub>2) i\<^sub>1"
definition int_rotr :: "'n word \<Rightarrow> 'n word \<Rightarrow> 'n word" where
  "int_rotr i\<^sub>1 i\<^sub>2 \<equiv> word_rotr (unat i\<^sub>2) i\<^sub>1"
definition int_eqz :: "'a \<Rightarrow> bool" where "int_eqz a \<equiv> a = 0"
definition int_eq :: "'n word \<Rightarrow> 'n word \<Rightarrow> bool" where "int_eq \<equiv> (=)"
definition int_lt_u :: "'n word \<Rightarrow> 'n word \<Rightarrow> bool" where "int_lt_u \<equiv> (<)"
definition int_lt_s :: "'n word \<Rightarrow> 'n word \<Rightarrow> bool" where "int_lt_s \<equiv> (<s)"
definition int_gt_u :: "'n word \<Rightarrow> 'n word \<Rightarrow> bool" where "int_gt_u \<equiv> (>)"
definition int_gt_s :: "'n word \<Rightarrow> 'n word \<Rightarrow> bool" where "int_gt_s \<equiv> signed.greater"
definition int_le_u :: "'n word \<Rightarrow> 'n word \<Rightarrow> bool" where "int_le_u \<equiv> (\<le>)"
definition int_le_s :: "'n word \<Rightarrow> 'n word \<Rightarrow> bool" where "int_le_s \<equiv> (\<le>s)"
definition int_ge_u :: "'n word \<Rightarrow> 'n word \<Rightarrow> bool" where "int_ge_u \<equiv> (\<ge>)"
definition int_ge_s :: "'n word \<Rightarrow> 'n word \<Rightarrow> bool" where "int_ge_s \<equiv> signed.greater_eq"

abbreviation "lift0 \<equiv> abs"
abbreviation "lift1 \<equiv> map_fun rep abs"
abbreviation "liftid1 \<equiv> map_fun id abs"
abbreviation "lift1id \<equiv> map_fun rep id"
abbreviation "lift2 \<equiv> map_fun rep (map_fun rep abs)"
abbreviation "lift2o \<equiv> map_fun rep (map_fun rep (map_option abs))"
abbreviation "lift2id \<equiv> map_fun rep (map_fun rep id)"

definition nat_of_int :: "'a \<Rightarrow> nat" where "nat_of_int \<equiv> lift1id unat"
definition int_of_nat :: "nat \<Rightarrow> 'a" where "int_of_nat \<equiv> liftid1 of_nat"

sublocale Ops: wasm_int_ops where
  len_of = len_of and zero = "lift0 zero" and
  int_clz = "lift1 int_clz" and int_ctz = "lift1 int_ctz" and int_popcnt = "lift1 int_popcnt" and
  int_add = "lift2 int_add" and int_sub = "lift2 int_sub" and int_mul = "lift2 int_mul" and
  int_div_u = "lift2o int_div_u" and int_div_s = "lift2o int_div_s" and
  int_rem_u = "lift2o int_rem_u" and int_rem_s = "lift2o int_rem_s" and
  int_and = "lift2 int_and" and int_or = "lift2 int_or" and int_xor = "lift2 int_xor" and
  int_shl = "lift2 int_shl" and int_shr_u = "lift2 int_shr_u" and int_shr_s = "lift2 int_shr_s" and
  int_rotl = "lift2 int_rotl" and int_rotr = "lift2 int_rotr" and int_eqz = "int_eqz" and
  int_eq = "lift2id int_eq" and int_lt_u = "lift2id int_lt_u" and int_lt_s = "lift2id int_lt_s" and
  int_gt_u = "lift2id int_gt_u" and int_gt_s = "lift2id int_gt_s" and int_le_u = "lift2id int_le_u" and
  int_le_s = "lift2id int_le_s" and int_ge_u = "lift2id int_ge_u" and int_ge_s = "lift2id int_ge_s" and
  int_of_nat = int_of_nat and nat_of_int = nat_of_int by standard simp

abbreviation abs_int :: "'a \<Rightarrow> int"
  where "abs_int a \<equiv> int (nat_of_int a)"

abbreviation rep_int :: "int \<Rightarrow> 'a"
  where "rep_int a \<equiv> int_of_nat (nat a)"

abbreviation abs_int_bits :: "'a \<Rightarrow> bool list"
  where "abs_int_bits a \<equiv> ibits TYPE('a) (abs_int a)"

abbreviation rep_int_bits :: "bool list \<Rightarrow> 'a"
  where "rep_int_bits a \<equiv> rep_int (ibits_inv TYPE('a) a)"

abbreviation abs_int_s :: "'a \<Rightarrow> int"
  where "abs_int_s a \<equiv> signed TYPE('a) (abs_int a)"

abbreviation rep_int_s :: "int \<Rightarrow> 'a"
  where "rep_int_s a \<equiv> rep_int (signed_inv TYPE('a) a)"

lemma abs_int: "abs_int a = uint (rep a)"
  by (simp add: nat_of_int_def)

sublocale Int: wasm_int where
  len_of = len_of and zero = 0 and
  int_clz = "lift1 int_clz" and int_ctz = "lift1 int_ctz" and int_popcnt = "lift1 int_popcnt" and
  int_add = "lift2 int_add" and int_sub = "lift2 int_sub" and int_mul = "lift2 int_mul" and
  int_div_u = "lift2o int_div_u" and int_div_s = "lift2o int_div_s" and
  int_rem_u = "lift2o int_rem_u" and int_rem_s = "lift2o int_rem_s" and
  int_and = "lift2 int_and" and int_or = "lift2 int_or" and int_xor = "lift2 int_xor" and
  int_shl = "lift2 int_shl" and int_shr_u = "lift2 int_shr_u" and int_shr_s = "lift2 int_shr_s" and
  int_rotl = "lift2 int_rotl" and int_rotr = "lift2 int_rotr" and int_eqz = "int_eqz" and
  int_eq = "lift2id int_eq" and int_lt_u = "lift2id int_lt_u" and int_lt_s = "lift2id int_lt_s" and
  int_gt_u = "lift2id int_gt_u" and int_gt_s = "lift2id int_gt_s" and int_le_u = "lift2id int_le_u" and
  int_le_s = "lift2id int_le_s" and int_ge_u = "lift2id int_ge_u" and int_ge_s = "lift2id int_ge_s" and
  int_of_nat = int_of_nat and nat_of_int = nat_of_int
proof (standard, goal_cases)
  case 1
  show ?case sorry
next
  case (2 i\<^sub>1 i\<^sub>2)
  have "(x::'n word) + y = word_of_int ((uint x + uint y) mod (2^LENGTH('n)))" for x y
    apply (subst word_add_def)
    apply (subst word_uint.norm_norm(1)[THEN sym])
    by simp
  then show ?case unfolding int_add_def int_of_nat_def abs_int
    (* TODO: fix *)
    by (metis id_apply length map_fun_apply uint_word_of_int unat_eq_nat_uint word_add_def word_unat.Rep_inverse)
next
  case (3 i\<^sub>1 i\<^sub>2)
  then show ?case sorry
next
  case (4 i\<^sub>1 i\<^sub>2)
  then show ?case sorry
next
  case (5 i\<^sub>2 i\<^sub>1)
  then show ?case sorry
next
  case (6 i\<^sub>2 i\<^sub>1)
  then show ?case sorry
next
  case (7 i\<^sub>2 i\<^sub>1)
  then show ?case sorry
next
  case (8 i\<^sub>2 i\<^sub>1)
  then show ?case sorry
next
  case (9 i\<^sub>2 i\<^sub>1)
  then show ?case sorry
next
  case (10 i\<^sub>2 i\<^sub>1)
  then show ?case sorry
next
  case (11 i\<^sub>2 i\<^sub>1)
  then show ?case sorry
next
  case (12 i\<^sub>2 i\<^sub>1)
  then show ?case sorry
next
  case (13 i\<^sub>2 i\<^sub>1)
  then show ?case sorry
next
  case (14 i\<^sub>1 i\<^sub>2)
then show ?case sorry
next
  case (15 i\<^sub>1 i\<^sub>2)
then show ?case sorry
next
  case (16 i\<^sub>1 i\<^sub>2)
  then show ?case sorry
next
  case (17 i\<^sub>1 d\<^sub>1 d\<^sub>2 k i\<^sub>2)
then show ?case sorry
next
  case (18 i\<^sub>1 d\<^sub>1 d\<^sub>2 k i\<^sub>2)
  then show ?case sorry
next
  case (19 i\<^sub>1 d\<^sub>0 d\<^sub>1 d\<^sub>2 k i\<^sub>2)
  then show ?case sorry
next
  case (20 i\<^sub>1 d\<^sub>1 d\<^sub>2 k i\<^sub>2)
  then show ?case sorry
next
  case (21 i\<^sub>1 d\<^sub>1 d\<^sub>2 k i\<^sub>2)
  then show ?case sorry
next
  case (22 i\<^sub>1 k)
  then show ?case sorry
next
  case (23 i\<^sub>1 k d)
  then show ?case sorry
next
  case (24 i\<^sub>1 k)
  then show ?case sorry
next
  case (25 i\<^sub>1 d k)
  then show ?case sorry
next
  case (26 i\<^sub>1 bls k)
  then show ?case sorry
next
  case (27 i\<^sub>1)
  then show ?case sorry
next
  case (28 i\<^sub>1 i\<^sub>2)
  then show ?case sorry
next
  case (29 i\<^sub>1 i\<^sub>2)
  then show ?case sorry
next
  case (30 i\<^sub>1 i\<^sub>2)
  then show ?case sorry
next
  case (31 i\<^sub>1 i\<^sub>2)
  then show ?case sorry
next
  case (32 i\<^sub>1 i\<^sub>2)
  then show ?case sorry
next
  case (33 i\<^sub>1 i\<^sub>2)
  then show ?case sorry
next
  case (34 i\<^sub>1 i\<^sub>2)
  then show ?case sorry
next
  case (35 i\<^sub>1 i\<^sub>2)
  then show ?case sorry
next
  case (36 i\<^sub>1 i\<^sub>2)
  then show ?case sorry
qed

end

instantiation i32 :: wasm_base begin
lift_definition zero_i32 :: i32 is "of_nat 0" .
instance ..
end

instantiation i32 :: len begin
definition len_of_i32 :: "i32 itself \<Rightarrow> nat" where [simp]: "len_of_i32 _ = 32"
instance apply standard unfolding len_of_i32_def by simp
end

interpretation I32: Wasm_Int_Word Rep_i32 Abs_i32
  apply standard using Rep_i32_inverse  Abs_i32_inverse by auto

instantiation i32 :: wasm_int begin
  lift_definition int_clz_i32 :: "i32 \<Rightarrow> i32" is "I32.int_clz" .
  lift_definition int_ctz_i32 :: "i32 \<Rightarrow> i32" is "I32.int_ctz" .
  lift_definition int_popcnt_i32 :: "i32 \<Rightarrow> i32" is "I32.int_popcnt" .
  lift_definition int_add_i32 :: "i32 \<Rightarrow> i32 \<Rightarrow> i32" is "I32.int_add" .
  lift_definition int_sub_i32 :: "i32 \<Rightarrow> i32 \<Rightarrow> i32" is "I32.int_sub" .
  lift_definition int_mul_i32 :: "i32 \<Rightarrow> i32 \<Rightarrow> i32" is "I32.int_mul" .
  lift_definition int_div_u_i32 :: "i32 \<Rightarrow> i32 \<Rightarrow> i32 option" is "I32.int_div_u" .
  lift_definition int_div_s_i32 :: "i32 \<Rightarrow> i32 \<Rightarrow> i32 option" is "I32.int_div_s" .
  lift_definition int_rem_u_i32 :: "i32 \<Rightarrow> i32 \<Rightarrow> i32 option" is "I32.int_rem_u" .
  lift_definition int_rem_s_i32 :: "i32 \<Rightarrow> i32 \<Rightarrow> i32 option" is "I32.int_rem_s".
  lift_definition int_and_i32 :: "i32 \<Rightarrow> i32 \<Rightarrow> i32" is "I32.int_and" .
  lift_definition int_or_i32 :: "i32 \<Rightarrow> i32 \<Rightarrow> i32" is "I32.int_or" .
  lift_definition int_xor_i32 :: "i32 \<Rightarrow> i32 \<Rightarrow> i32" is "I32.int_xor" .
  lift_definition int_shl_i32 :: "i32 \<Rightarrow> i32 \<Rightarrow> i32" is "I32.int_shl" .
  lift_definition int_shr_u_i32 :: "i32 \<Rightarrow> i32 \<Rightarrow> i32" is "I32.int_shr_u" .
  lift_definition int_shr_s_i32 :: "i32 \<Rightarrow> i32 \<Rightarrow> i32" is "I32.int_shr_s" .
  lift_definition int_rotl_i32 :: "i32 \<Rightarrow> i32 \<Rightarrow> i32" is "I32.int_rotl" .
  lift_definition int_rotr_i32 :: "i32 \<Rightarrow> i32 \<Rightarrow> i32" is "I32.int_rotr" .
  lift_definition int_eqz_i32 :: "i32 \<Rightarrow> bool" is "I32.int_eqz" .
  lift_definition int_eq_i32 :: "i32 \<Rightarrow> i32 \<Rightarrow> bool" is "I32.int_eq" .
  lift_definition int_lt_u_i32 :: "i32 \<Rightarrow> i32 \<Rightarrow> bool" is "I32.int_lt_u" .
  lift_definition int_lt_s_i32 :: "i32 \<Rightarrow> i32 \<Rightarrow> bool" is "I32.int_lt_s" .
  lift_definition int_gt_u_i32 :: "i32 \<Rightarrow> i32 \<Rightarrow> bool" is "I32.int_gt_u" .
  lift_definition int_gt_s_i32 :: "i32 \<Rightarrow> i32 \<Rightarrow> bool" is "I32.int_gt_s" .
  lift_definition int_le_u_i32 :: "i32 \<Rightarrow> i32 \<Rightarrow> bool" is "I32.int_le_u" .
  lift_definition int_le_s_i32 :: "i32 \<Rightarrow> i32 \<Rightarrow> bool" is "I32.int_le_s" .
  lift_definition int_ge_u_i32 :: "i32 \<Rightarrow> i32 \<Rightarrow> bool" is "I32.int_ge_u" .
  lift_definition int_ge_s_i32 :: "i32 \<Rightarrow> i32 \<Rightarrow> bool" is "I32.int_ge_s" .
  definition nat_of_int_i32 :: "i32 \<Rightarrow> nat" where "nat_of_int_i32 \<equiv> I32.nat_of_int"
  definition int_of_nat_i32 :: "nat \<Rightarrow> i32" where "int_of_nat_i32 \<equiv> I32.int_of_nat"
instance apply (rule Wasm_Type_Abs.class.Wasm_Type_Abs.wasm_int.of_class.intro)
  unfolding
  int_clz_i32_def
  int_ctz_i32_def
  int_popcnt_i32_def
  int_add_i32_def
  int_sub_i32_def
  int_mul_i32_def
  int_div_u_i32_def
  int_div_s_i32_def
  int_rem_u_i32_def
  int_rem_s_i32_def
  int_and_i32_def
  int_or_i32_def
  int_xor_i32_def
  int_shl_i32_def
  int_shr_u_i32_def
  int_shr_s_i32_def
  int_rotl_i32_def
  int_rotr_i32_def
  int_eqz_i32_def
  int_eq_i32_def
  int_lt_u_i32_def
  int_lt_s_i32_def
  int_gt_u_i32_def
  int_gt_s_i32_def
  int_le_u_i32_def
  int_le_s_i32_def
  int_ge_u_i32_def
  int_ge_s_i32_def
  nat_of_int_i32_def
  int_of_nat_i32_def
  using I32.Int.wasm_int_axioms by simp (* should work with minor fixes as a direct proof *)
end


end