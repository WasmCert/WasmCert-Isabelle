section \<open>Augmented Type Syntax for Concrete Checker\<close>

theory Wasm_Checker_Types imports Wasm Wasm_Subtyping_Properties "HOL-Library.Sublist" begin

datatype reach = Reach | Unreach

type_synonym c_t = "(t list \<times> reach)"

fun pop :: "c_t \<Rightarrow> (t \<times> c_t) option" where
  "pop ([], r) = (case r of Reach \<Rightarrow> None | Unreach \<Rightarrow> Some (T_bot, ([], Unreach)))"
| "pop (t#ts, r) = Some (t, (ts, r))"

fun push :: "c_t \<Rightarrow> t \<Rightarrow> c_t" where
  "push (ts, r) t =(t#ts, r)"

fun pop_expect :: "c_t \<Rightarrow> t \<Rightarrow> c_t option" where
  "pop_expect ct t =
    (case pop ct of
      None \<Rightarrow> None
    | Some (t', ct') \<Rightarrow> (if t' <t: t then Some ct' else None))"

fun pop_expect_list :: "c_t \<Rightarrow> t list \<Rightarrow> c_t option" where
  "pop_expect_list ct [] = Some ct"
| "pop_expect_list ct (t#ts) =
    (case (pop_expect ct t) of
      None \<Rightarrow> None
    | Some ct' \<Rightarrow> (pop_expect_list ct' ts))"

fun consume :: "c_t \<Rightarrow> t list \<Rightarrow> c_t option" where
  "consume ct ts = pop_expect_list ct (rev ts)"

fun push_rev_list :: "c_t \<Rightarrow> t list \<Rightarrow> c_t" where
  "push_rev_list (ts, r) ts' =(ts'@ts, r)"

fun produce :: "c_t \<Rightarrow> t list \<Rightarrow> c_t" where
  "produce ct ts' = push_rev_list ct (rev ts')"

fun c_types_agree :: "c_t \<Rightarrow> t list \<Rightarrow> bool" where
  "c_types_agree ct ts =
    (case consume ct ts of
      None \<Rightarrow> False
    | Some (ts, _) \<Rightarrow> ts = [])"

fun type_update :: "c_t \<Rightarrow> t list \<Rightarrow> t list \<Rightarrow> c_t option" where
  "type_update ct cons prods = map_option (\<lambda> ct'. produce ct' prods) (consume ct cons)"

fun type_update_ref_is_null :: "c_t \<Rightarrow> c_t option" where
  "type_update_ref_is_null ct =
    (case pop ct of
      None \<Rightarrow> None
    | Some (t, ct') \<Rightarrow> if (is_ref_type t \<or> t = T_bot) then Some (push ct' (T_num T_i32)) else None)"

fun type_update_drop :: "c_t \<Rightarrow> c_t option" where
  "type_update_drop ct = map_option snd (pop ct)"

fun type_update_select :: "c_t \<Rightarrow> t option \<Rightarrow> c_t option" where
  "type_update_select ct None =
    (case (pop_expect ct (T_num T_i32)) of
      None \<Rightarrow> None
    | Some ct' \<Rightarrow>
      (case (pop ct') of
        None \<Rightarrow> None
      | Some (t1, ct'') \<Rightarrow>
          (case (pop ct'') of
            None \<Rightarrow> None
          | Some (t2, ct''') \<Rightarrow>
            if (\<not>(((is_num_type t1 \<or> t1 = T_bot) \<and> (is_num_type t2 \<or> t2 = T_bot)) \<or> ((is_vec_type t1 \<or> t1 = T_bot) \<and> (is_vec_type t2 \<or> t2 = T_bot))))
            then
              None
            else
              if (t1 \<noteq> t2 \<and> t1 \<noteq> T_bot \<and> t2 \<noteq> T_bot)
              then None
              else Some (push ct''' (if t1 = T_bot then t2 else t1))
          )
      )
    )"
| "type_update_select ct (Some t) = type_update ct [t, t, T_num T_i32] [t]"

lemma pop_some_reachability_inv:
  assumes "pop ct = Some (t, ct')"
  shows "snd ct = snd ct'"
  using assms
  apply(cases "ct" rule: pop.cases)
  apply simp_all
  apply (metis (mono_tags, lifting) option.inject option.simps(3) reach.exhaust reach.simps(3) reach.simps(4) snd_conv)
  by fastforce

lemma pop_expect_list_some_reachability_inv:
  assumes "pop_expect_list ct ts = Some ( ct')"
  shows "snd ct = snd ct'"
  using assms
  apply(induction ts arbitrary: ct ct')
  by (auto simp add: pop_some_reachability_inv handy_if_lemma split:option.splits prod.splits)

lemma consume_some_reachability_inv:
  assumes "consume ct ts = Some ct'"
  shows "snd ct = snd ct'"
  using assms
proof(induction ts arbitrary: ct ct' rule: rev_induct)
  case Nil
  then show ?case
    by simp
next
  case (snoc x xs)
  then show ?case
    using pop_some_reachability_inv consume.simps pop_expect_list_some_reachability_inv snoc.prems by metis
qed

lemma consume_some_split:
  assumes "consume ct (t1s@t2s) = Some ct'"
  shows "\<exists> ct''. consume ct t2s = Some ct'' \<and> consume ct'' t1s = Some ct'"
  using assms
proof(induction t2s arbitrary: ct ct' rule: List.rev_induct)
  case Nil
  then show ?case
    by simp
next
  case (snoc x xs)
  then have "consume ct (t1s @ xs @ [x]) = Some ct'" by simp
  then have "pop_expect_list ct (x # (rev xs @ rev t1s)) = Some ct'" by simp
  then obtain  ct'' where ct''_def: "pop_expect ct x = Some ct''" "Some ct' = pop_expect_list ct'' (rev xs @ rev t1s)"
    apply simp
    by (metis (no_types, lifting) not_None_eq option.simps(4) option.simps(5))
  then have ct''_consume: "consume ct'' (t1s@xs) = Some ct'" by simp
  then obtain ct''' where ct'''_def:  "consume ct'' xs = Some ct'''" "consume ct''' t1s = Some ct'"
    using snoc(1)[OF ct''_consume] by blast
  have "consume ct (xs @ [x]) = Some ct'''" using ct'''_def ct''_def by simp
  then show ?case
    using ct'''_def(2) by blast
qed

lemma consume_some_unsplit:
  assumes "consume ct t2s = Some ct''" "consume ct'' t1s = Some ct'"
  shows "consume ct (t1s@t2s) = Some ct'"
  using assms
proof(induction t2s arbitrary: ct ct' rule: List.rev_induct)
  case Nil
  then show ?case
    by simp
next
  case (snoc x xs)
  then obtain ct''' where ct'''_def: "consume ct [x] = Some ct'''" "consume ct''' xs = Some ct''"
    using consume_some_split[OF snoc(2)] by blast
  then have "consume ct''' (t1s @ xs) = Some ct'"
    using snoc.IH snoc.prems(2) by blast
  then have "consume ct (t1s @ xs @ [x]) = Some ct'" using ct'''_def(1) by (auto split: option.splits)
  then show ?case by auto
qed

lemma types_eq_c_types_agree: "c_types_agree (ts, r) (rev ts)"
proof (induction ts)
qed (simp add: t_subtyping_refl split: option.splits)+

lemma c_types_agree_append:
  assumes "c_types_agree (cts, r) ts"
  shows "c_types_agree (rev(ts')@cts, r) (ts@ts')"
  using assms t_subtyping_refl
proof (induction ts' rule: rev_induct)
qed (simp add: t_subtyping_refl split: option.splits)+

lemma c_types_agree_drop_append:
  assumes "c_types_agree (rev(ts')@cts, r) (ts@ts'')" "ts' <ts: ts''"
  shows "c_types_agree (cts, r) ts"
  using assms t_subtyping_refl
proof (induction ts' arbitrary: ts'' rule: rev_induct)
  case Nil
  then show ?case
    by (simp add: t_list_subtyping_def)
next
  case (snoc x xs)
  obtain ts''' t' where ts'''_def: "ts'' = ts'''@[t']" "xs <ts: ts'''" "[x] <ts: [t']"
    by (metis (full_types) list_all2_Cons1 list_all2_Nil snoc.prems(2) t_list_subtyping_def t_list_subtyping_split1)
  then have "c_types_agree (rev xs @ cts, r) (ts @ ts''')" using snoc(2) apply (auto split: option.splits)
    by (metis Pair_inject option.inject option.simps(3))+
  then show ?case using ts'''_def snoc.IH t_subtyping_refl by blast
qed

lemma c_types_agree_subtyping_reach:
  assumes "c_types_agree (cts, Reach) ts'"
  shows "rev cts <ts: ts'"
  using assms
proof(induction cts arbitrary: ts')
  case Nil
  then show ?case
    by (metis (no_types, lifting) Nil_is_rev_conv c_types_agree.elims(2) consume.simps option.simps(4) pop.simps(1) pop_expect.simps pop_expect_list.elims reach.simps(3) t_list_subtyping_refl)
next
  case (Cons x xs)
  then show ?case
  proof(cases ts' rule: List.rev_cases)
    case Nil
    then show ?thesis
      using Cons.prems by fastforce
  next
    case (snoc ys y)
    then obtain r where "consume (x#xs, Reach) (ys@[y]) = Some ([], r)" using Cons by (auto split: option.splits)
    then obtain ct' where ct'_def: "consume (x#xs, Reach) [y] = Some ct'" "consume ct' ys = Some ([], r)" using consume_some_split by blast
    have "ct' = (xs, Reach)" using ct'_def(1) by (auto simp add: handy_if_lemma split: option.splits)
    then have "rev xs <ts: ys"
      using Cons.IH ct'_def(2) by auto
    moreover have "[x] <ts: [y]"
      unfolding t_list_subtyping_def
      using ct'_def(1) by (auto simp add: handy_if_lemma split: option.splits)
    ultimately show ?thesis using t_list_subtyping_concat
      by (simp add: snoc t_list_subtyping_def)
  qed
qed

lemma c_types_agree_subtyping_unreach:
  assumes "c_types_agree (cts, Unreach) ts'"
  shows "\<exists> ts''. ts''@(rev cts) <ts: ts'"
  using assms
proof(induction cts arbitrary: ts')
  case Nil
  then show ?case
    using t_list_subtyping_refl by auto
next
  case (Cons x xs)
  then show ?case
  proof(cases ts' rule: List.rev_cases)
    case Nil
    then show ?thesis
      using Cons.prems by auto
  next
    case (snoc ys y)
    then obtain r where r_def: "consume (x#xs, Unreach) (ys@[y]) = Some ([], r)" using Cons by (auto split: option.splits)
    then obtain ct' where ct'_def: "consume (x#xs, Unreach) [y] = Some ct'" "consume ct' ys = Some ([], r)" using consume_some_split by blast
    have "ct' = (xs, Unreach)" using ct'_def(1) by (auto simp add: handy_if_lemma split: option.splits)
    then obtain ts'' where ts''_def: "ts''@(rev xs) <ts: ys"
      using Cons.IH ct'_def(2) by fastforce
    moreover have "[x] <ts: [y]"
      unfolding t_list_subtyping_def
      using ct'_def ts''_def r_def by (auto simp add: handy_if_lemma split: option.splits)
    ultimately show ?thesis
      using snoc t_list_subtyping_concat[of "ts'' @ rev xs" ys "[x]" "[y]"] by auto
  qed
qed

lemma c_types_agree_subtyping:
  assumes "c_types_agree (cts, r) ts'"
  shows "(r = Reach \<and> rev cts <ts: ts') \<or> (r = Unreach \<and> (\<exists> ts''. ts''@(rev cts) <ts: ts'))"
  using assms c_types_agree_subtyping_unreach  c_types_agree_subtyping_reach
  apply(cases r) by simp_all


lemma pop_expect_list_unreach_empty:
  "pop_expect_list ([], Unreach) (ts) = Some ([], Unreach)"
proof(induction ts)
qed (simp add: t_subtyping_def)+

lemma pop_expect_list_unreach_append: "pop_expect_list (ts, Unreach) (ts @ ts') = Some ([], Unreach)"
proof(induction ts)
qed (simp add: pop_expect_list_unreach_empty t_subtyping_def)+

lemma pop_expect_list_reach_subtypes:
  assumes "ts <ts: ts'"
  shows "pop_expect_list (ts, Reach) (ts') = Some ([], Reach)" 
  using assms
proof(induction ts arbitrary: ts')
  case Nil
  then show ?case by (simp add: t_subtyping_def t_list_subtyping_def)
next
  case (Cons a ts)
  then show ?case
    apply (auto simp add:  t_list_subtyping_def)
    using list.rel_cases by force
qed

lemma pop_some:
  assumes "pop ct = Some (t, ct')" "c_types_agree ct' ts'"
  shows "snd ct = snd ct'" "\<exists> ts. c_types_agree ct ts \<and> [t] _> [] <ti: ts _> ts'" 
proof -
  show h_r: "snd ct = snd ct'"
    using assms
    apply (cases ct)
    apply (rule pop.cases[of ct])
    apply (simp split: reach.splits)
    by fastforce+   
  show "\<exists> ts . c_types_agree ct ts \<and> [t] _> [] <ti: ts _> ts'"
  proof (cases "snd ct")
    case Reach
    then obtain cts cts' where cts_def: "ct = (cts, Reach)" "ct' = (cts', Reach)" "pop (cts, Reach) = Some (t, (cts', Reach))"
      using h_r
      by (metis assms(1) eq_snd_iff)
    have "cts' <ts: rev ts'" using c_types_agree_subtyping_reach assms(2) cts_def(2)
      by (simp add: list_all2_rev1 t_list_subtyping_def)
    then have 1: "rev cts' <ts: ts'" unfolding t_list_subtyping_def
      using list_all2_rev1 by blast
    have t_append: "cts = t#cts'"
      using cts_def
      apply(cases cts)
      by simp+
    then have "[t] _> [] <ti: (rev cts _> rev cts')" unfolding instr_subtyping_def using t_list_subtyping_def
      by (metis append.right_neutral rev.simps(2) t_list_subtyping_refl tf.sel(1) tf.sel(2))
    then have "[t] _> [] <ti: (rev cts _> ts')" using 1
      by (metis append.right_neutral instr_subtyping_def rev.simps(2) t_append t_list_subtyping_refl tf.sel(1) tf.sel(2))
    moreover have "c_types_agree ct (rev cts)" "c_types_agree ct' (rev cts')" using cts_def types_eq_c_types_agree
      by fastforce+
    ultimately show ?thesis unfolding c_types_agree.simps 1 by blast
  next
    case Unreach
    then obtain cts cts' where cts_def: "ct = (cts, Unreach)" "ct' = (cts', Unreach)" "pop (cts, Unreach) = Some (t, (cts', Unreach))"
      using h_r
      by (metis assms eq_snd_iff)
    then have cts_is: "cts = t#cts' \<or> (cts = [] \<and> t = T_bot \<and> cts' = [])"
      apply (cases cts)
      by simp+
    then show ?thesis
    proof 
      assume cts_t: "cts = t#cts'"

      obtain ts'' where ts''_def: "cts'@ts'' <ts: rev ts'"
        using assms(2) c_types_agree_subtyping_unreach cts_def(2)
        by (metis list_all2_rev1 rev_append rev_rev_ident t_list_subtyping_def)
      then have 1: "rev ts'' @ rev cts' <ts: ts'"
        by (metis list_all2_rev1 rev_append t_list_subtyping_def)
      have "([t] _> [] <ti: rev (cts) _> rev cts')"
        using cts_t
        by (metis fold_Cons_rev instr_subtyping_def rev.simps(2) rev_conv_fold t_list_subtyping_refl tf.sel(1) tf.sel(2))
      then have "([t] _> [] <ti: rev ts'' @ rev (cts) _> rev ts'' @ rev cts')" using instr_subtyping_trans
        by (metis (no_types, lifting) instr_subtyping_def t_list_subtyping_refl tf.sel(1) tf.sel(2))
      then have "([t] _> [] <ti: rev ts'' @ rev (cts) _> ts')" using 1 instr_subtyping_replace4 by simp
      moreover have "c_types_agree ct (rev ts'' @ rev (cts))" using cts_def(1) by (auto simp add: pop_expect_list_unreach_append split: option.splits)
      ultimately show ?thesis by blast
    next
      assume h: "(cts = [] \<and> t = T_bot \<and> cts' = [])"
      then obtain cts'' where "cts'' = [T_bot]" "c_types_agree ct (rev cts'')"
        by (simp add: assms cts_def(2) t_subtyping_def)
      then show ?thesis
        by (metis append_self_conv c_types_agree.simps consume.simps cts_def(1) h instr_subtyping_def pop_expect_list_unreach_empty t_list_subtyping_refl tf.case tf.dom_def tf.ran_def)
    qed
  qed
qed

lemma pop_expect_some:
  assumes "pop_expect ct t = Some ct'" "c_types_agree ct' ts'"
  shows "snd ct = snd ct'" "\<exists> ts. c_types_agree ct ts  \<and> [t] _> [] <ti: ts _> ts'" 
proof -
  obtain t' where t'_def: "pop ct = Some (t', ct')" "t' <t: t" using assms by (auto simp add: handy_if_lemma split: option.splits)
  then obtain ts where ts_def: "snd ct = snd ct'" "c_types_agree ct ts " "[t'] _> [] <ti: ts _> ts'"
    using pop_some assms(2) by blast
  then have "[t] _> [] <ti: ts _> ts'" using t'_def
    by (meson instr_subtyping_replace1 list.rel_intros(2) list_all2_Nil t_list_subtyping_def)
  then show "snd ct = snd ct'" "\<exists> ts. c_types_agree ct ts  \<and> [t] _> [] <ti: ts _> ts'" 
    using ts_def by blast+
qed

lemma c_types_agree_t_list_subtyping_inv:
  assumes
    "c_types_agree ct ts"
    "ts <ts:ts'"
  shows
    "c_types_agree ct ts'"
  using assms
proof(induction ts arbitrary: ts' ct rule: rev_induct)
  case Nil
  then show ?case
    by (metis list.distinct(1) pop_expect_list.elims rev.simps(1) rev.simps(2) rev_rev_ident t_list_subtyping_snoc_right1)
next
  case (snoc x xs)
  then obtain y ys where ys_def: "ts' = ys@[y]" "x <t: y" "xs <ts: ys"
    by (metis (full_types) list_all2_Cons1 list_all2_Nil t_list_subtyping_def t_list_subtyping_split1)
  obtain ct' where ct'_def: "Some (ct') = pop_expect ct x" "c_types_agree ct' xs"
    using snoc(2) handy_if_lemma by (auto simp add: handy_if_lemma split: if_splits option.splits prod.splits)
  then have "Some ct' = pop_expect ct y" using ys_def(2) by (auto simp add: t_subtyping_def split: option.splits)
  moreover have "c_types_agree ct' ys" using snoc(1) ys_def(3) ct'_def(2) by blast
  ultimately show ?case using ys_def(1)
    by (metis c_types_agree.simps consume.simps option.simps(5) pop_expect_list.simps(2) rev.simps(2) rev_swap)
qed

lemma c_types_agree_cons_prods_same:
  "consume (produce ct ts) ts = Some ct"
proof(induction ts rule: rev_induct)
  case Nil
  then show ?case
    apply simp
    by (metis append_Nil prod.exhaust_sel push_rev_list.simps)
next
  case (snoc x xs)
  obtain ct' where ct'_def: "Some ct' = consume (produce ct (xs @ [x])) ([x])" apply (auto split: option.splits)
    by (metis (mono_tags, lifting) Cons_eq_append_conv case_prod_conv option.simps(5) pop.simps(2) pop_expect_list.simps(1) push_rev_list.simps split_pairs t_subtyping_def)
  then have "ct' = (produce ct xs)" apply (auto split: option.splits)
    by (metis append_Cons old.prod.exhaust option.sel option.simps(3) pop.simps(2) push_rev_list.simps snd_conv)
  then show ?case
    using snoc ct'_def
    by (metis consume_some_unsplit)
qed

lemma c_types_agree_produce:
  assumes
    "c_types_agree ct ts"
  shows
    "\<exists> ct'. ct' = produce ct ts' \<and> c_types_agree ct' (ts@ts')"
proof -
  have "consume (produce ct ts') ts' = Some ct" using c_types_agree_cons_prods_same assms by auto
  then show ?thesis
    by (metis assms c_types_agree_append produce.simps push_rev_list.elims)
qed

lemma c_types_agree_consume:
  assumes
    "c_types_agree ct (ts@ts')"
  shows
    "\<exists> ct'. Some ct' = consume ct ts' \<and> c_types_agree ct' ts"
  using assms
proof(induction ts' arbitrary: ts ct rule: rev_induct)
  case Nil
  then show ?case by simp
next
  case (snoc x xs)
  then obtain r where r_def: "consume ct (ts @ xs @ [x]) = Some ([], r)"
    by(auto split: option.splits)
  then obtain ct'' where ct''_def: "consume ct [x] = Some ct''" "consume ct'' (ts @ xs) = Some ([], r)"
    by (metis append_assoc consume_some_split)
  then obtain ct' where ct'_def: "Some ct' = consume ct'' xs" "c_types_agree ct' ts"
    using c_types_agree.simps r_def snoc.IH snoc.prems by metis
  then have "consume ct (xs @ [x]) = Some ct'" using ct''_def
    by (metis consume_some_unsplit)
  then show ?case using ct'_def(2) by auto
qed

lemma consume_t_list_subtyping:
  assumes
    "consume ct ts = Some ct'"
    "ts <ts: ts'"
  shows
    "consume ct ts' = Some ct'"
  using assms
proof(induction ts arbitrary: ts' ct rule: rev_induct)
  case Nil
  then show ?case
    by (metis snoc_eq_iff_butlast t_list_subtyping_snoc_right1)
next
  case (snoc x xs)
  then obtain y ys where ys_def: "ts' = ys@[y]" "x <t: y" "xs <ts: ys"
    by (metis (full_types) list_all2_Cons1 list_all2_Nil t_list_subtyping_def t_list_subtyping_split1)
  obtain ct'' where ct'_def: "Some (ct'') = pop_expect ct x" "consume ct'' xs = Some ct'"
    using snoc(2) handy_if_lemma by (auto simp add: handy_if_lemma split: if_splits option.splits prod.splits)
  then have "Some ct'' = pop_expect ct y" using ys_def(2) by (auto simp add: t_subtyping_def split: option.splits)
  moreover have "consume ct'' ys = Some ct'" using snoc(1) ys_def(3) ct'_def(2) by blast
  ultimately show ?case using ys_def(1)
    by (metis consume.simps option.simps(5) pop_expect_list.simps(2) rev.simps(2) rev_swap)
qed

lemma c_types_agree_unreach_append:
  assumes
    "c_types_agree ct ts"
    "snd ct = Unreach"
  shows
    "c_types_agree ct (ts'@ts)"
  using assms
proof(induction ts' arbitrary: ts )
  case Nil
  then show ?case by simp
next
  case (Cons t' ts')
  then have "c_types_agree ct (ts' @ ts)"
    by blast
  then have 1: "consume ct (ts' @ ts) = Some ([], Unreach)"
    using assms(2) pop_expect_list_some_reachability_inv
    by (auto split: option.splits prod.splits)
  have 2: "consume ([], Unreach) [t'] = Some ([], Unreach)" using t_subtyping_def by simp
  have "consume ct (t'#ts' @ ts) = Some ([], Unreach)" using 1 2
    by (metis append.left_neutral append_Cons consume_some_unsplit)
  then show ?case by simp
qed

lemma pop_c_type_agrees_snoc:
  assumes
    "pop ct = Some (t', ct')"
    "c_types_agree ct (ts@[t])"
  shows
    "c_types_agree ct' ts"
  using assms c_types_agree_consume 
  apply (simp split: option.splits)
  by (metis (mono_tags, lifting) case_prodD option.sel option.simps(3) split_pairs)

lemma c_types_agree_snoc_pop:
  assumes
    "c_types_agree ct (ts@[t])"
  shows
    "\<exists> ct' t'. pop ct = Some (t', ct') \<and> t' <t: t \<and> c_types_agree ct' ts"
  using assms 
  apply (auto simp add: prod.exhaust_sel split_beta split: option.splits)
   by (metis Pair_inject option.sel option.simps(3) snd_conv)

lemma push_c_types_agree_snoc:
  assumes
    "push ct t = ct'"
    "c_types_agree ct ts"
  shows
    "c_types_agree ct' (ts@[t])"
  using assms c_types_agree_consume 
  apply (auto split: option.splits)
  apply (metis eq_snd_iff pop.simps(2) push.simps)
  apply (metis option.sel pop.simps(2) push.simps split_pairs)
  apply (metis option.sel pop.simps(2) push.simps split_pairs)
  by (metis option.sel pop.simps(2) push.simps split_pairs t_subtyping_def)

lemma consume_unreach_nonempty:
  assumes
    "consume (cts1, Unreach) ts = Some (cts2, Unreach)"
    "cts2 \<noteq> []"
  shows
    "\<exists> ts'. rev cts1 = rev cts2@ts' \<and> ts' <ts: ts"
  using assms
proof(induction ts arbitrary: cts1 cts2 rule: rev_induct)
  case Nil
  then show ?case
    by (simp add: t_list_subtyping_refl)
next
  case (snoc x xs)
  then obtain cts3 where cts3_def:
    "consume (cts1, Unreach) ([x]) = Some (cts3, Unreach)"
    "consume (cts3, Unreach) (xs) = Some (cts2, Unreach)"
    using consume_some_reachability_inv consume_some_split
    apply (auto split: option.splits) by blast
  then obtain ts' where ts'_def: "rev cts3 = rev cts2 @ ts' \<and> ts' <ts: xs" using snoc by blast
  have cts1_not_empty: "cts1 \<noteq> []"
    by (metis consume.elims old.prod.inject option.sel pop_expect_list_unreach_empty snoc.prems(1) snoc.prems(2))
  then obtain t' ts' where t'_def: "cts1 = t'#ts'" apply (cases cts1) by simp
  then have t'_props: "pop (cts1, Unreach) = Some (t', (cts3, Unreach))" "t' <t: x" "cts1 = [t']@cts3"
    apply (cases "(cts1, Unreach)" rule: pop.cases)
    using t'_def cts3_def(1) apply (auto simp add: handy_if_lemma split: option.split)
    
    by (metis (mono_tags, lifting) Pair_inject option.case_eq_if option.sel option.simps(3) pop_expect_list.simps(1))+
  then have "rev ts'  <ts: rev cts3"
    by (simp add: t'_def t_list_subtyping_refl)
  then have "rev ts' <ts: rev cts2 @ xs" using ts'_def 
    using t_list_subtyping_trans 
    by (metis t_list_subtyping_prepend)
  then have 2: "rev ts'@[t'] <ts: rev cts2 @ xs@[t']"
    using t_list_subtyping_append by fastforce
  have "rev cts1 = rev ts'@[t']" using t'_def by simp
  show ?case using ts'_def t'_def t'_props
    by (simp add: list_all2_appendI t_list_subtyping_def)
qed

lemma consume_c_types_agree:
  assumes
    "consume ct ts = Some ct'"
    "c_types_agree ct' ts'"
  shows "c_types_agree ct (ts'@ts)"
  using assms c_types_agree_consume consume_some_unsplit
  by (auto split: option.splits)

end
