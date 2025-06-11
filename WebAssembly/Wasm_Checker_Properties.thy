section \<open>Correctness of Type Checker\<close>

theory Wasm_Checker_Properties imports Wasm_Checker Wasm_Properties begin

lemma consume_subtyping:
  assumes "consume ct cons = Some ct'" "c_types_agree ct' ts'"
  shows "\<exists> ts. c_types_agree ct ts  \<and> (cons _> []) <ti: (ts _> ts')"
  using assms
proof(induction cons arbitrary: ct ct' rule: List.rev_induct)
  case Nil
  then show ?case
    using b_e_weakening empty
    by (metis append_Nil2 b_e_type_empty1 consume.simps handy_if_lemma pop_expect_list.simps(1) rev_is_Nil_conv)
next
  case (snoc x xs)
  then obtain ct'' where ct''_def: "consume ct [x] = Some ct''" "consume ct'' xs = Some ct'"
    using consume_some_split[OF snoc(2)] by blast
  then obtain x' where x'_def: "pop ct = Some (x', ct'')" "x' <t: x" by (auto simp add: handy_if_lemma split: option.splits)
  obtain ts'' where ts''_def: "c_types_agree ct'' ts''" "xs _> [] <ti: ts'' _> ts'"
    using snoc(1)[OF ct''_def(2)]
    using snoc.prems(2) by blast
  then obtain ts where ts_def: "c_types_agree ct ts" "[x'] _> [] <ti: ts _> ts''" using x'_def pop_some by blast
  have "xs@[x'] _> [] <ti: ts _> ts'"
    using instr_subtyping_concat_left ts''_def(2) ts_def(2) by blast
  then have "xs@[x] _> [] <ti: ts _> ts'"
    using x'_def(2) using instr_subtyping_replace2[of "[x']" "[x]"]
    by (metis instr_subtyping_replace1 list.rel_inject(2) list_all2_Nil t_list_subtyping_def t_list_subtyping_prepend)
  then show ?case using ts_def by blast
qed

lemma produce_subtyping:
  assumes "produce ct prods = ct'" "c_types_agree ct' ts'"
  shows "\<exists> ts. c_types_agree ct ts \<and> ([] _> prods) <ti: (ts _> ts')"
proof -
  obtain r cts cts' where cts_def: "ct' = (cts', r)" "ct = (cts, r)"
    by (metis assms(1) prod.exhaust_sel produce.simps push_rev_list.simps)
  then have 0: "consume ct' ts' = Some ([],r)"
    using assms(2) pop_expect_list_some_reachability_inv
    apply (simp split: option.splits)
    by fastforce
  have 1: "ct' = ((rev prods)@cts, r)" using assms(1) cts_def by simp
  obtain ts_tail where ts''_def: "ts_tail@(rev cts)@prods <ts: ts'"
    by (metis "1" assms(2) c_types_agree_subtyping rev_append rev_rev_ident self_append_conv2)
  then obtain ts prods' where ts_def: "ts'=ts@prods'" "ts_tail@rev (cts) <ts: ts" "prods <ts: prods'"
    by (metis append.assoc t_list_subtyping_split1)
  have "([] _> prods) <ti: (ts _> ts @ prods)"
    by (metis append.right_neutral instr_subtyping_def t_list_subtyping_refl tf.sel(1) tf.sel(2))
  then have "([] _> prods) <ti: (ts _> ts')"
    using ts_def instr_subtyping_replace4 t_list_subtyping_prepend by blast
  moreover have "c_types_agree ct ts"
     using "1" assms(2) c_types_agree_drop_append cts_def(2) ts_def(1) ts_def(3) by blast
  ultimately show ?thesis by blast
qed

lemma type_update_type:
  assumes "type_update ct t1s t2s = Some ct'" "c_types_agree ct' ts'"
  shows "\<exists> ts. c_types_agree ct ts  \<and> (t1s _> t2s <ti: ts _> ts')"
proof -
  obtain ct'' where ct''_def: "consume ct t1s = Some ct''" "produce ct'' t2s = ct'" using assms(1) by auto
  then obtain ts'' where ts''_def: "c_types_agree ct'' ts''" "[] _> t2s <ti: ts'' _> ts'"
    using produce_subtyping using assms(2) by blast
  then obtain ts where ts_def: "c_types_agree ct ts" "t1s _> [] <ti: ts _> ts''"
    using consume_subtyping ct''_def(1) by blast
  then show ?thesis
    using instr_subtyping_comp ts''_def(2) by blast
qed

lemma b_e_type_checker_drop_sound:
  assumes "check_single \<C> Drop ct = Some ct'"
         "c_types_agree ct' ts'"
  shows "\<exists>ts. c_types_agree ct ts \<and> \<C> \<turnstile> [Drop] : ts _> ts'"
proof -
  obtain cts r where cts_def: "ct = (cts, r)"
    by fastforce
  show ?thesis
  proof(cases cts)
    case Nil
    then show ?thesis using cts_def assms apply (simp split: reach.splits)
      by (metis append.right_neutral b_e_typing.drop b_e_weakening pop_expect_list_unreach_empty)
  next
    case (Cons a list)
    then show ?thesis using cts_def assms apply (simp split: reach.splits)
      by (metis assms(2) b_e_typing.drop c_types_agree.elims(2) consume.simps pop.simps(2) pop_some(2) subsumption)
  qed
qed

lemma b_e_type_checker_is_null_ref_sound:
  assumes "check_single \<C> Ref_is_null ct = Some ct'"
          "c_types_agree ct' ts'"
  shows "\<exists>ts. c_types_agree ct ts \<and> \<C> \<turnstile> [Ref_is_null] : ts _> ts'"
proof -
  obtain t ct'' where t_def:
    "pop ct = Some (t, ct'')" 
    using assms(1) Wasm_Checker.check_ref_is_null
    apply simp
    by (metis (no_types, lifting) option.case_eq_if option.collapse option.discI surj_pair)
  then have 1: "is_ref_type t \<or> t = T_bot" "(push ct'' (T_num T_i32)) = ct'"
    using assms Wasm_Checker.check_ref_is_null t_def
    by (auto simp add: handy_if_lemma split: option.splits prod.splits)
  have "produce ct'' [T_num T_i32] = ct'"
    using 1(2)
    apply simp
    by (metis append.left_neutral append_Cons push.simps push_rev_list.elims)
  then obtain ts'' where ts''_def: "c_types_agree ct'' ts''" "[] _> [T_num T_i32] <ti: ts'' _> ts'"
    using assms(2) produce_subtyping by blast
  then obtain ts where ts_def: "c_types_agree ct ts" "[t] _> [] <ti: ts _> ts''"
    using pop_some(2) t_def by blast
  then have 2: "[t] _> [T_num T_i32] <ti: ts _> ts'"
    using instr_subtyping_comp ts''_def(2) by blast
  obtain tr where tr_def: "t <t: T_ref tr"
    using 1(1) t_subtyping_def
    by (auto simp add: is_ref_type_def split: t.splits)
  then have "[T_ref tr] _> [T_num T_i32] <ti: [t] _> [T_num T_i32]"
    by (meson instr_subtyping_refl instr_subtyping_replace1 list.rel_intros(2) list_all2_Nil t_list_subtyping_def)
  then have "\<C> \<turnstile> [Ref_is_null] : [t] _> [T_num T_i32]" using 1 b_e_typing.ref_is_null subsumption by blast
  then have "\<C> \<turnstile> [Ref_is_null] : ts _> ts'"
    using 2 subsumption by blast
  then show ?thesis using ts_def by blast
qed

lemma b_e_type_checker_select_sound:
  assumes "check_single \<C> (Select t_tag) ct = Some ct'"
          "c_types_agree ct' ts'"
  shows "\<exists>ts. c_types_agree ct ts \<and> \<C> \<turnstile> [Select t_tag] : ts _> ts'"
proof(cases t_tag)
  case None
  obtain t0 ct0 where t0_def: "pop ct = Some (t0, ct0)" "t0 <t: T_num T_i32"
    using assms(1) None
    apply (auto simp del: c_types_agree.simps produce.simps consume.simps split: option.splits)
    by fastforce
  obtain t1 ct1 where t1_def: "pop ct0 = Some (t1, ct1)"
    using t0_def assms(1) None
    by (auto split: option.splits)
  obtain t2 ct2 where t2_def: "pop ct1 = Some (t2, ct2)"
    using t0_def t1_def assms(1) None
    by (auto split: option.splits)
  have h1: "(is_num_type t1 \<or> t1 = T_bot) \<and> (is_num_type t2 \<or> t2 = T_bot) \<or>
                        (is_vec_type t1 \<or> t1 = T_bot) \<and> (is_vec_type t2 \<or> t2 = T_bot)"
    using t0_def t1_def t2_def assms(1) None
    apply (simp del: c_types_agree.simps produce.simps consume.simps)
    by (metis option.simps(3))
  then have h2: "t1 = t2 \<or> t1 = T_bot \<or> t2 = T_bot"
    using t0_def t1_def t2_def assms(1) None
    apply (simp del: c_types_agree.simps produce.simps consume.simps)
    by (metis option.simps(3))
  obtain t3 where t3_def: "t3 = (if t1 = T_bot then t2 else t1)" "push ct2 t3 = ct'"
    using t0_def t1_def t2_def h1 h2 assms(1) None
    by (auto simp del: c_types_agree.simps produce.simps consume.simps split: option.splits)
  then have "produce ct2 [t3] = ct'" apply simp
    by (metis (mono_tags, lifting) append.left_neutral append_Cons push.simps push_rev_list.elims)
  then obtain ts2 where ts2_def: "c_types_agree ct2 ts2" "[] _> [t3] <ti: ts2 _> ts'"
    using assms(2) produce_subtyping by blast
  then obtain ts1 where  ts1_def: "c_types_agree ct1 ts1" "[t2] _> [] <ti: ts1 _> ts2"
    using pop_some(2) t2_def by blast
  then obtain ts0 where ts0_def: "c_types_agree ct0 ts0" "[t1] _> [] <ti: ts0 _> ts1"
    using pop_some(2) t1_def by blast
  then obtain ts where ts_def: "c_types_agree ct ts" "[t0] _> [] <ti: ts _> ts0"
    using pop_some(2) t0_def(1) by blast
  have "\<C> \<turnstile> [Select t_tag] : ts _> ts'"
  proof -
    have "[t1, t0] _> [] <ti: ts _> ts1" using ts_def ts0_def
      using instr_subtyping_concat_left by fastforce
    then have  "[t2, t1, t0] _> [] <ti: ts _> ts2"
      using ts1_def instr_subtyping_concat_left by fastforce
    then have 1:  "[t2, t1, t0] _> [t3] <ti: ts _> ts'"
      using instr_subtyping_comp ts2_def(2) by blast
    have "t2 <t: t3" "t1 <t: t3" using t3_def(1) h2 t_subtyping_def by metis+
    then have 2: "[t3, t3, T_num T_i32] _> [t3] <ti: [t2, t1, t0] _> [t3]"
      unfolding instr_subtyping_def using t_list_subtyping_def t0_def(2)
      apply auto
      by (metis eq_Nil_appendI list.rel_inject(2) t_list_subtyping_refl)
    have "\<C> \<turnstile> [Select t_tag] : [t3, t3, T_num T_i32] _> [t3]"
    proof(cases "t3 = T_bot")
      case True
      then show ?thesis
        using None b_e_typing.select by blast
    next
      case False
      then have "is_num_type t3 \<or> is_vec_type t3"
        using h1 t3_def(1) by metis
      then show ?thesis
        using None b_e_typing.select by metis
    qed
    then show ?thesis
      using 1 2 subsumption by blast
  qed
  then show ?thesis
    using ts_def(1) by blast
next
  case (Some a)
  then show ?thesis using assms check_select
    by (metis b_e_typing.select subsumption type_update_type type_update_select.simps(2))
qed

lemma b_e_type_checker_sound:
  assumes "b_e_type_checker \<C> es (ts _> ts')"
  shows "\<C> \<turnstile> es : (ts _> ts')"
  using assms
proof -
  fix e ct
  have "b_e_type_checker \<C> es (ts _> ts') \<Longrightarrow>
          \<C> \<turnstile> es : (ts _> ts')"
  and "\<And>ct' ts'.
       check \<C> es ct = Some ct' \<Longrightarrow>
       c_types_agree ct' ts' \<Longrightarrow>
         \<exists>ts. c_types_agree ct ts \<and> \<C> \<turnstile> es : (ts _> ts')"
  and "\<And>ct' ts'.
       check_single \<C> e ct = Some ct' \<Longrightarrow>
       c_types_agree ct' ts' \<Longrightarrow>
         \<exists>ts. c_types_agree ct ts \<and> \<C> \<turnstile> [e] : (ts _> ts')"
  proof (induction rule: b_e_type_checker_check_check_single.induct)
    case (1 \<C> es ts ts')
    obtain ct' where "check \<C> es (rev ts, Reach) = Some ct'" "c_types_agree ct' ts'"
      by (metis "1.prems" Wasm_Checker.check_top case_optionE)
    then obtain ts'' where ts''_def: "c_types_agree (rev ts, Reach) ts''" "\<C> \<turnstile> es : ts'' _> ts'"
      using "1.IH" types_eq_c_types_agree by fastforce
    have "ts <ts: ts''" using ts''_def(1) c_types_agree_subtyping_reach[of "rev ts" ts'']
      by (simp add: t_list_subtyping_def)
    then show ?case
      using instr_subtyping_refl instr_subtyping_replace1 subsumption ts''_def(2) by blast
  next
    case (2 \<C> es ct)
    then show ?case
    proof(cases es)
      case Nil
      then have "ct = ct'" using 2(3) by simp
      then show ?thesis using 2(4)
        by (metis append.right_neutral b_e_weakening empty local.Nil)
    next
      case (Cons e' es')
      then obtain ct'' where ct''_def: "check_single \<C> e' ct = Some ct''" "check \<C> es' ct'' = Some ct'"
        using 2(3) by (simp split: option.splits)
      then show ?thesis using Cons 2(1)[OF Cons ct''_def(1)]  2(2)[OF Cons ct''_def(1,2)]
        by (metis "2.prems"(2) append_Cons b_e_type_comp_conc self_append_conv2)
    qed  
  next
    case (3 \<C> v ct)
    then show ?case
      by (metis Wasm_Checker.check_const_num const_num subsumption type_update_type)
  next
    case (4 \<C> v ct)
    then show ?case
      by (metis check_single.simps(2) const_vec subsumption type_update_type)
  next
    case (5 \<C> t op ct)
    then show ?case
      by (metis Wasm_Checker.check_unop b_e_typing.unop option.simps(3) subsumption type_update_type)
  next
    case (6 \<C> t op ct)
    then show ?case
      by (metis Wasm_Checker.check_binop binop option.simps(3) subsumption type_update_type)
  next
    case (7 \<C> t uu ct)
    then show ?case
      by (metis Wasm_Checker.check_testop b_e_typing.testop option.simps(3) subsumption type_update_type)
  next
    case (8 \<C> t op ct)
    then show ?case 
      by (metis Wasm_Checker.check_relop b_e_typing.relop option.simps(3) subsumption type_update_type)
  next
    case (9 \<C> op ct)
    then show ?case
      by (metis Wasm_Checker.check_unop_vec b_e_typing.unop_vec subsumption type_update_type)
  next
    case (10 \<C> op ct)
    then show ?case
      by (metis Wasm_Checker.check_binop_vec binop_vec option.simps(3) subsumption type_update_type)
  next
    case (11 \<C> op ct)
    then show ?case
      by (metis Wasm_Checker.check_ternop_vec b_e_typing.ternop_vec subsumption type_update_type)
  next
    case (12 \<C> op ct)
    then show ?case
      by (metis Wasm_Checker.check_test_vec b_e_typing.test_vec subsumption type_update_type)
  next
    case (13 \<C> op ct)
    then show ?case
      by (metis Wasm_Checker.check_shift_vec b_e_typing.shift_vec subsumption type_update_type)
  next
    case (14 \<C> sv ct)
    then show ?case
      by (metis Wasm_Checker.check_splat_vec b_e_typing.splat_vec subsumption type_update_type)
  next
    case (15 \<C> sv sx i ct)
    then show ?case
      by (metis (no_types, lifting) b_e_typing.extract_vec check_single.simps(13) option.simps(3) subsumption type_update_type)
  next
    case (16 \<C> sv i ct)
    then show ?case
      by (metis Wasm_Checker.check_replace_vec b_e_typing.replace_vec option.simps(3) subsumption type_update_type)
  next
    case (17 \<C> t ct)
    then show ?case
      by (metis Wasm_Checker.check_ref_null ref_null subsumption type_update_type)
  next
    case (18 \<C> ct)
    then show ?case using b_e_type_checker_is_null_ref_sound by blast
  next
    case (19 \<C> j ct)
    then show ?case
      by (metis Wasm_Checker.check_ref_func b_e_typing.ref_func option.simps(3) subsumption type_update_type)
  next
    case (20 \<C> t1 t2 sat_sx ct)
    then have "convert_cond t1 t2 sat_sx" "Some ct' = type_update ct [T_num t2] [T_num t1]"
      apply (simp del: c_types_agree.simps convert_cond.simps)
       apply (meson option.distinct(1))
       by (metis "20.prems"(1) Wasm_Checker.check_convert option.distinct(1))
    then show ?case using b_e_typing.convert type_update_type
      by (metis (full_types) "20.prems"(2) convert_cond.elims(1) subsumption)
  next
    case (21 \<C> t1 t2 sx ct)
    then have "t1 \<noteq> t2 \<and> t_num_length t1 = t_num_length t2 \<and> sx = None"
              "Some ct' = type_update ct [T_num t2] [T_num t1]"
      apply (simp del: c_types_agree.simps)
      apply (metis not_None_eq)
      by (metis "21.prems"(1) Wasm_Checker.check_reinterpret option.distinct(1))
    then show ?case using b_e_typing.reinterpret type_update_type
      by (metis "21.prems"(2) subsumption)
  next
    case (22 \<C> ct)
    then show ?case
      by (metis b_e_typing.unreachable pop.elims types_eq_c_types_agree)
  next
    case (23 \<C> ct)
    then show ?case
      using b_e_typing.nop b_e_weakening by fastforce
  next
    case (24 \<C> ct)
    then show ?case
      using b_e_type_checker_drop_sound by blast
  next
    case (25 \<C> t_tag ct)
    then show ?case
      using b_e_type_checker_select_sound by blast
  next
    case (26 \<C> tb es ct)
    obtain tn tm where tn_tm_def: "tb_tf_t \<C> tb = Some (tn _> tm)"
      by (metis (no_types, lifting) "26.prems"(1) Wasm_Checker.check_block is_none_code(2) is_none_simps(1) option.split_sel_asm tf.split_sel_asm)
    then have 1: "b_e_type_checker (\<C>\<lparr>label := [tm] @ label \<C>\<rparr>) es (tn _> tm)" "type_update ct tn tm = Some ct'" 
      using "26.prems"(1) Wasm_Checker.check_block 
      apply (auto simp add: handy_if_lemma simp del: b_e_type_checker.simps type_update.simps)
      by (meson option.distinct(1))+
    then obtain ts where ts_def: "c_types_agree ct ts" "tn _> tm <ti: ts _> ts'"
      using "26.prems"(2) type_update_type by blast
    have "\<C> \<turnstile> [Block tb es] : tn _> tm"
      using "1"(1) "26"(1) b_e_typing.block tn_tm_def by metis
    then have "\<C> \<turnstile> [Block tb es] : ts _> ts'"
      using ts_def(2) subsumption by blast
    then show ?case using ts_def(1) by blast
  next
    case (27 \<C> tb es ct)
    obtain tn tm where tn_tm_def: "tb_tf_t \<C> tb = Some (tn _> tm)"
      by (metis (no_types, lifting) "27.prems"(1) Wasm_Checker.check_loop is_none_code(2) is_none_simps(1) option.split_sel_asm tf.split_sel_asm)
    then have 1: "b_e_type_checker (\<C>\<lparr>label := [tn] @ label \<C>\<rparr>) es (tn _> tm)" "type_update ct tn tm = Some ct'" 
      using "27.prems"(1) Wasm_Checker.check_block 
      apply (auto simp add: handy_if_lemma simp del: b_e_type_checker.simps type_update.simps)
      by (meson option.distinct(1))+
    then obtain ts where ts_def: "c_types_agree ct ts" "tn _> tm <ti: ts _> ts'"
      using "27.prems"(2) type_update_type by blast
    have "\<C> \<turnstile> [Loop tb es] : tn _> tm"
      using "1"(1) "27"(1) b_e_typing.loop tn_tm_def by metis
    then have "\<C> \<turnstile> [Loop tb es] : ts _> ts'"
      using ts_def(2) subsumption by blast
    then show ?case using ts_def by blast
  next
    case (28 \<C> tb es1 es2 ct)
    obtain tn tm where tn_tm_def: "tb_tf_t \<C> tb = Some (tn _> tm)"
      using "28.prems"(1) Wasm_Checker.check_if
      apply (simp del: b_e_type_checker.simps)
      by (metis (no_types, lifting) option.case_eq_if option.collapse option.distinct(1) tf.split_sel_asm)
    then have 1: "b_e_type_checker (\<C>\<lparr>label := [tm] @ label \<C>\<rparr>) es1 (tn _> tm)" "b_e_type_checker (\<C>\<lparr>label := [tm] @ label \<C>\<rparr>) es2 (tn _> tm)"
      using "28.prems"(1,2) Wasm_Checker.check_if
      apply (simp_all del: b_e_type_checker.simps)
      by (meson option.distinct(1))+
    then have 2: "type_update ct (tn @ [T_num T_i32]) tm = Some ct'"
      using "28.prems"(1) tn_tm_def by fastforce
    then obtain ts where ts_def: "c_types_agree ct ts" "tn@[T_num T_i32] _> tm <ti: ts _> ts'"
      using "28.prems"(2) type_update_type by blast
    have "\<C> \<turnstile> [b_e.If tb es1 es2] : tn@[T_num T_i32] _> tm"
      by (meson "1"(1) "1"(2) "28"(1) "28"(2) if_wasm tn_tm_def)
    then have "\<C> \<turnstile> [b_e.If tb es1 es2] : ts _> ts'" using ts_def(2) subsumption by blast
    then show ?case using ts_def by blast
  next
    case (29 \<C> i ct)
    then obtain ct'' cts'' r'' where ct''_def: "ct' = ([], Unreach)" "i < length (label \<C>)" "consume ct (label \<C> ! i) = Some ct''" "ct'' = (cts'', r'')"
      by (metis Wasm_Checker.check_br not_Some_eq option.sel surj_pair)
    have "c_types_agree ct ((rev cts'') @label \<C> ! i)" using ct''_def(3,4) consume_some_unsplit[OF ct''_def(3), of "rev cts''"]
      by (metis (no_types, lifting) c_types_agree.simps option.case_eq_if option.exhaust types_eq_c_types_agree)
    moreover have "\<C> \<turnstile> [Br i] : ((rev cts'') @label \<C> ! i) _> ts'"
      using b_e_typing.br ct''_def(2) by blast
    ultimately show ?case by blast
  next
    case (30 \<C> i ct)
    then show ?case
      by (metis (no_types, lifting) Wasm_Checker.check_br_if br_if option.simps(3) subsumption type_update_type)
  next
    case (31 \<C> "is" i ct)
    then obtain ct'' cts'' r'' tls where ct''_def: "ct' = ([], Unreach)" "min_lab (is @ [i]) (label \<C>) = Some tls" "consume ct (tls @ [T_num T_i32]) = Some ct''" "ct'' = (cts'', r'')"
      apply (simp del: consume.simps split: option.splits)
      by (metis option.inject option.simps(3))
    have "c_types_agree ct ((rev cts'') @(tls @ [T_num T_i32]))" using ct''_def(3,4) consume_some_unsplit[OF ct''_def(3), of "rev cts''"]
      by (metis (no_types, lifting) c_types_agree.simps option.case_eq_if option.exhaust types_eq_c_types_agree)
    moreover have "\<C> \<turnstile> [Br_table is i] : ((rev cts'') @(tls@[T_num T_i32])) _> ts'"
      using b_e_typing.br_table ct''_def(2) min_lab_conv_list_all by blast
    ultimately show ?case by blast
  next
    case (32 \<C> ct)
    then obtain tls ct'' cts'' r'' where ct''_def: "ct' = ([], Unreach)" "return \<C> = Some tls" "consume ct tls = Some ct''" "ct'' = (cts'', r'')"
      apply (simp del: consume.simps split: option.splits)
      by (metis option.inject option.simps(3))
    have "c_types_agree ct ((rev cts'') @tls)" using ct''_def(3,4) consume_some_unsplit[OF ct''_def(3), of "rev cts''"]
      by (metis (no_types, lifting) c_types_agree.simps option.case_eq_if option.exhaust types_eq_c_types_agree)
    moreover have "\<C> \<turnstile> [Return] : ((rev cts'') @(tls)) _> ts'"
      using b_e_typing.return ct''_def  by blast
    ultimately show ?case by blast
  next
    case (33 \<C> i ct)
    then show ?case
      apply (auto simp add: handy_if_lemma simp del: c_types_agree.simps consume.simps split: option.splits)
      by (metis (mono_tags, lifting) b_e_typing.call option.discI subsumption tf.case tf.exhaust type_update_type)
  next
    case (34 \<C> ti i ct)
    then have 1: "i < length (types_t \<C>)" "ti < length (table \<C>)"
      by (metis Wasm_Checker.check_call_indirect option.distinct(1))+
    obtain tn tm lims where tn_defs:
      "(types_t \<C> ! i, table \<C> ! ti) = (tn _> tm, T_tab lims T_func_ref)"
      using 34(1) 1
      apply (auto simp add: handy_if_lemma  simp del: c_types_agree.simps consume.simps split: tab_t.splits prod.splits option.splits tf.splits)
      using t_ref.exhaust by force
    have 2: "type_update ct (tn @ [T_num T_i32]) tm = Some ct'"
      using 34(1) 1 tn_defs by fastforce
    then obtain ts where ts_def: "c_types_agree ct ts" "(tn @ [T_num T_i32]) _> tm <ti: ts _> ts'"
      using "34.prems"(2) type_update_type by blast
    have "\<C> \<turnstile> [Call_indirect ti i] : (tn @ [T_num T_i32])_> tm" using b_e_typing.call_indirect[OF 1(1), of tn tm ti lims] tn_defs
      using "1"(2) by fastforce
    then show ?case
      using 2 ts_def subsumption by blast
  next
    case (35 \<C> i ct)
    then show ?case
      by (metis Wasm_Checker.check_get_local b_e_typing.get_local option.simps(3) subsumption type_update_type)
  next
    case (36 \<C> i ct)
    then show ?case
      by (metis Wasm_Checker.check_set_local b_e_typing.set_local option.simps(3) subsumption type_update_type)
  next
    case (37 \<C> i ct)
    then show ?case
      by (metis (mono_tags, lifting) Wasm_Checker.check_tee_local b_e_typing.tee_local option.simps(3) subsumption type_update_type)
  next
    case (38 \<C> i ct)
    then show ?case
      by (metis Wasm_Checker.check_get_global b_e_typing.get_global option.simps(3) subsumption type_update_type)
  next
    case (39 \<C> i ct)
    then show ?case
      by (metis (no_types, lifting) Wasm_Checker.check_set_global b_e_typing.set_global option.simps(3) subsumption type_update_type)
  next
    case (40 \<C> t tp_sx a off ct)
    then show ?case
      by (metis Wasm_Checker.check_load load option.simps(3) subsumption type_update_type)
  next
    case (41 \<C> t tp a off ct)
    then show ?case
      by (metis Wasm_Checker.check_store store option.simps(3) subsumption type_update_type)
  next
    case (42 \<C> lv a off ct)
    then show ?case
      by (metis Wasm_Checker.check_load_vec load_vec option.simps(3) subsumption type_update_type)
  next
    case (43 \<C> svi i a off ct)
    then show ?case
      by (metis Wasm_Checker.check_load_lane_vec load_lane_vec option.simps(3) subsumption type_update_type)
  next
    case (44 \<C> sv a off ct)
    then show ?case
      by (metis Wasm_Checker.check_store_vec store_vec option.simps(3) subsumption type_update_type)
  next
    case (45 \<C> ct)
    then show ?case
      by (metis Wasm_Checker.check_current_memory b_e_typing.current_memory option.simps(3) subsumption type_update_type)
  next
    case (46 \<C> ct)
    then show ?case
      by (metis Wasm_Checker.check_grow_memory b_e_typing.grow_memory option.simps(3) subsumption type_update_type)
  next
    case (47 \<C> i ct)
    then show ?case
      by (metis (no_types, lifting) Wasm_Checker.check_memory_init b_e_typing.memory_init option.simps(3) subsumption type_update_type)
  next
    case (48 \<C> ct)
    then show ?case
      by (metis Wasm_Checker.check_memory_copy memory_copy option.simps(3) subsumption type_update_type)
  next
    case (49 \<C> ct)
    then show ?case
      by (metis Wasm_Checker.check_memory_fill b_e_typing.memory_fill option.simps(3) subsumption type_update_type)
  next
    case (50 \<C> ti ct)
    then show ?case
      by (metis (no_types, lifting) Wasm_Checker.check_table_set b_e_typing.table_set option.simps(3) subsumption type_update_type)
  next
    case (51 \<C> ti ct)
    then show ?case
      by (metis (no_types, lifting) Wasm_Checker.check_table_get b_e_typing.table_get option.simps(3) subsumption type_update_type)
  next
    case (52 \<C> ti ct)
    then show ?case
      by (metis Wasm_Checker.check_table_size b_e_typing.table_size option.simps(3) subsumption type_update_type)
  next
    case (53 \<C> ti ct)
    then show ?case
      using  Wasm_Checker.check_table_grow b_e_typing.table_grow option.simps(3) subsumption type_update_type
      by (metis (no_types, lifting))
  next
    case (54 \<C> x y ct)
    then show ?case
      by (metis (no_types, lifting) Wasm_Checker.check_table_init b_e_typing.table_init option.simps(3) subsumption type_update_type)
  next
    case (55 \<C> x y ct)
    then show ?case
      using  Wasm_Checker.check_table_copy b_e_typing.table_copy option.simps(3) subsumption type_update_type
      by (metis (no_types, lifting))
  next
    case (56 \<C> x ct)
    then show ?case
      by (metis (no_types, lifting) Wasm_Checker.check_table_fill b_e_typing.table_fill option.simps(3) subsumption type_update_type)
  next
    case (57 \<C> x ct)
    then show ?case
      by (metis Wasm_Checker.check_elem_drop b_e_typing.elem_drop option.simps(3) subsumption type_update_type)
  next
    case (58 \<C> x ct)
    then show ?case
      by (metis Wasm_Checker.check_data_drop b_e_typing.data_drop option.simps(3) subsumption type_update_type)
  qed
  then show ?thesis
    using assms by blast
qed

lemma check_single_imp_unreach:
  assumes "check_single \<C> e ct = Some ct'" "e = Unreachable \<or>(e = Br i) \<or> (e = Br_table is i) \<or> (e = Return)"
  shows "(\<exists> tls. check_single \<C> e = (\<lambda> ct''. (if (consume ct'' tls \<noteq> None) then Some ([], Unreach) else None)))"
  using assms(2)
proof(cases e)
  case Unreachable
  then show ?thesis
    by (metis Wasm_Checker.check_unreachable consume.simps not_None_eq pop_expect_list.simps(1) rev.simps(1))
next
  case (Br x8)
  then show ?thesis
    using assms(1)
    by fastforce
next
  case (Br_table x101 x102)
  then show ?thesis
    using assms(1)
    by (fastforce simp del: consume.simps split: option.splits)
next
  case Return
  then show ?thesis
    using assms(1)
    by (fastforce simp del: consume.simps split: option.splits)
qed auto+

lemma check_single_id_impl:
  assumes "check_single \<C> e = (\<lambda> ct''. Some ct'')"
  shows "check_single \<C> e  = (\<lambda> ct''. type_update ct'' [] [])"
  using assms
proof(cases e)
qed auto

lemma check_single_select_impl:
  assumes "e = Select t_tag"
  shows "t_tag = None \<and> check_single \<C> e  = (\<lambda> ct''. type_update_select ct'' None) \<or> (\<exists> t. t_tag = Some t \<and> check_single \<C> e  = (\<lambda> ct''. type_update ct'' [t,t,T_num T_i32] [t]))"
proof(cases e)
  case (Select x4)
  then show ?thesis
    by (metis Wasm_Checker.check_select assms not_None_eq type_update_select.simps(2))
qed (fastforce simp add: assms)+

lemma check_single_imp':
  assumes "check_single \<C> e ct = Some ct'"
  shows " check_single \<C> e = (\<lambda> ct''. Some ct'')
         \<or> (\<exists> t_tag. check_single \<C> e = (\<lambda> ct''. type_update_select ct'' t_tag) \<and> e = Select t_tag)
         \<or> (check_single \<C> e = type_update_ref_is_null \<and> e = Ref_is_null)
         \<or> (check_single \<C> e = type_update_drop \<and> e = Drop)
         \<or> (\<exists>cons prods. (check_single \<C> e = (\<lambda> ct''. type_update ct'' cons prods)))
         \<or> (\<exists> tls. check_single \<C> e = (\<lambda> ct''. (if (consume ct'' tls \<noteq> None) then Some ([], Unreach) else None)))"
  using assms
  apply (cases rule: check_single.cases[of "(\<C>, e, ct)"])
  using check_single_imp_unreach
  apply (simp_all add: check_single_imp_unreach  del: convert_cond.simps b_e_type_checker.simps c_types_agree.simps type_update.simps type_update_select.simps type_update_ref_is_null.simps consume.simps)
  by(fastforce simp del: convert_cond.simps b_e_type_checker.simps c_types_agree.simps type_update.simps type_update_select.simps type_update_ref_is_null.simps split: option.splits if_splits tf.splits t_ref.splits tab_t.splits)+

lemma check_single_imp:
  assumes "check_single \<C> e ct = Some ct'"
  shows   "(check_single \<C> e = (\<lambda> ct''. type_update_select ct'' None ) \<and> e = Select None)
         \<or> (check_single \<C> e = type_update_ref_is_null \<and> e = Ref_is_null)
         \<or> (check_single \<C> e = type_update_drop \<and> e = Drop)
         \<or> (\<exists>cons prods. (check_single \<C> e = (\<lambda> ct''. type_update ct'' cons prods)))
         \<or> (\<exists> tls. check_single \<C> e = (\<lambda> ct''. (if (consume ct'' tls \<noteq> None) then Some ([], Unreach) else None)))"
proof -
  consider
    (1) "check_single \<C> e = Some" 
  | (2) " (\<exists> t_tag. check_single \<C> e = (\<lambda> ct''. type_update_select ct'' t_tag) \<and> e = Select t_tag)"
  | (3) "(check_single \<C> e = type_update_ref_is_null) \<and> e = Ref_is_null"
  | (4) "(check_single \<C> e = type_update_drop) \<and> e = Drop"
  | (5) "(\<exists>cons prods. (check_single \<C> e = (\<lambda> ct''. type_update ct'' cons prods)))"
  | (6) "(\<exists> tls. check_single \<C> e = (\<lambda> ct''. (if (consume ct'' tls \<noteq> None) then Some ([], Unreach) else None)))"
    using assms check_single_imp' by blast
  then show ?thesis
    apply(cases)
    using check_single_id_impl check_single_select_impl by blast+
qed

lemma check_snoc:
  assumes "check \<C> es ct = Some ct'" "check \<C> [e] ct' = Some ct''"
  shows "check \<C> (es @ [e]) ct = Some ct''"
  using assms
proof(induction es arbitrary: ct ct' ct'')
  case Nil
  then show ?case by simp
next
  case (Cons e' es')
  then show ?case
    apply (auto split: option.splits)
    using Cons.IH by auto
qed

lemma c_types_agree_type_update:
  assumes
    "(cons _> prods) <ti: (ts _> ts')"
    "c_types_agree ct ts"
  shows
    "\<exists> ct'. type_update ct cons prods = Some ct' \<and> c_types_agree ct' ts'"
proof -
  obtain ts'' cons'' ts''' prods''' where defs:
    "ts = ts''@cons''"
    "cons'' <ts: cons"
    "ts' = ts'''@prods'''"
    "prods <ts: prods'''"
    "ts'' <ts: ts'''"
    using assms(1) instr_subtyping_def
    by auto
  then have ts'_subtyping: "(ts''@prods) <ts: ts'"
    using 
    t_list_subtyping_replace1[OF defs(5) t_list_subtyping_refl, of prods]
    t_list_subtyping_replace2[OF defs(4) t_list_subtyping_refl, of ts''']
    t_list_subtyping_trans by blast
  obtain ct' where ct'_def: "consume ct cons'' = Some ct'" "c_types_agree ct' ts''"
    using defs(1) c_types_agree_consume assms(2) by metis
  have ct'_cons: "consume ct cons = Some ct'" using consume_t_list_subtyping ct'_def(1) defs(2) by metis
  obtain ct'' where ct''_def: "ct'' = produce ct' prods" "c_types_agree ct'' (ts''@prods)"
    using c_types_agree_produce ct'_def by metis
  then have "c_types_agree ct'' ts'" using ts'_subtyping
    using c_types_agree_t_list_subtyping_inv by blast
  moreover have "type_update ct cons prods = Some ct''"
    using ct'_def ct''_def apply (auto split: option.splits)
    by (metis consume.simps ct'_cons push_rev_list.elims)
  ultimately show ?thesis by blast
qed

lemma type_update_instr_subtyping:
  assumes
    "type_update ct cons prods = Some ct'"
    "snd ct = Reach"
  shows
    "\<exists> ts ts'. c_types_agree ct ts \<and> c_types_agree ct' ts' \<and> (cons _> prods) <ti: (ts _> ts')"
proof-
  have "snd ct' = Reach"
    using assms apply (simp split: option.splits reach.splits)
    using pop_expect_list_some_reachability_inv by fastforce
  then obtain ts ts' where ts_def: "ct = (rev ts, Reach)" "ct' = (rev ts', Reach)"
    by (metis assms(2) prod.exhaust_sel rev_rev_ident)
  then have "(cons _> prods) <ti: (ts _> ts')"
    by (metis assms(1) c_types_agree_subtyping_reach instr_subtyping_replace3 list_all2_rev1 rev_rev_ident t_list_subtyping_def type_update_type types_eq_c_types_agree)
  then show ?thesis using ts_def
    using types_eq_c_types_agree by auto
qed

lemma type_update_reach_subtyping:
  assumes
    "type_update (rev ts, Reach) cons prods = Some (rev ts', Reach)"
  shows
    "(cons _> prods) <ti: (ts _> ts')"
  using assms c_types_agree_subtyping_reach instr_subtyping_replace3 list_all2_rev1 rev_rev_ident t_list_subtyping_def type_update_type types_eq_c_types_agree
  by metis

lemma check_single_unreach_inv:
  assumes
    "check_single \<C> e ct = Some ct'"
    "snd ct = Unreach"
  shows
    "snd ct' = Unreach"
proof -
  consider
    (1) " (check_single \<C> e = (\<lambda> ct''. type_update_select ct'' None) \<and> e = Select None)"
  | (2) "(check_single \<C> e = type_update_ref_is_null) \<and> e = Ref_is_null"
  | (3) "(check_single \<C> e = type_update_drop)"
  | (4) "(\<exists>cons prods. (check_single \<C> e = (\<lambda> ct''. type_update ct'' cons prods)))"
  | (5) "(\<exists> tls. check_single \<C> e = (\<lambda> ct''. (if (consume ct'' tls \<noteq> None) then Some ([], Unreach) else None)))"
    using assms(1) check_single_imp by blast
  then show ?thesis
  proof(cases)
    case 1
    then show ?thesis
      using assms
      apply (auto split: option.splits)
      by (metis (no_types, lifting) option.inject option.simps(3) pop_some_reachability_inv push.simps snd_conv)
  next
    case 2
    then show ?thesis using assms
      by (auto simp add: handy_if_lemma pop_some_reachability_inv split: option.splits)
  next
    case 3
    then show ?thesis
      using assms
      by (auto simp add: pop_some_reachability_inv split: option.splits)
  next
    case 4
    then obtain cons prods where "check_single \<C> e = (\<lambda>ct''. type_update ct'' cons prods)" by blast
    then show ?thesis
      using assms
      apply (auto simp del: consume.simps produce.simps simp add:  handy_if_lemma pop_some_reachability_inv split: option.splits)
      by (simp add: consume_some_reachability_inv)
  next
    case 5
    then show ?thesis
      apply (auto simp add: handy_if_lemma pop_some_reachability_inv split: option.splits)
      by (metis (no_types, lifting) assms(1) option.sel option.simps(3) snd_conv)
  qed
qed

lemma b_e_type_checker_imp_check_single:
  assumes
    "b_e_type_checker \<C> [e] (ts _> ts')"
    "c_types_agree ct ts"
  shows
    "\<exists> ct'. check_single \<C> e ct = Some ct' \<and> c_types_agree ct' ts'"
proof -
  obtain ct'' where ct''_def: "check_single \<C> e (rev ts, Reach) = Some ct''" "c_types_agree ct'' ts'"
    using assms(1) by (auto split: option.splits)
  consider
    (1) " (check_single \<C> e = (\<lambda> ct''. type_update_select ct'' None) \<and> e = Select None)"
  | (2) "(check_single \<C> e = type_update_ref_is_null) \<and> e = Ref_is_null"
  | (3) "(check_single \<C> e = type_update_drop) \<and> e = Drop"
  | (4) "(\<exists>cons prods. (check_single \<C> e = (\<lambda> ct''. type_update ct'' cons prods)))"
  | (5) "(\<exists> tls. check_single \<C> e = (\<lambda> ct''. (if (consume ct'' tls \<noteq> None) then Some ([], Unreach) else None)))"
    using ct''_def(1) check_single_imp by blast
  then show ?thesis
  proof(cases)
    case 1
    then obtain t where t_def: "[t, t, T_num T_i32] _> [t] <ti: ts _> ts'" "(is_num_type t \<or> is_vec_type t \<or> t = T_bot)" using b_e_type_select
      using assms(1) b_e_type_checker_sound
      using 1
      by (metis option.simps(3))
    obtain ts'' where ts''_def: "ts <ts: ts''@[t,t,T_num T_i32]" "ts''@[t] <ts: ts'"
      using instr_subtyping_def t_def(1) t_list_subtyping_concat
      using t_list_subtyping_refl by fastforce
    then have "c_types_agree ct (ts''@[t, t, T_num T_i32])"
      using assms(2) c_types_agree_t_list_subtyping_inv by blast
    then obtain ct1 where ct1_def: "pop_expect ct (T_num T_i32) = Some ct1" "c_types_agree ct1 (ts''@[t, t])"
      using c_types_agree_snoc_pop[of ct "(ts'@[t,t])" "T_num T_i32"]
      by (auto split: option.splits)
    then obtain ct2 t1 where ct2_def: "pop ct1 = Some (t1, ct2)" "t1 <t: t" "c_types_agree ct2 (ts''@[t])"
      using c_types_agree_snoc_pop
      by (metis append_Cons append_Nil append_assoc)
    then obtain ct3 t2 where ct3_def: "pop ct2 = Some (t2, ct3)" "t2 <t: t"
      using c_types_agree_snoc_pop
      by (metis)
    then obtain t'' where t''_def: "t'' = (if t1 = T_bot then t2 else t1)"
      by blast
    then have t_props: "t1 <t: t''" "t2 <t: t''" "t'' <t: t"
      using t''_def ct2_def(2) ct3_def(2) 
      by (auto simp add: t_subtyping_def)
    then have t''_prop: "(is_num_type t'' \<or> is_vec_type t'' \<or> t'' = T_bot)"
      using t_def(2) t_subtyping_def by auto
    then obtain ct4 where ct4_def: "push ct3 t'' = ct4" "c_types_agree ct4 (ts''@[t''])"
      using push_c_types_agree_snoc ct3_def
      using ct2_def(3) pop_c_type_agrees_snoc by blast
    then have "c_types_agree ct4 (ts''@[t])"
      by (metis c_types_agree_t_list_subtyping_inv list_all2_Cons2 list_all2_Nil t_list_subtyping_def t_list_subtyping_prepend t_props(3))
    then have "c_types_agree ct4 ts'"
      using ts''_def(2)
      using c_types_agree_t_list_subtyping_inv by blast
    moreover have "type_update_select ct None = Some ct4"
      using ct1_def ct2_def ct3_def ct4_def t''_prop
      using t''_def t_subtyping_def by force
    ultimately show ?thesis using 1 by fastforce
  next
    case 2
    then obtain tr where tr_def: "[T_ref tr] _> [T_num T_i32] <ti: ts _> ts'"
      using assms b_e_type_ref_is_null
      using b_e_type_checker_sound by blast
    then obtain ts'' where ts''_def: "ts <ts: ts''@[T_ref tr]" "ts''@[T_num T_i32] <ts: ts'"
      using instr_subtyping_def t_list_subtyping_concat t_list_subtyping_refl by fastforce
    then obtain ct'' t'' where ct''_def: "pop ct = Some (t'', ct'')" "t'' <t: T_ref tr" " c_types_agree ct'' ts''"
      using assms(2) c_types_agree_snoc_pop c_types_agree_t_list_subtyping_inv
      by blast
    then obtain ct' where ct'_def: "ct' = push ct'' (T_num T_i32)" "c_types_agree ct' (ts''@[T_num T_i32])"
      using push_c_types_agree_snoc by metis
    then have "check_single \<C> e ct = Some ct'"
      using ct''_def ct'_def 2 is_ref_type_def t_subtyping_def
      apply (simp split: option.splits)
      by fastforce
    moreover have "c_types_agree ct' ts'"
      using ct''_def
      using c_types_agree_t_list_subtyping_inv ct'_def(2) ts''_def(2) by blast
    ultimately show ?thesis using assms b_e_type_ref_is_null by simp
  next
    case 3
    then obtain t where t_def: "[t] _> [] <ti: ts _> ts'"
      using assms b_e_type_checker_sound b_e_type_drop by blast
    then obtain ts'' where ts''_def: "ts <ts: ts''@[t]" "ts'' <ts: ts'"
      using instr_subtyping_def t_list_subtyping_concat t_list_subtyping_refl by fastforce
    then obtain ct' t' where ct'_def: "pop ct = Some (t', ct')" "t' <t: t" " c_types_agree ct' ts''"
      using assms(2) c_types_agree_snoc_pop c_types_agree_t_list_subtyping_inv
      by blast
    then have "check_single \<C> e ct = Some ct'"
      using 3 by fastforce
    moreover have "c_types_agree ct' ts'"
      using c_types_agree_t_list_subtyping_inv ts''_def(2)
      using ct'_def(3) by blast
    ultimately show ?thesis by simp
  next
    case 4
    then obtain prods cons where prods_cons_def: "check_single \<C> e = (\<lambda>ct''. type_update ct'' cons prods)"
      by blast
    then have "cons _> prods <ti: ts _> ts'"
      by (metis c_types_agree_subtyping_reach ct''_def(1) ct''_def(2) instr_subtyping_replace3 list_all2_rev1 rev_rev_ident t_list_subtyping_def type_update_type)
    then show ?thesis
      using assms prods_cons_def c_types_agree_type_update by metis
  next
    case 5
    then obtain tls where tls_def: "check_single \<C> e = (\<lambda>ct''. if consume ct'' tls \<noteq> None then Some ([], Unreach) else None)"
      by blast
    then obtain cts' where cts'_def: "consume (rev ts, Reach) tls = Some (cts', Reach)"
      using assms
      by (metis consume_some_reachability_inv ct''_def(1) option.collapse prod.exhaust_sel snd_conv)
    then have "ts <ts: (rev cts')@tls"
      using c_types_agree_subtyping_reach consume_some_unsplit rev_rev_ident types_eq_c_types_agree
      apply (auto simp del: consume.simps split: option.splits)
      using c_types_agree_subtyping_reach consume_some_unsplit rev_rev_ident types_eq_c_types_agree
      by (metis (no_types, lifting) case_optionE)
    then have "c_types_agree ct ((rev cts')@tls)"
      using assms(2) c_types_agree_t_list_subtyping_inv by blast
    then have "consume ct tls \<noteq> None"
      by (metis c_types_agree_consume is_none_code(2) is_none_simps(1))
    then have "check_single \<C> e ct = Some ([], Unreach)" using tls_def by auto
    then show ?thesis
      by (metis ct''_def(1) ct''_def(2) option.distinct(1) tls_def)
  qed
qed

lemma b_e_type_checker_single_subsumption:
  assumes
    "b_e_type_checker \<C> [e] (tf1 _> tf2)"
    "(tf1 _> tf2) <ti: (tf1' _> tf2')"
  shows
    "b_e_type_checker \<C> [e] (tf1' _> tf2')"
proof -
  obtain ts ts' tf1_dom_sub tf1_ran_sub where defs:
    "tf1'= ts @ tf1_dom_sub"
    "tf2' = ts' @ tf1_ran_sub"
    "ts <ts: ts'"
    "tf1_dom_sub <ts: tf1"
    "tf2  <ts: tf1_ran_sub"
    using assms(2) unfolding instr_subtyping_def by auto
  obtain ct'' where ct''_def: "check_single \<C> e (rev tf1, Reach) = Some ct''" "c_types_agree ct'' tf2"
    using assms(1) by (auto split: option.splits)
  then consider
    (1) " (check_single \<C> e = (\<lambda> ct''. type_update_select ct'' None) \<and> e = Select None)"
  | (2) "(check_single \<C> e = type_update_ref_is_null) \<and> e = Ref_is_null"
  | (3) "(check_single \<C> e = type_update_drop) \<and> e = Drop"
  | (4) "(\<exists>cons prods. (check_single \<C> e = (\<lambda> ct''. type_update ct'' cons prods)))"
  | (5) "(\<exists> tls. check_single \<C> e = (\<lambda> ct''. (if (consume ct'' tls \<noteq> None) then Some ([], Unreach) else None)))"
    using check_single_imp assms by blast
  then show ?thesis
  proof(cases)
    case 1
    then obtain t where t_def: "[t, t, T_num T_i32] _> [t] <ti: tf1 _> tf2" "(is_num_type t \<or> is_vec_type t \<or> t = T_bot)" using b_e_type_select
      using assms(1) b_e_type_checker_sound 1
      by (metis option.simps(3))
    then have "[t, t, T_num T_i32] _> [t] <ti: tf1' _> tf2'"
      using assms(2) instr_subtyping_trans by blast
    then obtain ts'' where ts''_def: "tf1' <ts: ts''@[t,t,T_num T_i32]" "ts''@[t] <ts: tf2'"
      using instr_subtyping_def t_def(1) t_list_subtyping_concat
      using t_list_subtyping_refl by fastforce
    then obtain ct where ct_def: "ct = (rev tf1', Reach)" by blast
    then have "c_types_agree ct (ts''@[t, t, T_num T_i32])"
      using assms(2) c_types_agree_t_list_subtyping_inv
      by (metis rev_rev_ident ts''_def(1) types_eq_c_types_agree)
    then obtain ct1 where ct1_def: "pop_expect ct (T_num T_i32) = Some ct1" "c_types_agree ct1 (ts''@[t, t])"
      using c_types_agree_snoc_pop[of ct "(ts'@[t,t])" "T_num T_i32"]
      by (auto split: option.splits)
    then obtain ct2 t1 where ct2_def: "pop ct1 = Some (t1, ct2)" "t1 <t: t" "c_types_agree ct2 (ts''@[t])"
      using c_types_agree_snoc_pop
      by (metis append_Cons append_Nil append_assoc)
    then obtain ct3 t2 where ct3_def: "pop ct2 = Some (t2, ct3)" "t2 <t: t"
      using c_types_agree_snoc_pop
      by (metis)
    then obtain t'' where t''_def: "t'' = (if t1 = T_bot then t2 else t1)"
      by blast
    then have t_props: "t1 <t: t''" "t2 <t: t''" "t'' <t: t"
      using ct2_def(2) ct3_def(2) t_subtyping_def by metis+
    then have t''_prop: "(is_num_type t'' \<or> is_vec_type t'' \<or> t'' = T_bot)"
      using t_def(2) t_subtyping_def by auto
    then obtain ct4 where ct4_def: "push ct3 t'' = ct4" "c_types_agree ct4 (ts''@[t''])"
      using push_c_types_agree_snoc ct3_def
      using ct2_def(3) pop_c_type_agrees_snoc by blast
    then have "c_types_agree ct4 (ts''@[t])"
      by (metis c_types_agree_t_list_subtyping_inv list_all2_Cons2 list_all2_Nil t_list_subtyping_def t_list_subtyping_prepend t_props(3))
    then have "c_types_agree ct4 tf2'"
      using ts''_def(2)
      using c_types_agree_t_list_subtyping_inv by blast
    moreover have "type_update_select ct None = Some ct4"
      using ct1_def ct2_def ct3_def ct4_def t''_prop
      using t''_def t_subtyping_def by force
    ultimately show ?thesis using ct_def 1 by fastforce
  next
    case 2
    then obtain tr where tr_def: "[T_ref tr] _> [T_num T_i32] <ti: tf1 _> tf2"
      using assms(1) b_e_type_checker_sound b_e_type_ref_is_null by blast
    then have "[T_ref tr] _> [T_num T_i32] <ti: tf1' _> tf2'"
      using assms(2) instr_subtyping_trans by blast
    then obtain ts'' where ts''_def: "tf1' <ts: ts''@[T_ref tr]" "ts''@[T_num T_i32] <ts: tf2'"
      using instr_subtyping_def t_list_subtyping_concat t_list_subtyping_refl by fastforce
    then obtain ct'' t'' where ct''_def: "pop (rev tf1', Reach) = Some (t'', ct'')" "t'' <t: T_ref tr" "c_types_agree ct'' ts''"
      by (metis (no_types, opaque_lifting) c_types_agree_snoc_pop c_types_agree_t_list_subtyping_inv rev_rev_ident types_eq_c_types_agree)
    then obtain ct' where ct'_def: "push ct'' (T_num T_i32) = ct'" "c_types_agree ct' (ts''@[T_num T_i32])"
      using push_c_types_agree_snoc by blast
    then have "c_types_agree ct' tf2'" using ts''_def
      using c_types_agree_t_list_subtyping_inv by blast
    moreover have "check_single \<C> e (rev tf1', Reach) = Some ct'"
      using ct''_def(1,2) ct'_def(1) 2 is_ref_type_def t_subtyping_def
      by fastforce    
    ultimately show ?thesis by simp
  next
    case 3
    then obtain t where t_def: "[t] _> [] <ti: tf1 _> tf2"
      using assms(1) b_e_type_checker_sound b_e_type_drop
      by blast
    then have "[t] _> [] <ti: tf1' _> tf2'"
      using assms(2) instr_subtyping_trans by blast
    then obtain ts'' where ts''_def: "tf1' <ts: ts''@[t]" "ts'' <ts: tf2'"
      using instr_subtyping_def t_list_subtyping_concat t_list_subtyping_refl by fastforce
    then obtain ct' t' where ct'_def: "pop (rev tf1', Reach) = Some (t', ct')" "t' <t: t" "c_types_agree ct' ts''"
      by (metis (no_types, opaque_lifting) c_types_agree_snoc_pop c_types_agree_t_list_subtyping_inv rev_rev_ident types_eq_c_types_agree)
    then have "c_types_agree ct' tf2'" using ts''_def
      using c_types_agree_t_list_subtyping_inv by blast
    moreover have "check_single \<C> e (rev tf1', Reach) = Some ct'"
      using ct''_def(1,2) ct'_def(1) 3
      by fastforce    
    ultimately show ?thesis by simp
  next
    case 4
    then obtain prods cons where prods_cons_def: "check_single \<C> e = (\<lambda>ct''. type_update ct'' cons prods)"
      by blast
    then have "cons _> prods <ti: tf1 _> tf2"
      by (metis c_types_agree_subtyping_reach ct''_def(1) ct''_def(2) instr_subtyping_replace3 list_all2_rev1 rev_rev_ident t_list_subtyping_def type_update_type)
    then have "cons _> prods <ti: tf1' _> tf2'" using assms(2) instr_subtyping_trans by blast
    then obtain ct' where "check_single \<C> e (rev tf1', Reach) = Some ct'" "c_types_agree ct' tf2'"
      by (metis c_types_agree_type_update prods_cons_def rev_swap types_eq_c_types_agree)
    then show ?thesis
      by auto
  next
    case 5
    then obtain tls where tls_def: "check_single \<C> e =
          (\<lambda>ct''. if consume ct'' tls \<noteq> None then Some ([], Unreach) else None)" by blast
    then obtain ct'' where ct''_def: "consume (rev tf1, Reach) tls = Some ct''"
      using ct''_def(1) by fastforce
    then have "c_types_agree (rev tf1, Reach) ((rev (fst ct'')) @ tls)"
      using consume_c_types_agree[OF ct''_def]
      by (metis prod.collapse types_eq_c_types_agree)
    then have "tf1 <ts: (rev (fst ct''))@tls"
      using c_types_agree_subtyping_reach by fastforce
    then obtain ts'' tls'' where "tf1'=ts''@tls''" "tls'' <ts: tls"
      using defs(1,4)
      by (metis append.assoc t_list_subtyping_split2 t_list_subtyping_trans)
    then have "consume (rev tf1', Reach) tls \<noteq> None"
      by (metis c_types_agree_consume consume_t_list_subtyping option.distinct(1) rev_rev_ident types_eq_c_types_agree)
    moreover have "c_types_agree ([], Unreach) tf2'"
      by (simp add: pop_expect_list_unreach_empty)
    ultimately show ?thesis using tls_def by simp
  qed
qed

lemma check_single_unreach_imp_b_e_typing:
  assumes
    "check_single \<C> e (cts1, Unreach) = Some (cts2, Unreach)"
  shows
    "\<exists> ts1. b_e_type_checker \<C> [e] (ts1@(rev cts1) _> (rev cts2))"
proof -
   consider
    (1) " (check_single \<C> e = (\<lambda> ct''. type_update_select ct'' None) \<and> e = Select None)"
  | (2) "(check_single \<C> e = type_update_ref_is_null) \<and> e = Ref_is_null"
  | (3) "(check_single \<C> e = type_update_drop) \<and> e = Drop"
  | (4) "(\<exists>cons prods. (check_single \<C> e = (\<lambda> ct''. type_update ct'' cons prods)))"
  | (5) "(\<exists> tls. check_single \<C> e = (\<lambda> ct''. (if (consume ct'' tls \<noteq> None) then Some ([], Unreach) else None)))"
    using check_single_imp assms by blast
  then show ?thesis
  proof(cases)
    case 1
    then have "c_types_agree (cts1, Unreach) (rev cts1)"
      using types_eq_c_types_agree by blast
    then obtain ct2 where ct2_def: "pop_expect (cts1, Unreach) (T_num T_i32) = Some ct2"
      by (metis (no_types, lifting) 1 assms b_e.inject(1) not_Some_eq option.case_eq_if type_update_select.simps(1))
    then obtain ct3 t1 where ct3_def: "pop ct2 = Some (t1, ct3)"
      by (metis pop.elims pop_expect_some(1) reach.simps(4) snd_eqD types_eq_c_types_agree)
    then obtain ct4 t2 where ct4_def: "pop ct3 = Some (t2, ct4)"
      by (metis (no_types, opaque_lifting) ct2_def eq_fst_iff fst_swap pop.elims pop_expect_some(1) pop_some_reachability_inv reach.simps(4) swap_simp types_eq_c_types_agree)
    then obtain t'' where t''_def: "t'' = (if t1 = T_bot then t2 else t1)"
      by blast
    then have t1_t2_prop: "(((is_num_type t1 \<or> t1 = T_bot) \<and> (is_num_type t2 \<or> t2 = T_bot)) \<or> ((is_vec_type t1 \<or> t1 = T_bot) \<and> (is_vec_type t2 \<or> t2 = T_bot)))"
      using assms 1 ct2_def ct3_def ct4_def
      using  not_None_eq by fastforce
    then have t''_props: "(is_num_type t'' \<or> is_vec_type t'' \<or> t'' = T_bot)" "t1 <t: t''" "t2 <t: t''"
      using t''_def t1_t2_prop
      apply metis
      apply (auto simp add: t''_def t_subtyping_def)
      using 1 assms ct2_def ct3_def ct4_def option.sel t1_t2_prop by fastforce
    then obtain ct5 where ct5_def: "ct5 = push ct4 t''"
      by blast
    have ct5_is: "ct5 = (cts2, Unreach)"
      using 1 ct2_def ct3_def ct4_def ct5_def t''_def t1_t2_prop is_num_type_def is_vec_type_def assms
      apply (auto split: option.splits)
      by (metis (mono_tags, opaque_lifting) option.sel option.simps(3))+
    have ct2_cons: "Some ct2 = consume (cts1, Unreach) [T_num T_i32]" using ct2_def by simp
    have ct3_cons: "Some ct3 = consume ct2 [t'']" using ct3_def t''_def t''_props
      by simp
    have ct4_cons: "Some ct4 = consume ct3 [t'']" using ct4_def t''_def t''_props
      by simp
    have ct5_prods: "ct5 = produce ct4 [t'']" using ct5_def t''_def t''_props
      by (metis append_eq_Cons_conv eq_Nil_appendI produce.simps push.simps push_rev_list.simps rev_singleton_conv split_pairs)
    then have "Some ct4 = consume (cts1, Unreach) [t'', t'', T_num T_i32]"
      using ct2_cons ct3_cons ct4_cons
      by (metis append_Cons append_Nil consume_some_unsplit)
    then obtain cons prods where "Some ct5 = type_update (cts1, Unreach) [t'', t'', T_num T_i32] [t'']" "cons = [t'', t'', T_num T_i32]" "prods = [t'']"
      using ct5_prods
      by (metis map_option_eq_Some type_update.simps)
    consider
        (l1) "length cts1 = 0" 
      | (l2) "length cts1 = 1" 
      | (l3) "length cts1 = 2" 
      | (l4) "length cts1 \<ge> 3" 
      using less_2_cases nat_less_le not_less_eq_eq by fastforce
    then show ?thesis
    proof(cases)
      case l1
      then have cts1_is: "cts1 =  []" by simp
      then have "ct5 = ([t''], Unreach)"
        by (metis consume.simps ct2_cons ct3_cons ct3_def ct4_def ct5_def option.sel pop_expect_list_unreach_append push.simps rev.simps(1) rev.simps(2) snd_conv)
      moreover have "b_e_type_checker \<C> [e] ([t'', t'', T_num T_i32] _> [t''])"
        using 1 assms t''_def t1_t2_prop t_subtyping_def
        apply simp
        by metis
      ultimately show ?thesis using ct5_is
        by (metis append.right_neutral cts1_is fst_conv rev.simps(1) rev_singleton_conv)
    next
      case l2
      then obtain t0' where t'_defs: "cts1 = [t0']"
        apply (auto split: list.splits)
        by (metis Groups.add_ac(2) One_nat_def Suc_1 le_zero_eq list.exhaust list.size(3) list.size(4) nat.simps(3) not_less_eq_eq numeral_eq_Suc plus_1_eq_Suc pred_numeral_simps(3))
      then have ct5_is2: "ct5 = ([t''], Unreach)"
        using ct2_cons ct3_cons ct3_def ct4_def ct5_def option.sel pop_expect_list_unreach_append push.simps rev.simps(1) rev.simps(2) snd_conv
        apply (auto split: option.splits)
        by (metis consume.simps ct3_cons option.sel option.simps(3) push.simps rev.simps(1) rev.simps(2) snd_conv)
      have "t0' <t: T_num T_i32"
        using ct2_cons ct3_cons ct3_def ct4_def ct5_def t'_defs t''_props
        by (auto simp add: handy_if_lemma split: option.splits prod.splits)
      then have "check_single \<C> e (cts1@[t'', t''], Reach) = Some (cts2, Reach)"
        using t'_defs t''_props t''_def 1
        apply (simp split: option.splits)
        by (metis ct5_is2 append.left_neutral append_Cons ct5_is fst_conv t1_t2_prop )
      then have "b_e_type_checker \<C> [e] ([t'', t'']@rev cts1 _> rev cts2)"
        apply (simp split: option.splits)
        by (simp add: pop_expect_list_reach_subtypes t_list_subtyping_refl)
      then show ?thesis
        by metis
    next
      case l3
      then obtain t0' t1' where t'_defs: "cts1 = [t0', t1']"
        by (metis Groups.add_ac(2) One_nat_def Suc_1 le_zero_eq list.exhaust list.size(3) list.size(4) nat.simps(3) not_less_eq_eq numeral_eq_Suc plus_1_eq_Suc pred_numeral_simps(3))
      then have ct5_is2: "ct5 = ([t''], Unreach)"
        using ct2_cons ct3_cons ct3_def ct4_def ct5_def option.sel pop_expect_list_unreach_append push.simps rev.simps(1) rev.simps(2) snd_conv
        apply (auto split: option.splits)
        by (metis (mono_tags, lifting) consume.simps ct4_cons option.discI option.inject option.inject pop.simps(2) push.simps self_append_conv2 snd_eqD)
      have "t0' <t: T_num T_i32" "t1' <t: t''" "t1' = t1"
        using ct2_cons ct3_cons ct3_def ct4_def ct5_def t'_defs t''_props
        by (auto simp add: handy_if_lemma split: option.splits prod.splits)
      then have "check_single \<C> e (cts1@[t''], Reach) = Some (cts2, Reach)"
        using t'_defs t''_props t''_def 1
        apply (simp split: option.splits)
        by (metis ct5_is2  ct5_is fst_conv t1_t2_prop)
      then have "b_e_type_checker \<C> [e] ([t'']@rev cts1 _> rev cts2)"
        apply (simp split: option.splits)
        by (simp add: pop_expect_list_reach_subtypes t_list_subtyping_refl)
      then show ?thesis
        by (metis)
    next
      case l4
      then obtain t0' t1' t2' cts' where t'_defs: "cts1 = [t0', t1', t2']@cts'"
        apply (auto split: list.splits)
        by (metis Groups.add_ac(2) One_nat_def Suc_1 le_zero_eq list.exhaust list.size(3) list.size(4) nat.simps(3) not_less_eq_eq numeral_eq_Suc plus_1_eq_Suc pred_numeral_simps(3))
      then have ct5_is2: "ct5 = ([t'']@cts', Unreach)"
        using ct2_cons ct3_cons ct3_def ct4_def ct5_def option.sel pop_expect_list_unreach_append push.simps rev.simps(1) rev.simps(2) snd_conv
        apply (auto split: option.splits)
        by (metis (no_types, lifting) Pair_inject option.inject option.simps(3) pop.simps(2) push.simps)
      have "t0' <t: T_num T_i32" "t1' <t: t''" "t2' <t: t''" "t1' = t1" "t2' = t2"
        using ct2_cons ct3_cons ct3_def ct4_def ct5_def t'_defs t''_props
        by (auto simp add: handy_if_lemma split: option.splits prod.splits)
      then have "check_single \<C> e (cts1, Reach) = Some (cts2, Reach)"
        using t'_defs t''_props t''_def 1 apply (simp split: option.splits)
        by (metis ct5_is2 append.left_neutral append_Cons ct5_is fst_conv t1_t2_prop t_subtyping_def)
      then have "b_e_type_checker \<C> [e] (rev cts1 _> rev cts2)"
        apply (simp split: option.splits)
        by (simp add: pop_expect_list_reach_subtypes t_list_subtyping_refl)
      then show ?thesis
        by (metis append.left_neutral)
    qed
  next
    case 2
    then show ?thesis
    proof(cases cts1)
      case Nil
      then have "cts2 = [T_num T_i32]" using 2 assms by simp
      then have "b_e_type_checker \<C> [e] ([T_bot] _> rev cts2)"
        using 2 t_subtyping_def by simp
      then show ?thesis using Nil
        by (metis append_Nil2 rev.simps(1))
    next
      case (Cons t' cts')
      then have t'_prop: "(is_ref_type t' \<or> t' = T_bot)"
        using 2 assms by (simp add: handy_if_lemma)
      then have cts2_is: "cts2 = (T_num T_i32)#cts'" using 2 assms Cons by (auto simp add: handy_if_lemma split: option.splits)
      then have "check_single \<C> e (cts1, Reach) = Some (cts2, Reach)" using Cons t'_prop 2 by simp
      then have "b_e_type_checker \<C> [e] (rev cts1 _> rev cts2)"
        using types_eq_c_types_agree by fastforce
      then show ?thesis
        by (metis append_self_conv2)
    qed
  next
    case 3
    then show ?thesis
    proof(cases cts1)
      case Nil
      then have "cts2 = []" using 3 assms by simp
      then have "b_e_type_checker \<C> [e] ([T_bot] _> rev cts2)"
        using 3 t_subtyping_def by simp
      then show ?thesis using Nil
        by (metis append_Nil2 rev.simps(1))
    next
      case (Cons t' cts')
      then have cts2_is: "cts2 = cts'" using 3 assms Cons by (auto simp add: handy_if_lemma split: option.splits)
      then have "check_single \<C> e (cts1, Reach) = Some (cts2, Reach)" using Cons 3 by simp
      then have "b_e_type_checker \<C> [e] (rev cts1 _> rev cts2)"
        using types_eq_c_types_agree by fastforce
      then show ?thesis
        by (metis append_self_conv2)
    qed
  next
    case 4
    then obtain cons prods where cons_prods_def: "check_single \<C> e = (\<lambda>ct''. type_update ct'' cons prods)"
      by blast
    then obtain cts3 where cts3_def: "consume (cts1, Unreach) cons = Some (cts3, Unreach)" "produce (cts3, Unreach) prods = (cts2, Unreach)"
      using assms by auto
    then show ?thesis
    proof(cases cts3)
      case Nil
      then have "c_types_agree (cts1, Unreach) cons" using cts3_def by simp
      then obtain ts where ts_def: "ts@rev cts1 <ts: cons"
        using c_types_agree_subtyping_unreach by blast
      then have "rev cts2 = prods"
        using cts3_def(2) local.Nil by fastforce
      then have a: "produce ([], Reach) prods = (cts2, Reach)" by fastforce
      have b: "consume (cts1 @ rev ts, Reach) cons = Some ([], Reach)" using ts_def
        by (metis consume.simps consume_t_list_subtyping pop_expect_list_reach_subtypes rev_append rev_rev_ident t_list_subtyping_refl)
      then have  "check_single \<C> e (cts1 @ rev ts, Reach) = Some (cts2, Reach)" using a b cons_prods_def by simp
      then show ?thesis apply (auto simp del: c_types_agree.simps split: option.splits)
        using types_eq_c_types_agree by fastforce
    next
      case (Cons x xs)
      then have "consume (cts1, Unreach) cons = Some (cts3, Unreach)" using cts3_def by simp
      then obtain cons' where "rev cts1 =  rev(cts3)@cons'" "cons' <ts: cons"
        using Cons consume_unreach_nonempty
        by fastforce
      then have a: "consume (cts1, Reach) cons = Some (cts3, Reach)"
        by (metis c_types_agree_cons_prods_same consume_t_list_subtyping produce.simps push_rev_list.simps rev_append rev_rev_ident)
      have b: "produce (cts3, Reach) prods = (cts2, Reach)"
        using cts3_def(2) by auto
      have "b_e_type_checker \<C> [e] (rev cts1 _> rev cts2)"
        using a b types_eq_c_types_agree cons_prods_def
        by (auto simp del: consume.simps produce.simps split: option.splits)
      then show ?thesis
        by (metis append.left_neutral)
    qed
  next
    case 5
    then obtain tls where tls_def: "check_single \<C> e =
        (\<lambda>ct''. if consume ct'' tls \<noteq> None then Some ([], Unreach) else None)" by blast
    then obtain cts3 where cts3_def: "consume (cts1, Unreach) tls = Some (cts3, Unreach)"
      using assms
      by (metis consume_some_reachability_inv option.collapse prod.exhaust_sel snd_conv)
    have cts2_is: "cts2 = []" using tls_def assms
      by (metis option.inject option.simps(3) prod.inject)
    show ?thesis
    proof(cases cts3)
      case Nil
      then have "c_types_agree (cts1, Unreach) tls"
        using tls_def cts3_def by fastforce
      then obtain ts' where "ts'@(rev cts1) <ts: tls"
        using c_types_agree_subtyping_unreach
        by blast
      then have "check_single \<C> e (cts1@(rev ts'), Reach) = Some ([], Unreach)"
        by (metis append_Nil c_types_agree_consume c_types_agree_t_list_subtyping_inv option.distinct(1) rev_append rev_rev_ident tls_def types_eq_c_types_agree)
      then show ?thesis using cts2_is
        apply (auto split: option.splits)
        by (metis Pair_inject  option.inject)
    next
      case (Cons a list)
      then obtain ts' where "rev cts1 = rev cts3 @ ts'" "ts' <ts: tls"
        using consume_unreach_nonempty cts3_def by blast
      then have "check_single \<C> e (cts1, Reach) = Some ([], Unreach)"
        by (metis c_types_agree_consume consume_t_list_subtyping not_Some_eq tls_def types_eq_c_types_agree)
      moreover have "b_e_type_checker \<C> [e] (rev cts1 _> [])"
        using calculation by simp
      ultimately show ?thesis using cts2_is
        apply (auto split: option.splits)
        by (metis Pair_inject append_Nil2 option.inject rev.simps(1))
    qed
  qed
qed

lemma b_e_type_checker_composition_complete:
  assumes "\<C> \<turnstile> es : t1s _> t2s"
          "b_e_type_checker \<C> es (t1s _> t2s)"
          "\<C> \<turnstile> [e] : t2s _> t3s"
          "b_e_type_checker \<C> [e] (t2s _> t3s)"
  shows "b_e_type_checker \<C> (es @ [e]) (t1s _> t3s)"
proof -
  obtain ct2 where ct2_def: "check \<C> es (rev t1s, Reach) = Some ct2" "c_types_agree ct2 t2s" using assms(2)
    by (metis Wasm_Checker.check_top case_optionE)
  have "\<exists> ct3. check_single \<C> e ct2 = Some ct3 \<and> c_types_agree ct3 t3s"
    using assms(4) b_e_type_checker_imp_check_single ct2_def(2) by blast
  then show ?thesis using ct2_def check_snoc by (auto split: option.splits)
qed

lemma check_unsnoc:
  assumes "check \<C> (es@[e]) ct = Some ct'"
  shows "\<exists> ct''. check \<C> es ct = Some ct'' \<and> check_single \<C> e ct'' = Some ct'"
  using assms
proof(induction es arbitrary: ct ct')
  case Nil
  then show ?case
    by (metis (no_types, lifting) check.elims list.simps(4) list.simps(5) option.case_eq_if option.collapse self_append_conv2)
next
  case (Cons x xs)
  obtain ct''' where ct'''_def: "check_single \<C> x ct = Some ct'''" "check \<C> (xs@[e]) ct''' = Some ct'"
    using Cons(2)
    by (auto split: option.splits)
  then obtain ct'' where ct''_def: "check \<C> xs ct''' = Some ct''"  "check_single \<C> e ct'' = Some ct'"
    using Cons.IH by blast
  then have "check \<C> (x#xs) ct = Some ct''" using ct'''_def by simp
  then show ?case using ct''_def by blast
qed

lemma check_reachability_some_invariant:
  assumes
    "check \<C> es ct1 = Some ct2"
    "check \<C> es ct1' = Some ct2'"
    "snd ct1 = snd ct1'"
  shows
    "snd ct2 = snd ct2'"
  using assms
proof(induction es arbitrary: ct1 ct2 ct1' ct2' rule: rev_induct)
  case Nil
  then show ?case
    by simp
next
  case (snoc x xs)
  obtain ct3 ct3' where ct3_defs: "check \<C> (xs) ct1 = Some ct3" "check_single \<C> x ct3 = Some ct2" "check \<C> (xs) ct1' = Some ct3'" "check_single \<C> x ct3' = Some ct2'"
    by (meson check_unsnoc snoc.prems(1) snoc.prems(2))
  then have snd_ct3_eq: "snd ct3 = snd ct3'"
    using snoc.IH snoc.prems(3) by blast
  consider
    (1) " (check_single \<C> x = (\<lambda> ct''. type_update_select ct'' None) \<and> x = Select None)"
  | (2) "(check_single \<C> x = type_update_ref_is_null) \<and> x = Ref_is_null"
  | (3) "(check_single \<C> x = type_update_drop) \<and> x = Drop"
  | (4) "(\<exists>cons prods. (check_single \<C> x = (\<lambda> ct''. type_update ct'' cons prods)))"
  | (5) "(\<exists> tls. check_single \<C> x = (\<lambda> ct''. (if (consume ct'' tls \<noteq> None) then Some ([], Unreach) else None)))"
    using check_single_imp ct3_defs by blast
  then show ?case
  proof(cases)
    case 1
    then show ?thesis
      using snd_ct3_eq ct3_defs(2,4) handy_if_lemma pop_some_reachability_inv
      apply (auto simp add: pop_some_reachability_inv handy_if_lemma split: option.splits)
      using handy_if_lemma pop_some_reachability_inv
      by (metis (no_types, opaque_lifting) option.distinct(1) push.simps snd_conv)
  next
    case 2
    then show ?thesis
      apply(cases "snd ct3")
      using snd_ct3_eq ct3_defs(2,4)
       apply (auto simp add: handy_if_lemma split: option.splits)
      by (auto simp add: pop_some_reachability_inv)
  next
    case 3
    then show ?thesis
      apply(cases "snd ct3")
      using snd_ct3_eq ct3_defs(2,4) by (auto simp add: pop_some_reachability_inv)
  next
    case 4
    then obtain cons prods where "check_single \<C> x = (\<lambda>ct''. type_update ct'' cons prods)" by blast
    then show ?thesis
      apply(cases "snd ct3") using snd_ct3_eq ct3_defs(2,4)
      by (auto simp add: pop_expect_list_some_reachability_inv)+
  next
    case 5
    then show ?thesis
      by (metis ct3_defs(2) ct3_defs(4) option.discI option.inject)
  qed
qed

lemma check_to_unreach_stack_eq:
  assumes
    "check \<C> es ct1 = Some ct2"
    "check \<C> es ct1' = Some ct2'"
    "snd ct1 = Reach"
    "snd ct1' = Reach"
    "snd ct2 = Unreach"
  shows
    "ct2 = ct2'"
  using assms
proof(induction es arbitrary: ct1 ct2 ct1' ct2' rule: rev_induct)
  case Nil
  then show ?case
    using reach.distinct(1)
    by fastforce
next
  case (snoc x xs)
  obtain ct3 ct3' where ct3_defs: "check \<C> (xs) ct1 = Some ct3" "check_single \<C> x ct3 = Some ct2" "check \<C> (xs) ct1' = Some ct3'" "check_single \<C> x ct3' = Some ct2'"
    by (meson check_unsnoc snoc.prems(1) snoc.prems(2))
  then have snd_ct3_eq: "snd ct3 = snd ct3'"
    using snoc.IH snoc.prems(3)
    by (metis check_reachability_some_invariant snoc.prems(4))
  consider
    (1) " (check_single \<C> x = (\<lambda> ct''. type_update_select ct'' None) \<and> x = Select None)"
  | (2) "(check_single \<C> x = type_update_ref_is_null) \<and> x = Ref_is_null"
  | (3) "(check_single \<C> x = type_update_drop) \<and> x = Drop"
  | (4) "(\<exists>cons prods. (check_single \<C> x = (\<lambda> ct''. type_update ct'' cons prods)))"
  | (5) "(\<exists> tls. check_single \<C> x = (\<lambda> ct''. (if (consume ct'' tls \<noteq> None) then Some ([], Unreach) else None)))"
    using check_single_imp assms ct3_defs by blast
  then show ?case
  proof(cases)
    case 1
    then show ?thesis
      using ct3_defs(2,4) handy_if_lemma pop_some_reachability_inv
      apply (auto simp add: pop_some_reachability_inv handy_if_lemma split: option.splits)
      using handy_if_lemma pop_some_reachability_inv
      by (metis (no_types, lifting) ct3_defs(1) ct3_defs(2) ct3_defs(3) ct3_defs(4) push.simps snd_conv snoc.IH snoc.prems(3) snoc.prems(4) snoc.prems(5))
  next
    case 2
    then show ?thesis
      using snd_ct3_eq ct3_defs(2,4)
       apply (auto simp add: handy_if_lemma split: option.splits)
      using pop_some_reachability_inv snoc.prems(5) apply auto
      by (metis (mono_tags, lifting) ct3_defs(1) ct3_defs(3) handy_if_lemma snoc.IH snoc.prems(3) snoc.prems(4) split_pairs)+
  next
    case 3
    then show ?thesis
      using snd_ct3_eq ct3_defs(2,4) apply (auto simp add: pop_some_reachability_inv)
      by (metis (no_types, lifting) ct3_defs(1) ct3_defs(3) option.inject pop_some_reachability_inv prod.inject snoc.IH snoc.prems(3) snoc.prems(4) snoc.prems(5))
  next
    case 4
    then obtain cons prods where "check_single \<C> x = (\<lambda>ct''. type_update ct'' cons prods)" by blast
    then show ?thesis
      using snd_ct3_eq ct3_defs(2,4)
      apply (auto simp add: pop_expect_list_some_reachability_inv)
      by (metis (mono_tags, lifting) ct3_defs(1) ct3_defs(3) old.prod.inject option.inject pop_expect_list_some_reachability_inv snd_conv snoc.IH snoc.prems(3) snoc.prems(4) snoc.prems(5))
  next
    case 5
    then show ?thesis
      by (metis ct3_defs(2) ct3_defs(4) option.discI option.inject)
  qed
qed

lemma b_e_type_checker_subsumption_complete:
  assumes
    "b_e_type_checker \<C> es (tf1 _> tf2)"
    "tf1 _> tf2 <ti: tf1' _> tf2'"
  shows
    "b_e_type_checker \<C> es (tf1' _> tf2')"
  using assms
proof(induction es arbitrary: tf1 tf2 tf1' tf2' rule: rev_induct)
  case Nil
  then have "[] _> [] <ti: tf1 _> tf2"
    using b_e_type_checker_sound by blast
  then have "[] _> [] <ti: tf1' _> tf2'"
    using Nil.prems(2) instr_subtyping_trans by blast
  then have "tf1' <ts: tf2'"
    by (metis self_append_conv t_list_subtyping_instr_subtyping_append t_list_subtyping_refl)
  then show ?case
    using c_types_agree_t_list_subtyping_inv types_eq_c_types_agree by fastforce
next
  case (snoc e' es')
  obtain ts ts' tf1_dom_sub tf1_ran_sub where defs:
     "tf1'= ts @ tf1_dom_sub"
     "tf2' = ts' @ tf1_ran_sub"
     "ts <ts: ts'"
     "tf1_dom_sub <ts: tf1"
     "tf2  <ts: tf1_ran_sub"
    using snoc.prems(2)  unfolding instr_subtyping_def by auto
  obtain ct' where ct'_def: "check \<C> (es' @ [e']) (rev tf1, Reach) = Some (ct')" "c_types_agree ct' tf2"
    by (metis b_e_type_checker.simps case_optionE snoc.prems(1))

  then obtain ct'' where ct''_def: "check \<C> (es') (rev tf1, Reach) = Some ct''" "check_single \<C> e' ct'' = Some ct'"
    using check_unsnoc by blast
  show ?case
  proof(cases "snd ct''")
    case Reach
    then have 1: "b_e_type_checker \<C> es' (tf1 _> rev (fst ct''))"
      by (metis b_e_type_checker.simps ct''_def(1) option.simps(5) prod.exhaust_sel types_eq_c_types_agree)
    have 2: "b_e_type_checker \<C> [e'] (rev (fst ct'') _> tf2)"
      by (metis Reach Wasm_Checker.check_iter ct'_def(1) b_e_type_checker.simps ct''_def(2) list.case(1) list.case(2) option.simps(5) rev_swap snoc.prems(1) split_pairs)
    obtain tf'' where tf''_def: "(tf1 _> rev (fst ct'')) <ti: tf1' _> tf''" "(rev (fst ct'') _> tf2) <ti: tf'' _> tf2'"
      using instr_subtyping_split snoc.prems(2) by blast
    then have "b_e_type_checker \<C> es' (tf1' _> tf'')"
      using 1 snoc.IH by blast
    then show ?thesis
      using 1 2 b_e_type_checker_composition_complete b_e_type_checker_single_subsumption b_e_type_checker_sound 
      using tf''_def(2) by blast
  next
    case Unreach
    then have 1: "b_e_type_checker \<C> es' (tf1 _> rev (fst ct''))"
      by (metis b_e_type_checker.simps ct''_def(1) option.simps(5) prod.exhaust_sel types_eq_c_types_agree)
    obtain tf'' where tf''_def: "(tf1 _> rev (fst ct'')) <ti: tf1' _> tf''" "(rev (fst ct'') _> tf2) <ti: tf'' _> tf2'"
      using instr_subtyping_split snoc.prems(2) by blast
    then have 2: "b_e_type_checker \<C> es' (tf1' _> tf'')"
      using 1 snoc.IH by blast
    then obtain ct''' where ct'''_def: "check \<C> es' (rev tf1', Reach) = Some ct'''" "snd ct''' = Unreach"
      using check_reachability_some_invariant
      by (metis (no_types, lifting) Unreach b_e_type_checker.simps case_optionE ct''_def(1) snd_conv)
    obtain ts'_tail where ts'_tail_def: "ts'_tail@(rev (fst ct')) <ts: tf2"
      by (metis append.left_neutral c_types_agree_subtyping ct'_def(2) eq_fst_iff)
    obtain ts_tail where ts_tail_def: "b_e_type_checker \<C> [e'] ((ts_tail@(rev (fst ct''))) _> rev (fst ct'))"
      by (metis Unreach check_single_unreach_imp_b_e_typing check_single_unreach_inv ct''_def(2) prod.collapse)
    obtain ts'' ts''' tf''' tf2'' where ts''_def: "tf'' = ts''@tf'''" "tf''' <ts: rev (fst ct'')" "ts'' <ts: ts'''" "tf2 <ts: tf2''"
      using instr_subtyping_def tf''_def(2) by auto
    have  "c_types_agree ct''' tf''"
      using "2" ct'''_def(1) by fastforce
    have a: "ct''' = ct''"
      by (meson check_to_unreach_stack_eq ct'''_def(1) ct'''_def(2) ct''_def(1) split_pairs)
    have 1: "b_e_type_checker \<C> [e'] (ts'_tail@(ts_tail@(rev (fst ct''))) _> ts'_tail@rev (fst ct'))"
        using ts_tail_def
      by (metis b_e_type_checker_single_subsumption instr_subtyping_def t_list_subtyping_refl tf.sel(1) tf.sel(2))
    have "c_types_agree ct''' (ts'_tail@(ts_tail@(rev (fst ct''))))"  using a
      by (metis Unreach append.assoc c_types_agree.simps consume.simps pop_expect_list.simps(1) pop_expect_list_unreach_append rev_append rev_swap split_pairs types_eq_c_types_agree)
    then obtain ct'''' where ct''''_def: "check_single \<C> e' ct''' = Some ct''''" "c_types_agree ct'''' (ts'_tail@rev (fst ct'))"
      using 1 b_e_type_checker_imp_check_single by blast
    then have 2: "c_types_agree ct'''' tf2"
      using ts'_tail_def c_types_agree_t_list_subtyping_inv by blast
    obtain tf2'' ts'' where tf2'_def: "tf2'=ts''@tf2''" "tf2 <ts: tf2''"
      using defs by blast
    then have "c_types_agree ct'''' tf2''"
      using 2 c_types_agree_t_list_subtyping_inv by blast
    then have 3: "c_types_agree ct'''' tf2'" using c_types_agree_unreach_append
      using tf2'_def check_single_unreach_inv ct''''_def(1) ct'''_def(2) by blast
    then have "check \<C> (es'@[e']) (rev tf1', Reach) = Some ct''''"
      using ct'''_def check_snoc
      by (simp add: ct''''_def(1))
    then show ?thesis
      using 3 by auto
  qed
qed

lemma b_e_type_checker_complete:
  assumes "\<C> \<turnstile> es : (ts _> ts')"
  shows "b_e_type_checker \<C> es (ts _> ts')"
  using assms 
       c_types_agree_cons_prods_same
       t_subtyping_def
       t_list_subtyping_refl
       pop_expect_list_reach_subtypes
       pop_expect_list_unreach_empty
       is_ref_type_def
proof(induction \<C> es "ts _> ts'" arbitrary: ts ts' rule: b_e_typing.induct)
  case (br_table \<C> ts "is" i t1s t2s)
  then show ?case using  list_all_conv_min_lab[OF br_table(1)]
    apply auto
    by (metis (no_types, opaque_lifting) consume.simps consume_t_list_subtyping)
next
  case (composition \<C> es t1s t2s e t3s)
  then show ?case using b_e_type_checker_composition_complete by blast
next
  case (subsumption \<C> es tf1 tf2 tf1' tf2')
  then show ?case using b_e_type_checker_subsumption_complete by blast
qed auto

theorem b_e_typing_equiv_b_e_type_checker:
  shows "(\<C> \<turnstile> es : tf) = (b_e_type_checker \<C> es tf)"
  by (metis b_e_type_checker_complete b_e_type_checker_sound tf.exhaust_sel)

end
