section {* Correctness of Type Checker *}

theory Wasm_Checker_Properties imports Wasm_Checker Wasm_Properties begin

subsection {* Soundness *}

lemma b_e_check_single_type_sound:
  assumes "type_update (Type x1) (to_ct_list t_in) (Type t_out) = Type x2"
          "c_types_agree (Type x2) tm"
          "\<C> \<turnstile> [e] : (t_in _> t_out)"
  shows "\<exists>tn. c_types_agree (Type x1) tn \<and> \<C> \<turnstile> [e] : (tn _> tm)"
  using assms(2) b_e_typing.weakening[OF assms(3)] type_update_type[OF assms(1)]
  by auto

lemma b_e_check_single_top_sound:
  assumes "type_update (TopType x1) (to_ct_list t_in) (Type t_out) = TopType x2"
          "c_types_agree (TopType x2) tm"
          "\<C> \<turnstile> [e] : (t_in _> t_out)"
  shows "\<exists>tn. c_types_agree (TopType x1) tn \<and> \<C> \<turnstile> [e] : (tn _> tm)"
proof -
  obtain t_ag where t_ag_def:"ct_suffix (to_ct_list t_out) x2"
                             "tm = t_ag @ t_out"
                             "c_types_agree (TopType x1) (t_ag @ t_in)"
    using type_update_top_top[OF assms(1,2)]
    by fastforce
  hence "\<C> \<turnstile> [e] : (t_ag@t_in _> t_ag@t_out)"
    using b_e_typing.weakening[OF assms(3)]
    by fastforce
  thus ?thesis
    using t_ag_def
    by fastforce
qed

lemma b_e_check_single_top_not_bot_sound:
  assumes "type_update ts (to_ct_list t_in) (TopType []) = ts'"
          "ts \<noteq> Bot"
          "ts' \<noteq> Bot"
  shows "\<exists>tn. c_types_agree ts tn \<and> suffix t_in tn"
proof (cases ts)
  case (TopType x1)
  then obtain t_int where "consume (TopType x1) (to_ct_list t_in) = t_int" "t_int \<noteq> Bot"
    using assms(1,2,3)
    by fastforce
  thus ?thesis
    using TopType ct_suffix_ct_list_compat_exists ct_suffix_ts_conv_suffix
    unfolding consume.simps
    by (metis append_Nil c_types_agree.simps(2) ct_suffix_def)
next
  case (Type x2)
  then obtain t_int where "consume (Type x2) (to_ct_list t_in) = t_int" "t_int \<noteq> Bot"
    using assms(1,2,3)
    by fastforce
  thus ?thesis
    using c_types_agree_id Type consume_type suffixI ct_suffix_ts_conv_suffix
    by fastforce
next
  case Bot
  thus ?thesis
    using assms(2)
    by simp
qed

lemma b_e_check_single_type_not_bot_sound:
  assumes "type_update ts (to_ct_list t_in) (Type t_out) = ts'"
          "ts \<noteq> Bot"
          "ts' \<noteq> Bot"
          "c_types_agree ts' tm"
          "\<C> \<turnstile> [e] : (t_in _> t_out)"
  shows "\<exists>tn. c_types_agree ts tn \<and> \<C> \<turnstile> [e] : (tn _> tm)"
  using assms b_e_check_single_type_sound
proof (cases ts)
  case (TopType x1)
  then obtain x1' where x_def:"TopType x1' = ts'"
    using assms
    by (simp, metis (full_types) produce.simps(1) produce.simps(6))
  thus ?thesis
    using assms b_e_check_single_top_sound TopType
    by fastforce
next
  case (Type x2)
  then obtain x2' where x_def:"Type x2' = ts'"
    using assms
    by (simp, metis (full_types) produce.simps(2) produce.simps(6))
  thus ?thesis
    using assms b_e_check_single_type_sound Type
    by fastforce
next
  case Bot
  thus ?thesis
    using assms(2)
    by simp
qed

lemma b_e_check_single_sound_unop_testop_cvtop:
  assumes "check_single \<C> e tn' = tm'"
          "(e = (Unop t uw) \<and> unop_t_num_agree op t)
           \<or> (e = (Testop t uv) \<and> is_int_t_num t)
           \<or> (e = (Cvtop t1 Convert t sx) \<and> convert_cond t1 t sx)
           \<or> (e = (Cvtop t1 Reinterpret t sx) \<and> ((t1 \<noteq> t) \<and> t_num_length t1 = t_num_length t \<and> sx = None))"
          "c_types_agree tm' tm"
          "tn' \<noteq> Bot"
          "tm' \<noteq> Bot"
 shows "\<exists>tn. c_types_agree tn' tn \<and> \<C> \<turnstile> [e] : (tn _> tm)"
proof -
  have "(e = (Cvtop t1 Convert t sx) \<Longrightarrow> convert_cond t1 t sx)"
    using assms(2)
    by simp
  have 1:"type_update tn' (to_ct_list [T_num t]) (Type [T_num (arity_1_result e)]) = tm'"
    using assms arity_1_result_def
    unfolding to_ct_list_def
    apply (simp del: convert_cond.simps)
    apply fastforce
    done
  have "\<C> \<turnstile> [e] : ([T_num t] _> [T_num (arity_1_result e)])"
    using assms(2) b_e_typing.intros(2,3,6,9,10)
    unfolding arity_1_result_def
    apply simp
    apply (metis (no_types, lifting) Wasm_Checker.check_unop assms(1,5) b_e.simps(1541,1543,1545) b_e_typing.reinterpret b_e_typing.testop convert)
    done
  thus ?thesis
    using b_e_check_single_type_not_bot_sound[OF 1 assms(4,5,3)]
    by fastforce
qed

lemma b_e_check_single_sound_binop_relop:
  assumes "check_single \<C> e tn' = tm'"
          "((e = Binop t iop \<and> binop_t_num_agree op t)
            \<or> (e = Relop t irop \<and> relop_t_num_agree irop t))"
          "c_types_agree tm' tm"
          "tn' \<noteq> Bot"
          "tm' \<noteq> Bot"
 shows "\<exists>tn. c_types_agree tn' tn \<and> \<C> \<turnstile> [e] : (tn _> tm)"
proof -
  have "type_update tn' (to_ct_list [T_num t,T_num t]) (Type [T_num (arity_2_result e)]) = tm'"
    using assms arity_2_result_def
    unfolding to_ct_list_def
    by auto
  moreover
  have "\<C> \<turnstile> [e] : ([T_num t,T_num t] _> [T_num (arity_2_result e)])"
    using assms(2) b_e_typing.intros(4,5,7,8)
    unfolding arity_2_result_def
    by (metis (no_types) assms(1,5) b_e.simps(1542,1544) b_e_typing.relop binop check_binop)
  ultimately
  show ?thesis
    using b_e_check_single_type_not_bot_sound[OF _ assms(4,5,3)]
    by fastforce
qed

lemma b_e_type_checker_sound:
  assumes "b_e_type_checker \<C> es (tn _> tm)"
  shows "\<C> \<turnstile> es : (tn _> tm)"
proof -
  fix e tn'
  have "b_e_type_checker \<C> es (tn _> tm) \<Longrightarrow>
          \<C> \<turnstile> es : (tn _> tm)"
  and "\<And>tm' tm.
       check \<C> es tn' = tm' \<Longrightarrow>
       c_types_agree tm' tm \<Longrightarrow>
         \<exists>tn. c_types_agree tn' tn \<and> \<C> \<turnstile> es : (tn _> tm)"
  and "\<And>tm' tm.
       check_single \<C> e tn' = tm' \<Longrightarrow>
       c_types_agree tm' tm \<Longrightarrow>
       tn' \<noteq> Bot \<Longrightarrow>
       tm' \<noteq> Bot \<Longrightarrow>
         \<exists>tn. c_types_agree tn' tn \<and> \<C> \<turnstile> [e] : (tn _> tm)"
  proof (induction rule: b_e_type_checker_check_check_single.induct)
    case (1 \<C> es tn' tm)
    thus ?case
      by simp
  next
    case (2 \<C> es' ts)
    show ?case
    proof (cases es')
      case Nil
      thus ?thesis
        using 2(5,6)
        by (simp add: b_e_type_empty)
    next
      case (Cons e es)
        thus ?thesis
        proof (cases ts)
        case (TopType x1)
        have check_expand:"check \<C> es (check_single \<C> e ts) = tm'"
          using 2(5,6) TopType Cons
          by simp
        obtain ts' where ts'_def:"check_single \<C> e ts = ts'"
          by blast
        obtain t_int where t_int_def:"\<C> \<turnstile> es : (t_int _> tm)"
                                     "c_types_agree ts' t_int"
          using 2(2)[OF Cons TopType check_expand 2(6)] ts'_def
          by blast
        obtain t_int' where "c_types_agree ts t_int'" "\<C> \<turnstile> [e] : (t_int' _> t_int)"
          using 2(1)[OF Cons _ ts'_def] TopType c_types_agree.simps(3) t_int_def(2)
          by blast
        thus ?thesis
          using t_int_def(1) b_e_type_comp_conc Cons
          by fastforce
      next
        case (Type x2)
        have check_expand:"check \<C> es (check_single \<C> e ts) = tm'"
          using 2(5,6) Type Cons
          by simp
        obtain ts' where ts'_def:"check_single \<C> e ts = ts'"
          by blast
        obtain t_int where t_int_def:"\<C> \<turnstile> es : (t_int _> tm)"
                                     "c_types_agree ts' t_int"
          using 2(4)[OF Cons Type check_expand 2(6)] ts'_def
          by blast
        obtain t_int' where "c_types_agree ts t_int'" "\<C> \<turnstile> [e] : (t_int' _> t_int)"
          using 2(3)[OF Cons _ ts'_def] Type c_types_agree.simps(3) t_int_def(2)
          by blast
        thus ?thesis
          using t_int_def(1) b_e_type_comp_conc Cons
          by fastforce
      next
        case Bot
        then show ?thesis
          using 2(5,6) Cons
          by auto
      qed
    qed
  next
    case (3 \<C> v ts)
    hence "type_update ts [] (Type [typeof v]) = tm'"
      by simp
    moreover
    have "\<C> \<turnstile> [C v] : ([] _> [typeof v])"
      using b_e_typing.intros(1)
      by blast
    ultimately
    show ?case
      using b_e_check_single_type_not_bot_sound[OF _ 3(3,4,2)]
      by (metis list.simps(8) to_ct_list_def)
  next
    case (4 \<C> t op ts)
    thus ?case
      using b_e_check_single_sound_unop_testop_cvtop
      by (simp split: if_splits)
  next
    case (5 \<C> t op ts)
    thus ?case
      using b_e_check_single_sound_binop_relop
      by (simp split: if_splits)
  next
    case (6 \<C> t op ts)
    thus ?case
      using b_e_check_single_sound_unop_testop_cvtop
      by (simp split: if_splits)
  next
    case (7 \<C> t op ts)
    thus ?case
      using b_e_check_single_sound_binop_relop
      by (simp split: if_splits)
  next
    case (8 \<C> op ts)
    thus ?case
      using b_e_check_single_type_not_bot_sound[OF _ 8(3,4,2)]
      apply (simp add: to_ct_list_def)
      apply (metis (no_types) b_e_typing.unop_vec list.simps(8,9))
      done
  next
    case (9 \<C> op ts)
    thus ?case
      using b_e_check_single_type_not_bot_sound[OF _ 9(3,4,2)]
      apply (simp add: to_ct_list_def split: if_splits)
      apply (metis (no_types) b_e_typing.binop_vec list.simps(8,9))
      done
  next
    case (10 \<C> op ts)
    thus ?case
      using b_e_check_single_type_not_bot_sound[OF _ 10(3,4,2)]
      apply (simp add: to_ct_list_def split: if_splits)
      apply (metis (no_types) b_e_typing.ternop_vec list.simps(8,9))
      done
  next
    case (11 \<C> op ts)
    thus ?case
      using b_e_check_single_type_not_bot_sound[OF _ 11(3,4,2)]
      apply (simp add: to_ct_list_def split: if_splits)
      apply (metis (no_types) b_e_typing.test_vec list.simps(8,9))
      done
  next
    case (12 \<C> op ts)
    thus ?case
      using b_e_check_single_type_not_bot_sound[OF _ 12(3,4,2)]
      apply (simp add: to_ct_list_def split: if_splits)
      apply (metis (no_types) b_e_typing.shift_vec list.simps(8,9))
      done
  next
    case (13 \<C> sv ts)
    thus ?case
      using b_e_check_single_type_not_bot_sound[OF _ 13(3,4,2)]
      apply (simp add: to_ct_list_def split: if_splits)
      apply (metis (no_types) b_e_typing.splat_vec list.simps(8,9))
      done
  next
    case (14 \<C> sv sx i ts)
    thus ?case
      using b_e_check_single_type_not_bot_sound[OF _ 14(3,4,2)]
      apply (simp add: to_ct_list_def split: if_splits)
      apply (metis (no_types) b_e_typing.extract_vec list.simps(8,9))
      done
  next
    case (15 \<C> sv i ts)
    thus ?case
      using b_e_check_single_type_not_bot_sound[OF _ 15(3,4,2)]
      apply (simp add: to_ct_list_def split: if_splits)
      apply (metis (no_types) b_e_typing.replace_vec list.simps(8,9))
      done
  next
    case (16 \<C> t1 t2 sx ts)
    thus ?case
      using b_e_check_single_sound_unop_testop_cvtop
      by (simp split: if_splits)
  next
    case (17 \<C> t1 t2 sx ts)
    thus ?case
      using b_e_check_single_sound_unop_testop_cvtop
      by (simp split: if_splits)
  next
    case (18 \<C> ts)
    thus ?case
      using b_e_typing.intros(16) c_types_agree_not_bot_exists
      by blast
  next
    case (19 \<C> ts)
    thus ?case
      using b_e_typing.intros(17,43)
      by fastforce
  next
    case (20 \<C> ts)
    thus ?case
    proof (cases ts)
      case (TopType x1)
      thus ?thesis
        proof (cases x1 rule: List.rev_cases)
          case Nil
          have "\<C> \<turnstile> [Drop] : (tm@[T_num T_i32] _> tm)"
            using b_e_typing.intros(18,43)
            by fastforce
          thus ?thesis
            using c_types_agree_top1 Nil TopType
            by fastforce
        next
          case (snoc ys y)
            hence temp1:"(consume (TopType (ys@[y])) [TAny]) = tm'"
              using 20 TopType type_update_empty
              by (metis check_single.simps(18))
            hence temp2:"c_types_agree (TopType ys) tm"
              using consume_top_geq[OF temp1] 20(2,3,4)
              by (metis Suc_leI add_diff_cancel_right' append_eq_conv_conj consume.simps(2)
                        ct_suffix_def length_Cons length_append list.size(3) trans_le_add2
                        zero_less_Suc)
            obtain t where "ct_list_compat [y] (to_ct_list [t])"
              using ct_list_compat_exists
              unfolding ct_list_compat_def to_ct_list_def list_all2_map2
              by (metis list_all2_Cons1 list_all2_Nil)
            hence "c_types_agree ts (tm@[t])"
              using temp2 ct_suffix_extend_ct_list_compat snoc TopType
              by (simp add: to_ct_list_def)
            thus ?thesis
              using b_e_typing.intros(18,43)
              by fastforce
        qed
    next
      case (Type x2)
      thus ?thesis
      proof (cases x2 rule: List.rev_cases)
        case Nil
        hence "(consume (Type []) [TAny]) = tm'"
          using 20 Type type_update_empty
          by fastforce
        thus ?thesis
          using 20(4) ct_list_compat_def ct_suffix_def to_ct_list_def
          by simp
      next
        case (snoc ys y)
            hence temp1:"(consume (Type (ys@[y])) [TAny]) = tm'"
              using 20 Type type_update_empty
              by (metis check_single.simps(18))
            hence temp2:"c_types_agree (Type ys) tm"
              using 20(2,3,4) ct_suffix_def
              by (simp, metis One_nat_def butlast_conv_take butlast_snoc c_types_agree.simps(1)
                              length_Cons list.size(3))
            obtain t where "ct_list_compat [TSome y] (to_ct_list [t])"
              using ct_list_compat_exists
              unfolding ct_list_compat_def to_ct_list_def list_all2_map2
              by (metis list_all2_Cons1 list_all2_Nil)
            hence "c_types_agree ts (tm@[t])"
              using temp2 ct_suffix_extend_ct_list_compat snoc Type
              by (simp add: ct_list_compat_def to_ct_list_def)
            thus ?thesis
              using b_e_typing.intros(18,43)
              by fastforce
      qed
    qed simp
  next
    case (21 \<C> ts)
    thus ?case
    proof (cases ts)
      case (TopType x1)
      consider
          (1) "length x1 = 0"
        | (2) "length x1 = 1"
        | (3) "length x1 = 2"
        | (4) "length x1 \<ge> 3"
        by linarith
      thus ?thesis
      proof (cases)
        case 1
        hence "tm' = TopType [TAny]"
          using TopType 21
          by simp
        then obtain t'' tm'' where tm_def:"tm = tm''@[t'']"
          using 21(2) ct_suffix_def
          by (simp, metis Nil_is_append_conv append_butlast_last_id checker_type.inject(1)
                          ct_prefixI ct_prefix_nil(2) produce.simps(1) produce_nil)
        have "\<C> \<turnstile> [Select] : ([t'',t'',T_num T_i32] _> [t''])"
          using b_e_typing.intros(19)
          by blast
        thus ?thesis
          using TopType 21 1 tm_def b_e_typing.intros(43) c_types_agree.simps(2) c_types_agree_top1
          by fastforce
      next
        case 2
        have "type_update_select (TopType x1) = tm'"
          using 21 TopType
          unfolding check_single.simps
          by simp
        hence x1_def:"ct_list_compat x1 [TSome (T_num T_i32)]" "tm' = TopType [TAny]"
          using type_update_select_length1[OF _ 2 21(4)]
          by simp_all
        then obtain t'' tm'' where tm_def:"tm = tm''@[t'']"
          using 21(2) ct_suffix_def
          by (metis Nil_is_append_conv append_butlast_last_id c_types_agree.simps(2) ct_prefixI
                    ct_prefix_nil(2) list.simps(8) to_ct_list_def)
        have "c_types_agree (TopType x1) ((tm''@[t'',t''])@[T_num T_i32])"
          using x1_def(1)
          by (metis c_types_agree_top2 list.simps(8,9) to_ct_list_def)
        thus ?thesis
          using TopType b_e_typing.intros(19,43) tm_def
          by auto
      next
        case 3
        have "type_update_select (TopType x1) = tm'"
          using 21 TopType
          unfolding check_single.simps
          by simp
        then obtain ct1 ct2 where x1_def:"x1 = [ct1, ct2]"
                                         "ct_compat ct2 (TSome (T_num T_i32))"
                                         "tm' = TopType [ct1]"
          using type_update_select_length2[OF _ 3 21(4)]
          by blast
        then obtain t'' tm'' where tm_def:"tm = tm''@[t'']"
                                          "ct_list_compat [ct1] [(TSome t'')]"
          using 21(2) c_types_agree_imp_ct_list_compat[of "[ct1]" tm]
          by (metis append_Nil2 append_butlast_last_id append_eq_append_conv_if append_eq_conv_conj
                    ct_list_compat_length diff_Suc_1 length_Cons length_butlast length_map
                    list.simps(8,9) list.size(3) nat.distinct(2) to_ct_list_def)
        hence "ct_list_compat x1 (to_ct_list [ t'', T_num T_i32])"
          using x1_def(1,2)
          unfolding ct_list_compat_def to_ct_list_def
          by fastforce
        hence "c_types_agree (TopType x1) ((tm''@[t''])@[t'',T_num T_i32])"
          using c_types_agree_top2
          by blast
        thus ?thesis
          using TopType b_e_typing.intros(19,43) tm_def
          by auto
      next
        case 4
        then obtain nat where nat_def:"length x1 = Suc (Suc (Suc nat))"
          by (metis add_eq_if diff_Suc_1 le_Suc_ex numeral_3_eq_3 nat.distinct(2))
        hence tm'_def:"type_update_select (TopType x1) = tm'"
          using 21 TopType
          by simp
        then obtain tm_int where "(select_return_top x1
                                    (x1 ! (length x1 - 2))
                                    (x1 ! (length x1 - 3))) = tm_int"
                                 "tm_int \<noteq> Bot"
          using nat_def 21(4)
          unfolding type_update_select.simps
          by fastforce
        then obtain x2 where x2_def:"(select_return_top x1
                                       (x1 ! (length x1 - 2))
                                       (x1 ! (length x1 - 3))) = TopType x2"
          using select_return_top_exists
          by fastforce
        have "ct_suffix x1 [TAny, TAny, TSome (T_num T_i32)] \<or> ct_suffix [TAny, TAny, TSome (T_num T_i32)] x1"
          using tm'_def nat_def 21(4)
          by (simp, metis (full_types) produce.simps(6))
        hence tm'_eq:"tm' = TopType x2"
          using tm'_def nat_def 21(4) x2_def
          by force
        then obtain cts' ct1 ct2 ct3 where cts'_def:"x1 = cts'@[ct1, ct2, ct3]"
                                                    "ct_compat ct3 (TSome (T_num T_i32))"
          using type_update_select_length3 tm'_def 4
          by blast
        then obtain c' cm' where tm_def:"tm = cm'@[c']"
                                        "ct_suffix cts' (to_ct_list cm')"
                                        "ct_compat (x1 ! (length x1 - 2)) (TSome c')"
                                        "ct_compat (x1 ! (length x1 - 3)) (TSome c')"
          using select_return_top_ct_compat[OF x2_def 4] tm'_eq 4 21(2)
          by fastforce
        then obtain as bs where cm'_def:"cm' = as@bs"
                                        "ct_list_compat (to_ct_list bs) cts'"
          using ct_list_compat_cons_ct_list1 ct_list_compat_ts_conv_eq
          by (metis ct_suffix_def to_ct_list_append(2))
        hence "ct_compat ct1 (TSome c')"
              "ct_compat ct2 (TSome c')"
          using cts'_def tm_def
          apply simp_all
          apply (metis append.assoc append_Cons append_Nil length_append_singleton nth_append_length)
          done
        hence "c_types_agree ts (cm'@[c',c',T_num T_i32])"
          using c_types_agree_top2[of _ _ as] cm'_def(1) TopType
                ct_list_compat_concat[OF ct_list_compat_commute[OF cm'_def(2)]] cts'_def
          unfolding to_ct_list_def ct_list_compat_def
          by fastforce
        thus ?thesis
          using b_e_typing.intros(19,43) tm_def
          by auto
      qed
    next
      (* TODO: refactor *)
      case (Type x2)
      hence x2_cond:"(length x2 \<ge> 3 \<and> (x2!(length x2-2)) = (x2!(length x2-3)))"
        using 21
        by (simp, meson)
      hence tm'_def:"consume (Type x2) [TAny, TSome (T_num T_i32)] = tm'"
        using 21 Type
        by simp
      obtain ts' ts'' where cts_def:"x2 = ts'@ ts''" "length ts'' = 3"
        using x2_cond
        by (metis append_take_drop_id diff_diff_cancel length_drop)
      then obtain t1 ts''2 where "ts'' = t1#ts''2" "length ts''2 = Suc (Suc 0)"
        using List.length_Suc_conv[of ts' "Suc (Suc 0)"]
        by (metis length_Suc_conv numeral_3_eq_3)
      then obtain t2 t3 where "ts'' = [t1,t2,t3]"
        using List.length_Suc_conv[of ts''2 "Suc 0"]
        by (metis length_0_conv length_Suc_conv)
      hence cts_def2:"x2 = ts'@ [t1,t2,t3]"
        using cts_def
        by simp
      have ts'_suffix:"ct_suffix [TAny, TSome (T_num T_i32)] (to_ct_list (ts' @ [t1, t2, t3]))"
        using tm'_def 21(4)
        by (simp, metis cts_def2)
      hence tm'_def:"tm' = Type (ts'@[t1])"
        using tm'_def 21(4) cts_def2
        by simp
      obtain as bs where "(to_ct_list (ts' @ [t1])) @ (to_ct_list ([t2, t3])) = as@bs"
                         "ct_list_compat bs [TAny, TSome (T_num T_i32)]"
        using ts'_suffix
        unfolding ct_suffix_def to_ct_list_def
        by fastforce
      hence "t3 = T_num T_i32"
        unfolding to_ct_list_def ct_list_compat_def
        by (metis (no_types, lifting) Nil_is_map_conv append_eq_append_conv ct_compat.simps(1)
                  length_Cons list.sel(1,3) list.simps(9) list_all2_Cons2 list_all2_lengthD)
      moreover
      have "t1 = t2"
        using x2_cond cts_def2
        by (simp, metis append.left_neutral append_Cons append_assoc length_append_singleton
                        nth_append_length)
      ultimately
      have "c_types_agree (Type x2) ((ts'@[t1,t1])@[T_num T_i32])"
        using cts_def2
        by simp
      thus ?thesis
        using b_e_typing.intros(19,43) Type tm'_def 21(2)
        by fastforce
    qed simp
  next
    case (22 \<C> tb es ts)
    show ?case
      using 22 b_e_typing.intros(20)[OF _ 22(1)] b_e_check_single_type_not_bot_sound[OF _ 22(4,5,3)]
      by (simp split: tf.splits if_splits checker_type.splits option.splits)
  next
    case (23 \<C> tb es ts)
    show ?case
      using 23 b_e_typing.intros(21)[OF _ 23(1)] b_e_check_single_type_not_bot_sound[OF _ 23(4,5,3)]
      by (simp split: tf.splits if_splits checker_type.splits option.splits)
  next
    case (24 \<C> tb es1 es2 ts)
    show ?case
      using 24 b_e_typing.intros(22)[OF _ 24(1,2)] b_e_check_single_type_not_bot_sound[OF _ 24(5,6,4)]
      by (simp split: tf.splits if_splits checker_type.splits option.splits)
  next
    case (25 \<C> i ts)
    hence "type_update ts (to_ct_list ((label \<C>)!i)) (TopType []) = tm'"
      by auto
    moreover
    have "i < length (label \<C>)"
      using 25
      by (simp, meson)
    ultimately
    show ?case
      using b_e_check_single_top_not_bot_sound[OF _ 25(3,4)]
            b_e_typing.intros(23)
      by (metis suffix_def)
  next
    case (26 \<C> i ts)
    hence "type_update ts (to_ct_list ((label \<C>)!i @ [T_num T_i32])) (Type ((label \<C>)!i)) = tm'"
      by auto
    moreover
    have "i < length (label \<C>)"
      using 26
      by (simp, meson)
    hence "\<C> \<turnstile> [Br_if i] : ((label \<C>)!i @ [T_num T_i32] _> (label \<C>)!i)"
      using b_e_typing.intros(24)
      by fastforce
    ultimately
    show ?case
      using b_e_check_single_type_not_bot_sound[OF _ 26(3,4,2)]
      by fastforce
  next
    case (27 \<C> "is" i ts)
    then obtain tls where tls_def:"(same_lab (is@[i]) (label \<C>)) = Some tls"
      by fastforce
    hence "type_update ts (to_ct_list (tls @ [T_num T_i32])) (TopType []) = tm'"
      using 27
      by simp
    thus ?case
      using b_e_check_single_top_not_bot_sound[OF _ 27(3,4)]
            b_e_typing.intros(25)[OF same_lab_conv_list_all[OF tls_def]]
      by (metis suffix_def)
  next
    case (28 \<C> ts)
    thus ?case
      using b_e_typing.return
      unfolding to_ct_list_def
      apply (simp split: if_splits option.splits)
      apply (metis b_e_check_single_top_not_bot_sound suffixE type_update.elims)
      done
  next
    case (29 \<C> i ts)
    thus ?case
      using b_e_check_single_type_not_bot_sound b_e_typing.call
      unfolding to_ct_list_def
      apply (simp split: if_splits tf.splits)
      apply (metis to_ct_list_def)
      done
  next
    case (30 \<C> i ts)
    thus ?case
      using b_e_check_single_type_not_bot_sound b_e_typing.call_indirect
      unfolding to_ct_list_def
      apply (simp split: if_splits tf.splits)
      apply (metis to_ct_list_def)
      done
  next
    case (31 \<C> i ts)
    thus ?case
      using b_e_check_single_type_not_bot_sound b_e_typing.get_local
      unfolding to_ct_list_def
      apply (simp split: if_splits)
      apply (metis list.simps(8))
      done
  next
    case (32 \<C> i ts)
    thus ?case
      using b_e_check_single_type_not_bot_sound[OF _ 32(3,4,2)]
      unfolding to_ct_list_def
      apply (simp split: if_splits)
      apply (metis b_e_typing.set_local list.simps(8,9))
      done
  next
    case (33 \<C> i ts)
    thus ?case
      using b_e_check_single_type_not_bot_sound b_e_typing.tee_local
      unfolding to_ct_list_def
      apply (simp split: if_splits)
      apply (metis (no_types) list.simps(8,9))
      done
  next
    case (34 \<C> i ts)
    thus ?case
      using b_e_check_single_type_not_bot_sound b_e_typing.get_global
      unfolding to_ct_list_def
      apply (simp split: if_splits)
      apply (metis (no_types) list.simps(8))
      done
  next
    case (35 \<C> i ts)
    thus ?case
      using b_e_check_single_type_not_bot_sound b_e_typing.set_global
      unfolding to_ct_list_def
      apply (simp split: if_splits)
      apply (metis (no_types) list.simps(8,9))
      done
  next
    case (36 \<C> t tp_sx a off ts)
    thus ?case
      using b_e_check_single_type_not_bot_sound[OF _ 36(3,4,2)]
      unfolding to_ct_list_def
      apply (simp split: if_splits)
      apply (metis One_nat_def b_e_typing.load list.simps(8,9))
      done
  next
    case (37 \<C> t tp a off ts)
    thus ?case
      using b_e_check_single_type_not_bot_sound[OF _ 37(3,4,2)]
      unfolding to_ct_list_def
      apply (simp split: if_splits)
      apply (metis One_nat_def b_e_typing.store list.simps(8,9))
      done
  next
  case (38 \<C> lv a off ts)
    thus ?case
      using b_e_check_single_type_not_bot_sound[OF _ 38(3,4,2)]
      unfolding to_ct_list_def
      apply (simp split: if_splits)
      apply (metis One_nat_def b_e_typing.load_vec list.simps(8,9))
      done
  next
  case (39 \<C> svi i a off ts)
    thus ?case
      using b_e_check_single_type_not_bot_sound[OF _ 39(3,4,2)]
      unfolding to_ct_list_def
      apply (simp split: if_splits)
      apply (metis One_nat_def b_e_typing.load_lane_vec list.simps(8,9))
      done
  next
    case (40 \<C> sv a off ts)
    thus ?case
      using b_e_check_single_type_not_bot_sound[OF _ 40(3,4,2)]
      unfolding to_ct_list_def
      apply (simp split: if_splits)
      apply (metis One_nat_def b_e_typing.store_vec list.simps(8,9))
      done
  next
    case (41 \<C> ts)
    thus ?case
      using b_e_check_single_type_not_bot_sound b_e_typing.current_memory
      unfolding to_ct_list_def
      apply (simp split: if_splits)
      apply (metis Nil_is_map_conv)
      done
  next
    case (42 \<C> ts)
    thus ?case
      using b_e_check_single_type_not_bot_sound[OF _ 42(3,4,2)]
      unfolding to_ct_list_def
      apply (simp split: if_splits)
      apply (metis One_nat_def b_e_typing.grow_memory list.simps(8,9))
      done
  qed
  thus ?thesis
    using assms
    by simp
qed

subsection {* Completeness *}

lemma check_single_imp:
  assumes "check_single \<C> e ctn = ctm"
          "ctm \<noteq> Bot"
  shows "check_single \<C> e = id
         \<or> check_single \<C> e = (\<lambda>ctn. type_update_select ctn)
         \<or> (\<exists>cons prods. (check_single \<C> e = (\<lambda>ctn. type_update ctn cons prods)))"
  using assms
  apply (cases rule: check_single.cases[of "(\<C>, e, ctn)"])
  apply (fastforce split: if_splits option.splits tf.splits)+
  done

lemma check_equiv_fold:
  "check \<C> es ts = foldl (\<lambda> ts e. (case ts of Bot \<Rightarrow> Bot | _ \<Rightarrow> check_single \<C> e ts)) ts es"
proof (induction es arbitrary: ts)
  case Nil
  thus ?case
    by simp
next
  case (Cons e es)
  obtain ts' where ts'_def:"check \<C> (e # es) ts = ts'"
    by blast
  show ?case
  proof (cases "ts = Bot")
    case True
    thus ?thesis
      using ts'_def
      by (induction es, simp_all)
  next
    case False
    thus ?thesis
      using ts'_def Cons
      by (cases ts, simp_all)
  qed
qed

lemma check_neq_bot_snoc:
  assumes "check \<C> (es@[e]) ts \<noteq> Bot"
  shows "check \<C> es ts \<noteq> Bot"
  using assms
proof (induction es arbitrary: ts)
  case Nil
  thus ?case
    by (cases ts, simp_all)
next
  case (Cons a es)
  thus ?case
    by (cases ts, simp_all)
qed

lemma check_unfold_snoc:
  assumes "check \<C> es ts \<noteq> Bot"
  shows "check \<C> (es@[e]) ts = check_single \<C> e (check \<C> es ts)"
proof -
  obtain f where f_def:"f = (\<lambda> e ts. (case ts of Bot \<Rightarrow> Bot | _ \<Rightarrow> check_single \<C> e ts))"
    by blast
  have f_simp:"\<And>ts. ts \<noteq> Bot \<Longrightarrow> (f e ts = check_single \<C> e ts)"
  proof -
    fix ts
    show "ts \<noteq> Bot \<Longrightarrow> (f e ts = check_single \<C> e ts)"
      using f_def
      by (cases ts, simp_all)
  qed
  have "check \<C> (es@[e]) ts = foldl (\<lambda> ts e. (case ts of Bot \<Rightarrow> Bot | _ \<Rightarrow> check_single \<C> e ts)) ts (es@[e])"
    using check_equiv_fold
    by simp
  also
  have "... = foldr (\<lambda> e ts. (case ts of Bot \<Rightarrow> Bot | _ \<Rightarrow> check_single \<C> e ts)) (rev (es@[e])) ts"
    using foldl_conv_foldr
    by fastforce
  also
  have "... = f e (foldr (\<lambda> e ts. (case ts of Bot \<Rightarrow> Bot | _ \<Rightarrow> check_single \<C> e ts)) (rev es) ts)"
    using f_def
    by simp
  also
  have "... = f e (check \<C> es ts)"
    using foldr_conv_foldl[of _ "(rev es)" ts] rev_rev_ident[of es] check_equiv_fold
    by simp
  also
  have "... = check_single \<C> e (check \<C> es ts)"
    using assms f_simp
    by simp
  finally
  show ?thesis .
qed

lemma check_single_imp_weakening:
  assumes "check_single \<C> e (Type t1s) = ctm"
          "ctm \<noteq> Bot"
          "c_types_agree ctn t1s"
          "c_types_agree ctm t2s"
  shows "\<exists>ctm'. check_single \<C> e ctn = ctm' \<and> c_types_agree ctm' t2s"
proof -
  consider (1) "check_single \<C> e = id" 
         | (2) "check_single \<C> e = (\<lambda>ctn. type_update_select ctn)"
         | (3) "(\<exists>cons prods. (check_single \<C> e = (\<lambda>ctn. type_update ctn cons prods)))"
    using check_single_imp assms
    by blast
  thus ?thesis
  proof (cases)
    case 1
    thus ?thesis
      using assms(1,3,4)
      by fastforce
  next
    (* TODO: better proof *)
    case 2
    note outer_2 = 2
    hence t1s_cond:"(length t1s \<ge> 3 \<and> (t1s!(length t1s-2)) = (t1s!(length t1s-3)))"
      using assms(1,2)
      by (simp, meson)
    hence ctm_def:"ctm = consume (Type t1s) [TAny, TSome (T_num T_i32)]"
      using assms(1,2) 2
      by simp
    then obtain c_t where c_t_def:"ctm = Type c_t"
      using assms(2)
      by (meson consume.simps(1))
    hence t2s_eq:"t2s = c_t"
      using assms(4)
      by simp
    hence t2s_len:"length t2s > 0"
      using t1s_cond ctm_def c_t_def assms(2)
      by (metis Suc_leI Suc_n_not_le_n checker_type.inject(2) consume.simps(1)
                diff_is_0_eq dual_order.trans length_0_conv length_Cons length_greater_0_conv
                nat.simps(3) numeral_3_eq_3 take_eq_Nil)
    have t1s_suffix_full:"ct_suffix [TAny, TSome (T_num T_i32)] (to_ct_list t1s)"
      using assms(2) ctm_def ct_suffix_less
      by (metis consume.simps(1))
    hence t1s_suffix:"ct_suffix [TSome (T_num T_i32)] (to_ct_list t1s)"
      using assms(2) ctm_def ct_suffix_less
      by (metis append_butlast_last_id last.simps list.distinct(1))
    obtain t t1s' where t1s_suffix2:"t1s = t1s'@[t,t,(T_num T_i32)]"
      using type_update_select_type_length3 assms(1) c_t_def outer_2
      by fastforce
    hence t2s_def:"t2s = t1s'@[t]"
      using ctm_def c_t_def t2s_eq t1s_suffix assms(2) t1s_suffix_full
      by simp
    show ?thesis
      using assms(1,3,4)
    proof (cases ctn)
      case (TopType x1)
      consider
          (1) "length x1 = 0"
        | (2) "length x1 = 1"
        | (3) "length x1 = 2"
        | (4) "length x1 \<ge> 3"
        by linarith
      thus ?thesis
      proof (cases)
        case 1
        hence "check_single \<C> e ctn = TopType [TAny]"
          using 2 TopType
          by simp
        thus ?thesis
          using ct_suffix_singleton to_ct_list_def t2s_len
          by auto
      next
        case 2
        hence "ct_suffix [TSome (T_num T_i32)] x1"
          using assms(3) TopType ct_suffix_imp_ct_list_compat ct_suffix_shared t1s_suffix
          by (metis One_nat_def append_Nil c_types_agree.simps(2) ct_list_compat_commute ct_suffix_def
                    diff_self_eq_0 drop_0 length_Cons list.size(3))
        hence "check_single \<C> e ctn = TopType [TAny]"
          using outer_2 TopType 2
          by simp
        thus ?thesis
          using t2s_len ct_suffix_singleton
          by (simp add: to_ct_list_def)
      next
        case 3
        have "ct_list_compat (to_ct_list t1s) (to_ct_list (t1s' @ [t, t, (T_num T_i32)]))"
          using t1s_suffix2
          by (simp add: ct_list_compat_ts_conv_eq)
        hence temp1:"to_ct_list t1s = (to_ct_list (t1s' @ [t])) @ (to_ct_list [t, (T_num T_i32)])"
          using t1s_suffix2 to_ct_list_def
          by simp
        hence "ct_suffix (to_ct_list [t, T_num T_i32]) (to_ct_list t1s)"
          using ct_suffix_def[of "(to_ct_list [t, T_num T_i32])" "(to_ct_list t1s)"]
          by (simp add: ct_suffix_cons_it)
        hence "ct_suffix (to_ct_list [t, T_num T_i32]) x1"
          using assms(3) TopType 3
          by (simp, metis temp1 append_Nil ct_suffix_cons2 ct_suffix_def length_Cons length_map
                          list.size(3) numeral_2_eq_2 to_ct_list_def)
        hence temp3:"ct_list_compat (to_ct_list [t, T_num T_i32]) x1"
          using 3 ct_suffix_imp_ct_list_compat
          unfolding to_ct_list_def
          by (metis Suc_leI ct_list_compat_commute diff_is_0_eq drop_0 length_Cons length_map lessI
                    list.size(3) numeral_2_eq_2)
        hence temp4:"ct_suffix [TSome (T_num T_i32)] x1" 
          using ct_suffix_less[of "[TSome t]" "[TSome (T_num T_i32)]" x1]
                ct_suffix_extend_ct_list_compat[of "[]" "[]"] ct_suffix_nil
          unfolding to_ct_list_def
          by fastforce
        hence "ct_suffix (take 1 x1) (to_ct_list [t])"
          using temp3 ct_suffix_nil ct_list_compat_commute ct_suffix_extend_ct_list_compat[of "[]" "[]" "(take 1 x1)" "(to_ct_list [t])"]
          unfolding to_ct_list_def
          by (simp, metis butlast.simps(2) butlast_conv_take ct_list_compat_take diff_Suc_1 length_Cons
                          list.distinct(1) list.size(3))
        thus ?thesis
          using TopType 2 3 ct_suffix_nil temp3 temp4 t2s_def to_ct_list_def
          apply (simp, safe)
          apply (metis append.assoc ct_suffix_def)
          done
      next
        case 4
        then obtain nat where nat_def:"length x1 = Suc (Suc (Suc nat))"
          by (metis add_eq_if diff_Suc_1 le_Suc_ex numeral_3_eq_3 nat.distinct(2))
        obtain x1' x x' x'' where x1_split:"x1 = x1'@[x,x',x'']"
        proof -
          assume local_assms:"(\<And>x1' x x' x''. x1 = x1' @ [x, x', x''] \<Longrightarrow> thesis)"
          obtain x1' x1'' where tn_split:"x1 = x1'@x1''"
                               "length x1'' = 3"
            using 4
            by (metis append_take_drop_id diff_diff_cancel length_drop)
          then obtain x x1''2 where "x1'' = x#x1''2" "length x1''2 = Suc (Suc 0)"
            by (metis length_Suc_conv numeral_3_eq_3)
          then obtain x' x'' where tn''_def:"x1''= [x,x',x'']"
            using List.length_Suc_conv[of x1''2 "Suc 0"]
            by (metis length_0_conv length_Suc_conv)
          thus ?thesis
            using tn_split local_assms
            by simp
        qed
        hence a:"ct_suffix (x1'@[x,x',x'']) (to_ct_list (t1s' @ [t, t, T_num T_i32]))"
          using t1s_suffix2 assms(3) TopType
          by simp
        hence b:"ct_suffix (x1'@[x,x']) (to_ct_list (t1s' @ [t, t])) \<and> (ct_compat x'' (TSome (T_num T_i32)))"
          using to_ct_list_def ct_suffix_unfold_one[of "(x1'@[x,x'])" "x''" "to_ct_list (t1s' @ [t, t])"]
          by fastforce
        hence c:"ct_suffix (x1'@[x]) (to_ct_list (t1s' @ [t])) \<and> (ct_compat x' (TSome t))"
          using to_ct_list_def ct_suffix_unfold_one[of "(x1'@[x])" "x'" "to_ct_list (t1s' @ [t])"]
          by fastforce
        hence d:"ct_suffix x1' (to_ct_list t1s') \<and> (ct_compat x (TSome t))"
          using to_ct_list_def ct_suffix_unfold_one[of "(x1')" "x" "to_ct_list (t1s')"]
          by fastforce
        have "(take (length x1 - 3) x1) = x1'"
          using x1_split
          by simp
        have x'_ind:"(x1!(length x1-2)) = x'"
          using x1_split List.nth_append_length[of "x1' @ [x]"]
          by simp
        have x_ind:"(x1!(length x1-3)) = x"
          using x1_split
          by simp
        have "ct_suffix [TSome (T_num T_i32)] x1"
          using b x1_split ct_suffix_def ct_list_compat_def ct_suffixI[of x1 "x1' @ [x, x']"]
          by simp
        hence "check_single \<C> e (TopType x1) = (select_return_top x1 (x1!(length x1-2)) (x1!(length x1-3)))"
          using type_update_select_conv_select_return_top[OF _ 4]
          unfolding 2
          by blast
        moreover
        have "... = (TopType (x1'@[x])) \<or> ... = (TopType (x1'@[x']))"
          apply (cases x; cases x')
          using x1_split 4 nat_def 2 x_ind x'_ind c d
          by simp_all
        moreover
        have "ct_suffix (x1'@[x]) (to_ct_list t2s)"
          by (simp add: c t2s_def)
        moreover
        have "ct_suffix (x1'@[x']) (to_ct_list t2s)"
          using ct_suffix_unfold_one[symmetric, of x' "(TSome t)" x1' "(to_ct_list t1s')"] c d
                t2s_def
          unfolding to_ct_list_def
          by fastforce
        ultimately
        show ?thesis
          using TopType
          by auto
      qed
    qed simp_all
  next
    case 3
    then obtain cons prods where c_s_def:"check_single \<C> e = (\<lambda>ctn. type_update ctn cons prods)"
      by blast
    hence ctm_def:"ctm = type_update (Type t1s) cons prods"
      using assms(1)
      by fastforce
    hence cons_suffix:"ct_suffix cons (to_ct_list t1s)"
      using assms
      by (simp, metis (full_types) produce.simps(6))
    hence t_int_def:"consume (Type t1s) cons = (Type (take (length t1s - length cons) t1s))"
      using ctm_def
      by simp
    hence ctm_def2:"ctm = produce (Type (take (length t1s - length cons) t1s)) prods"
      using ctm_def
      by simp
    show ?thesis
    proof (cases ctn)
      case (TopType x1)
      hence "ct_suffix x1 (to_ct_list t1s)"
        using assms(3)
        by simp
      thus ?thesis
        using assms(2) ctm_def2
      proof (cases prods)
        case (TopType x1)
        thus ?thesis
          using consume_c_types_agree[OF t_int_def assms(3)] ctm_def2 assms(4) c_s_def
          by (metis c_types_agree.elims(2) produce.simps(3,4) type_update.simps)
      next
        case (Type x2)
        hence ctm_def3:"ctm = Type ((take (length t1s - length cons) t1s)@ x2)"
          using ctm_def2
          by simp
        have "ct_suffix x1 cons \<or> ct_suffix cons x1"
          using ct_suffix_shared assms(3) TopType cons_suffix
          by auto
        thus ?thesis
        proof (rule disjE)
          assume "ct_suffix x1 cons"
          hence "consume (TopType x1) cons = TopType []"
            by (simp add: ct_suffix_length)
          hence "check_single \<C> e ctn = TopType (to_ct_list x2)"
            using c_s_def TopType Type
            by simp
          thus ?thesis
            using TopType ctm_def3 assms(4) c_types_agree_top2 ct_list_compat_refl
            by auto
        next
          assume "ct_suffix cons x1"
          hence 4:"consume (TopType x1) cons = TopType (take (length x1 - length cons ) x1)"
            by (simp add: ct_suffix_length)
          hence 3:"check_single \<C> e ctn = TopType ((take (length x1 - length cons ) x1) @ to_ct_list x2)"
            using c_s_def TopType Type
            by simp
          have "((take (length t1s - length cons ) t1s) @  x2) = t2s"
            using assms(4) ctm_def3
            by simp
          have "c_types_agree (TopType (take (length x1 - length cons ) x1)) (take (length t1s - length cons) t1s)"
            using consume_c_types_agree[OF t_int_def assms(3)] 4 TopType
            by simp
          hence "c_types_agree (TopType (take (length x1 - length cons ) x1 @ to_ct_list x2)) (take (length t1s - length cons) t1s @ x2)"
            unfolding c_types_agree.simps to_ct_list_def
            by (simp add: ct_suffix_cons2 ct_suffix_cons_it ct_suffix_extend_ct_list_compat)
          thus ?thesis
            using ctm_def3 assms 3
            by simp
        qed
      qed simp
    next
      case (Type x2)
      thus ?thesis
        using assms
        by simp
    next
      case Bot
      thus ?thesis
        using assms
        by simp
    qed
  qed
qed

lemma b_e_type_checker_compose:
  assumes "b_e_type_checker \<C> es (t1s _> t2s)"
          "b_e_type_checker \<C> [e] (t2s _> t3s)"
  shows "b_e_type_checker \<C> (es @ [e]) (t1s _> t3s)"
proof -
  have "c_types_agree (check_single \<C> e (Type t2s)) t3s"
    using assms(2)
    by simp
  then obtain ctm where ctm_def:"check_single \<C> e (Type t2s) = ctm"
                                "c_types_agree ctm t3s"
                                "ctm \<noteq> Bot"
    by fastforce
  have "c_types_agree (check \<C> es (Type t1s)) t2s"
    using assms(1)
    by simp
  then obtain ctn where ctn_def:"check \<C> es (Type t1s) = ctn"
                                "c_types_agree ctn t2s"
                                "ctn \<noteq> Bot"
    by fastforce
  thus ?thesis
    using check_single_imp_weakening[OF ctm_def(1,3) ctn_def(2) ctm_def(2)]
          check_unfold_snoc[of \<C> es "(Type t1s)" e]
    by simp
qed

lemma b_e_check_single_type_type:
  assumes "check_single \<C> e xs = (Type tm)"
  shows "\<exists>tn. xs = (Type tn)"
proof -
  consider (1) "check_single \<C> e = id" 
         | (2) "check_single \<C> e = (\<lambda>ctn. type_update_select ctn)"
         | (3) "(\<exists>cons prods. (check_single \<C> e = (\<lambda>ctn. type_update ctn cons prods)))"
    using check_single_imp assms
    by blast
  thus ?thesis
  proof (cases)
    case 1
    thus ?thesis
      using assms
      by simp
  next
    case 2
    note outer_2 = 2
    thus ?thesis
      using assms
    proof (cases xs)
      case (TopType x1)
      consider
          (1) "length x1 = 0"
        | (2) "length x1 = Suc 0"
        | (3) "length x1 = Suc (Suc 0)"
        | (4) "length x1 \<ge> 3"
        by linarith
      thus ?thesis
      proof cases
        case 1
        thus ?thesis
          using assms 2 TopType
          by simp
      next
        case 2
        thus ?thesis
          using assms outer_2 TopType produce_type_type
          by fastforce
      next
        case 3
        thus ?thesis
          using assms 2 TopType
          by (simp, metis checker_type.distinct(1) checker_type.distinct(5))
      next
        case 4
        then obtain nat where nat_def:"length x1 = Suc (Suc (Suc nat))"
          by (metis add_eq_if diff_Suc_1 le_Suc_ex numeral_3_eq_3 nat.distinct(2))
        thus ?thesis
          using assms 2 TopType
        proof -
          {
            assume a1: "produce (if ct_suffix [TAny, TAny, TSome (T_num T_i32)] x1 then TopType (take (length x1 - length [TAny, TAny, TSome (T_num T_i32)]) x1) else if ct_suffix x1 [TAny, TAny, TSome (T_num T_i32)] then TopType [] else Bot) (select_return_top x1 (x1 ! Suc nat) (x1 ! nat)) = Type tm"
            obtain tts :: "checker_type \<Rightarrow> t list" where
              f2: "\<forall>c. (\<forall>ca ts. produce c ca \<noteq> Type ts) \<or> c = Type (tts c)"
              using produce_type_type by moura
            then have f3: "\<And>ts. \<not> ct_suffix [TAny, TAny, TSome (T_num T_i32)] x1 \<or> Type tm \<noteq> Type ts"
              using a1 by fastforce
            then have "\<And>ts. \<not> ct_suffix x1 [TAny, TAny, TSome (T_num T_i32)] \<or> Type tm \<noteq> Type ts"
              using f2 a1 by fastforce
            then have False
              using f3 a1 by fastforce
          }
          thus ?thesis
            using assms 2 TopType nat_def
            by simp
        qed
      qed
    qed simp_all
  next
    case 3
    then obtain cons prods where check_def:"check_single \<C> e = (\<lambda>ctn. type_update ctn cons prods)"
      by blast
    hence "produce (consume xs cons) prods = (Type tm)"
      using assms(1)
      by simp
    thus ?thesis
      using assms check_def consume_type_type produce_type_type
      by blast
  qed
qed

lemma b_e_check_single_weaken_type:
  assumes "check_single \<C> e (Type tn) = (Type tm)"
  shows "check_single \<C> e (Type (ts@tn)) = Type (ts@tm)"
proof -
  consider (1) "check_single \<C> e = id" 
         | (2) "check_single \<C> e = (\<lambda>ctn. type_update_select ctn)"
         | (3) "(\<exists>cons prods. (check_single \<C> e = (\<lambda>ctn. type_update ctn cons prods)))"
    using check_single_imp assms
    by blast
  thus ?thesis
  proof (cases)
    case 1
    thus ?thesis
      using assms(1)
      by simp
  next
    case 2
    hence cond:"(length tn \<ge> 3 \<and> (tn!(length tn-2)) = (tn!(length tn-3)))"
      using assms
      by (simp, metis checker_type.distinct(5))
    hence "consume (Type tn) [TAny, TSome (T_num T_i32)] = (Type tm)"
      using assms 2
      by simp
    hence "consume (Type (ts@tn)) [TAny, TSome (T_num T_i32)] = (Type (ts@tm))"
      using consume_weaken_type
      by blast
    moreover
    have "(length (ts@tn) \<ge> 3 \<and> ((ts@tn)!(length (ts@tn)-2)) = ((ts@tn)!(length (ts@tn)-3)))"
      using cond
      by (simp, metis add.commute add_leE nth_append_length_plus numeral_Bit1 numeral_One
                      one_add_one ordered_cancel_comm_monoid_diff_class.diff_add_assoc2)
    ultimately
    show ?thesis
      using 2
      by simp
  next
    case 3
    then obtain cons prods where check_def:"check_single \<C> e = (\<lambda>ctn. type_update ctn cons prods)"
      by blast
    hence "produce (consume (Type tn) cons) prods = (Type tm)"
      using assms(1)
      by simp
    then obtain t_int where t_int_def:"consume (Type tn) cons = (Type t_int)"
      by (metis consume.simps(1) produce.simps(6))
    thus ?thesis
      using assms(1) check_def
            consume_weaken_type[OF t_int_def, of ts]
            produce_weaken_type[of t_int prods tm ts]
      by simp
  qed
qed

lemma b_e_check_single_weaken_top:
  assumes "check_single \<C> e (Type tn) = TopType tm"
  shows "check_single \<C> e (Type (ts@tn)) = TopType tm"
proof -
  consider (1) "check_single \<C> e = id" 
         | (2) "check_single \<C> e = (\<lambda>ctn. type_update_select ctn)"
         | (3) "(\<exists>cons prods. (check_single \<C> e = (\<lambda>ctn. type_update ctn cons prods)))"
    using check_single_imp assms
    by blast
  thus ?thesis
  proof (cases)
    case 1
    thus ?thesis
      using assms
      by simp
  next
    case 2
    thus ?thesis
      using assms
      by (simp, metis checker_type.distinct(1) checker_type.distinct(3) consume.simps(1))
  next
    case 3
    then obtain cons prods where check_def:"check_single \<C> e = (\<lambda>ctn. type_update ctn cons prods)"
      by blast
    hence "produce (consume (Type tn) cons) prods = (TopType tm)"
      using assms(1)
      by simp
    moreover
    then obtain t_int where t_int_def:"consume (Type tn) cons = (Type t_int)"
      by (metis checker_type.distinct(3) consume.simps(1) produce.simps(6))
    ultimately
    show ?thesis
      using check_def consume_weaken_type
      by (cases prods, auto)
  qed
qed

lemma b_e_check_weaken_type:
  assumes "check \<C> es (Type tn) = (Type tm)"
  shows "check \<C> es (Type (ts@tn)) = (Type (ts@tm))"
  using assms
proof (induction es arbitrary: tn tm rule: List.rev_induct)
  case Nil
  thus ?case
    by simp
next
  case (snoc e es)
  hence "check_single \<C> e (check \<C> es (Type tn)) = Type tm"
    using check_unfold_snoc[OF check_neq_bot_snoc]
    by (metis checker_type.distinct(5))
  thus ?case
    using b_e_check_single_weaken_type b_e_check_single_type_type snoc
    by (metis check_unfold_snoc checker_type.distinct(5))
qed

lemma check_bot: "check \<C> es Bot = Bot"
  by (simp add: list.case_eq_if)

lemma b_e_check_weaken_top:
  assumes "check \<C> es (Type tn) = (TopType tm)"
  shows "check \<C> es (Type (ts@tn)) = (TopType tm)"
  using assms
proof (induction es arbitrary: tn tm)
  case Nil
  thus ?case
    by simp
next
  case (Cons e es)
  show ?case
  proof (cases "(check_single \<C> e (Type tn))")
    case (TopType x1)
    hence "check_single \<C> e (Type (ts@tn)) = TopType x1"
      using b_e_check_single_weaken_top
      by blast
    thus ?thesis
      using TopType Cons
      by simp
  next
    case (Type x2)
    hence "check_single \<C> e (Type (ts@tn)) = Type (ts@x2)"
      using b_e_check_single_weaken_type
      by blast
    thus ?thesis
      using Cons Type
      by fastforce
  next
    case Bot
    thus ?thesis
      using check_bot Cons
      by simp
  qed
  
qed

lemma b_e_type_checker_weaken:
  assumes "b_e_type_checker \<C> es (t1s _> t2s)"
  shows "b_e_type_checker \<C> es (ts@t1s _> ts@t2s)"
proof -
  have "c_types_agree (check \<C> es (Type t1s)) t2s"
    using assms(1)
    by simp
  then obtain ctn where ctn_def:"check \<C> es (Type t1s) = ctn"
                                "c_types_agree ctn t2s"
                                "ctn \<noteq> Bot"
    by fastforce
  show ?thesis
  proof (cases ctn)
    case (TopType x1)
    thus ?thesis
      using ctn_def(1,2) b_e_check_weaken_top[of \<C> es t1s x1 ts]
      by (metis append_assoc b_e_type_checker.simps c_types_agree_imp_ct_list_compat c_types_agree_top2)
  next
    case (Type x2)
    thus ?thesis
      using ctn_def(1,2) b_e_check_weaken_type[of \<C> es t1s x2 ts]
      by simp
  next
    case Bot
    thus ?thesis
      using ctn_def(3)
      by simp
  qed
qed

lemma b_e_type_checker_complete:
  assumes "\<C> \<turnstile> es : (tn _> tm)"
  shows "b_e_type_checker \<C> es (tn _> tm)"
  using assms
proof (induction es "(tn _> tm)" arbitrary: tn tm rule: b_e_typing.induct)
  case (select \<C> t)
  have "ct_list_compat [TAny, TSome (T_num T_i32)] [TSome t, TSome (T_num T_i32)]"
    by (simp add: to_ct_list_def ct_list_compat_def)
  thus ?case
    using ct_suffix_extend_ct_list_compat[OF ct_suffix_nil[of "[TSome t]"]] to_ct_list_def
    by auto
next
  case (br_table \<C> ts "is" i t1s t2s)
  show ?case
    using list_all_conv_same_lab[OF br_table]
    by (auto simp add: to_ct_list_def ct_suffix_nil ct_suffix_cons_it)
next
  case (set_global i \<C> t)
  thus ?case
    using to_ct_list_def ct_suffix_refl is_mut_def tg_t_def
    by auto
next
  case (composition \<C> es t1s t2s e t3s)
  thus ?case
    using b_e_type_checker_compose
    by simp
next
  case (weakening \<C> es t1s t2s ts)
  thus ?case
    using b_e_type_checker_weaken
    by simp
qed (auto simp add: to_ct_list_def ct_suffix_refl ct_suffix_nil ct_suffix_cons_it
                    ct_suffix_singleton_any)

theorem b_e_typing_equiv_b_e_type_checker:
  shows "(\<C> \<turnstile> es : tf) = (b_e_type_checker \<C> es tf)"
  using b_e_type_checker_sound b_e_type_checker_complete
  by (metis tf.exhaust)

end
