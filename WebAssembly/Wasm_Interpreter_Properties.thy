section \<open>Soundness of Interpreter\<close>

theory Wasm_Interpreter_Properties imports Wasm_Interpreter Wasm_Properties begin

lemma is_const_list_vs_to_es_list: "const_list ($C* vs)"
  using is_const_list
  by auto

lemma split_vals_e_not_const_list:
  assumes "\<not>const_list xs"
  shows "\<exists>as b bs. split_vals_e xs = (as, b#bs)"
  using assms
proof (induction xs)
  case Nil
  thus ?case
    by (simp add: const_list_def)
next
  case (Cons a xs)
  show ?case
  proof (cases "is_const a")
    case True
    hence 1:"\<not> const_list xs"
      using Cons(2)
      by (simp add: const_list_def)
    obtain ac where "a = $C ac"
      using e_type_const_unwrap[OF True]
      by blast
    thus ?thesis
      using Cons(1)[OF 1]
      by (metis Cons.prems append.right_neutral is_const_list_vs_to_es_list old.prod.exhaust split_vals_e.cases split_vals_e_conv_app)
  next
    case False
    hence "split_vals_e (a#xs) = ([],a#xs)"
    proof (cases a)
      case (Basic x1)
      thus ?thesis
        using False
        by (cases x1) (auto simp add: is_const_def)
    qed (auto simp add: is_const_def)
    thus ?thesis
      by blast
  qed
qed

lemma neq_label_nested:"[Label n les es] \<noteq> es"
proof -
  have "size_list size [Label n les es] > size_list size es"
    by simp
  thus ?thesis
    by fastforce
qed

lemma neq_local_nested:"[Frame n f es] \<noteq> es"
proof -
  have "size_list size [Frame n f es] > size_list size es"
    by simp
  thus ?thesis
    by fastforce
qed

lemma trap_not_value:"[Trap] \<noteq> $C*es"
  by (metis (full_types) e_typing_l_typing.intros(5) list.distinct(1) typing_map_typeof)

thm Lfilled.simps[of _ _ _ "[e]", simplified]

lemma lfilled_size:
  assumes "Lfilled j lholed es LI"
  shows "size_list size LI \<ge> size_list size es"
  using assms
  by (induction rule: Lfilled.induct) auto

thm Lfilled.simps[of _ _ es es, simplified]

lemma reduce_simple_not_eq:
  assumes "\<lparr>es\<rparr> \<leadsto> \<lparr>es'\<rparr>"
  shows "es \<noteq> es'"
  using assms
proof (induction es' rule: reduce_simple.induct)
  case (label_const vs n es)
  thus ?case
    using neq_label_nested
    by auto
next
  case (br vs n i lholed LI es)
  have "size_list size [Label n es LI] > size_list size (($C*vs) @ es)"
    using lfilled_size[OF br(2)]
    by simp
  thus ?case
    by fastforce
next
  case (local_const es f vs)
  thus ?case
    using neq_local_nested
    by auto
next
  case (return vs n j lholed es f)
  hence "size_list size [Frame n f es] > size_list size ($C*vs)"
        using lfilled_size[OF return(2)]
    by simp
  thus ?case
    by fastforce
qed auto
    
lemma reduce_not_eq:
  assumes "\<lparr>s;f;es\<rparr> \<leadsto> \<lparr>s';f';es'\<rparr>"
  shows "es \<noteq> es'"
  using assms
proof (induction es' rule: reduce.induct)
  case (basic e e' s vs)
  thus ?case
    using reduce_simple_not_eq
    by simp
next
  case (invoke_host_Some s i_cl t1s t2s h ves vcs n m hs s' vcs' f)
  then show ?case
    apply (cases vcs' rule:rev_cases)
     apply simp
    using v_to_e_def
    by (metis consts_cons_last(2) e.case(3) is_const_def)
next
  case (label s vs es s' vs' es' k lholed les les')
  thus ?case
    using lfilled_eq
    by fastforce
next
  case (get_local vi j f v vs s)
  then show ?case using v_to_e_def
    by (metis append.right_neutral const_list_def const_list_no_progress consts_app_ex(2) is_const1 is_const_list_vs_to_es_list list_all_simps(1) reduce.get_local)
next
  case (get_global s f j)
  then show ?case
    by (metis append_Nil consts_app_ex(1) list.simps(9) reduce.get_global reduce_not_value)
qed auto

lemma reduce_simple_call: "\<not>\<lparr>[$ Call j]\<rparr> \<leadsto> \<lparr>es'\<rparr>"
  using reduce_simple.simps[of "[$ Call j]", simplified] lfilled_single
  by fastforce

lemma reduce_call:
  assumes "\<lparr>s;f;[$ Call j]\<rparr> \<leadsto> \<lparr>s';f';es'\<rparr>"
  shows "s = s'"
        "f = f'"
        "es' = [Invoke (sfunc_ind (f_inst f) j)]"
  using assms
proof (induction "[$ Call j]:: e list" s' f' es' rule: reduce.induct)
  case (label s f es s' f' es' k lholed les')
  have "es = [$ Call j]"
       "lholed = LBase [] []"
    using reduce_not_nil[OF label(1)] lfilled_single[OF label(5)]
    by auto
  thus "s = s'"
       "f = f'"
       "les' = [Invoke (sfunc_ind (f_inst f) j)]"
    using label(2,3,4,6) Lfilled.simps[of k "LBase [] []" "[Invoke (sfunc_ind (f_inst f) j)]" les']
    by auto
qed (auto simp add: reduce_simple_call)

lemma app_v_s_drop_is:
  assumes "app_v_s_drop v_s = (v_s',res)"
  shows "(res = Step_normal \<and> (\<lparr>s;f;(v_stack_to_es v_s)@[$Drop]\<rparr> \<leadsto> \<lparr>s;f;(v_stack_to_es v_s')\<rparr>)) \<or>
         (res = crash_invalid)"
  using progress_L0_left[OF reduce.basic[OF reduce_simple.drop]] assms
  unfolding app_v_s_drop_def
  by (auto split: list.splits)

lemma app_v_s_unop_is:
  assumes "app_v_s_unop op v_s = (v_s',res)"
  shows "(res = Step_normal \<and> (\<lparr>s;f;(v_stack_to_es v_s)@[$Unop t op]\<rparr> \<leadsto> \<lparr>s;f;(v_stack_to_es v_s')\<rparr>)) \<or>
         (res = crash_invalid)"
  using progress_L0_left[OF reduce.basic[OF reduce_simple.unop]] assms v_to_e_def
  unfolding app_v_s_unop_def
  by (auto split: v.splits list.splits)

lemma app_v_s_testop_is:
  assumes "app_v_s_testop op v_s = (v_s',res)"
  shows "(res = Step_normal \<and> (\<lparr>s;f;(v_stack_to_es v_s)@[$Testop t op]\<rparr> \<leadsto> \<lparr>s;f;(v_stack_to_es v_s')\<rparr>)) \<or>
         (res = crash_invalid)"
  using progress_L0_left[OF reduce.basic[OF reduce_simple.testop]] assms v_to_e_def
  unfolding app_v_s_testop_def
  by (auto split: v.splits list.splits)

lemma app_v_s_binop_is:
  assumes "app_v_s_binop op v_s = (v_s',res)"
  shows "(res = Step_normal \<and> (\<lparr>s;f;(v_stack_to_es v_s)@[$Binop t op]\<rparr> \<leadsto> \<lparr>s;f;(v_stack_to_es v_s')\<rparr>)) \<or>
         (\<exists>str. res = Res_trap str \<and> (\<lparr>s;f;(v_stack_to_es v_s)@[$Binop t op]\<rparr> \<leadsto> \<lparr>s;f;(v_stack_to_es v_s')@[Trap]\<rparr>)) \<or>
         (res = crash_invalid)"
  using progress_L0_left[OF reduce.basic[OF reduce_simple.binop_Some]]
        progress_L0_left[OF reduce.basic[OF reduce_simple.binop_None]] assms v_to_e_def
  unfolding app_v_s_binop_def
  apply (simp split: v.splits list.splits cvtop.splits if_splits option.splits)
  apply blast
  apply fastforce
  done

lemma app_v_s_relop_is:
  assumes "app_v_s_relop op v_s = (v_s',res)"
  shows "(res = Step_normal \<and> (\<lparr>s;f;(v_stack_to_es v_s)@[$Relop t op]\<rparr> \<leadsto> \<lparr>s;f;(v_stack_to_es v_s')\<rparr>)) \<or>
         (res = crash_invalid)"
  using progress_L0_left[OF reduce.basic[OF reduce_simple.relop]] assms
  unfolding app_v_s_relop_def v_to_e_def
  by (auto split: v.splits list.splits)

lemma app_v_s_unop_vec_is:
  assumes "app_v_s_unop_vec op v_s = (v_s',res)"
  shows "(res = Step_normal \<and> (\<lparr>s;f;(v_stack_to_es v_s)@[$Unop_vec op]\<rparr> \<leadsto> \<lparr>s;f;(v_stack_to_es v_s')\<rparr>)) \<or>
         (res = crash_invalid)"
  using progress_L0_left[OF reduce.basic[OF reduce_simple.unop_vec]] assms
  unfolding app_v_s_unop_vec_def v_to_e_def
  by (auto split: v.splits list.splits)

lemma app_v_s_binop_vec_is:
  assumes "app_v_s_binop_vec op v_s = (v_s',res)"
  shows "(res = Step_normal \<and> (\<lparr>s;f;(v_stack_to_es v_s)@[$Binop_vec op]\<rparr> \<leadsto> \<lparr>s;f;(v_stack_to_es v_s')\<rparr>)) \<or>
         (\<exists>str. res = Res_trap str \<and> (\<lparr>s;f;(v_stack_to_es v_s)@[$Binop_vec op]\<rparr> \<leadsto> \<lparr>s;f;(v_stack_to_es v_s')@[Trap]\<rparr>)) \<or>
         (res = crash_invalid)"
  using progress_L0_left[OF reduce.basic[OF reduce_simple.binop_vec_Some]]
        progress_L0_left[OF reduce.basic[OF reduce_simple.binop_vec_None]] assms
  unfolding app_v_s_binop_vec_def v_to_e_def
  apply (simp split: v.splits list.splits cvtop.splits if_splits option.splits)
  apply blast
  apply fastforce
  done

lemma app_v_s_ternop_vec_is:
  assumes "app_v_s_ternop_vec op v_s = (v_s',res)"
  shows "(res = Step_normal \<and> (\<lparr>s;f;(v_stack_to_es v_s)@[$Ternop_vec op]\<rparr> \<leadsto> \<lparr>s;f;(v_stack_to_es v_s')\<rparr>)) \<or>
         (res = crash_invalid)"
  using progress_L0_left[OF reduce.basic[OF reduce_simple.ternop_vec]] assms
  unfolding app_v_s_ternop_vec_def v_to_e_def
  by (auto split: v.splits list.splits)

lemma app_v_s_test_vec_is:
  assumes "app_v_s_test_vec op v_s = (v_s',res)"
  shows "(res = Step_normal \<and> (\<lparr>s;f;(v_stack_to_es v_s)@[$Test_vec op]\<rparr> \<leadsto> \<lparr>s;f;(v_stack_to_es v_s')\<rparr>)) \<or>
         (res = crash_invalid)"
  using progress_L0_left[OF reduce.basic[OF reduce_simple.test_vec]] assms
  unfolding app_v_s_test_vec_def v_to_e_def
  by (auto split: v.splits list.splits)

lemma app_v_s_shift_vec_is:
  assumes "app_v_s_shift_vec op v_s = (v_s',res)"
  shows "(res = Step_normal \<and> (\<lparr>s;f;(v_stack_to_es v_s)@[$Shift_vec op]\<rparr> \<leadsto> \<lparr>s;f;(v_stack_to_es v_s')\<rparr>)) \<or>
         (res = crash_invalid)"
  using progress_L0_left[OF reduce.basic[OF reduce_simple.shift_vec]] assms
  unfolding app_v_s_shift_vec_def v_to_e_def
  by (auto split: v.splits v_num.splits list.splits)

lemma app_v_s_splat_vec_is:
  assumes "app_v_s_splat_vec sv v_s = (v_s',res)"
  shows "(res = Step_normal \<and> (\<lparr>s;f;(v_stack_to_es v_s)@[$Splat_vec sv]\<rparr> \<leadsto> \<lparr>s;f;(v_stack_to_es v_s')\<rparr>)) \<or>
         (res = crash_invalid)"
  using progress_L0_left[OF reduce.basic[OF reduce_simple.splat_vec]] assms
  unfolding app_v_s_splat_vec_def v_to_e_def
  by (auto split: v.splits list.splits)

lemma app_v_s_extract_vec_is:
  assumes "app_v_s_extract_vec sv sx i v_s = (v_s',res)"
  shows "(res = Step_normal \<and> (\<lparr>s;f;(v_stack_to_es v_s)@[$Extract_vec sv sx i]\<rparr> \<leadsto> \<lparr>s;f;(v_stack_to_es v_s')\<rparr>)) \<or>
         (res = crash_invalid)"
  using progress_L0_left[OF reduce.basic[OF reduce_simple.extract_vec]] assms
  unfolding app_v_s_extract_vec_def v_to_e_def
  by (auto split: v.splits list.splits)

lemma app_v_s_replace_vec_is:
  assumes "app_v_s_replace_vec sv i v_s = (v_s',res)"
  shows "(res = Step_normal \<and> (\<lparr>s;f;(v_stack_to_es v_s)@[$Replace_vec sv i]\<rparr> \<leadsto> \<lparr>s;f;(v_stack_to_es v_s')\<rparr>)) \<or>
         (res = crash_invalid)"
  using progress_L0_left[OF reduce.basic[OF reduce_simple.replace_vec]] assms
  unfolding app_v_s_replace_vec_def v_to_e_def
  by (auto split: v.splits list.splits)

lemma app_v_s_cvtop_cvt_is:
  assumes "app_v_s_cvtop Convert t1 t2 sx v_s = (v_s',res)"
  shows "(res = Step_normal \<and> (\<lparr>s;f;(v_stack_to_es v_s)@[$ Cvtop t2 Convert t1 sx]\<rparr> \<leadsto> \<lparr>s;f;(v_stack_to_es v_s')\<rparr>)) \<or>
         (\<exists>str. res = Res_trap str \<and> (\<lparr>s;f;(v_stack_to_es v_s)@[$ Cvtop t2 Convert t1 sx]\<rparr> \<leadsto> \<lparr>s;f;(v_stack_to_es v_s')@[Trap]\<rparr>)) \<or>
         (res = crash_invalid)"
  using progress_L0_left[OF reduce.basic[OF reduce_simple.convert_Some]]
        progress_L0_left[OF reduce.basic[OF reduce_simple.convert_None]] assms v_to_e_def
  unfolding app_v_s_cvtop_def
  apply (simp split: v.splits list.splits cvtop.splits if_splits option.splits)
  apply blast
  apply fastforce
  done

lemma app_v_s_cvtop_reinterpret_is:
  assumes "app_v_s_cvtop Reinterpret t1 t2 sx v_s = (v_s',res)"
  shows "(res = Step_normal \<and> (\<lparr>s;f;(v_stack_to_es v_s)@[$ Cvtop t2 Reinterpret t1 sx]\<rparr> \<leadsto> \<lparr>s;f;(v_stack_to_es v_s')\<rparr>)) \<or>
         (res = crash_invalid)"
  using progress_L0_left[OF reduce.basic[OF reduce_simple.reinterpret]] assms v_to_e_def
  unfolding app_v_s_cvtop_def
  by (auto split: v.splits list.splits cvtop.splits if_splits)

lemma app_v_s_cvtop_is:
  assumes "app_v_s_cvtop op t1 t2 sx v_s = (v_s',res)"
  shows "(res = Step_normal \<and> (\<lparr>s;f;(v_stack_to_es v_s)@[$ Cvtop t2 op t1 sx]\<rparr> \<leadsto> \<lparr>s;f;(v_stack_to_es v_s')\<rparr>)) \<or>
         (\<exists>str. res = Res_trap str \<and> (\<lparr>s;f;(v_stack_to_es v_s)@[$ Cvtop t2 op t1 sx]\<rparr> \<leadsto> \<lparr>s;f;(v_stack_to_es v_s')@[Trap]\<rparr>)) \<or>
         (res = crash_invalid)"
  using app_v_s_cvtop_cvt_is app_v_s_cvtop_reinterpret_is assms v_to_e_def
  apply (cases op)
  apply simp_all
  apply blast
  done

lemma app_v_s_select_is:
  assumes "app_v_s_select t_tag v_s = (v_s',res)"
  shows "(res = Step_normal \<and> (\<lparr>s;f;(v_stack_to_es v_s)@[$Select t_tag]\<rparr> \<leadsto> \<lparr>s;f;(v_stack_to_es v_s')\<rparr>)) \<or>
         (res = crash_invalid)"
  using progress_L0_left[OF reduce.basic[OF reduce_simple.select_true]]
        progress_L0_left[OF reduce.basic[OF reduce_simple.select_false]] assms
  unfolding app_v_s_select_def
  apply (auto simp add: v_to_e_def split: if_splits list.splits v.splits v_num.splits)
  using v.simps by metis+ 

lemma app_f_v_s_get_local_is:
  assumes "app_f_v_s_get_local k f v_s = (v_s',res)"
  shows "(res = Step_normal \<and> (\<lparr>s;f;(v_stack_to_es v_s)@[$Get_local k]\<rparr> \<leadsto> \<lparr>s;f;(v_stack_to_es v_s')\<rparr>)) \<or>
         (res = crash_invalid)"
proof (cases "k < length (f_locs f)")
  case True
  then obtain v1s v v2s where 1:"(f_locs f) = v1s@[v]@v2s" "length v1s = k"
    using id_take_nth_drop[OF True] length_take[of k "f_locs f"]
    by simp
  thus ?thesis
    using progress_L0_left[OF reduce.get_local] assms
    unfolding app_f_v_s_get_local_def
    by (auto simp add: Let_def split: list.splits v.splits if_splits)
next
  case False
  thus ?thesis
    using assms
    unfolding app_f_v_s_get_local_def
    by (auto simp add: Let_def split: list.splits v.splits if_splits)
qed

lemma app_f_v_s_set_local_is:
  assumes "app_f_v_s_set_local k f v_s = (f', v_s', res)"
  shows "(res = Step_normal \<and> (\<lparr>s;f;(v_stack_to_es v_s)@[$Set_local k]\<rparr> \<leadsto> \<lparr>s;f';(v_stack_to_es v_s')\<rparr>)) \<or>
         (res = crash_invalid)"
proof (cases "res = Step_normal")
  case True
  obtain va where 0:"v_s = va#v_s'"
                         "k < length (f_locs f)"
    using assms True
    unfolding app_f_v_s_set_local_def
    by (simp add: Let_def split: list.splits if_splits)
  obtain v1s v v2s where 1:"(f_locs f) = v1s@[v]@v2s" "length v1s = k"
    using id_take_nth_drop[OF 0(2)] length_take[of k "f_locs f"]
    by fastforce
  have 2:"f = \<lparr> f_locs = v1s@[v]@v2s, f_inst = (f_inst f)\<rparr>"
         "f' = \<lparr> f_locs = v1s@[va]@v2s, f_inst = (f_inst f)\<rparr>"
    using assms 1 0
    unfolding app_f_v_s_set_local_def
    by (fastforce simp add: Let_def split: list.splits if_splits)+
  show ?thesis
    using 0(1) True 2 progress_L0_left[OF reduce.set_local, OF 1(2), of _ v v2s "f_inst f" "rev v_s'" va]
    by (simp add: Let_def split: list.splits v.splits if_splits)
next
  case False
  thus ?thesis
    using assms
    unfolding app_f_v_s_set_local_def
    by (fastforce simp add: Let_def split: list.splits if_splits)
qed

lemma app_v_s_tee_local_is:
  assumes "app_v_s_tee_local k v_s = (v_s', es_cont, res)"
  shows "(res = Step_normal \<and> es_cont = [$Set_local k] \<and> (\<lparr>s;f;(v_stack_to_es v_s)@[$Tee_local k]\<rparr> \<leadsto> \<lparr>s;f;(v_stack_to_es v_s')@[$Set_local k]\<rparr>)) \<or>
         (res = crash_invalid)"
  using progress_L0_left[OF reduce.basic[OF reduce_simple.tee_local]] assms
  unfolding app_v_s_tee_local_def
  by (fastforce split: list.splits cvtop.splits if_splits option.splits)

lemma app_v_s_if_is:
  assumes "app_v_s_if tf es1 es2 v_s = (v_s', es_c, res)"
  shows "(res = Step_normal \<and> (\<lparr>s;f;(v_stack_to_es v_s)@[$If tf es1 es2]\<rparr> \<leadsto> \<lparr>s;f;(v_stack_to_es v_s')@es_c\<rparr>)) \<or>
         (res = crash_invalid)"
  using progress_L0_left[OF reduce.basic[OF reduce_simple.if_false]]
        progress_L0_left[OF reduce.basic[OF reduce_simple.if_true]] assms v_to_e_def
  unfolding app_v_s_if_def
  by (auto split: list.splits cvtop.splits if_splits option.splits v.splits v_num.splits)

lemma app_v_s_br_if_is:
  assumes "app_v_s_br_if k v_s = (v_s', es_c, res)"
  shows "(res = Step_normal \<and> (\<lparr>s;f;(v_stack_to_es v_s)@[$Br_if k]\<rparr> \<leadsto> \<lparr>s;f;(v_stack_to_es v_s')@es_c\<rparr>)) \<or>
         (res = crash_invalid)"
  using progress_L0_left[OF reduce.basic[OF reduce_simple.br_if_false]]
        progress_L0_left[OF reduce.basic[OF reduce_simple.br_if_true]] assms v_to_e_def
  unfolding app_v_s_br_if_def
  by (auto split: list.splits cvtop.splits if_splits option.splits v.splits v_num.splits)

lemma app_v_s_br_table_is:
  assumes "app_v_s_br_table ks k v_s = (v_s', es_c, res)"
  shows "(res = Step_normal \<and> (\<lparr>s;f;(v_stack_to_es v_s)@[$Br_table ks k]\<rparr> \<leadsto> \<lparr>s;f;(v_stack_to_es v_s')@es_c\<rparr>)) \<or>
         (res = crash_invalid)"
  using progress_L0_left[OF reduce.basic[OF reduce_simple.br_table]]
        progress_L0_left[OF reduce.basic[OF reduce_simple.br_table_length]] assms v_to_e_def
  unfolding app_v_s_br_table_def
  by (auto simp add: Let_def split: list.splits cvtop.splits if_splits option.splits v.splits v_num.splits)

lemma app_f_call_is:
  assumes "app_f_call k f = (es_c,res)"
  shows "(res = Step_normal \<and> (\<forall>s. \<lparr>s;f;(v_stack_to_es v_s)@[$ Call k]\<rparr> \<leadsto> \<lparr>s;f;(v_stack_to_es v_s)@es_c\<rparr>)) \<or>
         (res = crash_invalid)"
  using progress_L0_left[OF reduce.call] assms 
  unfolding app_f_call_def
  by (auto simp add: Let_def split: list.splits cvtop.splits if_splits option.splits v.splits)

lemma app_s_f_v_s_call_indirect_is:
  assumes "app_s_f_v_s_call_indirect x y tinsts cls f v_s = (v_s', es_c, res)"
  shows "(res = Step_normal \<and> ((tabs s = tinsts \<and> funcs s = cls) \<longrightarrow> \<lparr>s;f;(v_stack_to_es v_s)@[$ Call_indirect x y]\<rparr> \<leadsto> \<lparr>s;f;(v_stack_to_es v_s')@es_c\<rparr>)) \<or>
         (\<exists>str. res = Res_trap str \<and> es_c = [] \<and> ((tabs s = tinsts \<and> funcs s = cls) \<longrightarrow> \<lparr>s;f;(v_stack_to_es v_s)@[$ Call_indirect x y]\<rparr> \<leadsto> \<lparr>s;f;(v_stack_to_es v_s')@[Trap]\<rparr>)) \<or>
         (res = crash_invalid)"
proof (cases "res")
  case (Res_crash x1)
  thus ?thesis
    using assms
    unfolding app_s_f_v_s_call_indirect_def
    by (auto simp add: Let_def split: list.splits if_splits option.splits v_ref.splits v.splits v_num.splits)
next
  case (Res_trap x2)
  then obtain i a t c where 0:"(f_inst f) = i"
                                    "x < length (inst.tabs i)"
                                    "v_s = (V_num (ConstInt32 c))#v_s'"
                                    "es_c = []"
                                    "(tab_cl_ind tinsts (inst.tabs i!x) (nat_of_int c)) = None \<or>
                                     (tab_cl_ind tinsts (inst.tabs i!x) (nat_of_int c)) = Some (ConstNull t) \<or>
                                     (tab_cl_ind tinsts (inst.tabs i!x) (nat_of_int c)) = Some (ConstRefFunc a) \<and> (stypes i y \<noteq> cl_type (cls!a))"
    using assms
    unfolding app_s_f_v_s_call_indirect_def crash_invalid_def
    by (auto simp add: Let_def split: list.splits cvtop.splits if_splits option.splits v.splits v_num.splits v_ref.splits)
  have 1:"tabs s = tinsts \<Longrightarrow> funcs s = cls \<Longrightarrow> (stab s i x (nat_of_int c) = (Some (ConstRefFunc a)) \<and> stypes i y \<noteq> cl_type (funcs s!a)) \<or>  \<not> is_some_const_ref_func (stab s i x (nat_of_int c))"
    using 0 is_some_const_ref_func_def
    unfolding stab_def stab_cl_ind_def
    by auto
  show ?thesis
    using progress_L0_left[OF reduce.call_indirect_None, OF 0(1) 1, of "rev v_s'"] Res_trap 0 v_to_e_def
    unfolding crash_invalid_def tab_cl_ind_def
    by (auto simp add: Let_def split: if_splits option.splits v_ref.splits)
next
  case (Step_normal)
  then obtain i a c where 0: "(f_inst f) = i"
                             "x < length (inst.tabs i)"
                             "v_s = (V_num (ConstInt32 c))#v_s'"
                             "es_c = [Invoke a]"
                             "(tab_cl_ind tinsts (inst.tabs i!x) (nat_of_int c)) = Some (ConstRefFunc a)"
                             "(stypes i y = cl_type (cls!a))"
    using assms
    unfolding app_s_f_v_s_call_indirect_def crash_invalid_def
    by (auto simp add: Let_def split: list.splits v_ref.splits if_splits option.splits v.splits v_num.splits)
  have 1:"tabs s = tinsts \<Longrightarrow> stab s i x (nat_of_int c) = Some (ConstRefFunc a)"
    using 0
    by (simp add: stab_def stab_cl_ind_def split: list.splits)
  show ?thesis
    using progress_L0_left[OF reduce.call_indirect_Some, OF 0(1) 1 0(6), of "rev v_s'"] Step_normal 0
    unfolding crash_invalid_def
    using tab_cl_ind_def v_to_e_def
    by (auto simp add: Let_def split: if_splits option.splits v_ref.splits)
qed

lemma app_s_f_v_s_get_global_is:
  assumes "app_s_f_v_s_get_global k gs f v_s = (v_s',res)"
  shows "(res = Step_normal \<and> ((globs s = gs) \<longrightarrow> \<lparr>s;f;(v_stack_to_es v_s)@[$Get_global k]\<rparr> \<leadsto> \<lparr>s;f;(v_stack_to_es v_s')\<rparr>))"
  using progress_L0_left[OF reduce.get_global] assms
  unfolding sglob_val_def sglob_def app_s_f_v_s_get_global_def
  by fastforce

lemma app_s_f_v_s_set_global_is:
  assumes "app_s_f_v_s_set_global k gs f v_s = (gs', v_s', res)"
  shows "(res = Step_normal \<and> ((globs s = gs) \<longrightarrow> \<lparr>s;f;(v_stack_to_es v_s)@[$Set_global k]\<rparr> \<leadsto> \<lparr>s\<lparr>globs:=gs'\<rparr>;f;(v_stack_to_es v_s')\<rparr>)) \<or>
         (res = crash_invalid)"
  using progress_L0_left[OF reduce.set_global] assms
  unfolding supdate_glob_def app_s_f_v_s_set_global_def
  by (fastforce split: list.splits)

lemma app_s_f_v_s_load_is:
  assumes "app_s_f_v_s_load t off ms f v_s = (v_s',res)"
  shows "(res = Step_normal \<and> ((mems s = ms) \<longrightarrow> \<lparr>s;f;(v_stack_to_es v_s)@[$Load t None a off]\<rparr> \<leadsto> \<lparr>s;f;(v_stack_to_es v_s')\<rparr>)) \<or>
         (\<exists>str. res = Res_trap str \<and> ((mems s = ms) \<longrightarrow> \<lparr>s;f;(v_stack_to_es v_s)@[$Load t None a off]\<rparr> \<leadsto> \<lparr>s;f;(v_stack_to_es v_s')@[Trap]\<rparr>)) \<or>
         (res = crash_invalid)"
  using progress_L0_left[OF reduce.load_Some] progress_L0_left[OF reduce.load_None] assms v_to_e_def
  unfolding app_s_f_v_s_load_def
  apply (simp split: list.splits cvtop.splits if_splits option.splits v.splits v_num.splits)
  apply metis
  apply fastforce
  done

lemma app_s_f_v_s_load_packed_is:
  assumes "app_s_f_v_s_load_packed t tp sx off ms f v_s = (v_s',res)"
  shows "(res = Step_normal \<and> ((mems s = ms) \<longrightarrow> \<lparr>s;f;(v_stack_to_es v_s)@[$Load t (Some (tp, sx)) a off]\<rparr> \<leadsto> \<lparr>s;f;(v_stack_to_es v_s')\<rparr>)) \<or>
         (\<exists>str. res = Res_trap str \<and> ((mems s = ms) \<longrightarrow> \<lparr>s;f;(v_stack_to_es v_s)@[$Load t (Some (tp, sx)) a off]\<rparr> \<leadsto> \<lparr>s;f;(v_stack_to_es v_s')@[Trap]\<rparr>)) \<or>
         (res = crash_invalid)"
  using progress_L0_left[OF reduce.load_packed_Some] progress_L0_left[OF reduce.load_packed_None] assms v_to_e_def
  unfolding app_s_f_v_s_load_packed_def
  apply (simp split: list.splits cvtop.splits if_splits option.splits v.splits v_num.splits)
  apply metis
  apply fastforce
  done

lemma app_s_f_v_s_load_maybe_packed_is:
  assumes "app_s_f_v_s_load_maybe_packed t tp_sx off ms f v_s = (v_s',res)"
  shows "(res = Step_normal \<and> ((mems s = ms) \<longrightarrow> \<lparr>s;f;(v_stack_to_es v_s)@[$Load t tp_sx a off]\<rparr> \<leadsto> \<lparr>s;f;(v_stack_to_es v_s')\<rparr>)) \<or>
         (\<exists>str. res = Res_trap str \<and> ((mems s = ms) \<longrightarrow> \<lparr>s;f;(v_stack_to_es v_s)@[$Load t tp_sx a off]\<rparr> \<leadsto> \<lparr>s;f;(v_stack_to_es v_s')@[Trap]\<rparr>)) \<or>
         (res = crash_invalid)"
  using app_s_f_v_s_load_is[of t off ms f v_s]
        app_s_f_v_s_load_packed_is[of t _ _  off ms f v_s]
        assms
  unfolding app_s_f_v_s_load_maybe_packed_def
  by (simp split: option.splits prod.splits)


lemma app_s_f_v_s_store_is:
  assumes "app_s_f_v_s_store t off ms f v_s = (ms', v_s', res)"
  shows "(res = Step_normal \<and> ((mems s = ms) \<longrightarrow> \<lparr>s;f;(v_stack_to_es v_s)@[$Store t None a off]\<rparr> \<leadsto> \<lparr>s\<lparr>mems:=ms'\<rparr>;f;(v_stack_to_es v_s')\<rparr>)) \<or>
         (\<exists>str. res = Res_trap str \<and> ms = ms' \<and> ((mems s = ms) \<longrightarrow> \<lparr>s;f;(v_stack_to_es v_s)@[$Store t None a off]\<rparr> \<leadsto> \<lparr>s;f;(v_stack_to_es v_s')@[Trap]\<rparr>)) \<or>
         (res = crash_invalid)"
  using progress_L0_left[OF reduce.store_Some] progress_L0_left[OF reduce.store_None] assms v_to_e_def
  unfolding app_s_f_v_s_store_def
  apply (simp split: list.splits cvtop.splits if_splits option.splits v.splits v_num.splits)
  apply metis
  apply fastforce
  done

lemma app_s_f_v_s_store_packed_is:
  assumes "app_s_f_v_s_store_packed t tp off ms f v_s = (ms', v_s', res)"
  shows "(res = Step_normal \<and> ((mems s = ms) \<longrightarrow> \<lparr>s;f;(v_stack_to_es v_s)@[$Store t (Some tp) a off]\<rparr> \<leadsto> \<lparr>s\<lparr>mems:=ms'\<rparr>;f;(v_stack_to_es v_s')\<rparr>)) \<or>
         (\<exists>str. res = Res_trap str \<and> ms = ms' \<and> ((mems s = ms) \<longrightarrow> \<lparr>s;f;(v_stack_to_es v_s)@[$Store t (Some tp) a off]\<rparr> \<leadsto> \<lparr>s;f;(v_stack_to_es v_s')@[Trap]\<rparr>)) \<or>
         (res = crash_invalid)"
  using progress_L0_left[OF reduce.store_packed_Some] progress_L0_left[OF reduce.store_packed_None] assms v_to_e_def
  unfolding app_s_f_v_s_store_packed_def
  apply (simp split: list.splits cvtop.splits if_splits option.splits v.splits v_num.splits)
  apply metis
  apply fastforce
  done

lemma app_s_f_v_s_store_maybe_packed_is:
  assumes "app_s_f_v_s_store_maybe_packed t tp off ms f v_s = (ms', v_s', res)"
  shows "(res = Step_normal \<and> ((mems s = ms) \<longrightarrow> \<lparr>s;f;(v_stack_to_es v_s)@[$Store t tp a off]\<rparr> \<leadsto> \<lparr>s\<lparr>mems:=ms'\<rparr>;f;(v_stack_to_es v_s')\<rparr>)) \<or>
         (\<exists>str. res = Res_trap str \<and> ms = ms' \<and> ((mems s = ms) \<longrightarrow> \<lparr>s;f;(v_stack_to_es v_s)@[$Store t tp a off]\<rparr> \<leadsto> \<lparr>s;f;(v_stack_to_es v_s')@[Trap]\<rparr>)) \<or>
         (res = crash_invalid)"
  using app_s_f_v_s_store_is[of t off ms f v_s ms']
        app_s_f_v_s_store_packed_is[of t "the tp" off ms f v_s ms']
        assms
  unfolding app_s_f_v_s_store_maybe_packed_def
  by (simp split: option.splits)

lemma app_s_f_v_s_mem_size_is:
  assumes "app_s_f_v_s_mem_size ms f v_s = (v_s', res)"
  shows "(res = Step_normal \<and> ((mems s = ms) \<longrightarrow> \<lparr>s;f;(v_stack_to_es v_s)@[$ Current_memory]\<rparr> \<leadsto> \<lparr>s;f;(v_stack_to_es v_s')\<rparr>)) \<or>
         (res = crash_invalid)"
  using progress_L0_left[OF reduce.current_memory] assms v_to_e_def
  unfolding app_s_f_v_s_mem_size_def
  apply (auto split: list.splits cvtop.splits if_splits option.splits v.splits)
  by (metis old.prod.exhaust)

lemma app_s_f_v_s_load_vec_is:
  assumes "app_s_f_v_s_load_vec lv off ms f v_s = (v_s',res)"
  shows "(res = Step_normal \<and> ((mems s = ms) \<longrightarrow> \<lparr>s;f;(v_stack_to_es v_s)@[$Load_vec lv a off]\<rparr> \<leadsto> \<lparr>s;f;(v_stack_to_es v_s')\<rparr>)) \<or>
         (\<exists>str. res = Res_trap str \<and> ((mems s = ms) \<longrightarrow> \<lparr>s;f;(v_stack_to_es v_s)@[$Load_vec lv a off]\<rparr> \<leadsto> \<lparr>s;f;(v_stack_to_es v_s')@[Trap]\<rparr>)) \<or>
         (res = crash_invalid)"
  using progress_L0_left[OF reduce.load_vec_Some] progress_L0_left[OF reduce.load_vec_None] assms v_to_e_def
  unfolding app_s_f_v_s_load_vec_def
  apply (simp split: list.splits cvtop.splits if_splits option.splits v.splits v_num.splits)
  apply metis
  apply fastforce
  done

lemma app_s_f_v_s_load_lane_vec_is:
  assumes "app_s_f_v_s_load_lane_vec svi i off ms f v_s = (v_s',res)"
  shows "(res = Step_normal \<and> ((mems s = ms) \<longrightarrow> \<lparr>s;f;(v_stack_to_es v_s)@[$Load_lane_vec svi i a off]\<rparr> \<leadsto> \<lparr>s;f;(v_stack_to_es v_s')\<rparr>)) \<or>
         (\<exists>str. res = Res_trap str \<and> ((mems s = ms) \<longrightarrow> \<lparr>s;f;(v_stack_to_es v_s)@[$Load_lane_vec svi i a off]\<rparr> \<leadsto> \<lparr>s;f;(v_stack_to_es v_s')@[Trap]\<rparr>)) \<or>
         (res = crash_invalid)"
  using progress_L0_left[OF reduce.load_lane_vec_Some] progress_L0_left[OF reduce.load_lane_vec_None] assms v_to_e_def
  unfolding app_s_f_v_s_load_lane_vec_def
  apply (simp split: list.splits cvtop.splits if_splits option.splits v.splits v_num.splits v_vec.splits)
  apply metis
  apply fastforce
  done

lemma app_s_f_v_s_store_vec_is:
  assumes "app_s_f_v_s_store_vec sv off ms f v_s = (ms', v_s', res)"
  shows "(res = Step_normal \<and> ((mems s = ms) \<longrightarrow> \<lparr>s;f;(v_stack_to_es v_s)@[$Store_vec sv a off]\<rparr> \<leadsto> \<lparr>s\<lparr>mems:=ms'\<rparr>;f;(v_stack_to_es v_s')\<rparr>)) \<or>
         (\<exists>str. res = Res_trap str \<and> ms = ms' \<and> ((mems s = ms) \<longrightarrow> \<lparr>s;f;(v_stack_to_es v_s)@[$Store_vec sv a off]\<rparr> \<leadsto> \<lparr>s;f;(v_stack_to_es v_s')@[Trap]\<rparr>)) \<or>
         (res = crash_invalid)"
  using progress_L0_left[OF reduce.store_vec_Some] progress_L0_left[OF reduce.store_vec_None] assms v_to_e_def
  unfolding app_s_f_v_s_store_vec_def
  apply (simp add: Let_def split: list.splits cvtop.splits if_splits option.splits v.splits v_num.splits v_vec.splits)
  apply metis
  apply fastforce
  done

lemma app_s_f_v_s_mem_grow_is:
  assumes "app_s_f_v_s_mem_grow ms f v_s = (ms', v_s', res)"
  shows "(res = Step_normal \<and> ((mems s = ms) \<longrightarrow> \<lparr>s;f;(v_stack_to_es v_s)@[$Grow_memory]\<rparr> \<leadsto> \<lparr>s\<lparr>mems:=ms'\<rparr>;f;(v_stack_to_es v_s')\<rparr>)) \<or>
         (res = crash_invalid)"
proof (cases res)
  case (Res_crash x1)
  thus ?thesis
    using assms
    unfolding app_s_f_v_s_mem_grow_def
    by (simp split: list.splits cvtop.splits if_splits option.splits v.splits v_num.splits)
next
  case (Res_trap x2)
  thus ?thesis
    using assms
    unfolding app_s_f_v_s_mem_grow_def
    by (simp split: list.splits cvtop.splits if_splits option.splits v.splits v_num.splits)
next
  case (Step_normal)
  then show ?thesis
  proof(cases "(mems s = ms)")
    case True
      then obtain c c' j m' v_s'' where 0:
      "v_s = (V_num (ConstInt32 c))#v_s''"
      "v_s' = (V_num (ConstInt32 c'))#v_s''"
      "smem_ind (f_inst f) = Some j"
      "((mem_grow (ms!j) (nat_of_int c)) = Some m' \<and> ms' = ms[j:=m'] \<and> c' = (int_of_nat (mem_size (ms!j)))) \<or>
         ((mem_grow (ms!j) (nat_of_int c)) = None \<and> ms' = ms \<and> c' = (int32_minus_one))"
      using assms Step_normal
      unfolding app_s_f_v_s_mem_grow_def crash_invalid_def
      by (auto split: list.splits cvtop.splits if_splits option.splits v.splits v_num.splits)
    show ?thesis
      using 0(4)
    proof (rule disjE)
      assume assms: "((mem_grow (ms!j) (nat_of_int c)) = Some m' \<and> ms' = ms[j:=m'] \<and> c' = (int_of_nat (mem_size (ms!j))))"
      thus ?thesis
        using Step_normal progress_L0_left[OF reduce.grow_memory, OF 0(3), of s]
          0(1,2) Step_normal True v_to_e_def
        by auto
    next
      assume "((mem_grow (ms!j) (nat_of_int c)) = None \<and> ms' = ms \<and> c' = int32_minus_one)"
      thus ?thesis
        using progress_L0_left[OF reduce.grow_memory_fail, OF 0(3), of s] 0(1,2) True Step_normal v_to_e_def
        apply auto
        by (meson old.prod.exhaust)
    qed
  next
    case False
    then show ?thesis using Step_normal unfolding crash_invalid_def by auto
  qed
qed

lemma app_s_f_v_s_table_set_is:
  assumes "app_s_f_v_s_table_set x tabinsts f v_s = (tabinsts', v_s', res)"
  shows "res = Step_normal \<and> ((tabs s = tabinsts) \<longrightarrow> \<lparr>s;f;(v_stack_to_es v_s)@[$Table_set x]\<rparr> \<leadsto> \<lparr>s\<lparr>tabs:=tabinsts'\<rparr>;f;(v_stack_to_es v_s')\<rparr>) \<or>
         (\<exists>str. res = Res_trap str \<and> tabinsts = tabinsts' \<and> ((tabs s = tabinsts) \<longrightarrow> \<lparr>s;f;(v_stack_to_es v_s)@[$Table_set x]\<rparr> \<leadsto> \<lparr>s;f;(v_stack_to_es v_s')@[Trap]\<rparr>)) \<or>
         res = crash_invalid"
  using progress_L0_left[OF reduce.table_set] progress_L0_left[OF reduce.table_set_fail] assms v_to_e_def
  unfolding app_s_f_v_s_table_set_def
  apply (simp add: Let_def split: list.splits cvtop.splits if_splits option.splits v.splits v_num.splits v_vec.splits)
  by metis

lemma app_s_f_v_s_table_get_is:
  assumes "app_s_f_v_s_table_get x tabinsts f v_s = (v_s', res)"
  shows "res = Step_normal \<and> ((tabs s = tabinsts) \<longrightarrow> \<lparr>s;f;(v_stack_to_es v_s)@[$Table_get x]\<rparr> \<leadsto> \<lparr>s;f;(v_stack_to_es v_s')\<rparr>) \<or>
         (\<exists>str. res = Res_trap str \<and> ((tabs s = tabinsts) \<longrightarrow> \<lparr>s;f;(v_stack_to_es v_s)@[$Table_get x]\<rparr> \<leadsto> \<lparr>s;f;(v_stack_to_es v_s')@[Trap]\<rparr>)) \<or>
         res = crash_invalid"
  using progress_L0_left[OF reduce.table_get] progress_L0_left[OF reduce.table_get_fail] assms
  unfolding app_s_f_v_s_table_get_def v_to_e_def
  by (auto  split: list.splits cvtop.splits if_splits option.splits v.splits v_num.splits v_vec.splits)

lemma app_s_f_v_s_table_init_is:
  assumes "app_s_f_v_s_table_init x y tabinsts eleminsts f v_s = (tabinsts', v_s', es, res)"
  shows "res = Step_normal \<and> ((tabs s = tabinsts \<and> elems s = eleminsts) \<longrightarrow> reduce_trans (s,f,(v_stack_to_es v_s)@[$Table_init x y]) (s\<lparr>tabs:=tabinsts'\<rparr>,f,(v_stack_to_es v_s')@es) )  \<or>
         (\<exists>str. res = Res_trap str \<and> tabinsts = tabinsts' \<and> ((tabs s = tabinsts \<and> elems s = eleminsts) \<longrightarrow> \<lparr>s;f;(v_stack_to_es v_s)@[$Table_init x y]\<rparr> \<leadsto> \<lparr>s\<lparr>tabs:=tabinsts'\<rparr>;f;(v_stack_to_es v_s')@es@[Trap]\<rparr>)) \<or>
         res = crash_invalid"
proof(cases "res = crash_invalid")
  case True
  then show ?thesis by simp
next
  case False
  then have h_res: "res \<noteq> crash_invalid " by simp
  then obtain i n src dest v_s'' where v_s''_def:
    "f_inst f = i"
    "v_s = (V_num (ConstInt32 n))#(V_num (ConstInt32 src))#(V_num (ConstInt32 dest))#v_s''"
    using assms app_s_f_v_s_table_init_def by (auto split: list.splits v.splits v_num.splits)
  then obtain ta ndest nsrc nn tab ea el where ta_is:
    "(stab_ind (f_inst f) x) = Some ta"
    "ndest = nat_of_int dest"
    "nsrc = nat_of_int src"
    "nn = nat_of_int n"
    "tab = (tabinsts)!ta"
    "ea = (inst.elems (f_inst f))!y"
    "el = eleminsts!ea"
    using assms False app_s_f_v_s_table_init_def by (auto split: option.splits list.splits v.splits v_num.splits)
  then show ?thesis
  proof(cases "(nsrc+nn > length (snd el) \<or> ndest+nn > length (snd tab))")
    case True
    then have "app_s_f_v_s_table_init x y tabinsts eleminsts f v_s = (tabinsts, v_s'', [], Res_trap (STR ''table_init''))"
      using ta_is v_s''_def assms app_s_f_v_s_table_init_def[of x y tabinsts eleminsts f v_s]  False
      by (auto simp add: False Let_def split:  if_splits v_num.splits option.splits )
    then have "tabinsts = tabinsts'" "v_s'' = v_s'" "es = []" "res = Res_trap STR ''table_init''"
      using assms by auto
    moreover have "((tabs s = tabinsts \<and> elems s = eleminsts) \<longrightarrow> \<lparr>s;f;(v_stack_to_es v_s)@[$Table_init x y]\<rparr> \<leadsto> \<lparr>s\<lparr>tabs:=tabinsts'\<rparr>;f;(v_stack_to_es v_s')@es@[Trap]\<rparr>)"
      using calculation v_s''_def progress_L0_left[OF reduce.table_init_trap[OF ta_is(1)], of s tab y ea el ndest dest nsrc src nn n] ta_is
      apply (auto simp add: Let_def split: list.splits cvtop.splits if_splits option.splits v.splits v_num.splits v_vec.splits)
      by (metis True progress_L0_left table_init_trap v.simps(10) v_to_e_def)
    ultimately show ?thesis by auto

  next
    case False
    then show ?thesis
    proof(cases nn)
      case 0
      then have h_n: "nsrc \<le> length (snd el)" "ndest \<le> tab_size tab"
        using False by simp_all
      then have "app_s_f_v_s_table_init x y tabinsts eleminsts f v_s = (tabinsts, v_s'', [], Step_normal)"
        using ta_is v_s''_def assms app_s_f_v_s_table_init_def[of x y tabinsts eleminsts f v_s]  False 0
        by (auto simp add: False Let_def split:  if_splits v_num.splits option.splits)
      then have "tabinsts = tabinsts'" "v_s'' = v_s'" "es = []" "res = Step_normal"
        using assms by auto
      moreover have "((tabs s = tabinsts \<and> elems s = eleminsts) \<longrightarrow> \<lparr>s;f;(v_stack_to_es v_s)@[$Table_init x y]\<rparr> \<leadsto> \<lparr>s\<lparr>tabs:=tabinsts'\<rparr>;f;(v_stack_to_es v_s')@es\<rparr>)"
        using calculation v_s''_def progress_L0_left[OF reduce.table_init_done[OF ta_is(1)], of s tab y ea el ndest dest nsrc src nn n] ta_is 0 h_n
        apply (auto simp add: Let_def split: list.splits cvtop.splits if_splits option.splits v.splits v_num.splits v_vec.splits)
        using v_to_e_def
        by (metis add.right_neutral append.right_neutral progress_L0_left table_init_done v.simps(10))
      ultimately show ?thesis
        by (metis (no_types, lifting) reduce_trans_app_end reduce_trans_def rtranclp.rtrancl_refl)
    next
      case (Suc nn_pred)
      then have h_n: "nsrc < length (snd el)" "ndest < tab_size tab" "nsrc \<le> length (snd el)" "ndest \<le> tab_size tab"
        using False by simp_all
      obtain val where val_is: "val = (snd el)!nsrc"
        by fastforce
      obtain tabinsts'' where tabinsts''_is:
        "store_tabs1 tabinsts ta (nat_of_int dest) val = Some tabinsts''"
        using h_n
        by (simp add: store_tab1_def store_tabs1_def ta_is(2) ta_is(5))
      then have tabinsts''_prop1:
        "(tabinsts'', v_s'', Step_normal) = app_s_f_v_s_table_set x tabinsts f ((V_ref val)#(V_num (ConstInt32 dest))#v_s'')"
        
        using app_s_f_v_s_table_set_def ta_is(1) by (auto split: prod.splits list.splits v.splits v_num.splits)
      then have tabinsts''_prop2: "app_s_f_v_s_table_init x y tabinsts eleminsts f v_s = (tabinsts'', (V_num (ConstInt32 (int_of_nat nn_pred)))#(V_num (ConstInt32 (int_of_nat (nsrc+1))))#(V_num (ConstInt32 (int_of_nat (ndest+1))))#v_s'', [$Table_init x y], Step_normal)"
        using ta_is v_s''_def assms app_s_f_v_s_table_init_def[of x y tabinsts eleminsts f v_s]  False h_n Suc
        apply (auto simp add: False Let_def split: nat.splits if_splits v_num.splits option.splits )
        using val_is
        by (metis (no_types, lifting) old.prod.case)
      let ?c_table_set = "[$EConstNum (ConstInt32 dest), $C V_ref val, $Table_set x]"
      let ?c_table_init2 = "[$EConstNum (ConstInt32 (int_of_nat (ndest + 1))), $EConstNum (ConstInt32 (int_of_nat (nsrc + 1))),
                       $EConstNum (ConstInt32 (int_of_nat nn_pred)), $Table_init x y]"
     have a:
        "tabinsts' = tabinsts''"
        "v_s' = (V_num (ConstInt32 (int_of_nat nn_pred)))#(V_num (ConstInt32 (int_of_nat (nsrc+1))))#(V_num (ConstInt32 (int_of_nat (ndest+1))))#v_s''"
        "es = [$Table_init x y]"
        "res = Step_normal"
        using assms tabinsts''_prop2 by fastforce+
      moreover have
        "(s.tabs s = tabinsts \<and> s.elems s = eleminsts \<longrightarrow> \<lparr>s;f;v_stack_to_es v_s @ [$Table_init x y]\<rparr> \<leadsto> \<lparr>s;f;v_stack_to_es v_s'' @ ?c_table_set @ ?c_table_init2\<rparr>)"
        using progress_L0_left[OF reduce.table_init[OF ta_is(1)], of s tab ea y el ndest dest nsrc src nn n nn_pred val] 
        ta_is val_is v_s''_def h_n False local.Suc v_to_e_def by force
      moreover have
        "(s.tabs s = tabinsts \<longrightarrow> \<lparr>s;f;v_stack_to_es v_s'' @  ?c_table_set\<rparr> \<leadsto> \<lparr>s\<lparr>tabs:=tabinsts''\<rparr>;f;v_stack_to_es v_s''\<rparr>)"
        using progress_L0_left[OF reduce.table_set[OF ta_is(1)], of s dest val tabinsts''] tabinsts''_is v_to_e_def calculation(2)
        by auto
      moreover have
        "(s.tabs s = tabinsts \<and> s.elems s = eleminsts \<longrightarrow> \<lparr>s;f;v_stack_to_es v_s'' @ ?c_table_set @ ?c_table_init2\<rparr> \<leadsto> \<lparr>s\<lparr>tabs:=tabinsts''\<rparr>;f;v_stack_to_es v_s'' @ ?c_table_init2\<rparr>)"
        using progress_L0[of s f "v_stack_to_es v_s'' @  ?c_table_set"  "s\<lparr>tabs:=tabinsts''\<rparr>" f "v_stack_to_es v_s''" "[]" ?c_table_init2]
        calculation
        by simp
      moreover have "(s.tabs s = tabinsts \<and> s.elems s = eleminsts \<longrightarrow> reduce_trans (s,f,v_stack_to_es v_s @ [$Table_init x y]) (s\<lparr>tabs:=tabinsts''\<rparr>,f,v_stack_to_es v_s'' @?c_table_init2))"
        using calculation(5,7) v_s''_def(2)
         by (metis (no_types, lifting) reduce_trans_app_end reduce_trans_def rtranclp.rtrancl_refl)
      then show ?thesis
        using a v_s''_def v_to_e_def
        by auto
    qed
  qed
qed

(*
  \<comment> \<open>\<open>table set\<close>\<close>
| table_set: "\<lbrakk>stab_ind (f_inst f) ti = Some a; store_tabs1 (tabs s) a (nat_of_int n) vr = Some tabs'\<rbrakk> \<Longrightarrow> \<lparr>s;f;[$(EConstNum (ConstInt32 n)), Ref vr, $(Table_set ti)]\<rparr> \<leadsto> \<lparr>s\<lparr>tabs:= tabs'\<rparr>;f;[]\<rparr>"
  \<comment> \<open>\<open>table set fail\<close>\<close>
| table_set_fail: "\<lbrakk>(stab_ind (f_inst f) ti = None) \<or> (stab_ind (f_inst f) ti = Some a \<and> store_tabs1 (tabs s) a (nat_of_int n) vr = None)\<rbrakk> \<Longrightarrow> \<lparr>s;f;[$(EConstNum (ConstInt32 n)), Ref vr, $(Table_set ti)]\<rparr> \<leadsto> \<lparr>s;f;[Trap]\<rparr>"
*)

(*
lemma app_s_f_init_mem_is:
  assumes "app_s_f_init_mem off bs ms f = (ms', res)"
  shows "(res = Step_normal \<and> ((mems s = ms) \<longrightarrow> \<lparr>s;f;(v_stack_to_es v_s)@[Init_mem off bs]\<rparr> \<leadsto> \<lparr>s\<lparr>mems:=ms'\<rparr>;f;(v_stack_to_es v_s)\<rparr>)) \<or>
         (\<exists>str. res = Res_trap str \<and> ms = ms' \<and> ((mems s = ms) \<longrightarrow> \<lparr>s;f;(v_stack_to_es v_s)@[Init_mem off bs]\<rparr> \<leadsto> \<lparr>s;f;(v_stack_to_es v_s)@[Trap]\<rparr>)) \<or>
         (res = crash_invalid)"
  using progress_L0_left[OF reduce.init_mem_Some] progress_L0_left[OF reduce.init_mem_None] assms
  unfolding app_s_f_init_mem_def
  apply (simp split: list.splits cvtop.splits if_splits option.splits v.splits)
  apply metis
  apply fastforce
  done

lemma app_s_f_init_tab_is:
  assumes "app_s_f_init_tab off icls ts f = (ts', res)"
  shows "(res = Step_normal \<and> ((tabs s = ts) \<longrightarrow> \<lparr>s;f;(v_stack_to_es v_s)@[Init_tab off icls]\<rparr> \<leadsto> \<lparr>s\<lparr>tabs:=ts'\<rparr>;f;(v_stack_to_es v_s)\<rparr>)) \<or>
         (\<exists>str. res = Res_trap str \<and> ts = ts' \<and> ((tabs s = ts) \<longrightarrow> \<lparr>s;f;(v_stack_to_es v_s)@[Init_tab off icls]\<rparr> \<leadsto> \<lparr>s;f;(v_stack_to_es v_s)@[Trap]\<rparr>)) \<or>
         (res = crash_invalid)"
  using progress_L0_left[OF reduce.init_tab_Some] progress_L0_left[OF reduce.init_tab_None] assms
  unfolding app_s_f_init_tab_def
  apply (simp split: list.splits cvtop.splits if_splits option.splits v.splits)
  apply metis
  apply fastforce
  done
*)

fun es_redex_to_es :: "e list \<Rightarrow> redex \<Rightarrow> e list" where
  "es_redex_to_es es (Redex v_sr esr b_esr) = v_stack_to_es v_sr @ es @ esr @ ($*b_esr)"

fun es_label_context_to_es :: "e list \<Rightarrow> label_context \<Rightarrow> e list" where
  "es_label_context_to_es es (Label_context v_so eso n esc) = (v_stack_to_es v_so)@[Label n ($*esc) es]@($*eso)"

fun es_label_contexts_to_es :: "e list \<Rightarrow> label_context list \<Rightarrow> e list" where
  "es_label_contexts_to_es es [] = es"
| "es_label_contexts_to_es es (lc#lcs) = (let esl =  es_label_context_to_es es lc in es_label_contexts_to_es esl lcs)"

fun es_frame_context_to_e :: "e list \<Rightarrow> frame_context \<Rightarrow> e" where
  "es_frame_context_to_e es (Frame_context rdx lcs n f) =
   (let esl = es_redex_to_es es rdx in
    Frame n f (es_label_contexts_to_es esl lcs))"

fun es_frame_context_to_config :: "e list \<Rightarrow> frame_context \<Rightarrow> (f \<times> e list)" where
  "es_frame_context_to_config es (Frame_context rdx lcs n f) =
   (let esl = es_redex_to_es es rdx in
    (f, (es_label_contexts_to_es esl lcs)))"

fun es_frame_contexts_to_config :: "e list \<Rightarrow> frame_context \<Rightarrow> frame_context list \<Rightarrow> (f \<times> e list)" where
  "es_frame_contexts_to_config es fc [] = (es_frame_context_to_config es fc)"
| "es_frame_contexts_to_config es fc (fc'#fcs) =
     (let e' = es_frame_context_to_e es fc in es_frame_contexts_to_config [e'] fc' fcs)"

lemma es_frame_contexts_to_config_e_one:
  "es_frame_contexts_to_config [e] (Frame_context (Redex v_s es b_es) lcs nf f) fcs = 
     es_frame_contexts_to_config [] (Frame_context (Redex v_s (e#es) b_es) lcs nf f) fcs"
  by (cases fcs) auto

lemma es_frame_contexts_to_config_b_e_one:
  "es_frame_contexts_to_config [$b_e] (Frame_context (Redex v_s [] b_es) lcs nf f) fcs = 
     es_frame_contexts_to_config [] (Frame_context (Redex v_s [] (b_e#b_es)) lcs nf f) fcs"
  by (cases fcs) auto

lemma es_frame_contexts_to_config_b_es:
  "es_frame_contexts_to_config [] (Frame_context (Redex v_s es b_es) lcs nf f) fcs =
     es_frame_contexts_to_config [] (Frame_context (Redex v_s (es @ ($* b_es)) []) lcs nf f) fcs"
  apply (cases fcs)
  by simp_all

lemma es_frame_contexts_to_config_v_s:
  "es_frame_contexts_to_config [] (Frame_context (Redex v_s es b_es) lcs nf f) fcs =
     es_frame_contexts_to_config [] (Frame_context (Redex [] (($C* (rev v_s)) @ es) b_es) lcs nf f) fcs"
  apply (cases fcs)
   apply simp_all
  done

lemma es_frame_contexts_to_config_b_es_v_s:
    "es_frame_contexts_to_config [] (Frame_context (Redex (v_s) es b_es) lcs nf f) fcs =
     es_frame_contexts_to_config [] (Frame_context (Redex [] (($C* (rev v_s)) @ es @ ($* b_es)) []) lcs nf f) fcs"
  apply (cases fcs)
  using es_frame_contexts_to_config_b_es es_frame_contexts_to_config_v_s
  by simp_all

(*
lemma es_frame_contexts_to_config_b_e_split_v_s_b_s:
  "es_frame_contexts_to_config [] (Frame_context (Redex (v_s'@v_s) [] b_es) lcs nf f) fcs =
     es_frame_contexts_to_config [] (Frame_context (Redex v_s [] ((v_stack_to_b_es v_s')@b_es)) lcs nf f) fcs"
  apply (cases fcs)
   apply simp_all
 
  apply (metis comp_apply)+
  done *)


lemma es_frame_contexts_to_config_b_e_step:
  "es_frame_contexts_to_config [$b_e] (Frame_context (Redex (v_s'@v_s) [] b_es) lcs nf f) fcs =
     es_frame_contexts_to_config [] (Frame_context (Redex v_s ($C* (rev v_s')) (b_e#b_es)) lcs nf f) fcs"
  using es_frame_contexts_to_config_b_e_one es_frame_contexts_to_config_b_es_v_s es_frame_contexts_to_config_b_es es_frame_contexts_to_config_v_s
  by (metis append.left_neutral map_append rev_append)

(*
lemma es_frame_contexts_to_config_b_e_step:
  "es_frame_contexts_to_config [$b_e] (Frame_context (Redex (v_s'@v_s) [] b_es) lcs nf f) fcs =
     es_frame_contexts_to_config [] (Frame_context (Redex v_s [] ((v_stack_to_b_es v_s')@b_e#b_es)) lcs nf f) fcs"
  using es_frame_contexts_to_config_b_e_one es_frame_contexts_to_config_b_e_split_v_s_b_s
  by simp
*)

lemma es_redex_to_es_LN:
  assumes "\<lparr>s; f; es\<rparr> \<leadsto> \<lparr>s'; f'; es'\<rparr>"
  shows "\<lparr>s; f; es_redex_to_es es rdx\<rparr> \<leadsto> \<lparr>s'; f'; es_redex_to_es es' rdx\<rparr>"
  using assms progress_L0
  by (cases rdx) auto

lemma es_redex_to_es_LN_irrtrans:
  assumes "reduce_irrtrans (s, f, es) (s', f', es')"
  shows  "reduce_irrtrans (s, f, es_redex_to_es es rdx) (s', f', es_redex_to_es es' rdx)"
  using assms
  unfolding reduce_irrtrans_def
proof (induction "(s, f, es)" "(s', f', es')" arbitrary: s' f' es' rule: tranclp.induct)
case r_into_trancl
  thus ?case
    by (simp add: es_redex_to_es_LN tranclp.r_into_trancl)
next
  case (trancl_into_trancl b)
  thus ?case
    by (simp add: es_redex_to_es_LN tranclp.trancl_into_trancl split: prod.splits)
qed

lemma es_label_contexts_to_es_app:
  assumes "es_label_contexts_to_es es lcs = esl"
  shows "es_label_contexts_to_es es (lcs@lcs') = es_label_contexts_to_es esl lcs'"
  using assms
  by (induction es lcs arbitrary: esl rule: es_label_contexts_to_es.induct) auto

lemma es_label_contexts_to_es_snoc:
  assumes "es_label_contexts_to_es es lcs = esl"
  shows "es_label_contexts_to_es es (lcs@[lc]) = es_label_context_to_es esl lc"
  using es_label_contexts_to_es_app[OF assms, of "[lc]"]
  by simp

lemma es_label_context_to_es_LN:
  assumes "\<lparr>s; f; es\<rparr> \<leadsto> \<lparr>s'; f'; es'\<rparr>"
  shows "\<lparr>s; f; es_label_context_to_es es lc\<rparr> \<leadsto> \<lparr>s'; f'; es_label_context_to_es es' lc\<rparr>"
  using assms progress_L1[OF assms(1)]
  apply (cases lc)
  apply auto
  done

lemma es_label_context_to_es_LN_irrtrans:
  assumes "reduce_irrtrans (s, f, es) (s', f', es')"
  shows "reduce_irrtrans (s, f, es_label_context_to_es es lc) (s', f', es_label_context_to_es es' lc)"
  using assms
  unfolding reduce_irrtrans_def
proof (induction "(s, f, es)" "(s', f', es')" arbitrary: s' f' es' rule: tranclp.induct)
case r_into_trancl
  thus ?case
    by (simp add: es_label_context_to_es_LN tranclp.r_into_trancl)
next
  case (trancl_into_trancl b)
  thus ?case
    by (simp add: es_label_context_to_es_LN tranclp.trancl_into_trancl split: prod.splits)
qed

lemma es_label_contexts_to_es_lfilled:
  assumes "es_label_contexts_to_es es lcs = esl"
          "es_label_contexts_to_es es' lcs = esl'"
        shows "\<exists>lholed. Lfilled (length lcs) lholed es esl \<and> Lfilled (length lcs) lholed es' esl'"
  using assms
proof (induction lcs arbitrary: esl esl' rule: List.rev_induct)
  case Nil
  thus ?case
    using Lfilled.intros(1)[of _ "[]" "[]"]
    by auto
next
  case (snoc x xs)
  obtain esl_a esl'_a lholed' where 0:
    "es_label_contexts_to_es es xs = esl_a"
    "es_label_contexts_to_es es' xs = esl'_a"
    "Lfilled (length xs) lholed' es esl_a"
    "Lfilled (length xs) lholed' es' esl'_a"
    using snoc(1)
    by fastforce
  thus ?case
    using es_label_contexts_to_es_snoc[OF 0(1), of x] Lfilled.intros(2)[OF _ 0(3)]
          es_label_contexts_to_es_snoc[OF 0(2), of x] Lfilled.intros(2)[OF _ 0(4)]
          snoc(2,3)
    apply (cases x)
    apply fastforce
    done
qed

lemma es_label_contexts_to_es_lfilled1:
  assumes "es_label_contexts_to_es es lcs = esl"
        shows "\<exists>lholed. Lfilled (length lcs) lholed es esl"
  using es_label_contexts_to_es_lfilled[OF assms assms]
  by blast

lemma es_label_contexts_to_es_LN:
  assumes "\<lparr>s; f; es\<rparr> \<leadsto> \<lparr>s'; f'; es'\<rparr>"
        shows "\<lparr>s; f; es_label_contexts_to_es es lcs\<rparr> \<leadsto> \<lparr>s'; f'; es_label_contexts_to_es es' lcs\<rparr>"
  using assms
proof (induction lcs rule: List.rev_induct)
  case Nil
  thus ?case
    by auto
next
  case (snoc x xs)
  thus ?case
    using es_label_contexts_to_es_snoc
    by (metis es_label_context_to_es_LN)
qed

lemma es_label_contexts_to_es_LN_irrtrans:
  assumes "reduce_irrtrans (s, f, es) (s', f', es')"
  shows "reduce_irrtrans (s, f, es_label_contexts_to_es es lcs) (s', f', es_label_contexts_to_es es' lcs)"
  using assms
  unfolding reduce_irrtrans_def
proof (induction "(s, f, es)" "(s', f', es')" arbitrary: s' f' es' rule: tranclp.induct)
case r_into_trancl
  thus ?case
    by (simp add: es_label_contexts_to_es_LN tranclp.r_into_trancl)
next
  case (trancl_into_trancl b)
  thus ?case
    by (simp add: es_label_contexts_to_es_LN tranclp.trancl_into_trancl split: prod.splits)
qed

lemma es_frame_contexts_to_config_snoc:
  assumes "es_frame_contexts_to_config es fc_inner fcs = (f,esfc)"
  shows "es_frame_contexts_to_config es fc_inner (fcs@[fc]) = (es_frame_context_to_config ([Frame (frame_arity_outer fc_inner fcs) f esfc]) fc)"
  using assms
proof (induction es fc_inner fcs rule: es_frame_contexts_to_config.induct)
  case (1 es fc')
  then show ?case
    by (cases fc') (auto simp add: frame_arity_outer_def)
next
  case (2 es fc fc' fcs)
  then show ?case
    by (cases fc') (auto simp add: frame_arity_outer_def)
qed

lemma es_frame_context_to_config_ctx:
  assumes "\<lparr>s;f;es\<rparr> \<leadsto> \<lparr>s';f';es'\<rparr>"
          "es_frame_context_to_config ([Frame n f es]) fc = (f_fc, es_fc)"
  shows "\<exists>es_fc'. \<lparr>s;f_fc;es_fc\<rparr> \<leadsto> \<lparr>s';f_fc;es_fc'\<rparr> \<and> es_frame_context_to_config ([Frame n f' es']) fc = (f_fc, es_fc')"
proof -
  obtain v_sr esr b_esr lcs nf f_c rdx where fc_is:"fc = Frame_context rdx lcs nf f_c"
                                                   "rdx = Redex v_sr esr b_esr"
    by (metis frame_context.exhaust redex.exhaust)
  have "\<lparr>s;f_c;es_label_contexts_to_es (v_stack_to_es v_sr @ (Frame n f es) # esr @ ($* b_esr)) lcs\<rparr> \<leadsto>
          \<lparr>s';f_c;es_label_contexts_to_es (v_stack_to_es v_sr @ (Frame n f' es') # esr @ ($* b_esr)) lcs\<rparr>"
    using progress_L0[OF reduce.local[OF assms(1)]] es_label_contexts_to_es_LN
    by simp
  thus ?thesis
    using assms(2) fc_is
    by simp
qed

lemma es_frame_context_to_config_ctx_irrtrans:
  assumes "reduce_irrtrans (s, f, es) (s', f', es')"
          "es_frame_context_to_config ([Frame n f es]) fc = (f_fc, es_fc)"
  shows "\<exists>es_fc'. reduce_irrtrans (s,f_fc,es_fc) (s',f_fc,es_fc') \<and> es_frame_context_to_config ([Frame n f' es']) fc = (f_fc, es_fc')"
  using assms
  unfolding reduce_irrtrans_def
proof (induction "(s, f, es)" "(s', f', es')" arbitrary: s' f' es' rule: tranclp.induct)
  case r_into_trancl
  show ?case
    using es_frame_context_to_config_ctx[OF _ r_into_trancl(2)] r_into_trancl(1)
    by fastforce
next
  case (trancl_into_trancl b)
  obtain s'' f'' es'' where a: "b = (s'', f'', es'')"
                               "(\<lambda>(s, f, es) (s', x, y). \<lparr>s;f;es\<rparr> \<leadsto> \<lparr>s';x;y\<rparr>)\<^sup>+\<^sup>+ (s, f, es) (s'', f'', es'')"
                               "\<lparr>s'';f'';es''\<rparr> \<leadsto> \<lparr>s';f';es'\<rparr>"
    using trancl_into_trancl(1,3)
    by (simp split: prod.splits)
  then obtain es_fc'' where b:
       "(\<lambda>(s, f, es) (s', x, y). \<lparr>s;f;es\<rparr> \<leadsto> \<lparr>s';x;y\<rparr>)\<^sup>+\<^sup>+ (s, f_fc, es_fc) (s'', f_fc, es_fc'')"
       "es_frame_context_to_config [Frame n f'' es''] fc = (f_fc, es_fc'')"
    using trancl_into_trancl(2,4)
    by blast
  obtain es_fc' where c:
       "\<lparr>s'';f_fc;es_fc''\<rparr> \<leadsto> \<lparr>s';f_fc;es_fc'\<rparr>"
       "es_frame_context_to_config [Frame n f' es'] fc = (f_fc, es_fc')"
    using a(3) b(2) es_frame_context_to_config_ctx
    by blast
  thus ?case
    using a b
    by (metis (no_types, lifting) reduce_trans_app_end reduce_trans_def rtranclp.simps tranclp_rtranclp_tranclp)
qed

lemma es_frame_context_to_e_ctx:
  assumes "\<lparr>s;f;es\<rparr> \<leadsto> \<lparr>s';f';es'\<rparr>"
  shows "\<lparr>s;f_arb;[es_frame_context_to_e es (Frame_context rdx lcs nf f)]\<rparr> \<leadsto> \<lparr>s';f_arb;[es_frame_context_to_e es' (Frame_context rdx lcs nf f')]\<rparr>"
  using reduce.local
        es_label_contexts_to_es_LN
        progress_L0[OF assms]
  apply (cases rdx)
  apply fastforce
  done

lemma es_frame_context_to_e_ctx_irrtrans:
  assumes "reduce_irrtrans (s, f, es) (s', f', es')"
  shows "reduce_irrtrans (s,f_arb,[es_frame_context_to_e es (Frame_context rdx lcs nf f)]) (s',f_arb,[es_frame_context_to_e es' (Frame_context rdx lcs nf f')])"
  using assms
  unfolding reduce_irrtrans_def
proof (induction "(s, f, es)" "(s', f', es')" arbitrary: s' f' es' rule: tranclp.induct)
case r_into_trancl
  thus ?case
    by (simp add: es_label_contexts_to_es_LN es_redex_to_es_LN local tranclp.r_into_trancl)
next
  case (trancl_into_trancl b)
  obtain s'' f'' es'' where a: "b = (s'', f'', es'')"
                               "(\<lambda>(s, f, es) (s', x, y). \<lparr>s;f;es\<rparr> \<leadsto> \<lparr>s';x;y\<rparr>)\<^sup>+\<^sup>+ (s, f, es) (s'', f'', es'')"
                               "\<lparr>s'';f'';es''\<rparr> \<leadsto> \<lparr>s';f';es'\<rparr>"
    using trancl_into_trancl(1,3)
    by (simp split: prod.splits)
  hence b:
       "(\<lambda>(s, f, es) (s', x, y). \<lparr>s;f;es\<rparr> \<leadsto> \<lparr>s';x;y\<rparr>)\<^sup>+\<^sup>+
          (s, f_arb, [es_frame_context_to_e es (Frame_context rdx lcs nf f)])
            (s'', f_arb, [es_frame_context_to_e es'' (Frame_context rdx lcs nf f'')])"
    using trancl_into_trancl(2)
    by blast
  hence "\<lparr>s'';f_arb;[es_frame_context_to_e es'' (Frame_context rdx lcs nf f'')]\<rparr> \<leadsto> \<lparr>s';f_arb;[es_frame_context_to_e es' (Frame_context rdx lcs nf f')]\<rparr>"
    using a b es_frame_context_to_e_ctx
    by blast
  thus ?case
    using a b
    by (metis (no_types, lifting) reduce_trans_app_end reduce_trans_def rtranclp.simps tranclp_rtranclp_tranclp)
qed

lemma es_frame_contexts_to_config_ctx:
  assumes "\<lparr>s;f;es\<rparr> \<leadsto> \<lparr>s';f';es'\<rparr>"
          "es_frame_contexts_to_config es (Frame_context rdx lcs nf f) fcs = (f_fc,es_fc)"
  shows "\<exists>f_fc' es_fc'. \<lparr>s;f_fc;es_fc\<rparr> \<leadsto> \<lparr>s';f_fc';es_fc'\<rparr> \<and> es_frame_contexts_to_config es' (Frame_context rdx lcs nf f') fcs = (f_fc',es_fc')"
  using assms
proof (induction fcs arbitrary: f_fc es_fc rule: List.rev_induct)
  case Nil
  thus ?case
    using es_label_contexts_to_es_LN[OF es_redex_to_es_LN[OF Nil(1)]]
    by fastforce
next
  case (snoc x xs)
  obtain f_fci es_fci f_fci' es_fci' where 0:
    "es_frame_contexts_to_config es (Frame_context rdx lcs nf f) xs = (f_fci, es_fci)"
    "\<lparr>s;f_fci;es_fci\<rparr> \<leadsto> \<lparr>s';f_fci';es_fci'\<rparr>"
    "es_frame_contexts_to_config es' (Frame_context rdx lcs nf f') xs = (f_fci', es_fci')"
    using snoc(1)[OF snoc(2)]
    by (metis prod.exhaust)
  have "(frame_arity_outer (Frame_context rdx lcs nf f') xs) = (frame_arity_outer (Frame_context rdx lcs nf f) xs)"
    unfolding frame_arity_outer_def
    by (simp split: if_splits)
  thus ?case
    using es_frame_contexts_to_config_snoc[OF 0(1), of x]
          es_frame_contexts_to_config_snoc[OF 0(3), of x]
          es_frame_context_to_config_ctx[OF 0(2)] snoc(3)
    apply simp
    apply metis+
    done
qed

lemma es_frame_contexts_to_config_ctx_irrtrans:
  assumes "reduce_irrtrans (s, f, es) (s', f', es')"
          "es_frame_contexts_to_config es (Frame_context rdx lcs nf f) fcs = (f_fc,es_fc)"
  shows "\<exists>f_fc' es_fc'. reduce_irrtrans (s,f_fc,es_fc) (s',f_fc',es_fc') \<and> es_frame_contexts_to_config es' (Frame_context rdx lcs nf f') fcs = (f_fc',es_fc')"
  using assms
  unfolding reduce_irrtrans_def
proof (induction "(s, f, es)" "(s', f', es')" arbitrary: s' f' es' rule: tranclp.induct)
  case r_into_trancl
  show ?case
    using es_frame_contexts_to_config_ctx[OF _ r_into_trancl(2)] r_into_trancl(1)
    by fastforce
next
  case (trancl_into_trancl b)
  obtain s'' f'' es'' where a: "b = (s'', f'', es'')"
                               "(\<lambda>(s, f, es) (s', x, y). \<lparr>s;f;es\<rparr> \<leadsto> \<lparr>s';x;y\<rparr>)\<^sup>+\<^sup>+ (s, f, es) (s'', f'', es'')"
                               "\<lparr>s'';f'';es''\<rparr> \<leadsto> \<lparr>s';f';es'\<rparr>"
    using trancl_into_trancl(1,3)
    by (simp split: prod.splits)
  then obtain f_fc'' es_fc'' where b:
       "(\<lambda>(s, f, es) (s', x, y). \<lparr>s;f;es\<rparr> \<leadsto> \<lparr>s';x;y\<rparr>)\<^sup>+\<^sup>+ (s, f_fc, es_fc) (s'', f_fc'', es_fc'')"
       "es_frame_contexts_to_config es'' (Frame_context rdx lcs nf f'') fcs = (f_fc'',es_fc'')"
    using trancl_into_trancl(2)[OF a(1) trancl_into_trancl(4)]
    by blast
  obtain f_fc' es_fc' where c:
       "\<lparr>s'';f_fc'';es_fc''\<rparr> \<leadsto> \<lparr>s';f_fc';es_fc'\<rparr>"
       "es_frame_contexts_to_config es' (Frame_context rdx lcs nf f') fcs = (f_fc', es_fc')"
    using a(3) b(2) es_frame_contexts_to_config_ctx
    by blast
  thus ?case
    using a b
    by (metis (no_types, lifting) reduce_trans_app_end reduce_trans_def rtranclp.simps tranclp_rtranclp_tranclp)
qed


lemma es_frame_contexts_to_config_ctx1:
  assumes "\<lparr>s;f;(v_stack_to_es v_s)@es\<rparr> \<leadsto> \<lparr>s';f';(v_stack_to_es v_s')@es'\<rparr>"
          "es_frame_contexts_to_config es (Frame_context (Redex v_s es_ctx b_es_ctx) lcs nf f) fcs = (f_fc,es_fc)"
  shows "\<exists>f_fc' es_fc'. \<lparr>s;f_fc;es_fc\<rparr> \<leadsto> \<lparr>s';f_fc';es_fc'\<rparr> \<and> es_frame_contexts_to_config [] (Frame_context (update_redex_step (Redex v_s es_ctx b_es_ctx) v_s' es') lcs nf f') fcs = (f_fc',es_fc')"
  using assms
proof (induction fcs arbitrary: s f_fc es_fc rule: List.rev_induct)
  case Nil
  thus ?case
    using es_label_contexts_to_es_LN es_redex_to_es_LN progress_L0[OF Nil(1), of "[]" "es_ctx@($*b_es_ctx)"]
    by fastforce
next
  case (snoc fc fcs')
   obtain f_fci es_fci f_fci' es_fci' where 0:
    "es_frame_contexts_to_config es (Frame_context (Redex v_s es_ctx b_es_ctx) lcs nf f) fcs' = (f_fci, es_fci)"
    "\<lparr>s;f_fci;es_fci\<rparr> \<leadsto> \<lparr>s';f_fci';es_fci'\<rparr>"
    "es_frame_contexts_to_config [] (Frame_context (update_redex_step (Redex v_s es_ctx b_es_ctx) v_s' es') lcs nf f') fcs' = (f_fci', es_fci')"
    using snoc(1)[OF snoc(2)]
    by (metis prod.exhaust)
  have "(frame_arity_outer (Frame_context (update_redex_step (Redex v_s es_ctx b_es_ctx) v_s' es') lcs nf f') fcs') = (frame_arity_outer (Frame_context (Redex v_s es_ctx b_es_ctx) lcs nf f) fcs')"
    unfolding frame_arity_outer_def
    by (simp split: if_splits)
  thus ?case
    using es_frame_contexts_to_config_snoc[OF 0(3), of fc]
          es_frame_contexts_to_config_snoc[OF 0(1), of fc] snoc(3)
          es_frame_context_to_config_ctx[OF 0(2)]
    apply (simp split: if_splits)
    apply metis+
    done
qed

lemma es_frame_contexts_to_config_ctx2:
  assumes "\<lparr>s;f;(v_stack_to_es v_s)@es\<rparr> \<leadsto> \<lparr>s';f';(v_stack_to_es v_s')\<rparr>"
          "es_frame_contexts_to_config es (Frame_context (Redex v_s es_ctx b_es_ctx) lcs nf f) fcs = (f_fc,es_fc)"
  shows "\<exists>f_fc' es_fc'. \<lparr>s;f_fc;es_fc\<rparr> \<leadsto> \<lparr>s';f_fc';es_fc'\<rparr> \<and> es_frame_contexts_to_config [] (Frame_context (update_redex_step (Redex v_s es_ctx b_es_ctx) v_s' []) lcs nf f') fcs = (f_fc',es_fc')"
proof -
  have 1:"\<lparr>s;f;(v_stack_to_es v_s)@es\<rparr> \<leadsto> \<lparr>s';f';(v_stack_to_es v_s'@[])\<rparr>"
    using assms
    by simp
  thus ?thesis
    using es_frame_contexts_to_config_ctx1[OF 1]
    by (simp add: assms(2))
qed

lemma es_frame_contexts_to_config_trap_ctx:
  assumes "\<lparr>s;f;(v_stack_to_es v_s)@es\<rparr> \<leadsto> \<lparr>s';f';(v_stack_to_es v_s')@[Trap]\<rparr>"
          "es_frame_contexts_to_config es (Frame_context (Redex v_s es_ctx b_es_ctx) lcs nf f) fcs = (f_fc,es_fc)"
  shows "\<exists>f_fc' es_fc'. \<lparr>s;f_fc;es_fc\<rparr> \<leadsto> \<lparr>s';f_fc';es_fc'\<rparr> \<and> es_frame_contexts_to_config [Trap] (Frame_context (update_redex_step (Redex v_s es_ctx b_es_ctx) v_s' []) lcs nf f') fcs = (f_fc',es_fc')"
  using assms
proof (induction fcs arbitrary: f_fc es_fc rule: List.rev_induct)
  case Nil
  have "\<lparr>s;f;(v_stack_to_es v_s)@es@es_ctx@($*b_es_ctx)\<rparr> \<leadsto> \<lparr>s';f';(v_stack_to_es v_s')@Trap#es_ctx@($*b_es_ctx)\<rparr>"
    using progress_L0[OF assms(1),of "[]" "es_ctx@($*b_es_ctx)"]
    by (fastforce)
  thus ?case
    using Nil es_label_contexts_to_es_LN
    by auto
next
  case (snoc fc fcs')
  obtain f_fci es_fci f_fci' es_fci' where 0:
    "es_frame_contexts_to_config es (Frame_context (Redex v_s es_ctx b_es_ctx) lcs nf f) fcs' = (f_fci, es_fci)"
    "\<lparr>s;f_fci;es_fci\<rparr> \<leadsto> \<lparr>s';f_fci';es_fci'\<rparr>"
    "es_frame_contexts_to_config [Trap] (Frame_context (update_redex_step (Redex v_s es_ctx b_es_ctx) v_s' []) lcs nf f') fcs' = (f_fci', es_fci')"
    using snoc(1)[OF snoc(2)]
    by (metis prod.exhaust)
  have "(frame_arity_outer (Frame_context (update_redex_step (Redex v_s es_ctx b_es_ctx) v_s' []) lcs nf f') fcs') = (frame_arity_outer (Frame_context (Redex v_s es_ctx b_es_ctx) lcs nf f) fcs')"
    unfolding frame_arity_outer_def
    by (simp split: if_splits)
  thus ?case
    using es_frame_contexts_to_config_snoc[OF 0(3), of fc]
          es_frame_contexts_to_config_snoc[OF 0(1), of fc] snoc(3)
    apply (simp)
    apply (metis (no_types, lifting) 0(2) es_frame_context_to_config_ctx)
    done
qed

lemma es_redex_to_es_to_trap_reduce_trans:
  assumes "reduce_trans (s,f,es) (s',f',[Trap])"
          "es_redex_to_es es rdx = es'"
  shows "reduce_trans (s,f,es') (s',f',[Trap])"
  using assms
  by (metis es_redex_to_es.elims reduce_trans_to_trap_L0)

lemma es_label_context_to_es_to_trap_reduce_trans:
  assumes "reduce_trans (s,f,es) (s',f',[Trap])"
          "es_label_context_to_es es lc = es'"
  shows "reduce_trans (s,f,es') (s',f',[Trap])"
proof -
  obtain v_so eso n esc where lc_is:"lc = (Label_context v_so eso n esc)"
    by (metis label_context.exhaust)
  show ?thesis
    by (metis assms es_label_context_to_es.simps lc_is reduce_trans_to_trap_L0 reduce_trans_to_trap_label)
qed

lemma es_label_contexts_to_es_to_trap_reduce_trans:
  assumes "reduce_trans (s,f,es) (s',f',[Trap])"
          "es_label_contexts_to_es es lcs = es'"
  shows "reduce_trans (s,f,es') (s',f',[Trap])"
  using es_label_contexts_to_es_lfilled1[OF assms(2)]
        assms(1) reduce_trans_to_trap_LN
  by blast

lemma es_frame_contexts_to_config_to_trap_reduce_trans_weak:
  assumes "\<And>f_inner. reduce_trans (s,f_inner,es) (s',f_inner,[Trap])"
          "es_frame_contexts_to_config es fc fcs = (f, es')"
  shows "reduce_trans (s,f,es') (s',f,[Trap])"
  using assms
proof (induction es fc fcs arbitrary: s f es' rule: es_frame_contexts_to_config.induct)
  case (1 es fc)
  thus ?case
    apply (cases fc)
    apply simp
    apply (metis es_label_contexts_to_es_to_trap_reduce_trans es_redex_to_es_to_trap_reduce_trans)
    done
next
  case (2 es fc fc' fcs)
  obtain rdx lcs nf ff where fc_is:"fc = (Frame_context rdx lcs nf ff)"
    by (metis frame_context.exhaust)
  hence "\<And>f_inner. reduce_trans (s,f_inner,[es_frame_context_to_e es fc]) (s',f_inner,[Trap])"
    using fc_is 2(2)
    apply simp
    apply (meson es_label_contexts_to_es_to_trap_reduce_trans es_redex_to_es_to_trap_reduce_trans reduce_trans_to_trap_local)
    done
  thus ?case
    using 2(1,3) fc_is
    by simp
qed

lemma es_frame_contexts_to_config_trap_reduce_trans:
  assumes "es_frame_contexts_to_config [Trap] fc fcs = (f, es)"
  shows "reduce_trans (s,f,es) (s,f,[Trap])"
proof -
  have "(\<And>f_inner. reduce_trans (s, f_inner, [Trap]) (s, f_inner, [Trap]))"
    unfolding reduce_trans_def
    by simp
  thus ?thesis
    using es_frame_contexts_to_config_to_trap_reduce_trans_weak[OF _ assms]
    by simp
qed

lemma run_step_b_e_sound:
  assumes "run_step_b_e b_e (Config d s fc fcs) = ((Config d' s' fc' fcs'), res)"
  shows "(\<exists>f esfc f' esfc'.
            res = Step_normal \<and>
            es_frame_contexts_to_config ([$b_e]) fc fcs = (f,esfc) \<and>
            es_frame_contexts_to_config [] fc' fcs' = (f',esfc') \<and>
            \<lparr>s;f;esfc\<rparr> \<leadsto> \<lparr>s';f';esfc'\<rparr>) \<or>
         (\<exists>f esfc f' esfc'.
            res = Step_normal \<and>
            es_frame_contexts_to_config ([$b_e]) fc fcs = (f,esfc) \<and>
            es_frame_contexts_to_config [] fc' fcs' = (f',esfc') \<and>
            \<lparr>s;f;esfc\<rparr> \<leadsto> \<lparr>s';f';esfc'\<rparr>) \<or>
         (\<exists>str f esfc f' esfc'.
            res = Res_trap str \<and>
            es_frame_contexts_to_config ([$b_e]) fc fcs = (f,esfc) \<and>
            es_frame_contexts_to_config ([Trap]) fc' fcs' = (f',esfc') \<and>
            \<lparr>s;f;esfc\<rparr> \<leadsto> \<lparr>s';f';esfc'\<rparr>) \<or>
         (\<exists>str. res = Res_crash str)"
proof -
  obtain v_s es b_es lcs nf f rdx where fc_is: "fc = (Frame_context rdx lcs nf f)"
                                               "rdx = (Redex v_s es b_es)"
    by (metis frame_context.exhaust redex.exhaust)
  obtain f'' esfc'' where 0:
    "es_frame_contexts_to_config ([$b_e]) (Frame_context (Redex v_s es b_es) lcs nf f) fcs = (f'',esfc'')"
    by (metis prod.exhaust)
  show ?thesis
  proof (cases b_e)
    case Unreachable
    obtain str where 1:
      "res = Res_trap str"
      "s' = s"
      "fcs' = fcs"
      "fc' = fc"
      using assms Unreachable fc_is
      by auto
    obtain f''' esfc''' where
    "\<lparr>s;f'';esfc''\<rparr> \<leadsto> \<lparr>s;f''';esfc'''\<rparr>"
    "es_frame_contexts_to_config [Trap] fc' fcs = (f''', esfc''')"
      using 1(4) fc_is Unreachable es_frame_contexts_to_config_trap_ctx[OF progress_L0_left[OF reduce.basic[OF reduce_simple.unreachable, of s f], of "rev v_s"]] 0
      by simp blast
    thus ?thesis
      using 0 1 fc_is(1,2)
      by fastforce
  next
    case Nop
    have 1:
      "res = Step_normal"
      "s' = s"
      "fcs' = fcs"
      "fc = fc'"
      using Cons assms Nop fc_is
      by fastforce+
    obtain f''' esfc''' where
      "es_frame_contexts_to_config [] (Frame_context rdx lcs nf f) fcs = (f''',esfc''')"
      "\<lparr>s;f'';esfc''\<rparr> \<leadsto> \<lparr>s';f''';esfc'''\<rparr>"
      using es_frame_contexts_to_config_ctx[OF reduce.basic[OF reduce_simple.nop, of s f]] 0 1(2) fc_is(2) Nop
      by blast
    thus ?thesis
      using 0 1 Nop fc_is(1,2)
      by fastforce
  next
    case Drop
    consider
        (a) v_s' where
              "s' = s"
              "fcs' = fcs"
              "fc' = (update_fc_step fc v_s' [])"
              "res = Step_normal"
              "(\<lparr>s;f;(v_stack_to_es v_s)@[$Drop]\<rparr> \<leadsto> \<lparr>s;f;(v_stack_to_es v_s')\<rparr>)"
      | (b) "(res = crash_invalid)"
      using app_v_s_drop_is[of v_s _ res s f] assms Drop fc_is
      by (fastforce split: prod.splits)
    thus ?thesis
    proof (cases)
      case a
      thus ?thesis
        using es_frame_contexts_to_config_ctx2[OF a(5)] Drop fc_is 0
        by simp blast
    qed auto
  next
    case (Select t_tag)
    consider
        (a) v_s' where
              "s' = s"
              "fcs' = fcs"
              "fc' = (update_fc_step fc v_s' [])"
              "res = Step_normal"
              "(\<lparr>s;f;(v_stack_to_es v_s)@[$Select t_tag]\<rparr> \<leadsto> \<lparr>s;f;(v_stack_to_es v_s')\<rparr>)"
      | (b) "(res = crash_invalid)"
      using app_v_s_select_is assms Select fc_is
      by (fastforce split: prod.splits)
    thus ?thesis
    proof (cases)
      case a
      thus ?thesis
        using es_frame_contexts_to_config_ctx2[OF a(5)] Select fc_is Cons 0
        by simp blast
    qed auto
  next
    case (Block tb es_b)
    show ?thesis
    proof (cases "res = Step_normal")
      case True
      then obtain v_bs v_s' lc_b t1s t2s where fc'_is:
              "tb_tf (f_inst f) tb = (t1s _> t2s)"
              "es = []"
              "length v_s \<ge> length t1s"
              "(v_bs, v_s') = split_n v_s (length t1s)"
              "lc_b = (Label_context v_s' b_es (length t2s) [])"
              "s' = s"
              "fcs' = fcs"
              "fc' = (Frame_context (Redex v_bs [] es_b) (lc_b#lcs) nf f)"
        using assms Block fc_is
        by (simp add: Let_def split: tf.splits prod.splits if_splits)
      have fc_red1:"(\<lparr>s;f;(es_redex_to_es [$Block tb es_b] rdx)\<rparr> \<leadsto> \<lparr>s;f;es_label_context_to_es (es_redex_to_es [] (Redex v_bs [] es_b)) lc_b\<rparr>)"
        using progress_L0[OF reduce.block, of "rev v_bs"]
              fc'_is(1,2,3,4,5) split_n_conv_app fc_is
        by simp (metis append_assoc map_append rev_append split_n_length)
      hence fc_red2:"\<And>f. \<lparr>s;f;[es_frame_context_to_e ([$Block tb es_b]) fc]\<rparr> \<leadsto> \<lparr>s;f;[es_frame_context_to_e ([]) fc']\<rparr>"
        using fc_is fc'_is(7,8)
        by (simp add: es_label_contexts_to_es_LN local)
      obtain f''' esfc''' where f'''_is:
        "es_frame_contexts_to_config [] fc' fcs' = (f''', esfc''')"
        by (metis prod.exhaust)
      have "\<lparr>s;f'';esfc''\<rparr> \<leadsto> \<lparr>s';f''';esfc'''\<rparr>"
      proof (cases fcs)
        case Nil
        thus ?thesis
          using f'''_is 0 fc_red1 fc_is fc'_is(1,5,6,7,8) Block
          by simp (meson es_label_contexts_to_es_LN)
      next
        case (Cons a list)
        thus ?thesis
          using f'''_is 0 es_frame_contexts_to_config_ctx[OF fc_red2] fc_is fc'_is(1,5,6,7,8) Block
          by (cases a) fastforce
      qed
      thus ?thesis
        using True fc_is fc'_is(6,7,8) f'''_is 0
        by blast
    next
      case False
      thus ?thesis
        using assms Block fc_is
        by (fastforce simp add: Let_def split: prod.splits tf.splits if_splits)
    qed
  next
    case (Loop tb es_b)
    show ?thesis
    proof (cases "res = Step_normal")
      case True
      then obtain v_bs v_s' lc_b t1s t2s where fc'_is:
              "tb_tf (f_inst f) tb = (t1s _> t2s)"
              "es = []"
              "length v_s \<ge> length t1s"
              "(v_bs, v_s') = split_n v_s (length t1s)"
              "lc_b = (Label_context v_s' b_es (length t1s) [(Loop tb es_b)])"
              "s' = s"
              "fcs' = fcs"
              "fc' = (Frame_context (Redex v_bs [] es_b) (lc_b#lcs) nf f)"
        using assms Loop fc_is
        by (simp add: Let_def split: tf.splits prod.splits if_splits)
      have fc_red1:"(\<lparr>s;f;(es_redex_to_es [$Loop tb es_b] rdx)\<rparr> \<leadsto> \<lparr>s;f;es_label_context_to_es (es_redex_to_es [] (Redex v_bs [] es_b)) lc_b\<rparr>)"
        using progress_L0[OF reduce.loop, of "rev v_bs"]
              fc'_is(1,2,3,4,5) split_n_conv_app fc_is
        by simp (metis append_assoc map_append rev_append split_n_length)
      hence fc_red2:"\<And>f. \<lparr>s;f;[es_frame_context_to_e ([$Loop tb es_b]) fc]\<rparr> \<leadsto> \<lparr>s;f;[es_frame_context_to_e ([]) fc']\<rparr>"
        using fc_is fc'_is(7,8)
        by (simp add: es_label_contexts_to_es_LN local)
      then obtain f''' esfc''' where f'''_is:
        "es_frame_contexts_to_config [] fc' fcs' = (f''', esfc''')"
        by (metis prod.exhaust)
      have "\<lparr>s;f'';esfc''\<rparr> \<leadsto> \<lparr>s';f''';esfc'''\<rparr>"
      proof (cases fcs)
        case Nil
        thus ?thesis
        using f'''_is 0 fc_red1 fc_is fc'_is(1,5,6,7,8) Loop
        by simp (meson es_label_contexts_to_es_LN)
      next
        case (Cons a list)
        thus ?thesis
        using f'''_is 0 es_frame_contexts_to_config_ctx[OF fc_red2] fc_is fc'_is(1,5,6,7,8) Loop
        by (cases a) fastforce
      qed
      thus ?thesis
        using True fc_is fc'_is(6,7,8) f'''_is 0
        by blast
    next
      case False
      thus ?thesis
        using assms Loop fc_is
        by (fastforce simp add: Let_def split: prod.splits tf.splits if_splits)
    qed
  next
    case (If tb esif1 esif2)
    consider
        (a) v_s' es_cont where
              "s' = s"
              "fcs' = fcs"
              "fc' = (update_fc_step fc v_s' es_cont)"
              "res = Step_normal"
              "(\<lparr>s;f;(v_stack_to_es v_s)@[$If tb esif1 esif2]\<rparr> \<leadsto> \<lparr>s;f;(v_stack_to_es v_s')@es_cont\<rparr>)"
      | (b) "(res = crash_invalid)"
      using app_v_s_if_is assms If Cons fc_is
      by (fastforce split: prod.splits)
    thus ?thesis
    proof (cases)
      case a
      thus ?thesis
        using es_frame_contexts_to_config_ctx1[OF a(5)] If fc_is Cons 0
        by simp blast
    qed auto
  next
    case (Br k)
    consider (a) v_ls b_els nl b_ecls v_ls' where
                   "(length lcs > k)"
                   "(Label_context v_ls b_els nl b_ecls) = (lcs!k)"
                   "(length v_s \<ge> nl)"
                   "v_ls' = (take nl v_s)"
                   "s' = s"
                   "fcs' = fcs"
                   "fc' = (Frame_context (Redex (v_ls'@v_ls) [] (b_ecls@b_els)) (drop (Suc k) lcs) nf f)"
                   "res = Step_normal"
           | (b) "((d', s', fcs'), res) = ((d,s,fcs), crash_invalid)"
      using assms Br fc_is Cons
      by (simp split: if_splits prod.splits label_context.splits)
    thus ?thesis
    proof (cases)
      case a
      have 1:"lcs = (take k lcs)@(Label_context v_ls b_els nl b_ecls)#(drop (Suc k) lcs)"
             "length (take k lcs) = k"
        using a(1,2)
        by (simp_all add: Cons_nth_drop_Suc)
      have 2:"\<lparr>s; f; es_label_contexts_to_es (es_redex_to_es [$Br k] rdx) lcs\<rparr> \<leadsto> \<lparr>s; f; es_label_contexts_to_es (es_redex_to_es [] (Redex (v_ls'@v_ls) [] (b_ecls@b_els))) (drop (Suc k) lcs)\<rparr>"
      proof -
        obtain eslk lholed' where eslk_is:"es_label_contexts_to_es (es_redex_to_es [$Br k] rdx) (take k lcs) = eslk"
                                          "Lfilled k lholed' (es_redex_to_es [$Br k] rdx) eslk"
          using es_label_contexts_to_es_lfilled1[of "(es_redex_to_es [$Br k] rdx)" "(take k lcs)"] 1(2)
          by fastforce
        obtain lholed where lholed_is:"Lfilled k lholed ((v_stack_to_es v_ls')@[$Br k]) eslk"
          using eslk_is(2) fc_is a(3,4)
                lfilled_collapse2[of k lholed' "(v_stack_to_es v_s)@[($Br k)]" "es @ ($* b_es)" eslk]
                lfilled_collapse1[of k _ "rev v_s" "[($Br k)]" eslk nl]
          by (fastforce simp add: rev_take)
        have lholed_reduce:"\<lparr>s; f; es_label_context_to_es eslk (lcs!k)\<rparr> \<leadsto> \<lparr>s; f; (v_stack_to_es (v_ls'@v_ls))@($*b_ecls@b_els)\<rparr>"
          using progress_L0[OF reduce.basic[OF reduce_simple.br[OF _ lholed_is]], of nl s f "rev v_ls" "$*b_ecls" "$*b_els"]
                a(3,4) a(2)[symmetric]
          by simp
        have "es_label_contexts_to_es (es_redex_to_es [$Br k] rdx) lcs =
                es_label_contexts_to_es
                  (es_label_context_to_es (es_label_contexts_to_es (es_redex_to_es [$Br k] rdx) (take k lcs)) (lcs!k))
                  ((drop (Suc k) lcs))"
          by (metis 1(1) a(2) es_label_contexts_to_es.simps(2) es_label_contexts_to_es_app)
        thus ?thesis
          using lholed_reduce es_label_contexts_to_es_LN eslk_is(1)
          by auto
      qed
      show ?thesis
      proof (cases fcs)
        case Nil
        thus ?thesis
          using fc_is a Cons 2 Br
          by fastforce
      next
        case (Cons a list)
        have fc_red:"\<And>f. \<lparr>s;f;[es_frame_context_to_e ([$Br k]) fc]\<rparr> \<leadsto> \<lparr>s';f;[es_frame_context_to_e ([]) fc']\<rparr>"
          using 2 fc_is a(5) reduce.local[OF 2, of _ nf] a(7)
          by simp
        obtain f_fc es_fc where
          "es_frame_contexts_to_config [es_frame_context_to_e [$Br k] fc] a list = (f_fc, es_fc)"
          "\<exists>f_fc' es_fc'. \<lparr>s;f_fc;es_fc\<rparr> \<leadsto> \<lparr>s';f_fc';es_fc'\<rparr> \<and>
             es_frame_contexts_to_config [es_frame_context_to_e [] fc'] a list = (f_fc', es_fc')"
          using es_frame_contexts_to_config_ctx[OF fc_red, of _ _ _ _ list] 0 Br fc_is Cons
          apply (cases a)
          apply simp
          done
        thus ?thesis
          using a(6,8) Br fc_is Cons
          by fastforce
      qed
    qed auto
  next
    case (Br_if k)
    consider
        (a) v_s' es_cont where
              "s' = s"
              "fcs' = fcs"
              "fc' = (update_fc_step fc v_s' es_cont)"
              "res = Step_normal"
              "(\<lparr>s;f;(v_stack_to_es v_s)@[$Br_if k]\<rparr> \<leadsto> \<lparr>s;f;(v_stack_to_es v_s')@es_cont\<rparr>)"
      | (b) "(res = crash_invalid)"
      using app_v_s_br_if_is assms Br_if Cons fc_is
      by (fastforce split: prod.splits)
    thus ?thesis
    proof (cases)
      case a
      thus ?thesis
        using es_frame_contexts_to_config_ctx1[OF a(5)] Br_if fc_is 0
        by simp blast
    qed auto
  next
    case (Br_table ks k)
    consider
        (a) v_s' es_cont where
              "s' = s"
              "fcs' = fcs"
              "fc' = (update_fc_step fc v_s' es_cont)"
              "res = Step_normal"
              "(\<lparr>s;f;(v_stack_to_es v_s)@[$Br_table ks k]\<rparr> \<leadsto> \<lparr>s;f;(v_stack_to_es v_s')@es_cont\<rparr>)"
      | (b) "(res = crash_invalid)"
      using app_v_s_br_table_is assms Br_table Cons fc_is
      by (fastforce split: prod.splits)
    thus ?thesis
    proof (cases)
      case a
      thus ?thesis
        using es_frame_contexts_to_config_ctx1[OF a(5)] Br_table fc_is Cons 0
        by simp blast
    qed auto
  next
    case Return
    consider (a) t1 t2 t3 t4 where
                  "(length v_s \<ge> nf)"
                  "(fcs = (Frame_context t1 t2 t3 t4)#fcs')"
                  "s' = s"
                  "fc' = (update_fc_return (Frame_context t1 t2 t3 t4) (take nf v_s))"
                  "res = Step_normal"
           | (b) "((d', s', fcs'), res) = ((d,s,fcs), crash_invalid)"
      using assms Return
      apply (simp split: if_splits prod.splits list.splits frame_context.splits redex.splits)
      apply (metis fc_is(1,2) frame_context.exhaust frame_context.inject redex.inject update_fc_return.simps)
      done
    thus ?thesis
    proof (cases)
      case a
      obtain eslk lholed' where eslk_is:
        "es_label_contexts_to_es (es_redex_to_es [$Return] rdx) lcs = eslk"
        "Lfilled (length lcs) lholed' (es_redex_to_es [$Return] rdx) eslk"
        by (meson es_label_contexts_to_es_lfilled1)
      obtain lholed where lholed_is:
        "Lfilled (length lcs) lholed ((v_stack_to_es (take nf v_s))@[$Return]) eslk"
        using eslk_is(2) fc_is a(3,4)
              lfilled_collapse2[of "(length lcs)" lholed' "(v_stack_to_es v_s)@[($Return)]" "es @ ($* b_es)" eslk]
              lfilled_collapse1[of "(length lcs)" _ "rev v_s" "[($Return)]" eslk nf]
        by (fastforce simp add: rev_take)
      have fc_red:"\<And>f. \<lparr>s;f;[es_frame_context_to_e ([$Return]) fc]\<rparr> \<leadsto> \<lparr>s';f;(v_stack_to_es (take nf v_s))\<rparr>"
        using reduce.basic[OF reduce_simple.return[OF _ lholed_is], of nf s _ f] fc_is eslk_is(1) a(1,3)
        by simp
      obtain f_fc es_fc where f_fc_is:
        "es_frame_contexts_to_config [es_frame_context_to_e [$Return] fc] (Frame_context t1 t2 t3 t4) fcs' = (f_fc, es_fc)"
        by (metis prod.exhaust)
      have
        "\<exists>f_fc' es_fc'. \<lparr>s;f_fc;es_fc\<rparr> \<leadsto> \<lparr>s';f_fc';es_fc'\<rparr> \<and>
           es_frame_contexts_to_config [] fc' fcs' = (f_fc', es_fc')"
        using es_frame_contexts_to_config_ctx[OF fc_red f_fc_is] a(4)
        apply (cases t1)
        apply simp
        apply (cases fcs')
        apply simp_all
        done
      thus ?thesis
        using a Return f_fc_is
        by fastforce
    qed auto
  next
    case (Call k)
    consider
        (a) es' where
              "s' = s"
              "fcs' = fcs"
              "fc' = (update_fc_step fc v_s es')"
              "res = Step_normal"
              "(\<lparr>s;f;(v_stack_to_es v_s)@[$ Call k]\<rparr> \<leadsto> \<lparr>s;f;(v_stack_to_es v_s)@es'\<rparr>)"
      | (b) "(res = crash_invalid)"
      using app_f_call_is assms Call Cons fc_is
      by (simp split: prod.splits) fastforce
    thus ?thesis
    proof (cases)
      case a
      thus ?thesis
        using es_frame_contexts_to_config_ctx1[OF a(5)] Call fc_is 0
        by simp blast
    qed auto
  next
    case (Call_indirect x y)
    obtain v_s' esc where ms'_is:
      "fcs' = fcs"
      "fc' = (update_fc_step fc v_s' esc)"
      "app_s_f_v_s_call_indirect x y (tabs s) (funcs s) f v_s = (v_s',esc,res)"
      "s' = s"
      using Call_indirect Cons assms fc_is
      by (fastforce split: prod.splits)
    consider
        (a)  "res = Step_normal"
             "(\<lparr>s;f;(v_stack_to_es v_s)@[$ Call_indirect x y]\<rparr> \<leadsto> \<lparr>s';f;(v_stack_to_es v_s')@esc\<rparr>)"
      | (b) str where
        "res = Res_trap str"
        "esc = []"
        "\<lparr>s;f;v_stack_to_es v_s @ [$ Call_indirect x y]\<rparr> \<leadsto> \<lparr>s;f;(v_stack_to_es v_s') @ [Trap]\<rparr>"
      | (c) "(res = crash_invalid)"
      using app_s_f_v_s_call_indirect_is[OF ms'_is(3), of s] Call_indirect ms'_is
      by fastforce
    thus ?thesis
    proof (cases)
      case a
      thus ?thesis
        using es_frame_contexts_to_config_ctx1[OF a(2)] 0 Call_indirect fc_is ms'_is(1,2)
        by simp blast
    next
      case b
      thus ?thesis
        using es_frame_contexts_to_config_trap_ctx[OF b(3), of es b_es lcs nf fcs f'' esfc''] 0 Call_indirect fc_is ms'_is(1,2,4)
        by simp blast
    qed auto
  next
    case (Get_local k)
    consider
        (a) v_s' where
              "s' = s"
              "fcs' = fcs"
              "fc' = (update_fc_step fc v_s' [])"
              "res = Step_normal"
              "(\<lparr>s;f;(v_stack_to_es v_s)@[$Get_local k]\<rparr> \<leadsto> \<lparr>s;f;(v_stack_to_es v_s')\<rparr>)"
      | (b) "(res = crash_invalid)"
      using app_f_v_s_get_local_is assms Get_local fc_is
      by (fastforce split: prod.splits)
    thus ?thesis
    proof (cases)
      case a
      thus ?thesis
        using es_frame_contexts_to_config_ctx2[OF a(5)] Get_local fc_is 0
        by simp blast
    qed auto
  next
    case (Set_local k)
    consider
        (a) f' v_s' where
              "s' = s"
              "fcs' = fcs"
              "fc' = (Frame_context (Redex v_s' es b_es) lcs nf f')"
              "res = Step_normal"
              "(\<lparr>s;f;(v_stack_to_es v_s)@[$Set_local k]\<rparr> \<leadsto> \<lparr>s;f';(v_stack_to_es v_s')\<rparr>)"
      | (b) "(res = crash_invalid)"
      using app_f_v_s_set_local_is assms Set_local fc_is
      by (fastforce split: prod.splits)
    thus ?thesis
    proof (cases)
      case a
      thus ?thesis
        using es_frame_contexts_to_config_ctx2[OF a(5)] Set_local fc_is 0
        by simp blast
    qed auto
  next
    case (Tee_local k)
    consider
        (a) v_s' esc where
              "s' = s"
              "fcs' = fcs"
              "fc' = (update_fc_step fc v_s' esc)"
              "res = Step_normal"
              "(\<lparr>s;f;(v_stack_to_es v_s)@[$Tee_local k]\<rparr> \<leadsto> \<lparr>s;f;(v_stack_to_es v_s')@esc\<rparr>)"
      | (b) "(res = crash_invalid)"
      using app_v_s_tee_local_is assms Tee_local fc_is
      by (fastforce split: prod.splits)
    thus ?thesis
    proof (cases)
      case a
      thus ?thesis
        using es_frame_contexts_to_config_ctx1[OF a(5)] Tee_local fc_is 0
        by simp blast
    qed auto
  next
    case (Get_global k)
    obtain v_s' where a:
      "s' = s"
      "fcs' = fcs"
      "fc' = (update_fc_step fc v_s' [])"
      "res = Step_normal"
      "(\<lparr>s;f;(v_stack_to_es v_s)@[$Get_global k]\<rparr> \<leadsto> \<lparr>s;f;(v_stack_to_es v_s')\<rparr>)"
      using app_s_f_v_s_get_global_is[of _ "globs s"] assms Get_global fc_is
      by (fastforce split: prod.splits)
    thus ?thesis
      using es_frame_contexts_to_config_ctx2[OF a(5)] Get_global fc_is Cons 0
      by simp blast
  next
    case (Set_global k)
    consider
        (a) v_s' gs' where
              "fcs' = fcs"
              "fc' = (update_fc_step fc v_s' [])"
              "res = Step_normal"
              "app_s_f_v_s_set_global k (s.globs s) f v_s = (gs', v_s', res)"
              "s' = s\<lparr>globs := gs'\<rparr>"
              "(\<lparr>s;f;(v_stack_to_es v_s)@[$Set_global k]\<rparr> \<leadsto> \<lparr>s';f;(v_stack_to_es v_s')\<rparr>)"
      | (b) "(res = crash_invalid)"
      using app_s_f_v_s_set_global_is assms Set_global fc_is
      by (fastforce split: prod.splits)
    thus ?thesis
    proof (cases)
      case a
      thus ?thesis
        using es_frame_contexts_to_config_ctx2[OF a(6)] Set_global fc_is 0
        by simp blast
    qed auto
  next
    case (Table_get x19)
    then obtain v_s' where v_s'_is:
      "fcs' = fcs"
      "fc' = (update_fc_step fc v_s' [])"
      "app_s_f_v_s_table_get x19 (tabs s) f  v_s = (v_s', res)"
      "s' = s"
      using Cons assms fc_is
      by (fastforce split: prod.splits)
    consider
      (a) "res = Step_normal" "(\<lparr>s;f;(v_stack_to_es v_s)@[$Table_get x19]\<rparr> \<leadsto> \<lparr>s;f;(v_stack_to_es v_s')\<rparr>)"
    | (b) "(\<exists>str. res = Res_trap str \<and> (\<lparr>s;f;(v_stack_to_es v_s)@[$Table_get x19]\<rparr> \<leadsto> \<lparr>s;f;(v_stack_to_es v_s')@[Trap]\<rparr>))"
    | (c) "res = crash_invalid"
      using app_s_f_v_s_table_get_is[OF v_s'_is(3), of s] by blast
    thus ?thesis
    proof(cases)
      case a
      then show ?thesis using es_frame_contexts_to_config_ctx2[OF a(2)] v_s'_is fc_is Table_get 0
        by fastforce
    next
      case b
      then show ?thesis
        by (metis "0" Table_get es_frame_contexts_to_config_trap_ctx fc_is(1) fc_is(2) update_fc_step.simps v_s'_is(1) v_s'_is(2) v_s'_is(4))
    next
      case c
      then show ?thesis
        by simp
    qed
  next
    case (Table_set x20)
    obtain tabinsts' v_s' x where tabinsts'_is:
      "fcs' = fcs"
      "fc' = (update_fc_step fc v_s' [])"
      "app_s_f_v_s_table_set x (tabs s) f  v_s = (tabinsts', v_s', res)"
      "s' = s\<lparr>tabs:=tabinsts'\<rparr>"
      using Table_set Cons assms fc_is
      by (fastforce split: prod.splits)
    consider
      (a) "res = Step_normal"
          "(\<lparr>s;f;(v_stack_to_es v_s)@[$Table_set x20]\<rparr> \<leadsto> \<lparr>s';f;(v_stack_to_es v_s')\<rparr>)"
    | (b) str where 
          "res = Res_trap str"
          "\<lparr>s;f;(v_stack_to_es v_s)@[$Table_set x20]\<rparr> \<leadsto> \<lparr>s;f;(v_stack_to_es v_s')@[Trap]\<rparr>"
    | (c) "res = crash_invalid"
      using app_s_f_v_s_table_set_is[OF tabinsts'_is(3), of s] assms Table_set tabinsts'_is fc_is
      using app_s_f_v_s_table_set_is by (fastforce split: prod.splits)
    thus ?thesis
    proof(cases)
      case a
      then show ?thesis
        by (metis "0" Table_set es_frame_contexts_to_config_ctx2 fc_is(1) fc_is(2) tabinsts'_is(1) tabinsts'_is(2) update_fc_step.simps)
    next
      case b
      then have "s = s'"
        using tabinsts'_is app_s_f_v_s_table_set_is
        by fastforce
      then show ?thesis
        by (metis "0" Table_set b(1) b(2) es_frame_contexts_to_config_trap_ctx fc_is(1) fc_is(2) tabinsts'_is(1) tabinsts'_is(2) update_fc_step.simps)
    next
      case c
      then show ?thesis by simp
    qed   
  next
    case (Table_size x21)
    then show ?thesis sorry
  next
    case (Table_grow x22)
    then show ?thesis sorry
  next
    case (Load tp tp_sx a off)
    consider
        (a) v_s' where
              "s' = s"
              "fcs' = fcs"
              "fc' = (update_fc_step fc v_s' [])"
              "res = Step_normal"
              "(\<lparr>s;f;(v_stack_to_es v_s)@[$Load tp tp_sx a off]\<rparr> \<leadsto> \<lparr>s;f;(v_stack_to_es v_s')\<rparr>)"
      | (b) str v_s' where
              "s' = s"
              "fcs' = fcs"
              "fc' = (update_fc_step fc v_s' [])"
              "res = Res_trap str"
              "\<lparr>s;f;v_stack_to_es v_s @ [$Load tp tp_sx a off]\<rparr> \<leadsto> \<lparr>s;f;(v_stack_to_es v_s') @ [Trap]\<rparr>"
      | (c) "(res = crash_invalid)"
      using app_s_f_v_s_load_maybe_packed_is[of _ _ _ "mems s"] assms Load Cons fc_is
      by (fastforce split: prod.splits)
    thus ?thesis
    proof (cases)
      case a
      thus ?thesis
        using es_frame_contexts_to_config_ctx2[OF a(5)] Load fc_is 0
        by fastforce
    next
      case b
      thus ?thesis
        using es_frame_contexts_to_config_trap_ctx[OF b(5)] Load fc_is 0
        by fastforce
    qed auto
  next
    case (Store t tp a off)
    obtain ms' v_s' where ms'_is:
      "fcs' = fcs"
      "fc' = (update_fc_step fc v_s' [])"
      "app_s_f_v_s_store_maybe_packed t tp off (s.mems s) f  v_s = (ms', v_s', res)"
      "s' = s\<lparr>mems:=ms'\<rparr>"
      using Store Cons assms fc_is
      by (fastforce split: prod.splits)
    consider
        (a)   "res = Step_normal"
              "(\<lparr>s;f;(v_stack_to_es v_s)@[$Store t tp a off]\<rparr> \<leadsto> \<lparr>s';f;(v_stack_to_es v_s')\<rparr>)"
      | (b) str where
              "mems s = ms'"
              "res = Res_trap str"
              "\<lparr>s;f;v_stack_to_es v_s @ [$Store t tp a off]\<rparr> \<leadsto> \<lparr>s;f;(v_stack_to_es v_s') @ [Trap]\<rparr>"
      | (c) "(res = crash_invalid)"
      using app_s_f_v_s_store_maybe_packed_is[OF ms'_is(3), of s] Store ms'_is(4)
      by fastforce
    thus ?thesis
    proof (cases)
      case a
      thus ?thesis
        using es_frame_contexts_to_config_ctx2[OF a(2)] Store fc_is ms'_is(1,2) 0
        by simp blast
    next
      case b
      have "s = s'"
        using b(1) ms'_is(4)
        by simp
      thus ?thesis
        using es_frame_contexts_to_config_trap_ctx[OF b(3)] Store fc_is Cons ms'_is(1,2) b 0
        by simp blast
    qed auto
  next
    case (Load_vec lv a off)
    consider
        (a) v_s' where
              "s' = s"
              "fcs' = fcs"
              "fc' = (update_fc_step fc v_s' [])"
              "res = Step_normal"
              "(\<lparr>s;f;(v_stack_to_es v_s)@[$Load_vec lv a off]\<rparr> \<leadsto> \<lparr>s;f;(v_stack_to_es v_s')\<rparr>)"
      | (b) str v_s' where
              "s' = s"
              "fcs' = fcs"
              "fc' = (update_fc_step fc v_s' [])"
              "res = Res_trap str"
              "\<lparr>s;f;v_stack_to_es v_s @ [$Load_vec lv a off]\<rparr> \<leadsto> \<lparr>s;f;(v_stack_to_es v_s') @ [Trap]\<rparr>"
      | (c) "(res = crash_invalid)"
      using app_s_f_v_s_load_vec_is[of _ _ "mems s"] assms Load_vec Cons fc_is
      by (fastforce split: prod.splits)
    thus ?thesis
    proof (cases)
      case a
      thus ?thesis
        using es_frame_contexts_to_config_ctx2[OF a(5)] Load_vec fc_is 0
        by fastforce
    next
      case b
      thus ?thesis
        using es_frame_contexts_to_config_trap_ctx[OF b(5)] Load_vec fc_is 0
        by fastforce
    qed auto
  next
    case (Load_lane_vec svi i a off)
    consider
        (a) v_s' where
              "s' = s"
              "fcs' = fcs"
              "fc' = (update_fc_step fc v_s' [])"
              "res = Step_normal"
              "(\<lparr>s;f;(v_stack_to_es v_s)@[$Load_lane_vec svi i a off]\<rparr> \<leadsto> \<lparr>s;f;(v_stack_to_es v_s')\<rparr>)"
      | (b) str v_s' where
              "s' = s"
              "fcs' = fcs"
              "fc' = (update_fc_step fc v_s' [])"
              "res = Res_trap str"
              "\<lparr>s;f;v_stack_to_es v_s @ [$Load_lane_vec svi i a off]\<rparr> \<leadsto> \<lparr>s;f;(v_stack_to_es v_s') @ [Trap]\<rparr>"
      | (c) "(res = crash_invalid)"
      using app_s_f_v_s_load_lane_vec_is[of _ _ _ "mems s"] assms Load_lane_vec Cons fc_is
      by (fastforce split: prod.splits)
    thus ?thesis
    proof (cases)
      case a
      thus ?thesis
        using es_frame_contexts_to_config_ctx2[OF a(5)] Load_lane_vec fc_is 0
        by fastforce
    next
      case b
      thus ?thesis
        using es_frame_contexts_to_config_trap_ctx[OF b(5)] Load_lane_vec fc_is 0
        by fastforce
    qed auto
  next
    case (Store_vec sv a off)
    obtain ms' v_s' where ms'_is:
      "fcs' = fcs"
      "fc' = (update_fc_step fc v_s' [])"
      "app_s_f_v_s_store_vec sv off (s.mems s) f  v_s = (ms', v_s', res)"
      "s' = s\<lparr>mems:=ms'\<rparr>"
      using Store_vec Cons assms fc_is
      by (fastforce split: prod.splits)
    consider
        (a)   "res = Step_normal"
              "(\<lparr>s;f;(v_stack_to_es v_s)@[$Store_vec sv a off]\<rparr> \<leadsto> \<lparr>s';f;(v_stack_to_es v_s')\<rparr>)"
      | (b) str where
              "mems s = ms'"
              "res = Res_trap str"
              "\<lparr>s;f;v_stack_to_es v_s @ [$Store_vec sv a off]\<rparr> \<leadsto> \<lparr>s;f;(v_stack_to_es v_s') @ [Trap]\<rparr>"
      | (c) "(res = crash_invalid)"
      using app_s_f_v_s_store_vec_is[OF ms'_is(3), of s] Store_vec ms'_is(4)
      by fastforce
    thus ?thesis
    proof (cases)
      case a
      thus ?thesis
        using es_frame_contexts_to_config_ctx2[OF a(2)] Store_vec fc_is ms'_is(1,2) 0
        by simp blast
    next
      case b
      have "s = s'"
        using b(1) ms'_is(4)
        by simp
      thus ?thesis
        using es_frame_contexts_to_config_trap_ctx[OF b(3)] Store_vec fc_is Cons ms'_is(1,2) b 0
        by simp blast
    qed auto
  next
    case Current_memory
    consider
        (a) v_s' where
              "s' = s"
              "fcs' = fcs"
              "fc' = (update_fc_step fc v_s' [])"
              "res = Step_normal"
              "(\<lparr>s;f;(v_stack_to_es v_s)@[$ Current_memory]\<rparr> \<leadsto> \<lparr>s;f;(v_stack_to_es v_s')\<rparr>)"
      | (b) "(res = crash_invalid)"
      using app_s_f_v_s_mem_size_is[of "mems s"] assms Current_memory fc_is
      by (simp split: prod.splits) blast
    thus ?thesis
    proof (cases)
      case a
      thus ?thesis
        using es_frame_contexts_to_config_ctx2[OF a(5)] Current_memory fc_is 0
        by simp blast
    qed auto
  next
    case Grow_memory
    consider
        (a) ms' v_s' where
              "app_s_f_v_s_mem_grow (s.mems s) f v_s = (ms', v_s', res)"
              "fcs' = fcs"
              "fc' = (update_fc_step fc v_s' [])"
              "s' = s\<lparr>mems := ms'\<rparr>"
              "res = Step_normal"
              "(\<lparr>s;f;(v_stack_to_es v_s)@[$Grow_memory]\<rparr> \<leadsto> \<lparr>s';f;(v_stack_to_es v_s')\<rparr>)"
      | (b) "(res = crash_invalid)"
      using app_s_f_v_s_mem_grow_is[of "mems s"] assms Grow_memory fc_is
      by (fastforce split: prod.splits)
    thus ?thesis
    proof (cases)
      case a
      thus ?thesis
        using es_frame_contexts_to_config_ctx2[OF a(6)] Grow_memory fc_is 0
        by simp blast
    qed auto
  next
    case (Memory_init x30)
    then show ?thesis sorry
  next
    case Memory_fill
    then show ?thesis sorry
  next
    case Memory_copy
    then show ?thesis sorry
  next
    case (Table_init x331 x332)
    then show ?thesis sorry
  next
    case (Table_copy x341 x342)
    then show ?thesis sorry
  next
    case (Table_fill x35)
    then show ?thesis sorry
  next
    case (Elem_drop x36)
    then show ?thesis sorry
  next
    case (Data_drop x37)
  then show ?thesis sorry
  next
    case (EConstNum n)
    thus ?thesis
      using assms fc_is
      by fastforce
  next
    case (EConstVec x39)
    thus ?thesis
      using assms fc_is
      by fastforce
  next
    case (Unop t op)
    consider
        (a) v_s' where
              "s' = s"
              "fcs' = fcs"
              "fc' = (update_fc_step fc v_s' [])"
              "res = Step_normal"
              "(\<lparr>s;f;(v_stack_to_es v_s)@[$Unop t op]\<rparr> \<leadsto> \<lparr>s;f;(v_stack_to_es v_s')\<rparr>)"
      | (b) "(res = crash_invalid)"
      using app_v_s_unop_is assms Unop fc_is
      by (fastforce split: prod.splits)
    thus ?thesis
    proof (cases)
      case a
      thus ?thesis
        using es_frame_contexts_to_config_ctx2[OF a(5)] Unop fc_is 0
        by simp blast
    qed auto
  next
    case (Binop t op)
    consider
        (a) v_s' where
              "s' = s"
              "fcs' = fcs"
              "fc' = (update_fc_step fc v_s' [])"
              "res = Step_normal"
              "(\<lparr>s;f;(v_stack_to_es v_s)@[$Binop t op]\<rparr> \<leadsto> \<lparr>s;f;(v_stack_to_es v_s')\<rparr>)"
      | (b) str v_s' where
              "s' = s"
              "fcs' = fcs"
              "fc' = (update_fc_step fc v_s' [])"
              "res = Res_trap str"
              "\<lparr>s;f;v_stack_to_es v_s @ [$Binop t op]\<rparr> \<leadsto> \<lparr>s;f;(v_stack_to_es v_s') @ [Trap]\<rparr>"
      | (c) "(res = crash_invalid)"
      using app_v_s_binop_is assms Binop fc_is
      by (fastforce split: prod.splits)
    thus ?thesis
    proof (cases)
      case a
      thus ?thesis
        using es_frame_contexts_to_config_ctx2[OF a(5)] Binop fc_is 0
        by simp blast
    next
      case b
      thus ?thesis
        using es_frame_contexts_to_config_trap_ctx[OF b(5)] Binop fc_is 0
        by simp blast
    qed auto
  next
    case (Testop t op)
    consider
        (a) v_s' where
              "s' = s"
              "fcs' = fcs"
              "fc' = (update_fc_step fc v_s' [])"
              "res = Step_normal"
              "(\<lparr>s;f;(v_stack_to_es v_s)@[$Testop t op]\<rparr> \<leadsto> \<lparr>s;f;(v_stack_to_es v_s')\<rparr>)"
      | (b) "(res = crash_invalid)"
      using app_v_s_testop_is assms Testop fc_is
      by (fastforce split: prod.splits)
    thus ?thesis
    proof (cases)
      case a
      thus ?thesis
        using es_frame_contexts_to_config_ctx2[OF a(5)] Testop fc_is 0
        by simp blast
    qed auto
  next
    case (Relop t op)
    consider
        (a) v_s' where
              "s' = s"
              "fcs' = fcs"
              "fc' = (update_fc_step fc v_s' [])"
              "res = Step_normal"
              "(\<lparr>s;f;(v_stack_to_es v_s)@[$Relop t op]\<rparr> \<leadsto> \<lparr>s;f;(v_stack_to_es v_s')\<rparr>)"
      | (b) "(res = crash_invalid)"
      using app_v_s_relop_is assms Relop fc_is
      by (fastforce split: prod.splits)
    thus ?thesis
    proof (cases)
      case a
      thus ?thesis
        using es_frame_contexts_to_config_ctx2[OF a(5)] Relop fc_is 0
        by simp blast
    qed auto
  next
    case (Cvtop t2 op t1 sx)
    consider
        (a) v_s' where
              "s' = s"
              "fcs' = fcs"
              "fc' = (update_fc_step fc v_s' [])"
              "res = Step_normal"
              "(\<lparr>s;f;(v_stack_to_es v_s)@[$ Cvtop t2 op t1 sx]\<rparr> \<leadsto> \<lparr>s;f;(v_stack_to_es v_s')\<rparr>)"
      | (b) str v_s' where
              "s' = s"
              "fcs' = fcs"
              "fc' = (update_fc_step fc v_s' [])"
              "res = Res_trap str"
              "\<lparr>s;f;v_stack_to_es v_s @ [$ Cvtop t2 op t1 sx]\<rparr> \<leadsto> \<lparr>s;f;(v_stack_to_es v_s') @ [Trap]\<rparr>"
      | (c) "(res = crash_invalid)"
      using app_v_s_cvtop_is assms Cvtop fc_is
      by (fastforce split: prod.splits)
    thus ?thesis
    proof (cases)
      case a
      thus ?thesis
        using es_frame_contexts_to_config_ctx2[OF a(5)] Cvtop fc_is 0
        by simp blast
    next
      case b
      thus ?thesis
        using es_frame_contexts_to_config_trap_ctx[OF b(5)] Cvtop fc_is 0
        by simp blast
    qed auto
  next
    case (Ref_null x45)
    then show ?thesis sorry
  next
    case Ref_is_null
    then show ?thesis sorry
  next
    case (Ref_func x47)
    then show ?thesis sorry
  next
    case (Unop_vec op)
    consider
        (a) v_s' where
              "s' = s"
              "fcs' = fcs"
              "fc' = (update_fc_step fc v_s' [])"
              "res = Step_normal"
              "(\<lparr>s;f;(v_stack_to_es v_s)@[$Unop_vec op]\<rparr> \<leadsto> \<lparr>s;f;(v_stack_to_es v_s')\<rparr>)"
      | (b) "(res = crash_invalid)"
      using app_v_s_unop_vec_is assms Unop_vec fc_is
      by (fastforce split: prod.splits)
    thus ?thesis
    proof (cases)
      case a
      thus ?thesis
        using es_frame_contexts_to_config_ctx2[OF a(5)] Unop_vec fc_is 0
        by simp blast
    qed auto
  next
    case (Binop_vec op)
    consider
        (a) v_s' where
              "s' = s"
              "fcs' = fcs"
              "fc' = (update_fc_step fc v_s' [])"
              "res = Step_normal"
              "(\<lparr>s;f;(v_stack_to_es v_s)@[$Binop_vec op]\<rparr> \<leadsto> \<lparr>s;f;(v_stack_to_es v_s')\<rparr>)"
      | (b) str v_s' where
              "s' = s"
              "fcs' = fcs"
              "fc' = (update_fc_step fc v_s' [])"
              "res = Res_trap str"
              "\<lparr>s;f;v_stack_to_es v_s @ [$Binop_vec op]\<rparr> \<leadsto> \<lparr>s;f;(v_stack_to_es v_s') @ [Trap]\<rparr>"
      | (c) "(res = crash_invalid)"
      using app_v_s_binop_vec_is assms Binop_vec fc_is
      by (fastforce split: prod.splits)
    thus ?thesis
    proof (cases)
      case a
      thus ?thesis
        using es_frame_contexts_to_config_ctx2[OF a(5)] Binop_vec fc_is 0
        by simp blast
    next
      case b
      thus ?thesis
        using es_frame_contexts_to_config_trap_ctx[OF b(5)] Binop_vec fc_is 0
        by simp blast
    qed auto
  next
    case (Ternop_vec op)
    consider
        (a) v_s' where
              "s' = s"
              "fcs' = fcs"
              "fc' = (update_fc_step fc v_s' [])"
              "res = Step_normal"
              "(\<lparr>s;f;(v_stack_to_es v_s)@[$Ternop_vec op]\<rparr> \<leadsto> \<lparr>s;f;(v_stack_to_es v_s')\<rparr>)"
      | (b) "(res = crash_invalid)"
      using app_v_s_ternop_vec_is assms Ternop_vec fc_is
      by (fastforce split: prod.splits)
    thus ?thesis
    proof (cases)
      case a
      thus ?thesis
        using es_frame_contexts_to_config_ctx2[OF a(5)] Ternop_vec fc_is 0
        by simp blast
    qed auto
  next
    case (Test_vec op)
    consider
        (a) v_s' where
              "s' = s"
              "fcs' = fcs"
              "fc' = (update_fc_step fc v_s' [])"
              "res = Step_normal"
              "(\<lparr>s;f;(v_stack_to_es v_s)@[$Test_vec op]\<rparr> \<leadsto> \<lparr>s;f;(v_stack_to_es v_s')\<rparr>)"
      | (b) "(res = crash_invalid)"
      using app_v_s_test_vec_is assms Test_vec fc_is
      by (fastforce split: prod.splits)
    thus ?thesis
    proof (cases)
      case a
      thus ?thesis
        using es_frame_contexts_to_config_ctx2[OF a(5)] Test_vec fc_is 0
        by simp blast
    qed auto
  next
    case (Shift_vec op)
    consider
        (a) v_s' where
              "s' = s"
              "fcs' = fcs"
              "fc' = (update_fc_step fc v_s' [])"
              "res = Step_normal"
              "(\<lparr>s;f;(v_stack_to_es v_s)@[$Shift_vec op]\<rparr> \<leadsto> \<lparr>s;f;(v_stack_to_es v_s')\<rparr>)"
      | (b) "(res = crash_invalid)"
      using app_v_s_shift_vec_is assms Shift_vec fc_is
      by (fastforce split: prod.splits)
    thus ?thesis
    proof (cases)
      case a
      thus ?thesis
        using es_frame_contexts_to_config_ctx2[OF a(5)] Shift_vec fc_is 0
        by simp blast
    qed auto
  next
    case (Splat_vec op)
    consider
        (a) v_s' where
              "s' = s"
              "fcs' = fcs"
              "fc' = (update_fc_step fc v_s' [])"
              "res = Step_normal"
              "(\<lparr>s;f;(v_stack_to_es v_s)@[$Splat_vec op]\<rparr> \<leadsto> \<lparr>s;f;(v_stack_to_es v_s')\<rparr>)"
      | (b) "(res = crash_invalid)"
      using app_v_s_splat_vec_is assms Splat_vec fc_is
      by (fastforce split: prod.splits)
    thus ?thesis
    proof (cases)
      case a
      thus ?thesis
        using es_frame_contexts_to_config_ctx2[OF a(5)] Splat_vec fc_is 0
        by simp blast
    qed auto
  next
    case (Extract_vec sv sx i)
    consider
        (a) v_s' where
              "s' = s"
              "fcs' = fcs"
              "fc' = (update_fc_step fc v_s' [])"
              "res = Step_normal"
              "(\<lparr>s;f;(v_stack_to_es v_s)@[$Extract_vec sv sx i]\<rparr> \<leadsto> \<lparr>s;f;(v_stack_to_es v_s')\<rparr>)"
      | (b) "(res = crash_invalid)"
      using app_v_s_extract_vec_is assms Extract_vec fc_is
      by (fastforce split: prod.splits)
    thus ?thesis
    proof (cases)
      case a
      thus ?thesis
        using es_frame_contexts_to_config_ctx2[OF a(5)] Extract_vec fc_is 0
        by simp blast
    qed auto
  next
    case (Replace_vec sv i)
    consider
        (a) v_s' where
              "s' = s"
              "fcs' = fcs"
              "fc' = (update_fc_step fc v_s' [])"
              "res = Step_normal"
              "(\<lparr>s;f;(v_stack_to_es v_s)@[$Replace_vec sv i]\<rparr> \<leadsto> \<lparr>s;f;(v_stack_to_es v_s')\<rparr>)"
      | (b) "(res = crash_invalid)"
      using app_v_s_replace_vec_is assms Replace_vec fc_is
      by (fastforce split: prod.splits)
    thus ?thesis
    proof (cases)
      case a
      thus ?thesis
        using es_frame_contexts_to_config_ctx2[OF a(5)] Replace_vec fc_is 0
        by simp blast
    qed auto
  qed
qed

lemma run_step_e_sound:
  assumes "run_step_e e (Config d s fc fcs) = ((Config d' s' fc' fcs'), res)"
  shows "(\<exists>f esfc f' esfc'.
            res = Step_normal \<and>
            es_frame_contexts_to_config ([e]) fc fcs = (f,esfc) \<and>
            es_frame_contexts_to_config [] fc' fcs' = (f',esfc') \<and>
            \<lparr>s;f;esfc\<rparr> \<leadsto> \<lparr>s';f';esfc'\<rparr>) \<or>
         (\<exists>str f esfc f' esfc'.
            res = Res_trap str \<and>
            es_frame_contexts_to_config ([e]) fc fcs = (f,esfc) \<and>
            es_frame_contexts_to_config ([Trap]) fc' fcs' = (f',esfc') \<and>
            \<lparr>s;f;esfc\<rparr> \<leadsto> \<lparr>s';f';esfc'\<rparr>) \<or>
         (\<exists>str. res = Res_crash str)"
proof -
  obtain v_s es b_es lcs nf f rdx where fc_is: "fc = (Frame_context rdx lcs nf f)"
                                               "rdx = (Redex v_s es b_es)"
    by (metis frame_context.exhaust redex.exhaust)
  obtain f'' esfc'' where 0:
    "es_frame_contexts_to_config ([e]) (Frame_context (Redex v_s es b_es) lcs nf f) fcs = (f'',esfc'')"
    by (metis prod.exhaust)
  show ?thesis
    using assms fc_is
  proof (cases e)
    case (Basic b_e)
    thus ?thesis
      using assms run_step_b_e_sound fc_is
      by simp
  next
    case (Invoke i_cl)
    show ?thesis
    proof (cases "\<exists>str. res = Res_crash str")
      case True
      thus ?thesis
        by blast
    next
      case False
      show ?thesis
      proof (cases "(funcs s!i_cl)")
        case (Func_native i' tf ts_f es_f)
        obtain d' t1s t2s v_fs v_s' ts_f_zeros where tf_is:
          "s' = s"
          "d = Suc d'"
          "tf = (t1s _> t2s)"
          "(v_fs, v_s') = split_n v_s (length t1s)"
          "fcs' = (Frame_context (Redex v_s' es b_es) lcs nf f)#fcs"
          "n_zeros ts_f = Some ts_f_zeros"
          "fc' = (Frame_context (Redex [] [] es_f) [(Label_context [] [] (length t2s) [])] (length t2s) \<lparr> f_locs = ((rev v_fs)@ts_f_zeros), f_inst = i'\<rparr>)"
          "length v_s \<ge> length t1s"
          "res = Step_normal"
            using assms Invoke Func_native fc_is False
            apply (simp_all add: Let_def split: prod.splits if_splits option.splits tf.splits nat.splits)
            apply blast+
            done
      have v_s_rev_is:"v_stack_to_es v_s = v_stack_to_es v_s' @ v_stack_to_es v_fs"
        by (metis map_append rev_append split_n_conv_app tf_is(4))
      have fc_red1:"(\<lparr>s;f;(es_redex_to_es [Invoke i_cl] rdx)\<rparr> \<leadsto> \<lparr>s;f;es_redex_to_es [es_frame_context_to_e [] fc'] (Redex v_s' es b_es)\<rparr>)"
        using fc_is tf_is Func_native progress_L0[OF reduce.invoke_native, of s i_cl i' t1s t2s ts_f es_f "v_stack_to_es v_fs" "rev v_fs" "length (rev v_fs)" "length ts_f" "length t2s" "ts_f_zeros" f "rev v_s'" "es@($*b_es)"]
        by (simp add: v_s_rev_is) (metis split_n_length)
      hence fc_red2:"\<And>ff. \<lparr>s;ff;[es_frame_context_to_e ([Invoke i_cl]) fc]\<rparr> \<leadsto> \<lparr>s;ff;[es_frame_context_to_e ([es_frame_context_to_e [] fc']) (Frame_context (Redex v_s' es b_es) lcs nf f)]\<rparr>"
        using fc_is tf_is(1,5,6) reduce.local[OF es_label_contexts_to_es_LN[OF fc_red1]]
        by simp
      obtain f''' esfc''' where f'''_is:
        "es_frame_contexts_to_config [] fc' fcs' = (f''', esfc''')"
        by (metis prod.exhaust)
      have "\<lparr>s;f'';esfc''\<rparr> \<leadsto> \<lparr>s';f''';esfc'''\<rparr>"
      proof (cases fcs)
        case Nil
        thus ?thesis
        using f'''_is 0 fc_red1 fc_is tf_is Invoke Func_native
        by simp (meson es_label_contexts_to_es_LN)
      next
        case (Cons a list)
        thus ?thesis
        using f'''_is 0 es_frame_contexts_to_config_ctx[OF fc_red2] fc_is tf_is Invoke Func_native
        by (cases a) fastforce
      qed
      thus ?thesis
        using Invoke Func_native fc_is tf_is f'''_is 0
        by blast
      next
        case (Func_host tf host)
        obtain t1s t2s v_fs v_s' where tf_is:
          "tf = (t1s _> t2s)"
          "(v_fs, v_s') = split_n v_s (length t1s)"
          by (metis splice.cases tf.exhaust)
        have v_s_rev_is:"v_stack_to_es v_s = v_stack_to_es v_s' @ v_stack_to_es v_fs"
          by (metis map_append rev_append split_n_conv_app tf_is(2))
        show ?thesis
        proof (cases "host_apply_impl s (t1s _> t2s) host (rev v_fs)")
          case None
          have a_is:
            "s' = s"
            "fcs' = fcs"
            "fc' = (Frame_context (Redex v_s' es b_es) lcs nf f)"
            "\<exists>str. res = Res_trap str"
            "length v_s \<ge> length t1s"
            using assms Invoke Func_host fc_is tf_is False None
            apply (simp_all add: Let_def split: prod.splits if_splits option.splits tf.splits)
            apply blast+
            done
          have red_is:"(\<lparr>s;f;(v_stack_to_es v_s)@[Invoke i_cl]\<rparr> \<leadsto> \<lparr>s';f; (v_stack_to_es v_s')@[Trap]\<rparr>)"
            using fc_is tf_is Func_host None progress_L0_left[OF reduce.invoke_host_None, of s i_cl t1s t2s host "v_stack_to_es v_fs" "rev v_fs" _ _ f "rev v_s'"]
            by (simp add: a_is(1) v_s_rev_is) (metis a_is(5) split_n_length)
          show ?thesis
            using es_frame_contexts_to_config_trap_ctx[OF red_is] a_is(2,3,4) fc_is(1,2) 0 Invoke
            by simp blast
        next
          case (Some a)
          obtain rvs where a_is:
            "a = (s', rvs)"
            "fcs' = fcs"
            "fc' = (Frame_context (Redex ((rev rvs)@v_s') es b_es) lcs nf f)"
            "res = Step_normal"
            "length v_s \<ge> length t1s"
            using assms Invoke Func_host fc_is tf_is False Some
            by (fastforce simp add: Let_def split: prod.splits if_splits option.splits tf.splits)
          have red_is:"(\<lparr>s;f;(v_stack_to_es v_s)@[Invoke i_cl]\<rparr> \<leadsto> \<lparr>s';f; v_stack_to_es ((rev rvs)@v_s')\<rparr>)"
            using fc_is tf_is Func_host Some a_is(1,5) progress_L0_left[OF reduce.invoke_host_Some, of s i_cl t1s t2s host "v_stack_to_es v_fs" "rev v_fs" _ _ _ s' rvs f "rev v_s'"]
            by (simp add: v_s_rev_is) (metis host_apply_impl_correct split_n_length)
          show ?thesis
            using es_frame_contexts_to_config_ctx2[OF red_is] a_is(2,3,4) fc_is(1,2) 0 Invoke
            by simp blast
        qed
      qed
    qed  
   qed auto
qed


theorem run_iter_sound:
  assumes "run_iter fuel (Config d s fc fcs) = ((Config d' s' fc' fcs'), res)"
  shows "(\<exists>v_sres f esfc f'.
            res = RValue v_sres \<and>
            es_frame_contexts_to_config [] fc fcs = (f,esfc) \<and>
            reduce_trans (s,f,esfc) (s',f',v_stack_to_es v_sres)) \<or>
         (\<exists>str f esfc f'.
            res = RTrap str \<and>
            es_frame_contexts_to_config [] fc fcs = (f,esfc) \<and>
            reduce_trans (s,f,esfc) (s',f',[Trap])) \<or>
         (\<exists>str. res = RCrash str)"
  using assms
proof (induction fuel "(Config d s fc fcs)" arbitrary: d s fc fcs rule: run_iter.induct)
  case (1 n)
  consider
      (a) v_s nf f where "fc = (Frame_context (Redex v_s [] []) [] nf f)" "fcs = []"
    | (b) v_s nf f fc_hd fcs_tl where "fc =(Frame_context (Redex v_s [] []) [] nf f)" "fcs = fc_hd#fcs_tl"
    | (c) v_s v_ls b_els nl b_elcs lcs nf f where "fc = (Frame_context (Redex v_s [] []) ((Label_context v_ls b_els nl b_elcs)#lcs) nf f)"
    | (d) v_s b_e b_es lcs nf f where "fc = (Frame_context (Redex v_s [] (b_e#b_es)) lcs nf f)"
    | (e) v_s e es b_es lcs nf f where "fc = (Frame_context (Redex v_s (e#es) b_es) lcs nf f)"
    by (metis frame_context.exhaust label_context.exhaust list.exhaust redex.exhaust)
  thus ?case
  proof (cases)
    case a
    thus ?thesis
      using 1(6)
      by (fastforce simp add: reduce_trans_def)
  next
    case b
    obtain af bf cf df ef ff where fc_old_is:"fc_hd = (Frame_context (Redex af bf cf) df ef ff)"
      by (metis frame_context.exhaust redex.exhaust)
    have fc_red1:"\<lparr>s;ff;es_label_contexts_to_es (es_redex_to_es [Frame nf f (v_stack_to_es v_s)] (Redex af bf cf)) df\<rparr> \<leadsto>
            \<lparr>s;ff;es_label_contexts_to_es (es_redex_to_es (v_stack_to_es v_s) (Redex af bf cf)) df\<rparr>"
      using es_label_contexts_to_es_LN[OF es_redex_to_es_LN[OF reduce.basic[OF reduce_simple.local_const[of nf f "rev v_s"]]], of s ff "Redex af bf cf" df]
      by simp
    hence fc_red2:"\<And>ff. \<lparr>s;ff;[es_frame_context_to_e ([Frame nf f (v_stack_to_es v_s)]) fc_hd]\<rparr> \<leadsto> \<lparr>s;ff;[es_frame_context_to_e [] (update_fc_return fc_hd v_s)]\<rparr>"
      using fc_old_is
      by (simp add: reduce.local)
    obtain f'' esfc'' where 0:
      "es_frame_contexts_to_config [] (Frame_context (Redex v_s [] []) [] nf f) (fc_hd # fcs_tl) = (f'',esfc'')"
      by (metis prod.exhaust)
    obtain f''' esfc''' where f'''_is:
      "es_frame_contexts_to_config [] (update_fc_return fc_hd v_s) fcs_tl = (f''', esfc''')"
      by (fastforce simp del: run_iter.simps)
    have red_is:"\<lparr>s;f'';esfc''\<rparr> \<leadsto> \<lparr>s;f''';esfc'''\<rparr>"
    proof (cases fcs_tl)
      case Nil
      thus ?thesis
      using f'''_is 0 fc_red1 fc_old_is
      by simp
    next
      case (Cons a list)
      thus ?thesis
      using f'''_is 0 es_frame_contexts_to_config_ctx[OF fc_red2] fc_old_is
      by (cases a) fastforce
    qed
    thus ?thesis
      using 0 f'''_is 1(1,6) b
      by simp (metis reduce_trans_app)
  next
    case c
    have fc_red1:"\<lparr>s;f;es_label_contexts_to_es (es_label_context_to_es (v_stack_to_es v_s) (Label_context v_ls b_els nl b_elcs)) lcs\<rparr> \<leadsto>
            \<lparr>s;f;es_label_contexts_to_es (es_redex_to_es [] (Redex (v_s@v_ls) [] b_els)) lcs\<rparr>"
      using es_label_contexts_to_es_LN[OF progress_L0[OF reduce.basic[OF reduce_simple.label_const]]]
      by simp
    hence fc_red2:"\<And>ff. \<lparr>s;ff;[es_frame_context_to_e [] (Frame_context (Redex v_s [] []) ((Label_context v_ls b_els nl b_elcs) # lcs) nf f)]\<rparr> \<leadsto> \<lparr>s;ff;[es_frame_context_to_e [] (Frame_context (Redex (v_s@v_ls) [] b_els) lcs nf f)]\<rparr>"
      using reduce.local[OF fc_red1]
      by fastforce
    obtain f'' esfc'' where 0:
      "es_frame_contexts_to_config [] (Frame_context (Redex v_s [] []) ((Label_context v_ls b_els nl b_elcs)#lcs) nf f) fcs = (f'',esfc'')"
      by (metis prod.exhaust)
    obtain f''' esfc''' where f'''_is:
      "es_frame_contexts_to_config [] (Frame_context (Redex (v_s@v_ls) [] b_els) lcs nf f) fcs = (f''', esfc''')"
      by (metis prod.exhaust)
    have "\<lparr>s;f'';esfc''\<rparr> \<leadsto> \<lparr>s;f''';esfc'''\<rparr>"
    proof (cases fcs)
      case Nil
      thus ?thesis
        using f'''_is 0 fc_red1
        by simp
    next
      case (Cons a list)
      thus ?thesis
        using f'''_is 0 es_frame_contexts_to_config_ctx[OF fc_red2]
      by (cases a) fastforce
    qed
    thus ?thesis
      using 0 f'''_is 1(2,6) c
      by simp (metis reduce_trans_app)
  next
    case d
    obtain v_s' b_es' where b_es'_is:"split_v_s_b_s (b_e#b_es) = (v_s', b_es')" "(v_s', b_es') = split_v_s_b_s (b_e#b_es)"
      by (metis prod.exhaust)
    
    show ?thesis
    proof (cases b_es')
      case Nil
      thus ?thesis
        using b_es'_is 1(3,6) d es_frame_contexts_to_config_b_es_v_s split_v_s_b_s_conv_app
        append.left_neutral append_assoc map_append rev_append append_Nil
        apply(cases res, auto)        
         apply (metis append.left_neutral append_assoc map_append rev_append)
        by (metis append_Nil append_assoc map_append rev_append)
    next
      case (Cons b_e'' b_es'')
      obtain d_step s_step fc_step fcs_step res_step where run_step_b_e_is:
        "run_step_b_e b_e'' (Config d s (Frame_context (Redex (v_s' @ v_s) [] b_es'') lcs nf f) fcs) = ((Config d_step s_step fc_step fcs_step), res_step)"
        by (metis config.exhaust prod.exhaust)
      show ?thesis
      proof (cases res_step)
        case (Res_crash x1)
        thus ?thesis
          using 1(4,6) d run_step_b_e_is b_es'_is(1) Cons
          by (fastforce simp del: run_step_b_e.simps)
      next
        case (Res_trap x2)
        thus ?thesis
          using run_step_b_e_sound[OF run_step_b_e_is] 1(6) Cons d
                b_es'_is run_step_b_e_is es_frame_contexts_to_config_b_e_step split_v_s_b_s_conv_app
                es_frame_contexts_to_config_trap_reduce_trans reduce_trans_app
          apply (simp del: run_step_b_e.simps split_v_s_b_s.simps)
          by (metis (no_types, opaque_lifting) append_Nil es_frame_contexts_to_config_b_es_v_s)
      next
        case Step_normal
        then obtain fa esfc f' esfc' where defs:
          "es_frame_contexts_to_config [$b_e''] (Frame_context (Redex (v_s' @ v_s) [] b_es'') lcs nf f) fcs = (fa, esfc)"
          "es_frame_contexts_to_config [] fc_step fcs_step = (f', esfc')"
          "\<lparr>s;fa;esfc\<rparr> \<leadsto> \<lparr>s_step;f';esfc'\<rparr>"
          using run_step_b_e_sound[OF run_step_b_e_is]
          by (metis res_step.distinct(3) res_step.distinct(5))
        thus ?thesis        
          apply (cases res)
          using 1(4,6) es_frame_contexts_to_config_trap_reduce_trans reduce_trans_app  Cons d b_es'_is
            run_step_b_e_is es_frame_contexts_to_config_b_e_step split_v_s_b_s_conv_app
            reduce_trans_app Step_normal
            es_frame_contexts_to_config_b_es es_frame_contexts_to_config_v_s
          apply (auto simp del: run_step_b_e.simps split_v_s_b_s.simps)
          using  append.left_neutral append_assoc map_append rev_append
          by (smt (verit))+
      qed
    qed
  next
    case e
    obtain d_step s_step fc_step fcs_step res_step where run_step_e_is:
      "run_step_e e (Config d s (Frame_context (Redex v_s es b_es) lcs nf f) fcs) = ((Config d_step s_step fc_step fcs_step), res_step)"
      by (metis prod.exhaust config.exhaust)
    show ?thesis
    proof (cases res_step)
      case (Res_crash x1)
      thus ?thesis
        using 1(6) e run_step_e_is
        by fastforce
    next
      case (Res_trap x2)
      thus ?thesis
          using run_step_e_sound[OF run_step_e_is] 1(5)[OF _ _ _ _ run_step_e_is[symmetric]]
                run_step_e_is es_frame_contexts_to_config_e_one
                es_frame_contexts_to_config_trap_reduce_trans 1(6) e
          apply (simp del: run_step_e.simps)
          apply (metis reduce_trans_app)
          done
    next
      case Step_normal
      thus ?thesis
        using run_step_e_sound[OF run_step_e_is] 1(5)[OF _ _ _ _ run_step_e_is[symmetric]]
              run_step_e_is es_frame_contexts_to_config_e_one 1(6) e
        apply (simp del: run_step_e.simps)
        apply (metis (mono_tags, lifting) reduce_trans_app)
        done
    qed
  qed
next
  case 2
  thus ?case
    by fastforce
qed

theorem run_v_sound:
  assumes "run_v fuel d (s, f, b_es) = (s', RValue vs)"
  shows "(\<exists>f'. reduce_trans (s,f,$*b_es) (s',f',v_stack_to_es vs))"
  using assms run_iter_sound[of fuel d s "(Frame_context (Redex [] [] b_es) [] 0 f)" "[]"]
  by (simp split: prod.splits config.splits)

theorem run_v_sound_trap:
  assumes "run_v fuel d (s, f, b_es) = (s', RTrap str)"
  shows "(\<exists>f'. reduce_trans (s,f,$*b_es) (s',f',[Trap]))"
  using assms run_iter_sound[of fuel d s "(Frame_context (Redex [] [] b_es) [] 0 f)" "[]"]
  by (simp split: prod.splits config.splits)

theorem run_invoke_v_sound:
  assumes "run_invoke_v fuel d (s, vargs, i_cl) = (s', RValue vs)"
  shows "(\<exists>f'. reduce_trans (s,empty_frame,($C* vargs)@[Invoke i_cl]) (s',f',v_stack_to_es vs))"
  using assms run_iter_sound[of fuel d s "(Frame_context (Redex (rev vargs) [Invoke i_cl] []) [] 0 empty_frame)" "[]"]
  by (simp split: prod.splits config.splits)

theorem run_invoke_v_sound_trap:
  assumes "run_invoke_v fuel d (s, vargs, i_cl) = (s', RTrap str)"
  shows "(\<exists>f'. reduce_trans (s,empty_frame,($C* vargs)@[Invoke i_cl]) (s',f',[Trap]))"
  using assms run_iter_sound[of fuel d s "(Frame_context (Redex (rev vargs) [Invoke i_cl] []) [] 0 empty_frame)" "[]"]
  by (simp split: prod.splits config.splits)
  
theorem run_invoke_v_sound':
  assumes "run_invoke_v fuel d (s, vargs, i_cl) = (s', RValue vs)"
  shows "computes (invoke_config s vargs i_cl) s' vs"
  using run_invoke_v_sound[OF assms] unfolding computes_def invoke_config_def .
  
theorem run_invoke_v_sound_trap':
  assumes "run_invoke_v fuel d (s, vargs, i_cl) = (s', RTrap str)"
  shows "traps (invoke_config s vargs i_cl) s'"
  using run_invoke_v_sound_trap[OF assms] unfolding traps_def invoke_config_def .
  
end