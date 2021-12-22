theory Wasm_Instantiation_Properties 
  imports Wasm_Instantiation Wasm_Properties Wasm_Instantiation_Properties_Aux
begin

lemma list_all_ex_list_all2:
  assumes "\<And>i. i < length xs \<Longrightarrow> \<exists>y. P (xs!i) y"
  shows "\<exists>ys. list_all2 P xs ys"
  using assms
proof (induction xs)
  case (Cons x xs)
  have "\<exists>y. P x y"
       "\<And>i. i < length xs \<Longrightarrow> (\<exists>a. P (xs ! i) a)"
    using Cons(2)
    by fastforce+
  thus ?case
    using Cons(1)
    by blast
qed auto


lemma list_all2_in_set:
  assumes "x\<in>set xs" "list_all2 f xs ys" 
  shows "\<exists>y. f x y \<and> y\<in>set ys" 
  using assms 
  by (smt (verit, best) list_all2_conv_all_nth mem_Collect_eq set_conv_nth)

theorem instantiation_sound:
  assumes "store_typing s"
          "(instantiate s m v_imps ((s', inst, v_exps), start))"
  shows "store_typing s'"
        "\<exists>\<C>. inst_typing s' inst \<C>"
        "\<exists>tes. list_all2 (\<lambda>v_exp te. external_typing s' (E_desc v_exp) te) v_exps tes"
        "pred_option (\<lambda>i. i < length (s.funcs s')) start"
proof -
  obtain s1 s2 t_imps t_exps g_inits f e_offs d_offs where 
    "module_typing m t_imps t_exps"  
    and s_ext_typing:"list_all2 (external_typing s) v_imps t_imps"
    and s_alloc_module:"alloc_module s m v_imps g_inits (s1, inst, v_exps)"
    and "f = \<lparr> f_locs = [], f_inst = inst \<rparr>"
    "list_all2 (\<lambda>g v. reduce_trans (s1,f,$*(g_init g)) (s1,f,[$C v])) (m_globs m) g_inits"
    "list_all2 (\<lambda>e c. reduce_trans (s1,f,$*(e_off e)) (s1,f,[$C ConstInt32 c])) (m_elem m) e_offs"
    "list_all2 (\<lambda>d c. reduce_trans (s1,f,$*(d_off d)) (s1,f,[$C ConstInt32 c])) (m_data m) d_offs"
    and s_element_in_bounds:
    "list_all2 (\<lambda>e_off e. ((nat_of_int e_off) + (length (e_init e))) \<le> length (fst ((tabs s1)!((inst.tabs inst)!(e_tab e))))) e_offs (m_elem m)"
    and "list_all2 (\<lambda>d_off d. ((nat_of_int d_off) + (length (d_init d))) \<le> mem_length ((mems s1)!((inst.mems inst)!(d_data d)))) d_offs (m_data m)"
    "map_option (\<lambda>i_s. ((inst.funcs inst)!i_s)) (m_start m) = start"
    and s_init_tabs:"s2 = init_tabs s1 inst (map nat_of_int e_offs) (m_elem m)"
    and s_init_mems:"s' = init_mems s2 inst (map nat_of_int d_offs) (m_data m)" 
    using assms(2) instantiate.simps by auto

  have "store_extension s s1" using alloc_module_preserve_store_extension s_alloc_module by auto
  have "store_extension s1 s2" using init_tabs_preserve_store_extension s_init_tabs by auto 
  have "store_extension s2 s'" using init_mems_preserve_store_extension s_init_mems by auto 

  obtain \<C> fts ds i_opt gts ms
    where c_is:"list_all2 (module_func_typing \<C>) (m_funcs m) fts"
    "list_all (module_tab_typing) (m_tabs m)"
    "list_all (module_elem_typing \<C>) (m_elem m)"
    "list_all (module_data_typing \<C>) ds"
    "pred_option (module_start_typing \<C>) i_opt"
    "\<C> = \<lparr>types_t=(m_types m), 
          func_t=ext_t_funcs t_imps @ fts, 
          global=ext_t_globs t_imps @ gts, 
          table=ext_t_tabs t_imps @ (m_tabs m), 
          memory=ext_t_mems t_imps @ ms, 
          local=[], label=[], return=None\<rparr>"
    using \<open>module_typing m t_imps t_exps\<close> module_typing.simps
    by auto 

  have "funcs s1 = funcs s2" using init_tabs_only_modify_tabs[OF s_init_tabs] by auto
  also have "... = funcs s'" using init_mems_preserve_funcs s_init_mems by auto
  finally have "funcs s1 = funcs s'" by -
  obtain fs ts where 
    "funcs s1 = funcs s @ fs" 
    "tabs s1 = tabs s @ ts"
    using alloc_module_ext_arb[OF s_alloc_module]
    by metis
  then have "funcs s'= funcs s @ fs" using \<open>funcs s1 = funcs s'\<close> by auto

  have ts_alloc:"ts = alloc_tabs_simple (m_tabs m)" 
    using alloc_module_tabs_form[OF s_alloc_module \<open>tabs s1 = tabs s @ ts\<close>] by -


  have inst_typing_tabs:"list_all2 (tabi_agree (tabs s1)) (inst.tabs inst) (table \<C>)" 
  proof -
    define allocd_tabs where "allocd_tabs = snd (alloc_tabs s (m_tabs m))" 
    then have "inst.tabs inst = (ext_tabs v_imps)@allocd_tabs" 
      using alloc_module_tabs_only_alloc_tabs[OF s_alloc_module]
      by (metis prod.collapse) 
    moreover have "list_all2 (tabi_agree (tabs s1)) (ext_tabs v_imps) (ext_t_tabs t_imps)"
    proof -
      have "list_all2 (tabi_agree (tabs s)) (ext_tabs v_imps) (ext_t_tabs t_imps)" 
        using ext_typing_imp_tabi_agree[OF s_ext_typing] by -
      then show ?thesis
        unfolding tabi_agree_def \<open>tabs s1 = tabs s @ ts\<close>
        by (simp add: list_all2_mono nth_append)
    qed 
    moreover have "list_all2 (tabi_agree (tabs s1)) allocd_tabs (m_tabs m)"
    proof -
      have "length ts = length (m_tabs m)" using ts_alloc by auto
      then have allocd_interval:"allocd_tabs = [length (tabs s) ..< (length (tabs s) + length ts)]" 
        using allocd_tabs_def alloc_tabs_range surjective_pairing by metis  

      have "list_all2 tab_typing ts (m_tabs m)" 
        unfolding ts_alloc alloc_tab_simple_def tab_typing_def list.rel_map(1) limits_compat_def
        by(simp add:list_all2_refl pred_option_def)

      then have "list_all2 (tabi_agree (tabs s@ts)) allocd_tabs (m_tabs m)" 
        unfolding tabi_agree_def allocd_interval 
        by (simp add: list_all2_conv_all_nth) 
      then show ?thesis using \<open>tabs s1 = tabs s @ ts\<close> by auto
    qed
    ultimately show ?thesis
      using c_is by (simp add: list_all2_appendI)
  qed


  have "types inst = types_t \<C>" 
  proof -
    have "types inst = m_types m" using s_alloc_module unfolding alloc_module.simps 
      by(auto)
    also have "... = types_t \<C>" using c_is by auto
    finally show ?thesis by -
  qed                                         
  moreover have inst_typing_func:"list_all2 (funci_agree (funcs s')) (inst.funcs inst) (func_t \<C>)"
  proof -
    define allocd_funcs where "allocd_funcs = snd (alloc_funcs s (m_funcs m) inst)"  
    then have "inst.funcs inst = (ext_funcs v_imps)@allocd_funcs" 
      using s_alloc_module unfolding alloc_module.simps by auto
    moreover have "list_all2 (funci_agree (funcs s')) (ext_funcs v_imps) (ext_t_funcs t_imps)"
    proof -
      have "list_all2 (funci_agree (funcs s)) (ext_funcs v_imps) (ext_t_funcs t_imps)" 
        using ext_typing_imp_funci_agree[OF s_ext_typing] by -

      then show ?thesis unfolding funci_agree_def  \<open>funcs s' =funcs s @ fs\<close>
        by (simp add: list_all2_mono nth_append) 
    qed 
    moreover have "list_all2 (funci_agree (funcs s')) allocd_funcs fts" 
    proof - 
      have fs_alloc:"fs = alloc_funcs_simple (m_funcs m) inst" 
        using alloc_module_funcs_form[OF s_alloc_module \<open>funcs s1 = funcs s @ fs\<close>] by -
      then have "length fs = length (m_funcs m)" by auto
      then have allocd_interval:"allocd_funcs = [length (funcs s) ..< (length (funcs s) + length fs)]" 
        using allocd_funcs_def alloc_funcs_range surjective_pairing by metis  

      have "list_all2 (\<lambda>f i. cl_type f = (types inst)!(fst i)) fs (m_funcs m)" 
        unfolding cl_type_def alloc_func_simple_def fs_alloc list.rel_map(1) 
        by(simp add: list_all2_refl split:prod.splits)

      moreover have "list_all2 (\<lambda>f ft. (fst f) < length (types_t \<C>)\<and> (types_t \<C>)!(fst f) = ft) 
          (m_funcs m) fts"
        using list_all2_mono[OF c_is(1)] unfolding module_func_typing.simps 
        by (smt (z3) fst_conv) 

      ultimately have "list_all2 (\<lambda>f ft. cl_type f = ft) fs fts" using \<open>types inst = types_t \<C>\<close> 
        list_all2_trans[where as=fs and bs="(m_funcs m)" and cs=fts]
        by (metis (mono_tags, lifting))

      then have "list_all2 (funci_agree (funcs s@fs)) allocd_funcs fts" 
        unfolding funci_agree_def allocd_interval
        by (simp add: list_all2_conv_all_nth) 
      then show ?thesis using \<open>funcs s' = funcs s @ fs\<close> by auto
    qed 
    ultimately show ?thesis using c_is by (simp add: list_all2_appendI) 
  qed 
  moreover have "list_all2 (globi_agree (globs s')) (inst.globs inst) (global \<C>)" sorry 
  moreover have "list_all2 (tabi_agree (tabs s')) (inst.tabs inst) (table \<C>)" 
    using tabi_agree_store_extension init_tabs_tabi_agree[OF s_init_tabs] 
      list_all2_mono[OF inst_typing_tabs] \<open>store_extension s2 s'\<close> by blast
  moreover have "list_all2 (memi_agree (mems s')) (inst.mems inst) (memory \<C>)" sorry
  moreover have "local \<C> = [] \<and> label \<C> = [] \<and> return \<C> = None" using c_is by auto
  ultimately have "inst_typing s' inst \<C>" using inst_typing.simps
    by (metis (full_types) inst.surjective old.unit.exhaust t_context.surjective) 

  show "store_typing s'"
  proof -
    have 1:"list_all (\<lambda>cl. \<exists>tf. cl_typing s' cl tf) (funcs s')" 
    proof -

        have "list_all (\<lambda>cl. \<exists>tf. cl_typing s1 cl tf) (funcs s)" 
          using cl_typing_store_extension_inv[OF \<open>store_extension s s1\<close>] store_typing.simps assms(1)
          by (smt (verit, ccfv_threshold) list_all_length) 
        then have "list_all (\<lambda>cl. \<exists>tf. cl_typing s2 cl tf) (funcs s)" 
          using  cl_typing_store_extension_inv[OF \<open>store_extension s1 s2\<close>] list.pred_mono_strong
          by (smt (verit, best)) 
        then have "list_all (\<lambda>cl. \<exists>tf. cl_typing s' cl tf) (funcs s)" 
          using  cl_typing_store_extension_inv[OF \<open>store_extension s2 s'\<close>] list.pred_mono_strong
          by (smt (verit, best))

        moreover have "list_all (\<lambda>cl. \<exists>tf. cl_typing s' cl tf) fs" 
        proof -
          {
            fix f
            assume "f\<in>set fs" 
            
            obtain i_t loc_ts b_es where 1:
              "f = Func_native inst ((types inst)!i_t) loc_ts b_es"  
              "(i_t, loc_ts, b_es) \<in> set (m_funcs m)"
              using \<open>f\<in>set fs\<close> 
                  alloc_module_funcs_form[OF s_alloc_module \<open>funcs s1 = funcs s @ fs\<close>]
              unfolding alloc_func_simple_def
              by fastforce 
             
            obtain tn tm where 2:
              "i_t < length (types_t \<C>)"
              "(types_t \<C>)!i_t = (tn _> tm)"
              "\<C>\<lparr>local := tn @ loc_ts, label := ([tm] @ (label \<C>)), return := Some tm\<rparr> \<turnstile> b_es : ([] _> tm)"
              using list_all2_in_set[OF 1(2) c_is(1)]
              unfolding module_func_typing.simps by auto 

            have 3:"(types inst)!i_t = (types_t \<C>)!i_t"
              using store_typing_imp_types_eq[OF \<open>inst_typing s' inst \<C>\<close> 2(1)] by auto

            have "cl_typing s' f (tn _> tm)" 
              using 1(1) 2 3 
              cl_typing.intros(1)[OF \<open>inst_typing s' inst \<C>\<close>]
              by presburger 
            then have "\<exists>tf. cl_typing s' f tf" by auto
          }
          then show ?thesis by (simp add: list_all_iff) 
        qed
        ultimately show ?thesis using \<open>funcs s' = funcs s @ fs\<close>
          by (metis list_all_append) 
      qed 
    have 2:"list_all (tab_agree s') (tabs s')"
    proof -
      have "tabs s2 = tabs s'" using init_mems_form(2)[OF s_init_mems] by auto 
      have 1:"list_all (\<lambda>i. i< length (funcs s1)) (inst.funcs inst)" 
        using inst_typing_func \<open>funcs s1 = funcs s'\<close> unfolding funci_agree_def
        by (simp add: list_all2_conv_all_nth list_all_length) 
      {
        fix e 
        assume "e \<in> set (m_elem m)" 
        then have "module_elem_typing \<C> e" using \<open>list_all (module_elem_typing \<C>) (m_elem m)\<close>
          by (metis list_all_iff) 
        then have "list_all (\<lambda>i. i < length (func_t \<C>)) (e_init e)"  
          unfolding module_elem_typing.simps by auto 
        then have "list_all (\<lambda>i. i < length (inst.funcs inst)) (e_init e)"
          using \<open>list_all2 (funci_agree (funcs s')) (inst.funcs inst) (func_t \<C>)\<close>  
          list_all2_conv_all_nth
          by (simp add: list_all2_conv_all_nth) 
        then have "list_all (\<lambda>i. (inst.funcs inst)!i < length (s.funcs s1)) (e_init e)" using 1
          by (metis list_all_length)
      }
      then have 1:"list_all (element_funcs_in_bounds s1 inst) (m_elem m)" by (metis list_all_iff) 

      have 2:"list_all2 (element_in_bounds s1 inst) (map nat_of_int e_offs) (m_elem m)"  
      proof -
        have "list_all (\<lambda>i. i < length (tabs s1)) (inst.tabs inst)" 
          using inst_typing_tabs unfolding tabi_agree_def
          by (simp add: less_imp_le_nat list_all2_conv_all_nth list_all_length) 
        moreover have "list_all (\<lambda>e. e_tab e < length (inst.tabs inst)) (m_elem m)"
          using inst_typing_tabs c_is(3) unfolding list_all2_conv_all_nth module_elem_typing.simps
          by (smt (verit, best) list_all_iff module_elem.select_convs(1)) 
        ultimately show ?thesis using s_element_in_bounds unfolding element_in_bounds_def
          by (smt (verit, best) list.rel_map(1) list_all2_conv_all_nth list_all_length)
      qed 

      have "list_all (tab_agree s) (tabs s)" using assms(1) unfolding store_typing.simps by auto
      then have "list_all (tab_agree s1) (tabs s)" 
        using tab_agree_store_extension_inv2[OF \<open>store_extension s s1\<close>] 
        by (simp add: list_all_length) 
      moreover have "list_all (tab_agree s1) ts" 
        using \<open>list_all (module_tab_typing) (m_tabs m)\<close> 
        unfolding ts_alloc alloc_tab_simple_def tab_agree_def list.pred_map(1) comp_def 
        limit_typing.simps
        by(simp add:list.pred_set, auto)
      ultimately have "list_all (tab_agree s1) (tabs s1)" using \<open>tabs s1 = tabs s @ ts\<close>
        by simp 
      then have "list_all (tab_agree s2) (tabs s2)" using init_tabs_tab_agree[OF s_init_tabs 1 2]
        by simp
      then show ?thesis using \<open>funcs s2 = funcs s'\<close> \<open>tabs s2 = tabs s'\<close> 
        unfolding tab_agree_def by auto
    qed
    have 3:"list_all mem_agree (mems s')"
      sorry
    show ?thesis
      using 1 2 3 store_typing.intros
      by blast
  qed

  show "\<exists>\<C>. inst_typing s' inst \<C>" using \<open>inst_typing s' inst \<C>\<close> by auto

  show "\<exists>tes. list_all2 (\<lambda>v_exp te. external_typing s' (E_desc v_exp) te) v_exps tes"
  proof -
  have "\<And>i. i < length v_exps \<Longrightarrow> (\<exists>te. external_typing s' (E_desc (v_exps!i)) te)"
    sorry
  thus ?thesis
    by (simp add: list_all_ex_list_all2)
  qed

  show "pred_option (\<lambda>i. i < length (s.funcs s')) start"
    sorry
qed

end