theory Wasm_Instantiation_Properties 
  imports Wasm_Instantiation Wasm_Properties Wasm_Instantiation_Properties_Aux
begin

lemma ex_list_all2: 
  assumes "\<forall>x \<in> set xs. \<exists>y. P x y" 
  shows "\<exists>ys. list_all2 P xs ys" 
proof -
  have "list_all2 P xs (map (\<lambda>x. SOME y. P x y) xs)" 
    unfolding list.rel_map(2) using assms
    by (simp add: list.rel_refl_strong someI_ex)
  then show ?thesis by (rule exI)
qed

lemma list_all2_in_set:
  assumes "x\<in>set xs" "list_all2 f xs ys" 
  shows "\<exists>y. f x y \<and> y\<in>set ys" 
  using assms 
  by (smt (verit, best) list_all2_conv_all_nth mem_Collect_eq set_conv_nth)

lemma list_all2_forget:
  assumes "list_all2 P xs ys"
  shows "list_all (\<lambda>x. \<exists>y. P x y) xs" 
  using assms
  by (metis Ball_set list_all2_in_set) 

lemma limits_compat_refl:"limits_compat l l" 
  unfolding limits_compat_def by(simp add: pred_option_def)

lemma tab_typing_exists:"\<exists>tt. tab_typing t tt" 
  using limits_compat_refl tab_typing_def
  by (metis limit_t.select_convs(1,2) limits_compat_def) 

lemma mem_typing_exists:"\<exists>mt. mem_typing m mt" 
  using limits_compat_refl mem_typing_def
  by (metis limit_t.select_convs(1,2) limits_compat_def) 

lemma glob_typing_exists:"\<exists>gt. glob_typing g gt" 
  unfolding glob_typing_def typeof_def
  by (metis tg.select_convs(1,2))

lemma instantiation_external_typing:
  assumes "alloc_module s m v_imps g_inits (s1, inst, v_exps)"
          "inst_typing s' inst \<C>" 
          "list_all2 (\<lambda>exp. module_export_typing \<C> (E_desc exp)) (m_exports m) t_exps"
  shows "\<exists>tes. list_all2 (\<lambda>v_exp te. external_typing s' (E_desc v_exp) te) v_exps tes"
proof -
  have 1:"map E_desc v_exps = map (\<lambda>m_exp. export_get_v_ext inst (E_desc m_exp)) (m_exports m)"
    using assms(1) unfolding alloc_module.simps by auto
  {
    have funci_agree_s':"list_all2 (funci_agree (funcs s')) (inst.funcs inst) (func_t \<C>)"
      using assms(2) inst_typing.simps by auto

    fix i 
    assume "Ext_func i \<in> set (map E_desc v_exps)"
    then obtain j where "Ext_func j \<in> set (map E_desc (m_exports m))"  
                   "i = inst.funcs inst ! j"
      unfolding 1 export_get_v_ext_def 
      by(simp add: image_iff split:v_ext.splits, metis v_ext.exhaust)
    then have "j < length (inst.funcs inst)" 
      using list_all2_forget[OF assms(3)] funci_agree_s'
      unfolding list_all2_conv_all_nth module_export_typing.simps list_all_iff by fastforce  
    moreover have "list_all (\<lambda>x. x < length (funcs s')) (inst.funcs inst)" 
      using funci_agree_s' unfolding funci_agree_def
      by (simp add: list_all2_conv_all_nth list_all_length) 
    ultimately have "i < length (funcs s')" using \<open>i = inst.funcs inst ! j\<close>
      unfolding list_all_length by auto
    then have "\<exists> tf. external_typing s' (Ext_func i) tf" 
      unfolding external_typing.simps by auto
  }
  moreover {
    have tabi_agree_s':"list_all2 (tabi_agree (tabs s')) (inst.tabs inst) (table \<C>)"
      using assms(2) inst_typing.simps by auto

    fix i 
    assume "Ext_tab i \<in> set (map E_desc v_exps)"
    then obtain j where "Ext_tab j \<in> set (map E_desc (m_exports m))"  
                   "i = inst.tabs inst ! j"
      unfolding 1 export_get_v_ext_def 
      by(simp add: image_iff split:v_ext.splits, metis v_ext.exhaust)
    then have "j < length (inst.tabs inst)" 
      using list_all2_forget[OF assms(3)] tabi_agree_s'
      unfolding list_all2_conv_all_nth module_export_typing.simps list_all_iff by fastforce  
    moreover have "list_all (\<lambda>x. x < length (tabs s')) (inst.tabs inst)" 
      using tabi_agree_s' unfolding tabi_agree_def 
      by (simp add: list_all2_conv_all_nth list_all_length) 
    ultimately have "i < length (tabs s')" using \<open>i = inst.tabs inst ! j\<close>
      unfolding list_all_length by auto
    then have "\<exists> tt. external_typing s' (Ext_tab i) tt" 
      unfolding external_typing.simps by (simp add: tab_typing_exists)  
  }
  moreover {
    have memi_agree_s':"list_all2 (memi_agree (mems s')) (inst.mems inst) (memory \<C>)"
      using assms(2) inst_typing.simps by auto
                        
    fix i 
    assume "Ext_mem i \<in> set (map E_desc v_exps)"
    then obtain j where "Ext_mem j \<in> set (map E_desc (m_exports m))"  
                   "i = inst.mems inst ! j"
      unfolding 1 export_get_v_ext_def 
      by(simp add: image_iff split:v_ext.splits, metis v_ext.exhaust)
    then have "j < length (inst.mems inst)" 
      using list_all2_forget[OF assms(3)] memi_agree_s'
      unfolding list_all2_conv_all_nth module_export_typing.simps list_all_iff by fastforce
    moreover have "list_all (\<lambda>x. x < length (mems s')) (inst.mems inst)" 
      using memi_agree_s' unfolding memi_agree_def 
      by (simp add: list_all2_conv_all_nth list_all_length) 
    ultimately have "i < length (mems s')" using \<open>i = inst.mems inst ! j\<close>
      unfolding list_all_length by auto
    then have "\<exists> tm. external_typing s' (Ext_mem i) tm" 
      unfolding external_typing.simps by (simp add: mem_typing_exists)  
  }
  moreover {
    have globi_agree_s':"list_all2 (globi_agree (globs s')) (inst.globs inst) (global \<C>)"
      using assms(2) inst_typing.simps by auto

    fix i 
    assume "Ext_glob i \<in> set (map E_desc v_exps)"
    then obtain j where "Ext_glob j \<in> set (map E_desc (m_exports m))"  
                   "i = inst.globs inst ! j"
      unfolding 1 export_get_v_ext_def 
      by(simp add: image_iff split:v_ext.splits, metis v_ext.exhaust)
    then have "j < length (inst.globs inst)" 
      using list_all2_forget[OF assms(3)] globi_agree_s'
      unfolding list_all2_conv_all_nth module_export_typing.simps list_all_iff by fastforce
    moreover have "list_all (\<lambda>x. x < length (globs s')) (inst.globs inst)" 
      using globi_agree_s' unfolding globi_agree_def 
      by (simp add: list_all2_conv_all_nth list_all_length)
    ultimately have "i < length (globs s')" using \<open>i = inst.globs inst ! j\<close>
      unfolding list_all_length by auto
    then have "\<exists> tg. external_typing s' (Ext_glob i) tg" 
      unfolding external_typing.simps by(simp add: glob_typing_exists)
  }
  ultimately have "\<And>ext. ext \<in> set (map E_desc v_exps) \<Longrightarrow> \<exists> te. external_typing s' ext te"
    using v_ext.exhaust by metis 
  then show ?thesis by (simp add: ex_list_all2) 
qed

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
    and f_def:"f = \<lparr> f_locs = [], f_inst = inst \<rparr>"
    and g_inits_def:
    "list_all2 (\<lambda>g v. reduce_trans (s1,f,$*(g_init g)) (s1,f,[$C v])) (m_globs m) g_inits"
    and "list_all2 (\<lambda>e c. reduce_trans (s1,f,$*(e_off e)) (s1,f,[$C ConstInt32 c])) (m_elem m) e_offs"
    "list_all2 (\<lambda>d c. reduce_trans (s1,f,$*(d_off d)) (s1,f,[$C ConstInt32 c])) (m_data m) d_offs"
    and s_element_in_bounds:
    "list_all2 (\<lambda>e_off e. ((nat_of_int e_off) + (length (e_init e))) \<le> length (fst ((tabs s1)!((inst.tabs inst)!(e_tab e))))) e_offs (m_elem m)"
    and s_data_in_bounds:
    "list_all2 (\<lambda>d_off d. ((nat_of_int d_off) + (length (d_init d))) \<le> mem_length ((mems s1)!((inst.mems inst)!(d_data d)))) d_offs (m_data m)"
    and s_start:"map_option (\<lambda>i_s. ((inst.funcs inst)!i_s)) (m_start m) = start"
    and s_init_tabs:"s2 = init_tabs s1 inst (map nat_of_int e_offs) (m_elem m)"
    and s_init_mems:"s' = init_mems s2 inst (map nat_of_int d_offs) (m_data m)" 
    using assms(2) instantiate.simps by auto

  have "store_extension s s1" using alloc_module_preserve_store_extension s_alloc_module by auto
  have "store_extension s1 s2" using init_tabs_preserve_store_extension s_init_tabs by auto 
  have "store_extension s2 s'" using init_mems_preserve_store_extension s_init_mems by auto 

  obtain \<C> \<C>' fts ds gts ms
    where c_is:"list_all2 (module_func_typing \<C>) (m_funcs m) fts"
    "list_all (module_tab_typing) (m_tabs m)"
    "list_all (module_elem_typing \<C>) (m_elem m)"
    "list_all (module_data_typing \<C>) ds"
    "list_all2 (\<lambda>exp. module_export_typing \<C> (E_desc exp)) (m_exports m) t_exps"
    "pred_option (module_start_typing \<C>) (m_start m)"
    "\<C> = \<lparr>types_t=(m_types m), 
          func_t=ext_t_funcs t_imps @ fts, 
          global=ext_t_globs t_imps @ gts, 
          table=ext_t_tabs t_imps @ (m_tabs m), 
          memory=ext_t_mems t_imps @ ms, 
          local=[], label=[], return=None\<rparr>"
    "list_all2 (module_glob_typing \<C>') (m_globs m) gts"
    "\<C>' = \<lparr>types_t=[], func_t=[], global=ext_t_globs t_imps, table=[], memory=[], 
        local=[], label=[], return=None\<rparr>"
    using \<open>module_typing m t_imps t_exps\<close> module_typing.simps
    by auto 

  have "funcs s1 = funcs s2" using init_tabs_only_modify_tabs[OF s_init_tabs] by auto
  also have "... = funcs s'" using init_mems_only_modify_mems[OF s_init_mems] by auto
  finally have "funcs s1 = funcs s'" by -
  obtain fs ts gs where 
    "funcs s1 = funcs s @ fs" 
    "tabs s1 = tabs s @ ts"
    "globs s1 = globs s @ gs"
    using alloc_module_ext_arb[OF s_alloc_module]
    by metis
  then have "funcs s'= funcs s @ fs" using \<open>funcs s1 = funcs s'\<close> by auto

  have "globs s' =  globs s @ gs" using \<open>globs s1 = globs s @ gs\<close>
      init_tabs_only_modify_tabs[OF s_init_tabs] init_mems_only_modify_mems[OF s_init_mems] 
    by auto

  have ts_alloc:"ts = alloc_tabs_simple (m_tabs m)" 
    using alloc_module_tabs_form[OF s_alloc_module \<open>tabs s1 = tabs s @ ts\<close>] by -


  have tabi_agree_s1:"list_all2 (tabi_agree (tabs s1)) (inst.tabs inst) (table \<C>)" 
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
  moreover have funci_agree_s':"list_all2 (funci_agree (funcs s')) (inst.funcs inst) (func_t \<C>)"
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
  moreover have tabi_agree_s':"list_all2 (tabi_agree (tabs s')) (inst.tabs inst) (table \<C>)" 
    using tabi_agree_store_extension init_tabs_tabi_agree[OF s_init_tabs] 
      list_all2_mono[OF tabi_agree_s1] \<open>store_extension s2 s'\<close> by blast
  moreover have memi_agree_s':"list_all2 (memi_agree (mems s')) (inst.mems inst) (memory \<C>)" sorry
  moreover have globi_agree_s':"list_all2 (globi_agree (globs s')) (inst.globs inst) (global \<C>)"
  proof - 
    define allocd_globs where "allocd_globs = snd (alloc_globs s (m_globs m) g_inits)" 
    then have "inst.globs inst = (ext_globs v_imps)@allocd_globs" 
      using alloc_module_globs_only_alloc_globs[OF s_alloc_module]
      by (metis prod.collapse)
    moreover have "list_all2 (globi_agree (globs s')) (ext_globs v_imps) (ext_t_globs t_imps)"
    proof -
      have "list_all2 (globi_agree (globs s)) (ext_globs v_imps) (ext_t_globs t_imps)" 
        using ext_typing_imp_globi_agree[OF s_ext_typing] by -

      then show ?thesis unfolding globi_agree_def \<open>globs s' = globs s @ gs\<close>
        by (simp add: list_all2_mono nth_append) 
    qed 
    moreover have "list_all2 (globi_agree (globs s')) allocd_globs gts" 
    proof - 
      have zip_agree:"length (m_globs m) = length g_inits" 
        using g_inits_def unfolding list_all2_conv_all_nth by simp
      have gs_alloc:"gs = alloc_globs_simple (m_globs m) g_inits" 
        using alloc_module_globs_form[OF s_alloc_module \<open>globs s1 = globs s @ gs\<close>] by -
      then have "length gs = length (m_globs m)" using \<open>length (m_globs m) = length g_inits\<close>
        by auto
      then have allocd_interval:"allocd_globs = [length (globs s) ..< (length (globs s) + length gs)]" 
        using allocd_globs_def alloc_globs_range surjective_pairing \<open>length (m_globs m) = length g_inits\<close>
        by (metis min.idem)   

      have "list_all2 (\<lambda>g gt. gt = g_type g) (m_globs m) gts" 
        using c_is(8)  unfolding module_glob_typing.simps 
        by (smt (verit, best) list_all2_mono module_glob.select_convs(1))
      then have "gts = map g_type (m_globs m)"
        unfolding list_all2_conv_all_nth 
        by (metis map_intro_length) 

      have "map tg_t gts = map typeof g_inits" (*from typing preservation*)
      proof - 
        {
          fix g v
          assume assm:"(g, v) \<in> set (zip (m_globs m) g_inits)"

          have 1:"const_exprs \<C>' (g_init g)" using c_is(8) zip_agree assm
            unfolding module_glob_typing.simps list_all2_conv_all_nth
            by (metis in_set_conv_nth module_glob.select_convs(2) set_zip_leftD) 
          have 2:"\<C>' \<turnstile> g_init g : ([] _> [tg_t (g_type g)])" using c_is(8) zip_agree assm
            unfolding module_glob_typing.simps list_all2_conv_all_nth
            by (metis in_set_conv_nth module_glob.select_convs(1,2) set_zip_leftD) 
          have 3:"reduce_trans (s1,f,$*(g_init g)) (s1,f,[$C v])" 
            using g_inits_def assm zip_agree unfolding list_all2_conv_all_nth in_set_conv_nth
            by fastforce 
          have 4:"global \<C>' = ext_t_globs t_imps" unfolding c_is(9) by simp 

          have "tg_t (g_type g) = typeof v"
            using const_exprs_reduce_trans[OF 1 2 3 4
                list_all2_external_typing_glob_alloc[OF s_ext_typing] \<open>globs s1 = globs s @ gs\<close>]
            \<open>inst.globs inst = (ext_globs v_imps)@allocd_globs\<close> f_def by force 
        }
        then have "list_all2 (\<lambda>g g_init. tg_t (g_type g) = typeof g_init) (m_globs m) g_inits"
          using \<open>length (m_globs m) = length g_inits\<close> unfolding list_all2_conv_all_nth 
          (*todo: I have no idea why gs gets involved but whatever*)
          by (metis \<open>length gs = length (m_globs m)\<close> gs_alloc length_map nth_mem nth_zip) 
  
        then show ?thesis unfolding \<open>gts = map g_type (m_globs m)\<close> list_all2_conv_all_nth
          by (simp add: map_intro_length)
      qed

      moreover have "map g_val gs = g_inits"
        unfolding gs_alloc alloc_glob_simple_def using \<open>length (m_globs m) = length g_inits\<close>
        by(simp add:comp_def prod.case_eq_if)

      ultimately have "list_all2 (\<lambda>g gt. typeof (g_val g) = tg_t gt) gs gts"
        using length_map nth_map unfolding list_all2_conv_all_nth
        by metis 

      moreover have "list_all2 (\<lambda>g gt. g_mut g = tg_mut gt) gs gts"
        unfolding \<open>gts = map g_type (m_globs m)\<close> list_all2_map2 
        gs_alloc list_all2_map1 alloc_glob_simple_def list_all2_conv_all_nth
        using \<open>length (m_globs m) = length g_inits\<close> 
        by(simp add:prod.case_eq_if) 

      ultimately have "list_all2 glob_typing gs gts" unfolding glob_typing_def
        by (simp add: list_all2_conv_all_nth) 
      then have "list_all2 (globi_agree (globs s@gs)) allocd_globs gts" 
        unfolding globi_agree_def allocd_interval
        by (simp add: list_all2_conv_all_nth) 
      then show ?thesis using \<open>globs s' = globs s @ gs\<close> by auto
    qed 
    ultimately show ?thesis using c_is by (simp add: list_all2_appendI) 
  qed
  moreover have "local \<C> = [] \<and> label \<C> = [] \<and> return \<C> = None" using c_is by auto
  ultimately have "inst_typing s' inst \<C>" using inst_typing.simps
    by (metis (full_types) inst.surjective old.unit.exhaust t_context.surjective) 

  show "store_typing s'"
  proof -
    have 1:"list_all (\<lambda>cl. \<exists>tf. cl_typing s' cl tf) (funcs s')" 
    proof -
      have "list_all (\<lambda>cl. \<exists>tf. cl_typing s cl tf) (funcs s)" 
        using store_typing_imp_cl_typing[OF assms(1)] unfolding list_all_length by blast
      then have "list_all (\<lambda>cl. \<exists>tf. cl_typing s1 cl tf) (funcs s)" 
        using cl_typing_store_extension_inv[OF \<open>store_extension s s1\<close>] 
        unfolding list_all_length by blast 
      then have "list_all (\<lambda>cl. \<exists>tf. cl_typing s2 cl tf) (funcs s)" 
        using cl_typing_store_extension_inv[OF \<open>store_extension s1 s2\<close>] 
        unfolding list_all_length by blast
      then have "list_all (\<lambda>cl. \<exists>tf. cl_typing s' cl tf) (funcs s)" 
        using cl_typing_store_extension_inv[OF \<open>store_extension s2 s'\<close>]
        unfolding list_all_length by blast

      moreover have "list_all (\<lambda>cl. \<exists>tf. cl_typing s' cl tf) fs" 
      proof -
        {
          fix f
          assume "f\<in>set fs"
          then obtain i_t loc_ts b_es where 1:
            "f = Func_native inst ((types inst)!i_t) loc_ts b_es"  
            "(i_t, loc_ts, b_es) \<in> set (m_funcs m)"
            unfolding alloc_module_funcs_form[OF s_alloc_module \<open>funcs s1 = funcs s @ fs\<close>]
             alloc_func_simple_def by fastforce 
          obtain tn tm where 2:
            "i_t < length (types_t \<C>)"
            "(types_t \<C>)!i_t = (tn _> tm)"
            "\<C>\<lparr>local := tn @ loc_ts, label := ([tm] @ (label \<C>)), return := Some tm\<rparr> \<turnstile> b_es : ([] _> tm)"
            using list_all2_in_set[OF 1(2) c_is(1)]
            unfolding module_func_typing.simps by auto 
          have 3:"(types_t \<C>)!i_t = (types inst)!i_t"
            using store_typing_imp_types_eq[OF \<open>inst_typing s' inst \<C>\<close> 2(1)] by -

          have "cl_typing s' f (tn _> tm)" 
            using cl_typing.intros(1)[OF \<open>inst_typing s' inst \<C>\<close> 2(2) 2(3)]
            unfolding 1(1) 3 by -
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
        using funci_agree_s' \<open>funcs s1 = funcs s'\<close> unfolding funci_agree_def
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
          using tabi_agree_s1 unfolding tabi_agree_def
          by (simp add: less_imp_le_nat list_all2_conv_all_nth list_all_length) 
        moreover have "list_all (\<lambda>e. e_tab e < length (inst.tabs inst)) (m_elem m)"
          using tabi_agree_s1 c_is(3) unfolding list_all2_conv_all_nth module_elem_typing.simps
          by (smt (verit, best) list_all_iff module_elem.select_convs(1)) 
        ultimately show ?thesis using s_element_in_bounds unfolding element_in_bounds_def
          by (smt (verit, best) list.rel_map(1) list_all2_conv_all_nth list_all_length)
      qed 

      have "list_all (tab_agree s) (tabs s)" using assms(1) unfolding store_typing.simps by auto
      then have "list_all (tab_agree s1) (tabs s)" 
        using tab_agree_store_extension_inv[OF \<open>store_extension s s1\<close>] 
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
    using instantiation_external_typing[OF s_alloc_module \<open>inst_typing s' inst \<C>\<close> c_is(5)] by -

  show "pred_option (\<lambda>i. i < length (s.funcs s')) start"
  proof(cases "m_start m")
  case None
    then show ?thesis using s_start by simp
  next
    case (Some a)
    have "a < length (inst.funcs inst)" using c_is(6) Some funci_agree_s' 
      unfolding module_start_typing.simps list_all2_conv_all_nth by simp
    then have "inst.funcs inst ! a < length (funcs s')" using list_all2_forget[OF funci_agree_s']
      unfolding funci_agree_def list_all_length by simp
    then show ?thesis using s_start Some by auto
  qed
qed

end