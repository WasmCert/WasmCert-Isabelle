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
  using list_all2_iff[of f xs ys] assms
  by simp (metis case_prodD in_set_impl_in_set_zip1 set_zip_rightD)

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
          "(instantiate s m v_imps ((s', inst, v_exps), init_es))"
  shows "store_typing s'"
        "\<exists>\<C>. (inst_typing s' inst \<C> \<and> (s'\<bullet>\<C> \<turnstile> init_es : ([] _> [])))"
        "\<exists>tes. list_all2 (\<lambda>v_exp te. external_typing s' (E_desc v_exp) te) v_exps tes"
        "store_extension s s'"
proof -
  obtain t_imps t_exps g_inits f e_offs d_offs start e_init_tabs e_init_mems where 
    "module_typing m t_imps t_exps"  
    and s_ext_typing:"list_all2 (external_typing s) v_imps t_imps"
    and s_alloc_module:"alloc_module s m v_imps g_inits (s', inst, v_exps)"
    and f_def:"f = \<lparr> f_locs = [], f_inst = inst \<rparr>"
    and g_inits_def:
    "list_all2 (\<lambda>g v. reduce_trans (s',f,$*(g_init g)) (s',f,[$C v])) (m_globs m) g_inits"
    and "list_all2 (\<lambda>e c. reduce_trans (s',f,$*(e_off e)) (s',f,[$C ConstInt32 c])) (m_elem m) e_offs"
    "list_all2 (\<lambda>d c. reduce_trans (s',f,$*(d_off d)) (s',f,[$C ConstInt32 c])) (m_data m) d_offs"
    and s_element_in_bounds:
    "list_all2 (\<lambda>e_off e. ((nat_of_int e_off) + (length (e_init e))) \<le> length (fst ((tabs s')!((inst.tabs inst)!(e_tab e))))) e_offs (m_elem m)"
    and s_data_in_bounds:
    "list_all2 (\<lambda>d_off d. ((nat_of_int d_off) + (length (d_init d))) \<le> mem_length ((mems s')!((inst.mems inst)!(d_data d)))) d_offs (m_data m)"
    and s_start:"(case (m_start m) of None \<Rightarrow> [] | Some i_s \<Rightarrow> [Invoke ((inst.funcs inst)!i_s)]) = start"
    and s_init_tabs:"List.map2 (\<lambda>n e. Init_tab n (map (\<lambda>i. (inst.funcs inst)!i) (e_init e))) (map nat_of_int e_offs) (m_elem m) = e_init_tabs"
    and s_init_mems:"List.map2 (\<lambda>n d. Init_mem n (d_init d)) (map nat_of_int d_offs) (m_data m) = e_init_mems"
    and init_es_is:"init_es = e_init_tabs@e_init_mems@start"
    using assms(2) instantiate.simps by auto

  show "store_extension s s'"
    using alloc_module_preserve_store_extension s_alloc_module
    by auto

  obtain \<C> \<C>' fts gts 
    where c_is:"list_all2 (module_func_typing \<C>) (m_funcs m) fts"
    "list_all (module_tab_typing) (m_tabs m)"
    "list_all (module_elem_typing \<C>) (m_elem m)"
    "list_all (module_data_typing \<C>) (m_data m)"
    "list_all2 (\<lambda>exp. module_export_typing \<C> (E_desc exp)) (m_exports m) t_exps"
    "pred_option (module_start_typing \<C>) (m_start m)"
    "\<C> = \<lparr>types_t=(m_types m), 
          func_t=ext_t_funcs t_imps @ fts, 
          global=ext_t_globs t_imps @ gts, 
          table=ext_t_tabs t_imps @ (m_tabs m), 
          memory=ext_t_mems t_imps @ (m_mems m), 
          local=[], label=[], return=None\<rparr>"
    "list_all2 (module_glob_typing \<C>') (m_globs m) gts"
    "\<C>' = \<lparr>types_t=[], func_t=[], global=ext_t_globs t_imps, table=[], memory=[], 
        local=[], label=[], return=None\<rparr>"
    "list_all (module_mem_typing) (m_mems m)"
    using \<open>module_typing m t_imps t_exps\<close> module_typing.simps
    by auto 

  obtain fs ts ms gs where s'_is:
    "funcs s' = funcs s @ fs" 
    "tabs s' = tabs s @ ts"
    "mems s' = mems s @ ms"
    "globs s' = globs s @ gs"
    using alloc_module_ext_arb[OF s_alloc_module]
    by metis

  have ts_alloc:"ts = alloc_tabs_simple (m_tabs m)" 
    using alloc_module_tabs_form[OF s_alloc_module s'_is(2)] by simp
  have ms_alloc:"ms = alloc_mems_simple (m_mems m)" 
    using alloc_module_mems_form[OF s_alloc_module s'_is(3)] by simp

  have tabi_agree_s1:"list_all2 (tabi_agree (tabs s')) (inst.tabs inst) (table \<C>)" 
  proof -
    define allocd_tabs where "allocd_tabs = snd (alloc_tabs s (m_tabs m))" 
    then have "inst.tabs inst = (ext_tabs v_imps)@allocd_tabs" 
      using alloc_module_allocated_form(2)[OF s_alloc_module]
      by (metis prod.collapse) 
    moreover have "list_all2 (tabi_agree (tabs s')) (ext_tabs v_imps) (ext_t_tabs t_imps)"
    proof -
      have "list_all2 (tabi_agree (tabs s)) (ext_tabs v_imps) (ext_t_tabs t_imps)" 
        using ext_typing_imp_tabi_agree[OF s_ext_typing] by -
      then show ?thesis
        unfolding tabi_agree_def s'_is(2)
        by (simp add: list_all2_mono nth_append)
    qed 
    moreover have "list_all2 (tabi_agree (tabs s')) allocd_tabs (m_tabs m)"
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
      then show ?thesis using s'_is(2) by auto
    qed
    ultimately show ?thesis
      using c_is by (simp add: list_all2_appendI)
  qed


  have memi_agree_s1:"list_all2 (memi_agree (mems s')) (inst.mems inst) (memory \<C>)" 
  proof -
    define allocd_mems where "allocd_mems = snd (alloc_mems s (m_mems m))" 
    then have "inst.mems inst = (ext_mems v_imps)@allocd_mems" 
      using alloc_module_allocated_form(3)[OF s_alloc_module]
      by (metis prod.collapse) 
    moreover have "list_all2 (memi_agree (mems s')) (ext_mems v_imps) (ext_t_mems t_imps)"
    proof -
      have "list_all2 (memi_agree (mems s)) (ext_mems v_imps) (ext_t_mems t_imps)" 
        using ext_typing_imp_memi_agree[OF s_ext_typing] by -
      then show ?thesis
        unfolding memi_agree_def s'_is(3)
        by (simp add: list_all2_mono nth_append)
    qed 
    moreover have "list_all2 (memi_agree (mems s')) allocd_mems (m_mems m)"
    proof -
      have "length ms = length (m_mems m)" using ms_alloc by auto
      then have allocd_interval:"allocd_mems = [length (mems s) ..< (length (mems s) + length ms)]" 
        using allocd_mems_def alloc_mems_range surjective_pairing by metis  

      have "list_all2 mem_typing ms (m_mems m)" 
        unfolding ms_alloc alloc_mem_simple_def mem_typing_def list.rel_map(1) limits_compat_def
          mem_mk_def mem_rep_mk_def mem_size_def mem_length_def mem_rep_length_def bytes_replicate_def
          mem_max_def 
        by(rule list_all2_refl, simp add: pred_option_def mem_rep.Abs_mem_rep_inverse Ki64_def)        

      then have "list_all2 (memi_agree (mems s@ms)) allocd_mems (m_mems m)" 
        unfolding memi_agree_def allocd_interval 
        by (simp add: list_all2_conv_all_nth) 
      then show ?thesis using s'_is(3) by auto
    qed
    ultimately show ?thesis
      using c_is by(simp add: list_all2_appendI)
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
        using alloc_module_funcs_form[OF s_alloc_module s'_is(1)] by -
      then have "length fs = length (m_funcs m)" by auto
      then have allocd_interval:"allocd_funcs = [length (funcs s) ..< (length (funcs s) + length fs)]" 
        using allocd_funcs_def alloc_funcs_range surjective_pairing by metis  

      have "list_all2 (\<lambda>f i. cl_type f = (types inst)!(fst i)) fs (m_funcs m)" 
        unfolding cl_type_def alloc_func_simple_def fs_alloc list.rel_map(1) 
        by(simp add: list_all2_refl split:prod.splits)

      moreover 
     have "(\<And>x y.
              module_func_typing \<C> x y \<Longrightarrow>
                fst x < length (types_t \<C>) \<and> types_t \<C> ! fst x = y)"
       unfolding module_func_typing.simps
       by fastforce
     hence "list_all2 (\<lambda>f ft. (fst f) < length (types_t \<C>)\<and> (types_t \<C>)!(fst f) = ft) 
          (m_funcs m) fts"
        using list_all2_mono[OF c_is(1)]
        by simp

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
    using tabi_agree_store_extension
      list_all2_mono[OF tabi_agree_s1]
    by blast
  moreover have memi_agree_s':"list_all2 (memi_agree (mems s')) (inst.mems inst) (memory \<C>)"
    using memi_agree_store_extension
      list_all2_mono[OF memi_agree_s1]
    by blast


  moreover have globi_agree_s':"list_all2 (globi_agree (globs s')) (inst.globs inst) (global \<C>)"
  proof - 
    define allocd_globs where "allocd_globs = snd (alloc_globs s (m_globs m) g_inits)" 
    then have "inst.globs inst = (ext_globs v_imps)@allocd_globs" 
      using alloc_module_allocated_form(4)[OF s_alloc_module]
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
        using alloc_module_globs_form[OF s_alloc_module s'_is(4)]
        by simp
      then have "length gs = length (m_globs m)" using \<open>length (m_globs m) = length g_inits\<close>
        by auto
      then have allocd_interval:"allocd_globs = [length (globs s) ..< (length (globs s) + length gs)]" 
        using allocd_globs_def alloc_globs_range surjective_pairing \<open>length (m_globs m) = length g_inits\<close>
        by (metis min.idem)   

      have "list_all2 (\<lambda>g gt. gt = g_type g) (m_globs m) gts" 
        unfolding module_glob_typing.simps 
        by (metis (mono_tags, lifting) c_is(8) list_all2_mono module_glob_typing_equiv_module_glob_type_checker)
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
          have 3:"reduce_trans (s',f,$*(g_init g)) (s',f,[$C v])" 
            using g_inits_def assm zip_agree unfolding list_all2_conv_all_nth in_set_conv_nth
            by fastforce 
          have 4:"global \<C>' = ext_t_globs t_imps" unfolding c_is(9) by simp 

          have "tg_t (g_type g) = typeof v"
            using const_exprs_reduce_trans[OF 1 2 3 4
                list_all2_external_typing_glob_alloc[OF s_ext_typing] s'_is(4)]
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
  ultimately have s'_inst_t:"inst_typing s' inst \<C>" using inst_typing.simps
    by (metis (full_types) inst.surjective old.unit.exhaust t_context.surjective) 


  have "length (inst.mems inst) = length (memory \<C>)" using memi_agree_s1 
    unfolding list_all2_conv_all_nth by simp


  show "store_typing s'"
  proof -
    have 1:"list_all (\<lambda>cl. \<exists>tf. cl_typing s' cl tf) (funcs s')" 
    proof -
      have "list_all (\<lambda>cl. \<exists>tf. cl_typing s cl tf) (funcs s)" 
        using store_typing_imp_cl_typing[OF assms(1)] unfolding list_all_length by blast
      then have "list_all (\<lambda>cl. \<exists>tf. cl_typing s' cl tf) (funcs s)" 
        using cl_typing_store_extension_inv[OF \<open>store_extension s s'\<close>]
        unfolding list_all_length by blast

      moreover have "list_all (\<lambda>cl. \<exists>tf. cl_typing s' cl tf) fs" 
      proof -
        {
          fix f
          assume "f\<in>set fs"
          then obtain i_t loc_ts b_es where 1:
            "f = Func_native inst ((types inst)!i_t) loc_ts b_es"  
            "(i_t, loc_ts, b_es) \<in> set (m_funcs m)"
            unfolding alloc_module_funcs_form[OF s_alloc_module s'_is(1)]
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
      have 1:"list_all (\<lambda>i. i< length (funcs s')) (inst.funcs inst)" 
        using funci_agree_s' s'_is(1) unfolding funci_agree_def
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
        then have "list_all (\<lambda>i. (inst.funcs inst)!i < length (s.funcs s')) (e_init e)" using 1
          by (metis list_all_length)
      }
      then have 1:"list_all (element_funcs_in_bounds s' inst) (m_elem m)" by (metis list_all_iff) 

      have 2:"list_all2 (element_in_bounds s' inst) (map nat_of_int e_offs) (m_elem m)"  
      proof -
        have "list_all (\<lambda>i. i < length (tabs s')) (inst.tabs inst)" 
          using tabi_agree_s1 unfolding tabi_agree_def
          by (simp add: less_imp_le_nat list_all2_conv_all_nth list_all_length) 
        moreover have "list_all (\<lambda>e. e_tab e < length (inst.tabs inst)) (m_elem m)"
          using tabi_agree_s1 c_is(3)
          unfolding list_all2_conv_all_nth module_elem_typing.simps list_all_length
          by auto
        ultimately show ?thesis using s_element_in_bounds
          unfolding element_in_bounds_def list_all2_conv_all_nth list_all_length
          by auto
      qed
      have "list_all (tab_agree s) (tabs s)" using assms(1) unfolding store_typing.simps by auto
      then have "list_all (tab_agree s') (tabs s)" 
        using tab_agree_store_extension_inv[OF \<open>store_extension s s'\<close>] 
        by (simp add: list_all_length)
      moreover have "list_all (tab_agree s') ts" 
        using \<open>list_all (module_tab_typing) (m_tabs m)\<close> 
        unfolding ts_alloc alloc_tab_simple_def tab_agree_def list.pred_map(1) comp_def 
        limit_typing.simps
        by(simp add:list.pred_set, auto)
      ultimately show "list_all (tab_agree s') (tabs s')"
        using s'_is(2)
        by simp 
    qed
    have 3:"list_all mem_agree (mems s')"
    proof -
      have "list_all2 (data_in_bounds s' inst) (map nat_of_int d_offs) (m_data m)"
      proof -
        have "list_all (\<lambda>i. i < length (mems s')) (inst.mems inst)" 
          using list_all2_forget[OF memi_agree_s1] list.pred_mono_strong unfolding memi_agree_def
          by fastforce 
        moreover have "list_all (\<lambda>d. d_data d < length (inst.mems inst)) (m_data m)"
          using c_is(4) unfolding \<open>length (inst.mems inst) = length (memory \<C>)\<close> 
            module_data_typing.simps  list_all_length by auto
        ultimately show ?thesis using s_data_in_bounds unfolding data_in_bounds_def
          Let_def list.rel_map(1) list_all2_conv_all_nth list_all_length by(simp)
      qed
      then have 1:"list_all2 (data_in_bounds s' inst) (map nat_of_int d_offs) (m_data m)" 
        unfolding data_in_bounds_def
        by auto

      have "list_all mem_agree (mems s)" using assms(1) unfolding store_typing.simps by auto
      moreover have "list_all mem_agree ms" 
        using \<open>list_all (module_mem_typing) (m_mems m)\<close> 
        unfolding ms_alloc alloc_mem_simple_def limit_typing.simps list.pred_map(1) comp_def
        mem_mk_def mem_rep_mk_def 
        by(simp add:list.pred_set bytes_replicate_def 
            mem_size_def mem_length_def mem_rep_length.abs_eq Ki64_def mem_max_def, fastforce)

      ultimately show "list_all mem_agree (mems s')"
        unfolding s'_is(3)
        by simp
    qed
    show ?thesis
      using 1 2 3 store_typing.intros
      by blast
  qed

  show "\<exists>tes. list_all2 (\<lambda>v_exp te. external_typing s' (E_desc v_exp) te) v_exps tes"
    using instantiation_external_typing[OF s_alloc_module \<open>inst_typing s' inst \<C>\<close> c_is(5)] by -


  show "\<exists>\<C>. (inst_typing s' inst \<C> \<and> (s'\<bullet>\<C> \<turnstile> init_es : ([] _> [])))"
  proof -
    have "s'\<bullet>\<C> \<turnstile> (case (m_start m) of None \<Rightarrow> [] | Some i_s \<Rightarrow> [Invoke ((inst.funcs inst)!i_s)]) : ([] _> [])"
    proof (cases "m_start m")
      case None
      thus ?thesis
        by (simp add: e_type_empty)
    next
      case (Some a)
      have a_type:"a < length (inst.funcs inst)"
                  "(func_t \<C>)!a = ([] _> [])" using c_is(6) Some funci_agree_s' 
          unfolding module_start_typing.simps list_all2_conv_all_nth by simp_all
        then have "inst.funcs inst ! a < length (funcs s')" using list_all2_forget[OF funci_agree_s']
          unfolding funci_agree_def list_all_length by simp
        moreover have "cl_type ((funcs s')!(inst.funcs inst ! a)) = ([] _> [])"
          using a_type(1,2) c_is(7)
          by (metis funci_agree_def funci_agree_s' list_all2_conv_all_nth)
        ultimately show ?thesis
          using e_typing_l_typing.intros(6) Some
          by simp
      qed
      moreover have "s'\<bullet>\<C> \<turnstile> e_init_tabs : ([] _> [])"
      proof -
        have "length e_offs = length (m_elem m)"
          using s_element_in_bounds list_all2_lengthD
          by auto
        thus ?thesis
          using c_is(3) s_init_tabs
        proof (induction "m_elem m" arbitrary: e_offs e_init_tabs m rule: list.induct)
          case Nil
          thus ?case
            by (simp add: e_type_empty)
        next
          case (Cons a x)
          obtain e_off e_offs' where
            e_off_is:"e_off#e_offs' = e_offs" "length e_offs' = length x"
            using Cons(3) Cons(2)[symmetric] 
            by (metis length_Suc_conv)
          then obtain e_init_tab e_init_tabs' where
            e_init_tab_is:"e_init_tab#e_init_tabs' = e_init_tabs"
                          "length x = length e_init_tabs'"
                          "(Init_tab (nat_of_int e_off) (map (\<lambda>i. (inst.funcs inst)!i) (e_init a))) = e_init_tab"
                          "map2 (\<lambda>x y. Init_tab x (map (\<lambda>i. (inst.funcs inst)!i) (e_init y))) (map nat_of_int e_offs') x = e_init_tabs'"
            using Cons(5) Cons(2)[symmetric]
            by fastforce
          have "(module_elem_typing \<C> a)"
            using Cons(2,4)
            by (metis list_all_simps(1))
          hence len_tab_c:"length (table \<C>) > 0"
                          "list_all (\<lambda>ti. ti < length (s.funcs s')) (map (\<lambda>i. (inst.funcs inst)!i) (e_init a))"
            using c_is(7) funci_agree_s' inst_typing_func_length s'_inst_t
            unfolding funci_agree_def list_all2_conv_all_nth list_all_length module_elem_typing.simps
            by fastforce+
          hence "s'\<bullet>\<C> \<turnstile> [e_init_tab] : ([] _> [])"
            using e_init_tab_is(3) e_typing_l_typing.intros(9) len_tab_c(1)
            by (metis le_refl less_one nat_less_le nat_neq_iff)
          moreover
          have "s'\<bullet>\<C> \<turnstile> e_init_tabs' : ([] _> [])"
            using Cons(1)[of "\<lparr>m_types=[], m_funcs=[],m_tabs=[], m_mems=[], m_globs=[], m_elem=x, m_data=[],m_start=None,m_imports=[],m_exports=[]\<rparr>" "e_offs'" "e_init_tabs'"]
                  Cons(2,3,4) e_off_is e_init_tab_is
            by simp (metis list_all_simps(1))
          ultimately
          show ?case
            using e_init_tab_is(1) e_type_comp_conc
            by fastforce
        qed
      qed
    moreover have "s'\<bullet>\<C> \<turnstile> e_init_mems : ([] _> [])"
      proof -
        have "length d_offs = length (m_data m)"
          using s_data_in_bounds list_all2_lengthD
          by auto
        thus ?thesis
          using c_is(4) s_init_mems
        proof (induction "m_data m" arbitrary: d_offs e_init_mems m rule: list.induct)
          case Nil
          thus ?case
            by (simp add: e_type_empty)
        next
          case (Cons a x)
          obtain d_off d_offs' where
            e_off_is:"d_off#d_offs' = d_offs" "length d_offs' = length x"
            using Cons(3) Cons(2)[symmetric] 
            by (metis length_Suc_conv)
          then obtain e_init_mem e_init_mems' where
            e_init_mem_is:"e_init_mem#e_init_mems' = e_init_mems"
                          "length x = length e_init_mems'"
                          "(Init_mem (nat_of_int d_off) (d_init a)) = e_init_mem"
                          "map2 (\<lambda>x y. Init_mem x (d_init y)) (map nat_of_int d_offs') x = e_init_mems'"
            using Cons(5) Cons(2)[symmetric]
            by fastforce
          have "(module_data_typing \<C> a)"
            using Cons(2,4)
            by (metis list_all_simps(1))
          hence len_tab_c:"length (memory \<C>) > 0"
            unfolding module_data_typing.simps
            by auto
          hence "s'\<bullet>\<C> \<turnstile> [e_init_mem] : ([] _> [])"
            using e_init_mem_is(3) e_typing_l_typing.intros(8)
            by (metis le_refl less_one nat_less_le nat_neq_iff)
          moreover
          have "s'\<bullet>\<C> \<turnstile> e_init_mems' : ([] _> [])"
            using Cons(1)[of "\<lparr>m_types=[], m_funcs=[],m_tabs=[], m_mems=[], m_globs=[], m_elem=[], m_data=x,m_start=None,m_imports=[],m_exports=[]\<rparr>" "d_offs'" "e_init_mems'"]
                  Cons(2,3,4) e_off_is e_init_mem_is
            by simp (metis list_all_simps(1))
          ultimately
          show ?case
            using e_init_mem_is(1) e_type_comp_conc
            by fastforce
        qed
      qed
    ultimately have "(s'\<bullet>\<C> \<turnstile> init_es : ([] _> []))"
      using e_type_comp_conc init_es_is s_start
      by fastforce
    thus ?thesis
      using  s'_inst_t
    by auto
  qed
qed

end