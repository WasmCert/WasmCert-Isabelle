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

lemma tab_subtyping_exists:"\<exists>tt. tab_subtyping t tt" 
  using tab_subtyping_refl tab_subtyping_def
  by (metis limit_t.select_convs(1,2) limits_compat_def) 

lemma mem_subtyping_exists:"\<exists>mt. mem_subtyping m mt" 
  using limits_compat_refl mem_subtyping_def
  by (metis limit_t.select_convs(1,2) limits_compat_def) 

lemma glob_typing_exists:"\<exists>gt. glob_typing g gt" 
  unfolding glob_typing_def typeof_def
  by (metis tg.select_convs(1,2))

lemma instantiation_external_typing:
  assumes "alloc_module s m v_imps g_inits el_inits (s1, inst, v_exps)"
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
      unfolding external_typing.simps by (simp add: tab_subtyping_exists)  
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
      unfolding external_typing.simps by (simp add: mem_subtyping_exists)  
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


lemma b_e_type_preserved_refs:
  assumes "\<C> \<turnstile> b_es : (tn _> tm)"
          "\<C>'=\<C>\<lparr>refs := [0..< length (func_t \<C>)] \<rparr>"
        shows "\<C>' \<turnstile> b_es : (tn _> tm)"
  using assms
proof -
  have refs_subset_helper:
    "types_t \<C>' = types_t \<C>"
    "func_t \<C>' = func_t \<C>"
    "elem \<C>' = elem \<C>"
    "data \<C>' = data \<C>"
    "table \<C>' = table \<C>"
    "memory \<C>' = memory \<C>"
    "local \<C>' = local \<C>"
    "label \<C>' = label \<C>"
    "return \<C>' = return \<C>"
    using assms by auto
  show ?thesis
    using assms refs_subset_helper
  proof(induction \<C> b_es "tn _> tm" arbitrary: tn tm \<C>' rule: b_e_typing.induct)
    case (const_num \<C> v)
    then show ?case using b_e_typing.const_num by metis
  next
    case (const_vec \<C> v)
    then show ?case using b_e_typing.intros by metis
  next
    case (unop op t \<C>)
    then show ?case using b_e_typing.intros by metis
  next
    case (binop op t \<C>)
    then show ?case using b_e_typing.intros by metis
  next
    case (testop t \<C> uu)
    then show ?case using b_e_typing.intros by metis
  next
    case (relop op t \<C>)
    then show ?case using b_e_typing.intros by metis
  next
    case (ref_null \<C> t)
    then show ?case using b_e_typing.intros by metis
  next
    case (ref_is_null \<C> t)
    then show ?case using b_e_typing.intros by metis
  next
    case (ref_func j \<C>)
    have "j \<in> set (refs \<C>')" "j < length (func_t \<C>')" using ref_func(1,2,3,4)
      by auto
    then show ?case using b_e_typing.ref_func[of j \<C>'] by auto
  next
    case (unop_vec \<C> op)
    then show ?case using b_e_typing.intros by metis
  next
    case (binop_vec op \<C>)
    then show ?case using b_e_typing.intros by metis
  next
    case (ternop_vec \<C> op)
    then show ?case using b_e_typing.intros by metis
  next
    case (test_vec \<C> op)
    then show ?case using b_e_typing.intros by metis
  next
    case (shift_vec \<C> op)
    then show ?case using b_e_typing.intros by metis
  next
    case (splat_vec \<C> sv)
    then show ?case using b_e_typing.intros by metis
  next
    case (extract_vec i sv sx \<C>)
    then show ?case using b_e_typing.intros by metis
  next
    case (replace_vec i sv \<C>)
    then show ?case using b_e_typing.intros by metis
  next
    case (convert t1 t2 sat_sx \<C>)
    then show ?case using b_e_typing.convert by metis
  next
    case (reinterpret t1 t2 \<C>)
    then show ?case using b_e_typing.intros by metis
  next
    case (unreachable \<C>)
    then show ?case using b_e_typing.intros by metis
  next
    case (nop \<C>)
    then show ?case using b_e_typing.intros by metis
  next
    case (drop \<C> t)
    then show ?case using b_e_typing.intros by metis
  next
    case (select t_tag t \<C>)
    then show ?case using b_e_typing.select by metis
  next
    case (block \<C> tb tn tm es)
    then show ?case using b_e_typing.block tb_tf_t_def
      apply (cases \<C> rule:t_context.cases)
      by (auto split: tb.splits)
  next
    case (loop \<C> tb es)
    then show ?case using b_e_typing.loop tb_tf_t_def
      apply (cases \<C> rule:t_context.cases)
      by (auto split: tb.splits)
  next
    case (if_wasm \<C> tb tn es1 es2)
    then show ?case using b_e_typing.if_wasm tb_tf_t_def
      apply (cases \<C> rule:t_context.cases)
      by (auto split: tb.splits)
  next
    case (br i \<C> ts t1s)
    then show ?case using b_e_typing.intros by metis
  next
    case (br_if i \<C>)
    then show ?case using b_e_typing.br_if by metis
  next
    case (br_table \<C> ts "is" i t1s)
    then show ?case using b_e_typing.br_table by metis
  next
    case (return \<C> ts t1s)
    then show ?case using b_e_typing.intros by metis
  next
    case (call i \<C>)
    then show ?case using b_e_typing.intros by metis
  next
    case (call_indirect i \<C> t1s ti uv)
    then show ?case using b_e_typing.call_indirect by metis
  next
    case (get_local i \<C> t)
    then show ?case using b_e_typing.get_local by metis
  next
    case (set_local i \<C> t)
    then show ?case using b_e_typing.intros by metis
  next
    case (tee_local i \<C> t)
    then show ?case using b_e_typing.intros by metis
  next
    case (get_global i \<C> t)
    then show ?case using b_e_typing.get_global by auto
  next
    case (set_global i \<C> t)
    then show ?case using b_e_typing.set_global by auto
  next
    case (load \<C> a tp_sx t off)
    then show ?case using b_e_typing.load by simp
  next
    case (store \<C> a tp t off)
    then show ?case using b_e_typing.store by simp
  next
    case (load_vec \<C> lvop a off)
    then show ?case using b_e_typing.load_vec by simp
  next
    case (load_lane_vec \<C> i svi a off)
    then show ?case using b_e_typing.load_lane_vec by simp
  next
    case (store_vec \<C> svop a off)
    then show ?case using b_e_typing.store_vec by simp
  next
    case (current_memory \<C>)
    then show ?case using b_e_typing.current_memory by simp
  next
    case (grow_memory \<C>)
    then show ?case using b_e_typing.grow_memory by simp
  next
    case (table_set ti \<C> tr)
    then show ?case using b_e_typing.table_set by simp
  next
    case (table_get ti \<C> tr)
    then show ?case using b_e_typing.table_get by simp
  next
    case (table_size ti \<C>)
    then show ?case using b_e_typing.table_size by simp
  next
    case (table_grow ti \<C> tr)
    then show ?case using b_e_typing.table_grow by simp
  next
    case (empty \<C>)
    then show ?case using b_e_typing.empty by blast
  next
    case (composition \<C> es t2s e)
    then show ?case using b_e_typing.composition by auto
  next
    case (subsumption \<C> es tf1 tf2)
    then show ?case using b_e_typing.subsumption by auto
  next
    case (memory_init \<C> i)
    then show ?case using b_e_typing.memory_init by metis
  next
    case (memory_copy \<C>)
    then show ?case using b_e_typing.memory_copy by metis
  next
    case (memory_fill \<C>)
    then show ?case using b_e_typing.memory_fill by metis
  next
    case (table_init x \<C> y tr)
    then show ?case using b_e_typing.table_init by metis
  next
    case (table_copy x \<C> tr y)
    then show ?case using b_e_typing.table_copy by metis
  next
    case (table_fill x \<C> tr)
    then show ?case using b_e_typing.table_fill by metis
  next
    case (elem_drop x \<C>)
    then show ?case using b_e_typing.elem_drop by simp
  next
    case (data_drop x \<C>)
    then show ?case using b_e_typing.data_drop by simp
  qed
qed

(*
lemma alloc_module_helper:
  assumes
    "alloc_module s m v_imps g_inits el_inits (s', inst, v_exps)"
    "module_typing m t_imps t_exps"
    "x \<in> set (collect_funcidxs_module (m\<lparr>m_funcs := [], m_start := None\<rparr>))"
  shows
    "x < length (inst.funcs inst)"
proof -
  obtain from_elems from_datas where defs:
    "from_elems = concat (map collect_funcidxs_module_elem (m_elems m))"
    "from_datas = concat (map collect_funcidxs_module_data (m_datas m))"
    "(collect_funcidxs_module (m\<lparr>m_funcs := [], m_start := None\<rparr>)) = remdups (concat [from_elems, from_datas])"
    by auto
  consider
      (a) "x \<in> set from_elems"
    | (b) "x \<in> set from_datas"
    using defs(3) assms(3) by auto
  thus ?thesis
  proof(cases)
    case a
    then show ?thesis sorry
  next
    case b
    then show ?thesis sorry
  qed
qed


lemma alloc_module_prop:
  assumes
    "alloc_module s m v_imps g_inits el_inits (s', inst, v_exps)"
      "module_typing m t_imps t_exps"
    shows
     "set (collect_funcidxs_module (module\<lparr>m_funcs := [], m_start := None\<rparr>)) \<le> set ([0..< length (inst.funcs inst)])"
  sorry *)

theorem instantiation_sound:
  assumes "store_typing s"
          "(instantiate s m v_imps ((s', inst, v_exps), init_es))"
  shows "store_typing s'"
        "\<exists>\<C>. (inst_typing s' inst \<C> \<and> (s'\<bullet>\<C> \<turnstile> init_es : ([] _> [])))"
        "\<exists>tes. list_all2 (\<lambda>v_exp te. external_typing s' (E_desc v_exp) te) v_exps tes"
        "store_extension s s'"
proof -
  obtain t_imps t_exps g_inits el_inits f start where 
    m_typing:"module_typing m t_imps t_exps"  
    and s_ext_typing:"list_all2 (external_typing s) v_imps t_imps"
    and s_alloc_module:"alloc_module s m v_imps g_inits el_inits (s', inst, v_exps)"
    and f_def:"f = \<lparr> f_locs = [], f_inst = inst \<rparr>"
    and g_inits_def:
    "list_all2 (\<lambda>g v. reduce_trans (s',f,$*(g_init g)) (s',f,[$C v])) (m_globs m) g_inits"
    and el_inits_def:
    "list_all2 (\<lambda>el vs. list_all2 (\<lambda> el_init v. reduce_trans (s',f,$*(el_init)) (s',f,[$C (V_ref v)])) (e_init el) vs) (m_elems m) el_inits"
    and s_start:"(case (m_start m) of None \<Rightarrow> [] | Some i_s \<Rightarrow> [Invoke ((inst.funcs inst)!i_s)]) = start"
    and init_es_is:"init_es = (run_elems (m_elems m))@(run_datas (m_datas m))@start"
    using assms(2) instantiate.simps by auto

  show "store_extension s s'"
    using alloc_module_preserve_store_extension s_alloc_module
    by auto

  obtain \<C> \<C>' fts gts rts dts
    where c_is:"list_all2 (module_func_typing \<C>) (m_funcs m) fts"
    "list_all (module_tab_typing) (m_tabs m)"
    "list_all2 (module_elem_typing \<C>') (m_elems m) rts"
    "list_all (module_data_typing \<C>') (m_datas m)"
    "list_all2 (module_glob_typing \<C>') (m_globs m) gts"
    "list_all2 (\<lambda>exp. module_export_typing \<C> (E_desc exp)) (m_exports m) t_exps"
    "pred_option (module_start_typing \<C>) (m_start m)"
    "\<C> = \<lparr>types_t=(m_types m),
       func_t=ext_t_funcs t_imps @ fts,
       global=ext_t_globs t_imps @ gts,
       elem=rts,
       data=dts,
       table=ext_t_tabs t_imps @ (m_tabs m),
       memory=ext_t_mems t_imps @ (m_mems m),
       local=[],
       label=[],
       return=None,
       refs=collect_funcidxs_module (m\<lparr>m_funcs := [], m_start := None\<rparr>)\<rparr>"
    "\<C>' = \<C>\<lparr>global := ext_t_globs t_imps\<rparr>"
    "length dts = length (m_datas m)"
    "list_all (module_mem_typing) (m_mems m)"
    using m_typing module_typing.simps
    by auto 

  obtain fs ts ms gs els ds where s'_is:
    "funcs s' = funcs s @ fs" 
    "tabs s' = tabs s @ ts"
    "mems s' = mems s @ ms"
    "globs s' = globs s @ gs"
    "elems s' = elems s @ els"
    "datas s' = datas s @ ds"
    using alloc_module_ext_arb[OF s_alloc_module]
    by metis

  have ts_alloc:"ts = alloc_tabs_simple (m_tabs m)" 
    using alloc_module_tabs_form[OF s_alloc_module s'_is(2)] by simp
  have ms_alloc:"ms = alloc_mems_simple (m_mems m)" 
    using alloc_module_mems_form[OF s_alloc_module s'_is(3)] by simp
  have els_alloc:"els = alloc_elems_simple (m_elems m) el_inits"
    using alloc_module_elems_form[OF s_alloc_module s'_is(5)] by simp

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

      have "list_all2 tab_subtyping (map fst ts) (m_tabs m)" 
        unfolding ts_alloc alloc_tab_simple_def list.rel_map(1) limits_compat_def
        by(simp add:list_all2_refl tab_subtyping_refl pred_option_def)

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

      have "list_all2 mem_subtyping (map fst ms) (m_mems m)" 
        unfolding ms_alloc alloc_mem_simple_def mem_subtyping_def list.rel_map(1) limits_compat_def
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

  have types_inst_context: "types inst = types_t \<C>" 
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


  moreover have globi_agree_s':"list_all2 (globi_agree (globs s')) (inst.globs inst) (global \<C>)" "list_all (glob_agree s') (s.globs s')"
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
    moreover have "list_all2 (globi_agree (globs s')) allocd_globs gts" "map g_val gs = g_inits" "list_all (glob_agree s') (globs s')"
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
        using c_is(5)
        by (metis (mono_tags, lifting) list_all2_mono module_glob_typing_equiv_module_glob_type_checker)
      then have "gts = map g_type (m_globs m)"
        unfolding list_all2_conv_all_nth 
        by (metis map_intro_length) 

      have g_inits_props2: "map tg_t gts = map typeof g_inits" "list_all (\<lambda> g_v. v_typing s' g_v (typeof g_v)) g_inits"  (*from typing preservation*)
      proof - 
        {
          fix g v
          assume assm:"(g, v) \<in> set (zip (m_globs m) g_inits)"

          have 1:"const_exprs \<C>' (g_init g)" using c_is(5) zip_agree assm
            unfolding module_glob_typing.simps list_all2_conv_all_nth
            by (metis in_set_conv_nth module_glob.select_convs(2) set_zip_leftD) 
          have 2:"\<C>' \<turnstile> g_init g : ([] _> [tg_t (g_type g)])" using c_is(5) zip_agree assm
            unfolding module_glob_typing.simps list_all2_conv_all_nth
            by (metis in_set_conv_nth module_glob.select_convs(1,2) set_zip_leftD) 
          have 3:"reduce_trans (s',f,$*(g_init g)) (s',f,[$C v])" 
            using g_inits_def assm zip_agree unfolding list_all2_conv_all_nth in_set_conv_nth
            by fastforce 
          have 4:"global \<C>' = ext_t_globs t_imps" unfolding c_is(9) by simp 
          have 5: "length (inst.funcs inst) =length (func_t \<C>')"
            using funci_agree_s' c_is(9)
            by (simp add: list_all2_lengthD)

          have "v_typing s' v (typeof v)"
          proof -
            consider
              (a) v' where "$* g_init g = [$C v'] \<and> typeof v' = tg_t (g_type g)"
            | (b) j t' where "t' <t: tg_t (g_type g) \<and>
      g_init g = [Get_global j] \<and> j < length (global \<C>') \<and> tg_mut (global \<C>' ! j) = T_immut \<and> tg_t (global \<C>' ! j) = t'"
            | (c) j where "g_init g = [Ref_func j] \<and> j < length (func_t \<C>') \<and> tg_t (g_type g) = T_ref T_func_ref"
            | (d) t_r where "g_init g = [Ref_null t_r] \<and> tg_t (g_type g) = T_ref t_r"
              using const_exprs_is[OF 1 2] by auto
            thus ?thesis
            proof(cases)
              case a
              have v_v'_eq: "v =v'" using  3 a reduce_trans_consts[of s' f "[v']" s' f "[v]"] by auto
              consider (1) v_n where "g_init g = [EConstNum v_n]" "v' = V_num v_n" | (2)  v_v where "g_init g = [EConstVec v_v]" "v' = V_vec v_v"
                using 1 2 typeof_def v_to_e_def a
                by (auto split: v_num.splits v.splits)
              then show ?thesis using v_v'_eq v_typing.simps typeof_def
              proof(cases)
              qed (simp_all split: v.splits)
            next
              case b
              then have b1: "reduce_trans (s', f, $* g_init g) (s', f, [$C ((sglob_val s' (f_inst f) j))])"
                using 3 reduce.get_global[of s' f j] reduce_trans_def
                apply auto
                by (metis (no_types, lifting) reduce_trans_app_end rtranclp.rtrancl_refl)
              then have "sglob_val s' (f_inst f) j = v" using 3 const_exprs_reduce_trans[OF 1 2 3 4
                list_all2_external_typing_glob_alloc[OF s_ext_typing] s'_is(4) s'_is(4) _ \<open>inst.globs inst = (ext_globs v_imps)@allocd_globs\<close> _ 5,
                of _ "[]" "[]" "[]"]
                \<open>inst.globs inst = (ext_globs v_imps)@allocd_globs\<close>
                f_def
                const_exprs_reduce_trans[OF 1 2 b1 4
                list_all2_external_typing_glob_alloc[OF s_ext_typing] s'_is(4) s'_is(4) _ \<open>inst.globs inst = (ext_globs v_imps)@allocd_globs\<close> _ 5,
                of _ "[]" "[]" "[]"] by auto

              then have "v = g_val ((globs s')!((inst.globs inst)!j))"
                
                by (simp add: f_def sglob_def sglob_ind_def sglob_val_def)
              have "j < length (global \<C>')" "j < length (ext_globs v_imps)"
                using b apply blast
                by (metis "4" b calculation(2) list_all2_lengthD)
              
              have "list_all2 (globi_agree (globs s)) (ext_globs v_imps) (ext_t_globs t_imps)"
                using ext_typing_imp_globi_agree s_ext_typing by force
              then have "(((ext_globs v_imps))!j) < length (globs s)"
                unfolding globi_agree_def
                using "4" b list_all2_nthD2 by auto
            
              then have "((inst.globs inst)!j) < length (globs s)"
                by (simp add: \<open>j < length (ext_globs v_imps)\<close> calculation(1) nth_append)
              then have "glob_agree s (globs s! (((inst.globs inst)!j)))"
                
                by (meson assms(1) list_all_length store_typing.simps)
              then have "glob_agree s (globs s'! (((inst.globs inst)!j)))"
                using s'_is(4)
                by (simp add: \<open>inst.globs inst ! j < length (s.globs s)\<close> nth_append)
              then have "glob_agree s' (globs s'! (((inst.globs inst)!j)))"
                using s'_is(4)
                using \<open>store_extension s s'\<close> glob_agree_store_extension_inv by blast
              
              then show ?thesis unfolding glob_agree_def
                using \<open>v = g_val (s.globs s' ! (inst.globs inst ! j))\<close> v_typing_typeof by blast
            next
              case c
              then have c1: "reduce_trans (s', f, $* g_init g) (s', f, [$C (V_ref (ConstRefFunc (inst.funcs (f_inst f)! j)))])"
                using 3 reduce.ref_func reduce_trans_def v_to_e_def
                apply auto
                by (metis (no_types, lifting) reduce_trans_app_end rtranclp.rtrancl_refl)
              then have v_is: "V_ref (ConstRefFunc (inst.funcs (f_inst f)! j)) = v" using 3 
                \<open>inst.globs inst = (ext_globs v_imps)@allocd_globs\<close>
                f_def
                const_exprs_reduce_trans[OF 1 2 3 4
                list_all2_external_typing_glob_alloc[OF s_ext_typing] s'_is(4) s'_is(4) _ \<open>inst.globs inst = (ext_globs v_imps)@allocd_globs\<close> _ 5,
                of allocd_globs "[]" "[]" "[]"]
                const_exprs_reduce_trans[OF 1 2 c1 4
                list_all2_external_typing_glob_alloc[OF s_ext_typing] s'_is(4) s'_is(4) _ \<open>inst.globs inst = (ext_globs v_imps)@allocd_globs\<close> _ 5,
                of _ "[]" "[]" "[]"]
                by auto

              have "list_all2 (funci_agree (funcs s')) (inst.funcs inst) (func_t \<C>')"
                using c_is(9) funci_agree_s' by auto

              then have "(inst.funcs (f_inst f)! j) < length (funcs s')" using c
                unfolding funci_agree_def
                using "5" f_def list_all2_nthD by fastforce
              then show ?thesis using typeof_def typeof_ref_def v_is ref_typing.simps unfolding v_typing.simps by (auto split: v.splits)
            next
              case d
              then have d1: "reduce_trans (s', f, $* g_init g) (s', f, [$C (V_ref (ConstNull t_r))])"
                using 3 reduce.basic[OF reduce_simple.null] reduce_trans_def v_to_e_def
                apply auto
                by (metis (no_types, lifting) reduce_trans_app_end rtranclp.rtrancl_refl)
              then have v_is: "(V_ref (ConstNull t_r)) = v" using 3 
                \<open>inst.globs inst = (ext_globs v_imps)@allocd_globs\<close>
                f_def
                const_exprs_reduce_trans[OF 1 2 3 4
                list_all2_external_typing_glob_alloc[OF s_ext_typing] s'_is(4) s'_is(4) _ \<open>inst.globs inst = (ext_globs v_imps)@allocd_globs\<close> _ 5,
                of allocd_globs "[]" "[]" "[]"]
                const_exprs_reduce_trans[OF 1 2 d1 4
                list_all2_external_typing_glob_alloc[OF s_ext_typing] s'_is(4) s'_is(4) _ \<open>inst.globs inst = (ext_globs v_imps)@allocd_globs\<close> _ 5,
                of _ "[]" "[]" "[]"]
                by auto
              then show ?thesis using typeof_def typeof_ref_def ref_typing.simps unfolding v_typing.simps by (auto split: v.splits)
            qed
          qed

          then have "tg_t (g_type g) = typeof v" "v_typing s' v (typeof v)"
            using const_exprs_reduce_trans[OF 1 2 3 4
                list_all2_external_typing_glob_alloc[OF s_ext_typing] s'_is(4) _ _ \<open>inst.globs inst = (ext_globs v_imps)@allocd_globs\<close> _ 5]
                \<open>inst.globs inst = (ext_globs v_imps)@allocd_globs\<close>
                f_def by force+
        }
        then have "list_all2 (\<lambda>g g_init. tg_t (g_type g) = typeof g_init) (m_globs m) g_inits" "list_all (\<lambda> g_v. v_typing s' g_v (typeof g_v)) g_inits"
          using \<open>length (m_globs m) = length g_inits\<close> unfolding list_all2_conv_all_nth 
          (*todo: I have no idea why gs gets involved but whatever*)
           apply (metis \<open>length gs = length (m_globs m)\<close> gs_alloc length_map nth_mem nth_zip)
          by (metis \<open>\<And>v ga. (ga, v) \<in> set (zip (m_globs m) g_inits) \<Longrightarrow> v_typing s' v (typeof v)\<close> in_set_impl_in_set_zip2 list.pred_True list.pred_mono_strong zip_agree)
        moreover show "list_all (\<lambda> g_v. v_typing s' g_v (typeof g_v)) g_inits" using calculation by simp
        
        ultimately show "map tg_t gts = map typeof g_inits" unfolding \<open>gts = map g_type (m_globs m)\<close> list_all2_conv_all_nth
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
      then show  "list_all2 (globi_agree (globs s')) allocd_globs gts" using \<open>globs s' = globs s @ gs\<close> by auto
      then show "map g_val gs = g_inits"
        using \<open>map g_val gs = g_inits\<close> by blast

      have globs_s1: "list_all (glob_agree s) (globs s)" using assms(1) unfolding store_typing.simps by auto
      then have globs_s2: "list_all (glob_agree s') (globs s)"
        by (metis \<open>store_extension s s'\<close> glob_agree_store_extension_inv list_all_length)
      
      have "list_all (glob_agree s') gs"
        using \<open>map g_val gs = g_inits\<close> g_inits_props2(2)
        by (metis (mono_tags, lifting) \<open>length gs = length (m_globs m)\<close> glob_agree_def list_all_length nth_map zip_agree)

      then show "list_all (glob_agree s') (globs s')"
        by (simp add: globs_s2 s'_is(4))
    qed 
    ultimately show "list_all2 (globi_agree (globs s')) (inst.globs inst) (global \<C>)" "list_all (glob_agree s') (s.globs s')" using c_is(8) by (simp_all add: list_all2_appendI) 
  qed
  moreover have elemi_agree_s': "list_all2 (elemi_agree s' (s.elems s')) (inst.elems inst) (elem \<C>)" "list_all (elem_agree s') (s.elems s')"
  proof -
    obtain allocd_els where allocd_els_def: "allocd_els = snd (alloc_elems s (m_elems m) el_inits)"
      using el_inits_def
      by blast
    have "(length (m_elems m)) = (length el_inits)"
      using el_inits_def list_all2_conv_all_nth by blast
    then have allocd_els_is: "allocd_els = [length (elems s)..<length (elems s)+length (m_elems m)]"
      using alloc_elems_range[of s "m_elems m" el_inits _ allocd_els] allocd_els_def
      by (simp, metis prod.collapse)
    have "allocd_els = (inst.elems inst)"
      using allocd_els_def alloc_module_allocated_form(5)[OF s_alloc_module]
      by (metis eq_snd_iff)
    have "list_all2 (module_elem_typing \<C>') (m_elems m) rts"
      using c_is(3) by fastforce
    have "list_all2 (\<lambda> m_el rt. e_type m_el = rt) (m_elems m) rts"
      using list_all2_mono[OF c_is(3)]
      by (metis (mono_tags, lifting) module_elem.select_convs(1) module_elem_typing.simps)
    then have 1: "map e_type (m_elems m) = rts"
    proof(induction rts)
    qed auto
    have "elems s' = elems s @ els"
      using s'_is(5) by blast
    have "elems s' = elems (fst (alloc_elems s (m_elems m) el_inits))"
      by (metis alloc_module_allocated_form(5)[OF s_alloc_module] prod.collapse)
    then have "elems s' = elems s @ alloc_elems_simple (m_elems m) el_inits"
      using alloc_module_elems_form s'_is(5) s_alloc_module by blast
    then have "els = alloc_elems_simple (m_elems m) el_inits"
      by (simp add: s'_is(5))
    
    then have "length els = length allocd_els"
      by (metis allocd_els_def length_alloc_Xs length_map snd_conv surj_pair)

    have len_el_inits_rts: "length el_inits = length rts"
      using "1" \<open>length (m_elems m) = length el_inits\<close> by fastforce

    { fix i j
      assume local_assms: "i < length (el_inits)" "j < length (el_inits!i)"
      then have i_rts: "i < length rts"
        using "1" \<open>length (m_elems m) = length el_inits\<close> by fastforce
      have "length (el_inits!i) = length (e_init ((m_elems m)!i))"
        by (metis (no_types, lifting) el_inits_def list_all2_conv_all_nth local_assms(1))

      have "list_all2 (module_elem_typing \<C>') (m_elems m) rts"
        using c_is(3) el_inits_def by fastforce
      then have "list_all (\<lambda>e. \<C>' \<turnstile> e : ([] _> [T_ref (rts!i)]) \<and> const_exprs \<C>' e) (e_init ((m_elems m)!i))"
        by (metis (no_types, lifting) \<open>length (m_elems m) = length el_inits\<close> list_all2_nthD list_all_length local_assms(1) module_elem.select_convs(2) module_elem_typing.simps) 

      then have e_init1: "\<C>' \<turnstile> (e_init ((m_elems m)!i))!j : ([] _> [T_ref (rts!i)])" "const_exprs \<C>' ((e_init ((m_elems m)!i))!j)"
       
         apply (metis (no_types, lifting) \<open>length (el_inits ! i) = length (e_init (m_elems m ! i))\<close> list_all_length local_assms(2))
        by (metis (no_types, lifting) \<open>length (el_inits ! i) = length (e_init (m_elems m ! i))\<close> \<open>list_all (\<lambda>e. \<C>' \<turnstile> e : [] _> [T_ref (rts ! i)] \<and> const_exprs \<C>' e) (e_init (m_elems m ! i))\<close> list_all_length local_assms(2))
      
      have e_init2: "reduce_trans (s',f,$*((e_init ((m_elems m)!i))!j)) (s',f,[$C (V_ref (el_inits!i!j))])"
        using el_inits_def
        by (meson list_all2_nthD2 local_assms(1) local_assms(2))
      define allocd_globs where "allocd_globs = snd (alloc_globs s (m_globs m) g_inits)" 
      then have "inst.globs inst = (ext_globs v_imps)@allocd_globs" 
        using alloc_module_allocated_form(4)[OF s_alloc_module]
        by (metis prod.collapse)
      have func_len: "length (inst.funcs inst) =length (func_t \<C>')"
            using funci_agree_s' c_is(9)
            by (simp add: list_all2_lengthD)
      have global_\<C>': "global \<C>' = ext_t_globs t_imps"
        by (simp add: c_is(9))
      have "ref_typing s' (el_inits!i!j) (rts!i)"
      proof -
        consider
          (a) v' where "$* e_init (m_elems m ! i) ! j = [$C v'] \<and> typeof v' = T_ref (rts ! i)"
        | (b) j' t' where "t' <t: T_ref (rts ! i) \<and>
              e_init (m_elems m ! i) ! j = [Get_global j'] \<and> j' < length (global \<C>') \<and> tg_mut (global \<C>' ! j') = T_immut \<and> tg_t (global \<C>' ! j') = t'"
        | (c) j' where "e_init (m_elems m ! i) ! j = [Ref_func j'] \<and> j' < length (func_t \<C>') \<and> T_ref (rts ! i) = T_ref T_func_ref"
        | (d) t_r where "e_init (m_elems m ! i) ! j = [Ref_null t_r] \<and> T_ref (rts ! i) = T_ref t_r"
          using const_exprs_is[OF e_init1(2,1)] by auto
        thus ?thesis
        proof(cases)
          case a
          then show ?thesis using v_to_e_def typeof_def
            by (auto split: v.splits)
        next
          case b
          then have  b1: "reduce_trans (s',f,$*((e_init ((m_elems m)!i))!j)) (s',f,[$C(sglob_val s' (f_inst f) j')])"
            using reduce.get_global
            by (metis reduce_trans_app_end reduce_trans_def rtranclp.rtrancl_refl to_e_list_1)
          
          then have v_is: "(sglob_val s' (f_inst f) j') = V_ref (el_inits !i !j)" "typeof_ref ((el_inits !i !j)) = (rts ! i)"
            using
            f_def global_\<C>'
            const_exprs_reduce_trans[OF e_init1(2,1) e_init2 _
            list_all2_external_typing_glob_alloc[OF s_ext_typing] s'_is(4) s'_is(4) _ \<open>inst.globs inst = (ext_globs v_imps)@allocd_globs\<close> _ func_len,
            of allocd_globs "[]" "[]" "[]"]
            const_exprs_reduce_trans[OF e_init1(2,1) b1 _
            list_all2_external_typing_glob_alloc[OF s_ext_typing] s'_is(4) s'_is(4) _ \<open>inst.globs inst = (ext_globs v_imps)@allocd_globs\<close> _ func_len,
            of allocd_globs "[]" "[]" "[]"] \<open>inst.globs inst = ext_globs v_imps @ allocd_globs\<close>
            typeof_def
            by auto
          
          have el_inits_i_j: "V_ref (el_inits !i !j) = g_val ((globs s')! (inst.globs inst ! j'))" using b v_is
            by (simp add: f_def sglob_def sglob_ind_def sglob_val_def)
          have "j' < length (global \<C>')"
            using b by fastforce
          then have "j' < length (global \<C>)" using c_is(8,9) by auto
          then have "(inst.globs inst ! j') < length (globs s')" using globi_agree_s'(1) unfolding globi_agree_def
            using list_all2_nthD2 by blast
          then have "glob_agree s' (s.globs s'! (inst.globs inst ! j'))" using globi_agree_s'(2)
            by (simp add: list_all_length)
          then have "v_typing s' (V_ref (el_inits ! i ! j)) (T_ref (rts ! i))"
            using v_is el_inits_i_j
            by (metis (no_types, lifting) glob_agree_def typeof_def v.simps(12) v_typing_typeof)
          then show ?thesis unfolding v_typing.simps by auto
        next
          case c
          then have  c1: "reduce_trans (s',f,$*((e_init ((m_elems m)!i))!j)) (s',f,[$C (V_ref (ConstRefFunc ((inst.funcs inst)!j')))])"
            using reduce.ref_func[] v_to_e_def
            by (simp, metis f.select_convs(2) f_def reduce_trans_app reduce_trans_def rtranclp.rtrancl_refl)
           
          then have "el_inits!i!j = (ConstRefFunc ((inst.funcs inst)!j'))"
            using f_def global_\<C>' e_init1 e_init2
            const_exprs_reduce_trans[OF e_init1(2,1) e_init2 _
            list_all2_external_typing_glob_alloc[OF s_ext_typing] s'_is(4) s'_is(4) _ \<open>inst.globs inst = (ext_globs v_imps)@allocd_globs\<close> _ func_len,
            of allocd_globs "[]" "[]" "[]"]
            const_exprs_reduce_trans[OF e_init1(2,1) c1 _
            list_all2_external_typing_glob_alloc[OF s_ext_typing] s'_is(4) s'_is(4) _ \<open>inst.globs inst = (ext_globs v_imps)@allocd_globs\<close> _ func_len,
            of allocd_globs "[]" "[]" "[]"] \<open>inst.globs inst = ext_globs v_imps @ allocd_globs\<close>
            typeof_def by auto
          then show ?thesis using c ref_typing.simps
            using func_len funci_agree_def funci_agree_s' list_all2_nthD by fastforce
        next
          case d
          then show ?thesis using const_expr.cases e_init1(2) ref_typing.simps by auto
        qed
      qed
    }
    then have el_inits_typing1: "\<And> i j. i < length el_inits \<Longrightarrow> j < length (el_inits ! i) \<Longrightarrow> ref_typing s' (el_inits ! i ! j) (rts ! i)"
      by simp
    then have el_inits_typing2: "list_all2 (\<lambda> els tr. list_all (\<lambda> el. ref_typing s' el tr) els) el_inits rts"
      using len_el_inits_rts
      by (simp add: list_all2_conv_all_nth list_all_length)


    have elems_inst_length: "length (inst.elems inst) = length (elem \<C>)"
      by (metis \<open>allocd_els = inst.elems inst\<close> \<open>length (m_elems m) = length el_inits\<close> allocd_els_is c_is(8) diff_add_inverse len_el_inits_rts length_upt t_context.select_convs(4))
    { fix i
      assume local_assms: "i < length (inst.elems inst)"
      have "list_all2 (module_elem_typing \<C>') (m_elems m) rts"
        using c_is(3) el_inits_def by fastforce
      then have 1: "list_all2 (\<lambda> m_el rt. module_elem_typing \<C>' m_el rt) (m_elems m) rts"
        using el_inits_def
        by simp
      have 2: "i < length rts" using local_assms
        by (simp add: c_is(8) elems_inst_length)
      then have "module_elem_typing \<C>' ((m_elems m)!i) (rts!i)" using 1
        using list_all2_nthD2 by auto

      have 3: "inst.elems inst!i = length (elems s)+i" using \<open>allocd_els = inst.elems inst\<close> allocd_els_is
        using local_assms by fastforce
      then have 4: "s.elems s'! (inst.elems inst!i) = alloc_elem_simple (m_elems m!i, el_inits!i)"
        using els_alloc local_assms s'_is(5)
        by (simp add: "2" \<open>length (m_elems m) = length el_inits\<close> len_el_inits_rts)
      have 5: "(inst.elems inst) = [length (elems s) ..< length (elems s) + length (m_elems m)]"
        using \<open>allocd_els = inst.elems inst\<close> allocd_els_is by blast
      have 6: "list_all (\<lambda> vr. ref_typing s' vr (rts!i)) (el_inits!i)"
        using el_inits_typing1 len_el_inits_rts list_all_length 2
        by metis
      have 7: "elemi_agree s' (s.elems s') (inst.elems inst!i) (rts!i)"
        using 2 3 4 4 6 unfolding alloc_elem_simple_def elemi_agree_def elem_typing_def
        apply (auto simp add: \<open>allocd_els = inst.elems inst\<close> \<open>length els = length allocd_els\<close> local_assms s'_is(5))
        using \<open>list_all2 (\<lambda>m_el. (=) (e_type m_el)) (m_elems m) rts\<close> list_all2_nthD2 by blast
      then have "elemi_agree s' (s.elems s') (inst.elems inst!i) (elem \<C>!i)" "elem_agree s' (els!i)"
         apply (simp add: c_is(8))
        unfolding elem_agree_def
        
        using "3" 7 \<open>s.elems s' = s.elems s @ alloc_elems_simple (m_elems m) el_inits\<close> elem_typing_def elemi_agree_def els_alloc by auto
    }
    moreover show "list_all (elem_agree s') (s.elems s')"
      using s'_is(5) ref_typing_store_extension_inv[OF \<open>store_extension s s'\<close>] list_all_length
            \<open>allocd_els = inst.elems inst\<close> \<open>length els = length allocd_els\<close> elem_agree_def
            store_typing_in_elem_agree[OF assms(1)]
      by (metis calculation(2) list_all_append) 
    ultimately show "list_all2 (elemi_agree s' (s.elems s')) (inst.elems inst) (elem \<C>)"
      using elems_inst_length list_all2_all_nthI by blast
  qed
  moreover have datai_agree_s': "list_all2 (datai_agree (s.datas s')) (inst.datas inst) (data \<C>)"
  proof -
    have "(inst.datas inst) = [length (datas s) ..< length (datas s) + length (m_datas m)]"
      using alloc_datas_range alloc_module_allocated_form(6)[OF s_alloc_module]

      by (metis prod.collapse)
    moreover have "datas s' = datas s @ alloc_datas_simple (m_datas m)"
      using alloc_module_datas_form s'_is(6) s_alloc_module by blast
    ultimately show ?thesis using c_is(8,10) unfolding datai_agree_def data_typing_def
      apply (simp add: )
      by (simp add: list_all2_conv_all_nth)
  qed

  moreover have "local \<C> = [] \<and> label \<C> = [] \<and> return \<C> = None" using c_is(8) by auto
  moreover have funcs_inst_context_length: "length (inst.funcs inst) = length (func_t \<C>)"
    using funci_agree_s' list_all2_lengthD by blast
  moreover obtain \<C>'' where context_def: "\<C>'' = \<C>\<lparr>refs := [0..<length (inst.funcs inst)]\<rparr>" by simp
  ultimately have
    "types inst = types_t \<C>''"
    "list_all2 (funci_agree (s.funcs s')) (inst.funcs inst) (func_t \<C>'')"
    "list_all2 (tabi_agree (tabs s')) (inst.tabs inst) (table \<C>'')"
    "list_all2 (memi_agree (s.mems s')) (inst.mems inst) (memory \<C>'')"
    "list_all2 (globi_agree (s.globs s')) (inst.globs inst) (global \<C>'')"
    "list_all2 (elemi_agree s' (s.elems s')) (inst.elems inst) (elem \<C>'')"
    "list_all2 (datai_agree (s.datas s')) (inst.datas inst) (data \<C>'')"
    "local \<C>'' = [] \<and> label \<C>'' = [] \<and> return \<C>'' = None"
    "refs \<C>'' = [0..<length (inst.funcs inst)]"
    by auto
  then have s'_inst_t:"inst_typing s' inst \<C>''" using  inst_typing.intros
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
            "n_zeros loc_ts \<noteq> None"
            using list_all2_in_set[OF 1(2) c_is(1)]
            unfolding module_func_typing.simps by auto 
          have 3:"(types_t \<C>)!i_t = (types inst)!i_t"
            using types_inst_context by auto

          have "cl_typing s' f (tn _> tm)" 
          proof -
            have 4: "i_t < length (types_t \<C>'')"
                    "(types_t \<C>'')!i_t = (tn _> tm)"
              using 2 context_def by auto
            have "\<C>''\<lparr>local := tn @ loc_ts, label := [tm] @ label \<C>'', return := Some tm\<rparr> = \<C>\<lparr>local := tn @ loc_ts, label := ([tm] @ (label \<C>)), return := Some tm\<rparr> \<lparr> refs := [0..< length (func_t (\<C>''\<lparr>local := tn @ loc_ts, label := [tm] @ label \<C>'', return := Some tm\<rparr>))]\<rparr>"
              using context_def funcs_inst_context_length by auto
            then have 5: "\<C>''\<lparr>local := tn @ loc_ts, label := ([tm] @ (label \<C>'')), return := Some tm\<rparr> \<turnstile> b_es : ([] _> tm)"
              using  b_e_type_preserved_refs[OF 2(3)]
              using funcs_inst_context_length inst_typing_func_length s'_inst_t
              by auto
            have 32: "(types_t \<C>'')!i_t = (types inst)!i_t" using 3 context_def by simp
            then show ?thesis using cl_typing.intros(1)[OF \<open>inst_typing s' inst \<C>''\<close> 4(2) 5]
              using 1(1) "2"(4) by metis 
          qed
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
      (*{
        fix e 
        assume "e \<in> set (m_elems m)" 
        then have "module_elem_typing \<C> e" using \<open>list_all (module_elem_typing \<C>') (m_elems m)\<close>
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
      qed*)
      have "list_all (tab_agree s) (tabs s)" using assms(1) unfolding store_typing.simps by auto
      then have "list_all (tab_agree s') (tabs s)" 
        using tab_agree_store_extension_inv[OF \<open>store_extension s s'\<close>] 
        by (simp add: list_all_length)
      moreover have "list_all (tab_agree s') ts" 
        using \<open>list_all (module_tab_typing) (m_tabs m)\<close> 
        unfolding ts_alloc alloc_tab_simple_def tab_agree_def list.pred_map(1) comp_def 
        limit_typing.simps
        apply (auto simp add:  tab_t_reftype_def tab_max_def tab_t_lim_def list.pred_set split: tab_t.splits)
        using module_tab_typing.simps
        
        using limit_typing.simps apply auto[1]
        using ref_typing.intros(1) by blast
      ultimately show "list_all (tab_agree s') (tabs s')"
        using s'_is(2)
        by simp 
    qed
    have 3:"list_all mem_agree (mems s')"
    proof -
     (* have "list_all2 (data_in_bounds s' inst) (map nat_of_int d_offs) (m_data m)"
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
        by auto *)

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
    have 4: "list_all (glob_agree s') (s.globs s')"
      using globi_agree_s'(2) by blast
    have 5: "list_all (elem_agree s') (s.elems s')"
      using elemi_agree_s'(2) by blast
    have 6: "list_all (data_agree s') (s.datas s')"
      by (simp add: data_agree_def list_all_length)
    show ?thesis
      using 1 2 3 4 5 6 store_typing.intros
      by blast
  qed

  show "\<exists>tes. list_all2 (\<lambda>v_exp te. external_typing s' (E_desc v_exp) te) v_exps tes"
    using instantiation_external_typing[OF s_alloc_module \<open>inst_typing s' inst \<C>''\<close> ] c_is(6)
          context_def
    unfolding module_export_typing.simps
    by auto


  show "\<exists>\<C>. (inst_typing s' inst \<C> \<and> (s'\<bullet>\<C> \<turnstile> init_es : ([] _> [])))"
  proof -
    have "s'\<bullet>\<C>'' \<turnstile> (case (m_start m) of None \<Rightarrow> [] | Some i_s \<Rightarrow> [Invoke ((inst.funcs inst)!i_s)]) : ([] _> [])"
    proof (cases "m_start m")
      case None
      thus ?thesis
        by (simp add: e_type_empty instr_subtyping_refl)
    next
      case (Some a)
      have a_type:"a < length (inst.funcs inst)"
                  "(func_t \<C>'')!a = ([] _> [])" using c_is(6) Some funci_agree_s' 
        unfolding module_start_typing.simps list_all2_conv_all_nth
        using c_is(7) module_start_typing.simps context_def by auto
      then have "inst.funcs inst ! a < length (funcs s')" using list_all2_forget[OF funci_agree_s']
        unfolding funci_agree_def list_all_length by simp
      moreover have "cl_type ((funcs s')!(inst.funcs inst ! a)) = ([] _> [])"
        using a_type(1,2) c_is(7) context_def funci_agree_def funci_agree_s'
        unfolding module_start_typing.simps
        by (simp add: list_all2_conv_all_nth)
      ultimately show ?thesis
        using e_typing_l_typing.intros(7) Some
        by simp
    qed
    moreover have "s'\<bullet>\<C>'' \<turnstile> run_elems (m_elems m) : ([] _> [])"
    proof -
      have "list_all2 (module_elem_typing \<C>') (m_elems m) rts"
        using c_is(3) by blast
      { fix i
        assume local_assms: "i < length (m_elems m)"
        have i_elem_length: "i < length (elem \<C>)"
          by (metis c_is(3) c_is(8) list_all2_lengthD local_assms t_context.simps(4))
        have "module_elem_typing \<C>' ((m_elems m)!i) (rts!i)"
          using c_is(3) list_all2_nthD local_assms by blast
        then have elem_mode_typing: "elem_mode_typing \<C>' (e_mode ((m_elems m)!i)) (rts!i)"
          using module_elem_typing.simps by fastforce
        then have "\<C>'' \<turnstile> run_elem ((m_elems m)!i) i : [] _> []"
        proof(cases "(e_mode ((m_elems m)!i))")
          case Em_passive
          then show ?thesis using run_elem_def empty by auto
        next
          case (Em_active x offset)
          then have defs: "x < length (table \<C>')" "rts!i = tab_t_reftype (table \<C>'!x)" "\<C>' \<turnstile> offset : ([] _> [T_num T_i32])" "const_exprs \<C>' offset"
            using elem_mode_typing c_is(9) unfolding elem_mode_typing.simps const_expr.simps tab_t_reftype_def
            by (auto split: tab_t.splits)
          have h1: "const_exprs \<C>'' offset"
            using defs(4)
            apply(induction offset)
            using const_expr.simps c_is(9) c_is(8) context_def
            apply (auto )
            by (metis nth_append)
          consider
              (a) v where "$* offset = [$C v]"
                          "typeof v = T_num T_i32"
            | (b) j t' where "t' <t: T_num T_i32"
                             "offset = [Get_global j]"
                             "j < length (global \<C>')"
                             "tg_mut (global \<C>' ! j) = T_immut"
                             "tg_t (global \<C>' ! j) = t'"
            | (c) j where "offset = [Ref_func j]" "j < length (func_t \<C>')" "T_num T_i32 = T_ref T_func_ref"
            | (d) t_r where " offset = [Ref_null t_r]" "T_num T_i32 = T_ref t_r"
            using const_exprs_is[OF defs(4,3)] by auto
          then have h2: "\<C>'' \<turnstile> offset : ([] _> [T_num T_i32])"
          proof(cases)
            case a
            then show ?thesis using context_def v_to_e_def typeof_def typeof_num_def const_num apply (auto split: v_num.splits v.splits)
              by (metis v_num.simps(17))
          next
            case b
            then have "\<C> \<turnstile> [Get_global j] : [] _> [t']"
              using b_e_typing.get_global[of j \<C> t'] c_is(8) c_is(9)
              by (auto simp add: nth_append)
            then have "\<C>'' \<turnstile> [Get_global j] : [] _> [t']"
              using context_def b_e_type_preserved_refs funcs_inst_context_length by simp
            then show ?thesis
              using b(1,2) t_subtyping_def t_list_subtyping_def
                    instr_subtyping_def subsumption[of \<C>'' offset "[]" "[t']" "[]" "[T_num T_i32]"]
              by auto
          next
            case c
            then show ?thesis
              by blast
          next
            case d
            then show ?thesis using b_e_typing.ref_null by simp
          qed
 
          have h3: "\<C>'' \<turnstile> [EConstNum (ConstInt32 0), EConstNum (ConstInt32 (int_of_nat (length (e_init (m_elems m ! i)))))] : ([T_num T_i32] _> [T_num T_i32, T_num T_i32, T_num T_i32])"
          proof -
            have "\<C>'' \<turnstile> [EConstNum (ConstInt32 0)] : ([T_num T_i32] _> [T_num T_i32, T_num T_i32])"
              by (metis append_Cons append_Nil b_e_weakening const_num typeof_num_def v_num.simps(17))
            moreover have "\<C>'' \<turnstile> [ EConstNum (ConstInt32 (int_of_nat (length (e_init (m_elems m ! i)))))] : ([T_num T_i32, T_num T_i32] _> [T_num T_i32, T_num T_i32, T_num T_i32])"
              by (metis append_Cons append_Nil b_e_weakening const_num typeof_num_def v_num.simps(17))
            then show ?thesis using b_e_type_comp_conc[OF calculation] by auto
          qed
          have "x < length (table \<C>'')" using defs(1) c_is(8,9) context_def by auto
          moreover have "i < length (elem \<C>'')" using local_assms
            by (metis elemi_agree_s' i_elem_length list_all2_lengthD s'_inst_t store_elem_exists)
          moreover have "rts ! i = tab_t_reftype (table \<C>'' ! x)" using defs(2) c_is(8,9) context_def by auto
          moreover have "rts ! i = elem \<C>'' ! i" using c_is(8,9) context_def by auto
          ultimately have h4: "\<C>'' \<turnstile> [Table_init x i] : ([T_num T_i32, T_num T_i32, T_num T_i32] _> [])"
            using b_e_typing.table_init[of x \<C>'' i "rts!i"] by simp
          have h5: "\<C>'' \<turnstile> [Elem_drop i] : ([] _> [])"
            using \<open>i < length (elem \<C>'')\<close> b_e_typing.elem_drop by blast
          then show ?thesis using Em_active unfolding run_elem_def
            using b_e_type_comp_conc[OF b_e_type_comp_conc[OF b_e_type_comp_conc[OF h2 h3] h4] h5]
            by simp
        next
          case Em_declarative
          then show ?thesis using run_elem_def i_elem_length b_e_typing.elem_drop context_def by auto
        qed
        then have "s'\<bullet>\<C>'' \<turnstile> $* run_elem ((m_elems m)!i) i : [] _> []"
          using e_typing_l_typing.intros(1) by auto 
      }
      then have run_elem_t_type: "\<And> i. i < length (m_elems m) \<Longrightarrow> s'\<bullet>\<C>'' \<turnstile> $* run_elem ((m_elems m)!i) i : [] _> []"
        by simp
      { fix j
        assume local_assms: "j \<le> length (m_elems m)"
        then have "s'\<bullet>\<C>'' \<turnstile> $* concat (map2 run_elem (take j (m_elems m)) [0..<j]) : [] _> []"
        proof(induction j)
          case 0
          then show ?case
            by (simp add: e_type_empty instr_subtyping_refl)
        next
          case (Suc j)
          then have j_l: "j < length (m_elems m)" by auto
          then have "(map2 run_elem (take (Suc j) (m_elems m)) [0..<Suc j]) = ((map2 run_elem (take j (m_elems m)) [0..< j])@[run_elem (m_elems m!j) j])"
            using take_Suc_conv_app_nth[OF j_l]
            by auto
          then have j_suc_concat_map: "$* concat (map2 run_elem (take (Suc j) (m_elems m)) [0..<Suc j]) = ($* concat (map2 run_elem (take (j) (m_elems m)) [0..<j])) @ ($* run_elem ((m_elems m)!j) j)"
            by auto
          have "s'\<bullet>\<C>'' \<turnstile> ($* concat (map2 run_elem (take (j) (m_elems m)) [0..<j])) : ([] _> [])"
            using Suc by auto
          moreover have "s'\<bullet>\<C>'' \<turnstile> ($* run_elem ((m_elems m)!j) j) : ([] _> [])"
            using run_elem_t_type[OF j_l] by auto
          moreover show ?case
            using e_type_comp_conc[OF calculation] using j_suc_concat_map  by simp
        qed
      }
      then show ?thesis unfolding run_elems_def by fastforce
       
    qed
    
    moreover have "s'\<bullet>\<C>'' \<turnstile> run_datas (m_datas m) : ([] _> [])"
    proof -
      have "list_all (module_data_typing \<C>') (m_datas m)"
        using c_is(4) by blast
      { fix i
        assume local_assms: "i < length (m_datas m)"
        have i_data_length: "i < length (data \<C>)"
          by (simp add: c_is(10) c_is(8) local_assms)
        have "module_data_typing \<C>' ((m_datas m)!i)"
          using c_is(4) list_all2_nthD local_assms
          by (simp add: list_all_length)
        then have data_mode_typing: "data_mode_typing \<C>' (d_mode ((m_datas m)!i)) "
          using module_data_typing.simps by fastforce
        then have "\<C>'' \<turnstile> run_data ((m_datas m)!i) i : [] _> []"
        proof(cases "(d_mode ((m_datas m)!i))")
          case Dm_passive
          then show ?thesis using run_data_def empty by auto
        next
          case (Dm_active x offset)
          then have defs: "x < length (memory \<C>')"  "\<C>' \<turnstile> offset : ([] _> [T_num T_i32])" "const_exprs \<C>' offset"
            using data_mode_typing c_is(9) unfolding data_mode_typing.simps const_expr.simps
            by (auto split: tab_t.splits)
          have h1: "const_exprs \<C>'' offset"
            using defs(3)
            apply(induction offset)
            using const_expr.simps c_is(9) c_is(8) context_def
            apply (auto )
            by (metis nth_append)
          consider
              (a) v where "$* offset = [$C v]"
                          "typeof v = T_num T_i32"
            | (b) j t' where "t' <t: T_num T_i32"
                             "offset = [Get_global j]"
                             "j < length (global \<C>')"
                             "tg_mut (global \<C>' ! j) = T_immut"
                             "tg_t (global \<C>' ! j) = t'"
            | (c) j where "offset = [Ref_func j]" "j < length (func_t \<C>')" "T_num T_i32 = T_ref T_func_ref"
            | (d) t_r where " offset = [Ref_null t_r]" "T_num T_i32 = T_ref t_r"
            using const_exprs_is[OF defs(3,2)] by auto
          then have h2: "\<C>'' \<turnstile> offset : ([] _> [T_num T_i32])"
          proof(cases)
            case a
            then show ?thesis using context_def v_to_e_def typeof_def typeof_num_def const_num apply (auto split: v_num.splits v.splits)
              by (metis v_num.simps(17))
          next
            case b
            then have "\<C> \<turnstile> [Get_global j] : [] _> [t']"
              using b_e_typing.get_global[of j \<C> t'] c_is(8) c_is(9)
              by (auto simp add: nth_append)
            then have "\<C>'' \<turnstile> [Get_global j] : [] _> [t']"
              using context_def b_e_type_preserved_refs funcs_inst_context_length by simp
            then show ?thesis
              using b(1,2) t_subtyping_def t_list_subtyping_def
                    instr_subtyping_def subsumption[of \<C>'' offset "[]" "[t']" "[]" "[T_num T_i32]"]
              by auto
          next
            case c
            then show ?thesis
              by blast
          next
            case d
            then show ?thesis using b_e_typing.ref_null by simp
          qed
 
          have h3: "\<C>'' \<turnstile> [EConstNum (ConstInt32 0), EConstNum (ConstInt32 (int_of_nat (length (d_init (m_datas m ! i)))))] : ([T_num T_i32] _> [T_num T_i32, T_num T_i32, T_num T_i32])"
          proof -
            have "\<C>'' \<turnstile> [EConstNum (ConstInt32 0)] : ([T_num T_i32] _> [T_num T_i32, T_num T_i32])"
              by (metis append_Cons append_Nil b_e_weakening const_num typeof_num_def v_num.simps(17))
            moreover have "\<C>'' \<turnstile> [ EConstNum (ConstInt32 (int_of_nat (length (d_init (m_datas m ! i)))))] : ([T_num T_i32, T_num T_i32] _> [T_num T_i32, T_num T_i32, T_num T_i32])"
              by (metis append_Cons append_Nil b_e_weakening const_num typeof_num_def v_num.simps(17))
            then show ?thesis using b_e_type_comp_conc[OF calculation] by auto
          qed
          have "1 \<le> length (memory \<C>'')" 
            using defs(1) defs(2) c_is(8,9) context_def
            by auto
          moreover have "i < length (data \<C>'')" using local_assms
            by (metis datai_agree_s' i_data_length list_all2_lengthD s'_inst_t store_data_exists)
          moreover have h4: "\<C>'' \<turnstile> [Memory_init i] : ([T_num T_i32, T_num T_i32, T_num T_i32] _> [])"
            using b_e_typing.memory_init[OF calculation] by simp
          moreover have h5: "\<C>'' \<turnstile> [Data_drop i] : ([] _> [])"
            using calculation(2) b_e_typing.data_drop by blast
          then show ?thesis using Dm_active unfolding run_data_def
            using b_e_type_comp_conc[OF b_e_type_comp_conc[OF b_e_type_comp_conc[OF h2 h3] h4] h5]
            by simp
        qed
        then have "s'\<bullet>\<C>'' \<turnstile> $* run_data ((m_datas m)!i) i : [] _> []"
          using e_typing_l_typing.intros(1) by auto 
      }
      then have run_data_t_type: "\<And> i. i < length (m_datas m) \<Longrightarrow> s'\<bullet>\<C>'' \<turnstile> $* run_data ((m_datas m)!i) i : [] _> []"
        by simp
      { fix j
        assume local_assms: "j \<le> length (m_datas m)"
        then have "s'\<bullet>\<C>'' \<turnstile> $* concat (map2 run_data (take j (m_datas m)) [0..<j]) : [] _> []"
        proof(induction j)
          case 0
          then show ?case
            by (simp add: e_type_empty instr_subtyping_refl)
        next
          case (Suc j)
          then have j_l: "j < length (m_datas m)" by auto
          then have "(map2 run_data (take (Suc j) (m_datas m)) [0..<Suc j]) = ((map2 run_data (take j (m_datas m)) [0..< j])@[run_data (m_datas m!j) j])"
            using take_Suc_conv_app_nth[OF j_l]
            by auto
          then have j_suc_concat_map: "$* concat (map2 run_data (take (Suc j) (m_datas m)) [0..<Suc j]) = ($* concat (map2 run_data (take (j) (m_datas m)) [0..<j])) @ ($* run_data ((m_datas m)!j) j)"
            by auto
          have "s'\<bullet>\<C>'' \<turnstile> ($* concat (map2 run_data (take (j) (m_datas m)) [0..<j])) : ([] _> [])"
            using Suc by auto
          moreover have "s'\<bullet>\<C>'' \<turnstile> ($* run_data ((m_datas m)!j) j) : ([] _> [])"
            using run_data_t_type[OF j_l] by auto
          moreover show ?case
            using e_type_comp_conc[OF calculation] using j_suc_concat_map  by simp
        qed
      }
      then show ?thesis unfolding run_datas_def by fastforce
       
    qed
    ultimately have "(s'\<bullet>\<C>'' \<turnstile> init_es : ([] _> []))"
      using e_type_comp_conc init_es_is s_start
      by fastforce 
    thus ?thesis
      using  s'_inst_t
    by auto
  qed
qed
  
theorem run_instantiate_sound:
  assumes "run_instantiate n d (s,inst,es) = (s',RValue vs)"
  shows "computes (instantiate_config s inst es) s' vs"
  using assms
  by (auto  
    simp: instantiate_config_def computes_def
    dest!: run_iter_sound
    split: prod.splits config.splits)

theorem run_instantiate_sound_trap:
  assumes "run_instantiate n d (s,inst,es) = (s',RTrap str)"
  shows "traps (instantiate_config s inst es) s'"
  using assms
  by (auto  
    simp: instantiate_config_def traps_def
    dest!: run_iter_sound
    split: prod.splits config.splits)
    
    
    
(* TODO: Delete all those simp-lemmas, right after defs (best: change fun to definition! )*)  
lemmas [simp del] = run_invoke_v.simps
lemmas [simp del] = interp_instantiate.simps run_instantiate.simps
    
lemma interp_instantiate_init_sound:
  assumes "interp_instantiate_init s m v_imps = (s', RI_res inst exps es)"
  shows "\<exists>sh esh. 
    instantiate s m v_imps ((sh, inst, exps), esh)
  \<and> es = []
  \<and> computes (instantiate_config sh inst esh) s' []
  "
  using assms
  unfolding interp_instantiate_init_def
  by (auto 0 4
    split: prod.splits res_inst.splits res.splits list.splits config.splits
    dest!: run_instantiate_sound
    simp: instantiate_equiv_interp_instantiate[symmetric]
  )

(*  
lemma interp_instantiate_init_sound_traps:
  assumes "interp_instantiate_init s m v_imps = (s', RI_trap str)"
  shows "\<exists>sh esh. 
    instantiate s m v_imps ((sh, inst, exps), esh) \<leftarrow> This could fail, too!
  \<and> es = []
  \<and> traps (instantiate_config sh inst esh) s'
  "
  using assms
  unfolding interp_instantiate_init_def
  apply (auto 0 4
    split: prod.splits res_inst.splits res.splits list.splits config.splits
    dest!: run_instantiate_sound_trap
    simp: instantiate_equiv_interp_instantiate[symmetric]
  )
  find_theorems interp_instantiate RI_trap
  (* TODO: Missing abstract characterization of trapping instantiation. 
    There's only instantiate, which describes successful instantiation.
  *)
  oops
*)  
  
(* TODO: Also write simplified check in definitions! *)  
lemma simplify_check_is_Ext_func: "(\<lambda>exp. case E_desc exp of Ext_func i \<Rightarrow> True | _ \<Rightarrow> False) = is_Ext_func o E_desc"    
  by (auto simp: fun_eq_iff split: v_ext.splits)

  
  
  
theorem run_fuzz'_sound: "run_fuzz' n d s m v_imps vs_opt = (s',RValue vs) \<Longrightarrow>
  run_fuzz_abs s m v_imps vs_opt  s' vs"
  unfolding run_fuzz'_def run_fuzz_abs_def
  apply (auto 
    split: prod.splits res_inst.splits option.splits v_ext.splits tf.splits
    simp: instantiate_equiv_interp_instantiate[symmetric] simplify_check_is_Ext_func find_finds_first
    simp: make_params_def Let_def
    dest!: interp_instantiate_init_sound run_invoke_v_sound'
    dest: is_first_elem_with_prop_propI
  )
  apply fastforce+
  done

theorem run_fuzz_entry'_sound: "run_fuzz_entry' n m vs_opt = (s',RValue vs) \<Longrightarrow> run_fuzz_abs empty_store m [] vs_opt s' vs"
  by (auto simp: run_fuzz_entry'_def dest!: run_fuzz'_sound)
        


end