theory Wasm_Instantiation_Properties_Aux imports Wasm_Instantiation Wasm_Properties begin

(*
definition element_in_bounds where 
"element_in_bounds s inst e_ind e \<equiv>
   let i = inst.tabs inst ! e_tab e 
   in i < length (tabs s) \<and>  e_ind + length (e_init e) \<le> length (fst (tabs s ! i))"

definition data_in_bounds where 
"data_in_bounds s inst d_ind d \<equiv> 
  let i = inst.mems inst ! d_data d
  in i < length (mems s) \<and> d_ind + length (d_init d) \<le> mem_length (mems s ! i)"

abbreviation "element_funcs_in_bounds s inst e 
\<equiv>list_all (\<lambda>i. (inst.funcs inst)!i < length (s.funcs s)) (e_init e)" 
*)

(*
lemma tab_extension_trans:"tab_extension a b \<Longrightarrow> tab_extension b c \<Longrightarrow> tab_extension a c" 
  unfolding tab_extension_def by auto
lemma mem_extension_trans:"mem_extension a b \<Longrightarrow> mem_extension b c \<Longrightarrow> mem_extension a c" 
  unfolding mem_extension_def by auto *)

(* while mathematically superfluous, this form makes the following lemmas easier to prove *)
lemma store_extension_intros_with_refl: 
  assumes "funcs s = funcs s' \<or> (\<exists> fs. funcs s @ fs = funcs s')" 
  "tabs s = tabs s' \<or> (\<exists> t1 t2. t1 @ t2 = tabs s' \<and> list_all2 tab_extension (tabs s) t1)"
  "mems s = mems s' \<or> (\<exists> m1 m2. m1 @ m2 = mems s' \<and> list_all2 mem_extension (mems s) m1)" 
  "globs s = globs s' \<or> (\<exists> g1 g2. g1 @ g2 = globs s' \<and> list_all2 global_extension (globs s) g1)" 
  "elems s = elems s' \<or> (\<exists> el1 el2. el1 @ el2 = elems s' \<and> list_all2 elem_extension (elems s) el1)"
  "datas s = datas s' \<or> (\<exists> d1 d2. d1 @ d2 = datas s' \<and> list_all2 data_extension (datas s) d1)"
  shows "store_extension s s'"
proof -         
  have funcs:"\<exists> fs. funcs s @ fs = funcs s'" using assms(1) by auto
  have tabs: "\<exists> t1 t2. t1 @ t2 = tabs s' \<and> list_all2 tab_extension (tabs s) t1" 
    using assms(2) tab_extension_refl list_all2_refl by (metis append_Nil2) 
  have mems: "\<exists> m1 m2. m1 @ m2 = mems s' \<and> list_all2 mem_extension (mems s) m1" 
    using assms(3) mem_extension_refl list_all2_refl by (metis append_Nil2) 
  have globs: "\<exists> g1 g2. g1 @ g2 = globs s' \<and> list_all2 global_extension (globs s) g1"  
    using assms(4) global_extension_refl list_all2_refl by (metis append_Nil2) 
  have elems: "\<exists> el1 el2. el1 @ el2 = elems s' \<and> list_all2 elem_extension (elems s) el1"  
    using assms(5) elem_extension_refl list_all2_refl by (metis append_Nil2) 
  have datas: "\<exists> d1 d2. d1 @ d2 = datas s' \<and> list_all2 data_extension (datas s) d1"  
    using assms(6) data_extension_refl list_all2_refl by (metis append_Nil2) 
  show ?thesis using funcs mems tabs globs elems datas unfolding store_extension.simps
    by (metis (full_types) unit.exhaust s.surjective) 
qed

lemma alloc_module_preserve_store_extension:
  assumes "alloc_module s m imps gvs el_inits (s',inst,exps)" 
  shows "store_extension s s'"
  using alloc_module_ext_arb[OF assms] 
  store_extension_intros_with_refl list_all2_refl tab_extension_refl mem_extension_refl global_extension_refl elem_extension_refl data_extension_refl
  by metis

definition alloc_func_simple :: "module_func \<Rightarrow> inst \<Rightarrow> cl" where
  "alloc_func_simple m_f inst =
     (case m_f of (i_t, loc_ts, b_es) \<Rightarrow>
        Func_native inst ((types inst)!i_t) loc_ts b_es)"

lemma alloc_func_equiv:"fst (alloc_func s m_f i) = s\<lparr>funcs := funcs s @ [alloc_func_simple m_f i]\<rparr>"
  unfolding alloc_func_def alloc_func_simple_def by(simp split:prod.splits)

definition alloc_tab_simple :: "tab_t \<Rightarrow> tabinst" where
  "alloc_tab_simple t_t = (t_t, (replicate (l_min (tab_t_lim t_t)) (ConstNull (tab_t_reftype t_t))))"

lemma alloc_tab_equiv:"fst (alloc_tab s m_t) = s\<lparr>tabs := tabs s @ [alloc_tab_simple m_t]\<rparr>"
  unfolding alloc_tab_def alloc_tab_simple_def by simp

definition alloc_mem_simple :: "mem_t \<Rightarrow> mem" where
  "alloc_mem_simple m_m = mem_mk m_m"

lemma alloc_mem_equiv:"fst (alloc_mem s m_m) = s\<lparr>mems := mems s @ [alloc_mem_simple m_m]\<rparr>"
  unfolding alloc_mem_def alloc_mem_simple_def by simp

definition alloc_glob_simple :: "(module_glob \<times> v) \<Rightarrow> global" where 
  "alloc_glob_simple m_g_v = 
    (case m_g_v of (m_g, v) \<Rightarrow> \<lparr>g_mut=(tg_mut (module_glob.g_type m_g)), g_val=v\<rparr>)"

lemma alloc_glob_equiv:"fst (alloc_glob s m_g_v) = s\<lparr>globs := globs s @ [alloc_glob_simple m_g_v]\<rparr>"
  unfolding alloc_glob_def alloc_glob_simple_def by(simp split:prod.splits)

definition alloc_elem_simple :: "(module_elem \<times> v_ref list) \<Rightarrow> eleminst" where
  "alloc_elem_simple m_el_v_rs =
    (case m_el_v_rs of (m_el, v_rs) \<Rightarrow> (e_type m_el, v_rs))"

lemma alloc_elem_equiv:"fst (alloc_elem s (m_el_v_rs)) = s\<lparr>elems := elems s @ [alloc_elem_simple m_el_v_rs]\<rparr>"
  unfolding alloc_elem_def alloc_elem_simple_def by (simp split: prod.splits)

definition alloc_data_simple :: "(module_data) \<Rightarrow> datainst" where
  "alloc_data_simple m_d = (d_init m_d)"

lemma alloc_data_equiv:"fst (alloc_data s m_d) = s\<lparr>datas := datas s @ [alloc_data_simple m_d]\<rparr>"
  unfolding alloc_data_def alloc_data_simple_def by simp

abbreviation "alloc_funcs_simple m_fs i \<equiv> map (\<lambda>m_f. alloc_func_simple m_f i) m_fs"

lemma alloc_funcs_equiv:"fst (alloc_funcs s m_fs i) = s\<lparr>funcs := funcs s @ alloc_funcs_simple m_fs i\<rparr>"
proof(induct m_fs arbitrary: s)
  case Nil
  then show ?case by auto 
next
  case (Cons a m_fs)
  have "fst (alloc_funcs s (a # m_fs) i) = fst (alloc_funcs (fst (alloc_func s a i)) m_fs i)"
    by(simp split:prod.splits)
  then show ?case unfolding alloc_func_equiv Cons by simp
qed

abbreviation "alloc_tabs_simple m_ts \<equiv> map alloc_tab_simple m_ts"

lemma alloc_tabs_equiv:"fst (alloc_tabs s m_ts) = s\<lparr>tabs := tabs s @ alloc_tabs_simple m_ts\<rparr>"
proof(induct m_ts arbitrary:s)
  case Nil
  then show ?case by auto
next
  case (Cons a m_ts)
  have "fst (alloc_tabs s (a # m_ts)) = fst (alloc_tabs (fst (alloc_tab s a)) m_ts)"
    by(simp split:prod.splits)
  then show ?case unfolding alloc_tab_equiv Cons by simp
qed

abbreviation "alloc_mems_simple m_ms \<equiv> map alloc_mem_simple m_ms" 

lemma alloc_mems_equiv:"fst (alloc_mems s m_ms) = s\<lparr>mems := mems s @ alloc_mems_simple m_ms\<rparr>"
proof(induct m_ms arbitrary:s)
  case Nil
  then show ?case by auto
next
  case (Cons a m_ms)
  have "fst (alloc_mems s (a # m_ms)) = fst (alloc_mems (fst (alloc_mem s a)) m_ms)"
    by(simp split:prod.splits)
  then show ?case unfolding alloc_mem_equiv Cons by simp
qed

abbreviation "alloc_globs_simple m_gs vs \<equiv> map (\<lambda>m_g_v. alloc_glob_simple m_g_v) (zip m_gs vs)"

lemma alloc_globs_equiv:
  "fst (alloc_globs s m_gs vs) = s\<lparr>globs := globs s @ alloc_globs_simple m_gs vs\<rparr>"
proof(induct "zip m_gs vs" arbitrary:s m_gs vs)
  case Nil
  then show ?case by auto
next
  case (Cons a m_g_vs)
  have 1:"m_g_vs = zip (map fst m_g_vs) (map snd m_g_vs)"
    by (simp add: zip_map_fst_snd) 
  have "fst (alloc_globs s (map fst (a#m_g_vs)) (map snd (a#m_g_vs))) 
      = fst (alloc_globs (fst (alloc_glob s a)) (map fst m_g_vs) (map snd m_g_vs))"
    by(simp split:prod.splits)
  also have "... = s\<lparr>globs := globs s @ alloc_globs_simple (map fst (a#m_g_vs)) (map snd (a#m_g_vs))\<rparr>"
    unfolding alloc_glob_equiv Cons(1)[OF 1] by(simp)
  finally show ?case by(simp add: zip_map_fst_snd Cons(2)) 
qed

abbreviation "alloc_elems_simple m_els v_rss \<equiv> map (\<lambda>m_el_v_rs. alloc_elem_simple m_el_v_rs) (zip m_els v_rss)"

lemma alloc_elems_equiv:
  "fst (alloc_elems s m_els v_rss) = s\<lparr>elems := elems s @ alloc_elems_simple m_els v_rss\<rparr>"
proof(induct "zip m_els v_rss" arbitrary:s m_els v_rss)
  case Nil
  then show ?case by auto
next
  case (Cons m_el_v_rs' m_els_v_rss')
  have 1:"m_els_v_rss' = zip (map fst m_els_v_rss') (map snd m_els_v_rss')"
    by (simp add: zip_map_fst_snd) 
  have "fst (alloc_elems s (map fst (m_el_v_rs'#m_els_v_rss')) (map snd (m_el_v_rs'#m_els_v_rss'))) 
      = fst (alloc_elems (fst (alloc_elem s m_el_v_rs')) (map fst m_els_v_rss') (map snd m_els_v_rss'))"
    by(simp split:prod.splits)
  also have "... = s\<lparr>elems := elems s @ alloc_elems_simple (map fst (m_el_v_rs'#m_els_v_rss')) (map snd (m_el_v_rs'#m_els_v_rss'))\<rparr>"
    unfolding alloc_elem_equiv Cons(1)[OF 1] by(simp)
  finally show ?case by(simp add: zip_map_fst_snd Cons(2)) 
qed


abbreviation "alloc_datas_simple m_ds \<equiv> map alloc_data_simple m_ds"

lemma alloc_datas_equiv:
  "fst (alloc_datas s m_ds) = s\<lparr>datas := datas s @ alloc_datas_simple m_ds\<rparr>"
proof(induct "m_ds" arbitrary: s)
  case Nil
  then show ?case by auto
next
  case (Cons m_d' m_ds')
  then have "fst (alloc_datas s (m_d'#m_ds')) = fst (alloc_datas (fst (alloc_data s m_d')) m_ds')"
    apply (simp split: prod.splits)
    by (metis fst_conv)
  also have "... = s\<lparr>datas := datas s @ alloc_datas_simple (m_d'#m_ds')\<rparr>"
    unfolding alloc_data_equiv Cons(1) by simp

  then show ?case using alloc_data_equiv
    apply (simp split: prod.splits) 
    by (metis fst_conv) 
qed

lemma alloc_tabs_store_agnostic: 
  assumes "tabs s1 = tabs s2"
         "(s1', i1) = alloc_tabs s1 (m_tabs m)"
         "(s2', i2) = alloc_tabs s2 (m_tabs m)"
  shows "tabs s1' = tabs s2' \<and> i1 = i2"
  using alloc_tabs_range(1) assms  alloc_tabs_equiv
  by (metis (no_types, lifting) fst_conv s.select_convs(2) s.surjective s.update_convs(2))

lemma alloc_mems_store_agnostic: 
  assumes "mems s1 = mems s2"
         "(s1', i1) = alloc_mems s1 (m_mems m)"
         "(s2', i2) = alloc_mems s2 (m_mems m)"
  shows "mems s1' = mems s2' \<and> i1 = i2"
  using alloc_mems_range(1) assms  alloc_mems_equiv
  by (metis (no_types, lifting) fst_conv s.select_convs(3) s.surjective s.update_convs(3))

lemma alloc_globs_store_agnostic: 
  assumes "globs s1 = globs s2"
         "(s1', i1) = alloc_globs s1 (m_globs m) gvs"
         "(s2', i2) = alloc_globs s2 (m_globs m) gvs"
  shows "globs s1' = globs s2' \<and> i1 = i2"
  using alloc_globs_range(1) assms alloc_globs_equiv
  by (metis (no_types, lifting))

lemma alloc_elems_store_agnostic: 
  assumes "elems s1 = elems s2"
         "(s1', i1) = alloc_elems s1 (m_elems m) v_rss"
         "(s2', i2) = alloc_elems s2 (m_elems m) v_rss"
  shows "elems s1' = elems s2' \<and> i1 = i2"
  using alloc_elems_range(1) assms alloc_elems_equiv
  by (metis (no_types, lifting))

lemma alloc_datas_store_agnostic: 
  assumes "datas s1 = datas s2"
         "(s1', i1) = alloc_datas s1 (m_datas m)"
         "(s2', i2) = alloc_datas s2 (m_datas m)"
  shows "datas s1' = datas s2' \<and> i1 = i2"
  using alloc_datas_range(1) assms alloc_datas_equiv
  by (metis (no_types, lifting))

lemma alloc_module_allocated_form: 
  assumes "alloc_module s m imps gvs elvs (s',inst,exps)"
  shows "alloc_funcs s (m_funcs m) inst = (ss,i_fs) 
\<Longrightarrow> funcs s' = funcs ss \<and> inst.funcs inst = (ext_funcs imps)@i_fs"
  "alloc_tabs s (m_tabs m) = (ss,i_ts) 
\<Longrightarrow> tabs s' = tabs ss \<and> inst.tabs inst = (ext_tabs imps)@i_ts"
  "alloc_mems s (m_mems m) = (ss,i_ms) 
\<Longrightarrow> mems s' = mems ss \<and> inst.mems inst = (ext_mems imps)@i_ms"
  "alloc_globs s (m_globs m) gvs = (ss,i_gs) 
\<Longrightarrow> globs s' = globs ss \<and> inst.globs inst = (ext_globs imps)@i_gs"
  "alloc_elems s (m_elems m) elvs = (ss,i_es) 
\<Longrightarrow> elems s' = elems ss \<and> inst.elems inst = i_es"
  "alloc_datas s (m_datas m) = (ss,i_ds) 
\<Longrightarrow> datas s' = datas ss \<and> inst.datas inst = i_ds"
proof -
  obtain s1 s2 s3 s4 s5 i_fs' i_ts' i_ms' i_gs' i_es' i_ds' where
    inst:"inst = \<lparr>types=(m_types m), 
            funcs=(ext_funcs imps)@i_fs', 
           tabs=(ext_tabs imps)@i_ts',
           mems=(ext_mems imps)@i_ms',
           globs=(ext_globs imps)@i_gs',
           elems=i_es',
           datas=i_ds'\<rparr>" 
    and funcs:"alloc_funcs s (m_funcs m) inst = (s1,i_fs')" 
    and tabs:"alloc_tabs s1 (m_tabs m) = (s2,i_ts')" 
    and mems:"alloc_mems s2 (m_mems m) = (s3,i_ms')" 
    and globs:"alloc_globs s3 (m_globs m) gvs = (s4,i_gs')" 
    and elems:"alloc_elems s4 (m_elems m) elvs = (s5, i_es')"
    and datas:"alloc_datas s5 (m_datas m) = (s', i_ds')"
    using assms unfolding alloc_module.simps by auto

  show "alloc_funcs s (m_funcs m) inst = (ss,i_fs) 
  \<Longrightarrow> funcs s' = funcs ss \<and> inst.funcs inst = (ext_funcs imps)@i_fs" 
    using funcs alloc_tabs_range[OF tabs] 
      alloc_mems_range[OF mems]
      alloc_globs_range[OF globs]
      alloc_elems_range[OF elems]
      alloc_datas_range[OF datas]
      inst
    by simp

  show "alloc_tabs s (m_tabs m) = (ss,i_ts) 
  \<Longrightarrow> tabs s' = tabs ss \<and> inst.tabs inst = (ext_tabs imps)@i_ts" 
    using alloc_funcs_range[OF funcs] alloc_tabs_store_agnostic tabs
      alloc_mems_range[OF mems] alloc_globs_range[OF globs]
      alloc_elems_range[OF elems] alloc_datas_range[OF datas] inst 
    by (metis inst.select_convs(3)) 

  show "alloc_mems s (m_mems m) = (ss,i_ms) 
  \<Longrightarrow> mems s' = mems ss \<and> inst.mems inst = (ext_mems imps)@i_ms"
    using alloc_funcs_range[OF funcs] alloc_tabs_range[OF tabs]
      alloc_elems_range[OF elems] alloc_datas_range[OF datas] alloc_mems_store_agnostic mems
      alloc_globs_range[OF globs] inst
    by (metis inst.select_convs(4)) 

  show "alloc_globs s (m_globs m) gvs = (ss,i_gs) 
  \<Longrightarrow> globs s' = globs ss \<and> inst.globs inst = (ext_globs imps)@i_gs"
    using alloc_funcs_range[OF funcs] alloc_tabs_range[OF tabs] alloc_mems_range[OF mems]
    alloc_elems_range[OF elems] alloc_datas_range[OF datas]
      alloc_globs_store_agnostic globs inst
    by (metis inst.select_convs(5))

  show "alloc_elems s (m_elems m) elvs = (ss,i_es) 
  \<Longrightarrow> elems s' = elems ss \<and> inst.elems inst = i_es"
    using alloc_funcs_range[OF funcs] alloc_tabs_range[OF tabs] alloc_mems_range[OF mems]
    alloc_elems_range elems alloc_globs_range[OF globs] alloc_datas_range[OF datas] inst
    by (metis (mono_tags, lifting) inst.select_convs(6))
  
  show "alloc_datas s (m_datas m) = (ss,i_ds)
  \<Longrightarrow> datas s' = datas ss \<and> inst.datas inst = i_ds"
    using alloc_funcs_range[OF funcs] alloc_tabs_range[OF tabs] alloc_mems_range[OF mems]
          alloc_globs_range[OF globs] alloc_elems_range[OF elems] alloc_datas_range[OF datas]
          datas inst inst.select_convs(7) alloc_datas_range
    by (metis (mono_tags, lifting) inst.select_convs(7))
qed

lemma alloc_module_funcs_form:
  assumes "alloc_module s m v_imps g_inits el_inits (s', inst, v_exps)" 
        "funcs s' = funcs s @ fs"
  shows "fs = alloc_funcs_simple (m_funcs m) inst"
proof -
  define s_mid where s_mid_def:"s_mid = fst (alloc_funcs s (m_funcs m) inst)"
  then have "funcs s' = funcs s_mid" 
    using alloc_module_allocated_form(1)[OF assms(1)]
    by (metis eq_fst_iff) 
  then have "funcs s_mid = funcs s @ fs" using assms(2) by auto
  then show ?thesis using alloc_funcs_equiv s_mid_def by auto
qed

lemma alloc_module_tabs_form: 
  assumes "alloc_module s m v_imps g_inits el_inits (s', inst, v_exps)" 
          "tabs s' = tabs s @ ts" 
  shows "ts = alloc_tabs_simple (m_tabs m)"
proof - 
  have "tabs s' = tabs (fst (alloc_tabs s (m_tabs m)))" 
    using alloc_module_allocated_form(2)[OF assms(1)]
    by (metis eq_fst_iff) 
  then show ?thesis using alloc_tabs_equiv assms(2) by auto
qed

lemma alloc_module_mems_form: 
  assumes "alloc_module s m v_imps g_inits el_inits (s', inst, v_exps)" 
          "mems s' = mems s @ ms" 
  shows "ms = alloc_mems_simple (m_mems m)"
proof - 
  have "mems s' = mems (fst (alloc_mems s (m_mems m)))" 
    using alloc_module_allocated_form(3)[OF assms(1)]
    by (metis eq_fst_iff) 
  then show ?thesis using alloc_mems_equiv assms(2) by auto
qed

lemma alloc_module_globs_form: 
  assumes "alloc_module s m v_imps g_inits el_inits (s', inst, v_exps)" 
          "globs s' = globs s @ gs" 
  shows "gs = alloc_globs_simple (m_globs m) g_inits"
proof - 
  have "globs s' = globs (fst (alloc_globs s (m_globs m) g_inits))" 
    using alloc_module_allocated_form(4)[OF assms(1)]
    by (metis eq_fst_iff) 
  then show ?thesis using alloc_globs_equiv assms(2) by auto
qed

lemma alloc_module_elems_form: 
  assumes "alloc_module s m v_imps g_inits el_inits (s', inst, v_exps)" 
          "elems s' = elems s @ els" 
  shows "els = alloc_elems_simple (m_elems m) el_inits"
proof - 
  have "elems s' = elems (fst (alloc_elems s (m_elems m) el_inits))" 
    using alloc_module_allocated_form(5)[OF assms(1)]
    by (metis eq_fst_iff) 
  then show ?thesis using alloc_elems_equiv assms(2) by auto
qed

lemma alloc_module_datas_form: 
  assumes "alloc_module s m v_imps g_inits el_inits (s', inst, v_exps)" 
          "datas s' = datas s @ ds" 
  shows "ds = alloc_datas_simple (m_datas m)"
proof - 
  have "datas s' = datas (fst (alloc_datas s (m_datas m)))" 
    using alloc_module_allocated_form(6)[OF assms(1)]
    by (metis eq_fst_iff) 
  then show ?thesis using alloc_datas_equiv assms(2) by auto
qed

lemma ext_typing_imp_helper:
  assumes "list_all2 (external_typing s) v_imps t_imps" 
          "\<And>v t. external_typing s v t \<Longrightarrow> (\<exists>v'. f v = Some v') \<longleftrightarrow> (\<exists>e'. g t = Some e')"
          "\<And>v t v' t'. external_typing s v t \<Longrightarrow> f v = Some v' \<Longrightarrow> g t = Some t' \<Longrightarrow> P v' t'"
        shows "list_all2 P (List.map_filter f v_imps) (List.map_filter g t_imps)"
proof -
  {
    fix a
    have "list_all2 (external_typing s) (map fst a) (map snd a) 
    \<Longrightarrow> list_all2 P (List.map_filter f (map fst a)) (List.map_filter g (map snd a))"
    proof(induct a)
      case Nil
      then show ?case by (simp add: map_filter_simps(2)) 
    next
      case (Cons a1 a2)
      have 1:"list_all2 P (List.map_filter f (map fst a2)) (List.map_filter g (map snd a2))" 
        using Cons by auto 
      have 2:"external_typing s (fst a1) (snd a1)" using Cons(2) by auto
      show ?case
      proof(cases "\<exists>v'. f (fst a1) = Some v'")
        case True
        then obtain v' where v'_def:"f (fst a1) = Some v'" by auto
        then obtain t' where t'_def:"g (snd a1) = Some t'" using assms(2)[OF 2]
          by force
        have "P v' t'" using assms(3)[OF 2 v'_def t'_def]  by -
        then show ?thesis using 1 v'_def t'_def by(simp add: List.map_filter_simps)
      next
        case False
        then have no_t':"g (snd a1) = None" using assms(2)[OF 2] by auto 
        show ?thesis using False no_t' 1 by(simp add: List.map_filter_simps) 
      qed
    qed
  }
  then show ?thesis using assms
    by (metis list.in_rel) 
qed

lemma ext_typing_imp_funci_agree:
  assumes "list_all2 (external_typing s) v_imps t_imps"
  shows "list_all2 (funci_agree (funcs s)) (ext_funcs v_imps) (ext_t_funcs t_imps)" 
  apply(rule ext_typing_imp_helper[OF assms])  
   apply(simp add: external_typing.simps)
   apply auto
  apply(simp split:v_ext.splits extern_t.splits add: external_typing.simps funci_agree_def) 
  done 

lemma ext_typing_imp_globi_agree:
  assumes "list_all2 (external_typing s) v_imps t_imps"
  shows "list_all2 (globi_agree (globs s)) (ext_globs v_imps) (ext_t_globs t_imps)" 
  apply(rule ext_typing_imp_helper[OF assms])  
   apply(simp add: external_typing.simps)
   apply auto
  apply(simp split:v_ext.splits extern_t.splits add: external_typing.simps globi_agree_def) 
  done 

lemma ext_typing_imp_tabi_agree:
  assumes "list_all2 (external_typing s) v_imps t_imps"
  shows "list_all2 (tabi_agree (tabs s)) (ext_tabs v_imps) (ext_t_tabs t_imps)" 
  apply(rule ext_typing_imp_helper[OF assms])  
   apply(simp add: external_typing.simps)
   apply auto
  apply(simp split:v_ext.splits extern_t.splits add: external_typing.simps tabi_agree_def) 
  done 

lemma ext_typing_imp_memi_agree:
  assumes "list_all2 (external_typing s) v_imps t_imps"
  shows "list_all2 (memi_agree (mems s)) (ext_mems v_imps) (ext_t_mems t_imps)" 
  apply(rule ext_typing_imp_helper[OF assms])  
   apply(simp add: external_typing.simps)
   apply auto
  apply(simp split:v_ext.splits extern_t.splits add: external_typing.simps memi_agree_def) 
  done 

end