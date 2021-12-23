theory Wasm_Instantiation_Properties_Aux imports Wasm_Instantiation Wasm_Properties begin


definition element_in_bounds where 
"element_in_bounds s inst e_ind e \<equiv>
   let i = inst.tabs inst ! e_tab e 
   in i < length (tabs s) \<and>  e_ind + length (e_init e) \<le> length (fst (tabs s ! i))"

abbreviation "element_funcs_in_bounds s inst e 
\<equiv>list_all (\<lambda>i. (inst.funcs inst)!i < length (s.funcs s)) (e_init e)" 

lemma init_tab_form:
  assumes "s' = init_tab s inst e_ind e" 
  shows "list_all2 tab_extension (tabs s) (tabs s')" 
        "\<exists>tabs'. s' = s\<lparr>tabs := tabs'\<rparr>"
        "element_funcs_in_bounds s inst e
        \<Longrightarrow> element_in_bounds s inst e_ind e
        \<Longrightarrow> list_all (tab_agree s) (tabs s) 
        \<Longrightarrow> list_all (tab_agree s') (tabs s')"
        "list_all2 (\<lambda>t t'. tab_typing t tt \<longrightarrow> tab_typing t' tt) (tabs s) (tabs s')"
proof -
  obtain t_ind tab_e max e_pay tab'_e where init_tab_is:
    "t_ind = ((inst.tabs inst)!(e_tab e))" 
    "(tab_e,max) = (tabs s)!t_ind" 
    "e_pay = map (\<lambda>i. Some ((inst.funcs inst)!i)) (e_init e)"
    "tab'_e = ((take e_ind tab_e) @ e_pay @ (drop (e_ind + length e_pay) tab_e))" 
    by (metis prod.exhaust)

  then have "init_tab s inst e_ind e = s\<lparr>tabs := (tabs s)[t_ind := (tab'_e,max)]\<rparr>" 
    unfolding init_tab_def by(fastforce simp add: Let_def split: prod.splits)
  then have 1:"s' = s\<lparr>tabs := (tabs s)[t_ind := (tab'_e,max)]\<rparr>" using assms by auto 

  have 2: "tabs s' = (tabs s)[t_ind := (tab'_e,max)]" using 1 by auto

  have 3: "\<And>P. P (tab_e,max) (tab'_e, max) \<Longrightarrow> (\<And>a. P a a) \<Longrightarrow> list_all2 P (tabs s) (tabs s')"
    using init_tab_is(2) unfolding 1 list_all2_conv_all_nth  
    by (simp, metis nth_list_update_eq nth_list_update_neq)

  have "length tab_e \<le> length tab'_e" using init_tab_is
    by simp 
  then have "tab_extension (tab_e,max) (tab'_e, max)" 
    unfolding tab_extension_def using init_tab_is
    by (metis fst_conv snd_conv) 
  then show "list_all2 tab_extension (tabs s) (tabs s')"  
    using 3 tab_extension_refl by auto

  show "\<exists>tabs'. s' = s\<lparr>tabs := tabs'\<rparr>" unfolding assms init_tab_def
    by(simp add: Let_def exI split:prod.splits)

  have "funcs s = funcs s'" unfolding 1 by auto

  {
    assume "list_all (case_option True (\<lambda>i. i < length (s.funcs s))) e_pay" 
    then have within_funcs_bounds:"list_all (case_option True (\<lambda>i. i < length (s.funcs s'))) e_pay" 
      using \<open>funcs s = funcs s'\<close> by auto

    assume "element_in_bounds s inst e_ind e"
    then have "e_ind + (length e_pay) \<le> length tab_e" 
      using init_tab_is unfolding element_in_bounds_def
      by (metis fst_conv length_map) 
    then have same_length:"length tab'_e = length tab_e" using init_tab_is by auto

    have set_inclusion:"set tab'_e \<subseteq> set tab_e \<union> set e_pay " using init_tab_is
      (* ugly sledgehammer *)
      by (smt (z3) set_append set_drop_subset set_take_subset subset_trans sup.boundedI sup_ge1 sup_ge2)

    {
      assume "tab_agree s (tab_e,max)"  
      then have "tab_agree s' (tab_e,max)" 
        unfolding tab_agree_def using \<open>funcs s = funcs s'\<close> by auto
    
      then have "tab_agree s' (tab'_e, max)" unfolding tab_agree_def 
        using same_length within_funcs_bounds set_inclusion
        by (metis append_take_drop_id fst_conv init_tab_is(4) list_all_append snd_conv) 
    } 
    then have "list_all (tab_agree s) (tabs s) 
        \<Longrightarrow> list_all (tab_agree s') (tabs s')"
      using init_tab_is(2) length_list_update nth_list_update_eq nth_list_update_neq
      unfolding list_all_length by (metis "2" \<open>s.funcs s = s.funcs s'\<close> tab_agree_def) 
      
  }
  then show "element_funcs_in_bounds s inst e
        \<Longrightarrow> element_in_bounds s inst e_ind e
        \<Longrightarrow> list_all (tab_agree s) (tabs s) 
        \<Longrightarrow> list_all (tab_agree s') (tabs s')"
    using init_tab_is by (simp add: list_all_length)

  have "tab_typing (tab_e, max) tt \<longrightarrow> tab_typing (tab'_e, max) tt" 
    using init_tab_is(4) unfolding tab_typing_def limits_compat_def by (simp, auto)
  then show "list_all2 (\<lambda>t t'. tab_typing t tt \<longrightarrow> tab_typing t' tt) (tabs s) (tabs s')" 
    using 3 by simp
qed

lemma tab_extension_trans:"tab_extension a b \<Longrightarrow> tab_extension b c \<Longrightarrow> tab_extension a c" 
  unfolding tab_extension_def by auto


lemma init_tabs_trans_pred: 
  assumes "s' = init_tabs s inst e_inds es" 
          "\<And>a b c. P a b \<Longrightarrow> P b c \<Longrightarrow> P a c"
          "\<And>a. P a a"
          "\<And>s1 s2 e_inds es. s2 = init_tab s1 inst e_inds es \<Longrightarrow> P s1 s2"
  shows "P s s'" 
proof -
  {
    fix a
    have "s' = foldl (\<lambda>s' (e_ind,e). init_tab s' inst e_ind e) s a \<Longrightarrow> P s s'"
    proof (induction a arbitrary:s)
      case Nil
      show ?case using Nil assms(3) unfolding foldl_Nil 
        by(simp)  
    next
      case (Cons a1 a2)
      define s_mid where "s_mid = init_tab s inst (fst a1) (snd a1)" 
      then have 1:"s' = foldl (\<lambda>s' (e_ind,e). init_tab s' inst e_ind e) s_mid a2" 
        using Cons foldl_Cons
        by(simp add: case_prod_beta')
      show ?case using assms(2)[OF assms(4)[OF s_mid_def] Cons(1)[OF 1]] by auto
      qed 
  }
  then show "P s s'" using assms(1) unfolding init_tabs_def
    by blast
    
qed

lemma init_tabs_trans_list_pred: 
  assumes "s' = init_tabs s inst e_inds es" 
          "\<And>a b c. P a b \<Longrightarrow> P b c \<Longrightarrow> P a c"
          "\<And>a. P a a" 
          "\<And>s1 s2 inst e_ind e. s2 = init_tab s1 inst e_ind e \<Longrightarrow> list_all2 P (tabs s1) (tabs s2)"
        shows "list_all2 P (tabs s) (tabs s')" 
  using init_tabs_trans_pred[OF assms(1), where P="\<lambda>s1 s2. list_all2 P (tabs s1) (tabs s2)"] 
    assms list_all2_trans list_all2_refl
  by (smt (verit, best)) 

lemma init_tabs_tab_extension:
  assumes "s' = init_tabs s inst e_inds es" 
  shows "list_all2 tab_extension (tabs s) (tabs s')" 
  using init_tabs_trans_list_pred[OF assms, where P=tab_extension] tab_extension_trans
      tab_extension_refl init_tab_form(1) by blast

lemma init_tabs_only_modify_tabs: 
  assumes "s' = init_tabs s inst e_inds es" 
  shows "\<exists>tabs'. s' = s\<lparr>tabs := tabs'\<rparr>" 
  apply(rule init_tabs_trans_pred[OF assms], auto)
   apply(metis s.cases s.update_convs(2))
  apply(simp add: init_tab_form(2))
  done

lemma init_tabs_tab_typing:
  assumes "s' = init_tabs s inst e_inds es" 
  shows "list_all2 (\<lambda>t t'. tab_typing t tt \<longrightarrow> tab_typing t' tt) (tabs s) (tabs s')"
  apply(rule init_tabs_trans_list_pred[OF assms], auto)
  by (simp add: init_tab_form(4)) 

lemma init_tabs_tabi_agree:
  assumes "s' = init_tabs s inst e_inds es" 
        "tabi_agree (tabs s) n tt"
  shows "tabi_agree (tabs s') n tt"
  using init_tabs_tab_typing[OF assms(1)] assms(2) unfolding tabi_agree_def
  by (smt (verit, best) list_all2_conv_all_nth) 


lemma init_tabs_tab_agree:
  assumes "s' = init_tabs s inst e_inds es" 
"list_all (element_funcs_in_bounds s inst) es"
"list_all2 (element_in_bounds s inst) e_inds es"
"list_all (tab_agree s) (tabs s)"
  shows "list_all (tab_agree s') (tabs s')"
proof - 

  {
    fix a 
    have "list_all (element_funcs_in_bounds s inst) (map snd a)
      \<Longrightarrow> list_all2 (element_in_bounds s inst) (map fst a) (map snd a)
      \<Longrightarrow> list_all (tab_agree s) (tabs s)
      \<Longrightarrow> s' = foldl (\<lambda>s' (e_ind,e). init_tab s' inst e_ind e) s a
      \<Longrightarrow> list_all (tab_agree s') (tabs s')"
    proof(induct a arbitrary: s)
      case Nil
      then show ?case by simp 
    next
      case (Cons a1 a2)
      define s_mid where "s_mid = init_tab s inst (fst a1) (snd a1)" 
      then have 1:"s' = foldl (\<lambda>s' (e_ind,e). init_tab s' inst e_ind e) s_mid a2" 
        using Cons foldl_Cons
        by(simp add: case_prod_beta')

      have "funcs s_mid = funcs s" using init_tab_form(2)[OF s_mid_def] by auto 
      then have 2:"list_all (element_funcs_in_bounds s_mid inst) (map snd a2)" using Cons(2) by auto

      {
        fix x 
        assume "x \<in> set (zip (map fst a2) (map snd a2))" 
        then have "element_in_bounds s inst (fst x) (snd x)" 
          using Cons(3) case_prod_unfold zip_map_fst_snd unfolding list_all2_iff
          by (metis (no_types, lifting) set_subset_Cons subset_code(1))

        moreover have "list_all2 tab_extension (tabs s) (tabs s_mid)" 
          using init_tab_form(1)[OF s_mid_def] by -
         
        ultimately have "element_in_bounds s_mid inst (fst x) (snd x)" 
          unfolding element_in_bounds_def tab_extension_def Let_def 
          by (metis (no_types, lifting) le_trans list_all2_conv_all_nth)
      }
      then have 3:"list_all2 (element_in_bounds s_mid inst) (map fst a2) (map snd a2)"
        unfolding list_all2_iff by auto

      have "element_funcs_in_bounds s inst (snd a1)" using Cons(2) by auto 
      moreover have "element_in_bounds s inst (fst a1) (snd a1)" using Cons(3) by auto 
      ultimately have 4:"list_all (tab_agree s_mid) (tabs s_mid)" 
        using init_tab_form(3)[OF s_mid_def] Cons(4)  by auto
      then show ?case using Cons(1)[OF 2 3 4 1] by -
    qed
  }
  then show ?thesis using assms unfolding init_tabs_def
    by (metis (no_types, lifting) list_all2_lengthD map_fst_zip map_snd_zip) 
qed

  

lemma init_mem_form:
  assumes "s' = init_mem s inst d_ind d" 
  shows "list_all2 mem_extension (mems s) (mems s')" 
        "\<exists>mems'. s' = s\<lparr>mems := mems'\<rparr>"
proof -
  obtain m_ind mem mem' where init_mem_is: "m_ind = ((inst.mems inst)!(d_data d))"
                               "mem = (mems s)!m_ind"
                               "mem' = write_bytes mem d_ind (d_init d)"
                               "s' =s\<lparr>mems := (mems s)[m_ind := mem']\<rparr>" 
    using assms unfolding init_mem_def Let_def by auto 

  have "mem_size mem \<le> mem_size mem'" using init_mem_is
    by (simp add: div_le_mono mem_length_def mem_rep_length.rep_eq 
       mem_rep_write_bytes.rep_eq mem_size_def write_bytes_def)
     (* sledgehammer :P *) 

  moreover have "mem_max mem = mem_max mem'" using init_mem_is
    by (simp add: mem_max_def write_bytes_def) 

  ultimately have "mem_extension mem mem'" 
    unfolding mem_extension_def by auto

  then show "list_all2 mem_extension (mems s) (mems s')"  
    using init_mem_is mem_extension_refl unfolding init_mem_is(4) list_all2_conv_all_nth  
    by (simp, metis nth_list_update_eq nth_list_update_neq)

  show "\<exists>mems'. s' = s\<lparr>mems := mems'\<rparr>" unfolding assms init_mem_def
    by(simp add: Let_def exI split:prod.splits)
qed


lemma mem_extension_trans:"mem_extension a b \<Longrightarrow> mem_extension b c \<Longrightarrow> mem_extension a c" 
  unfolding mem_extension_def by auto

(* todo: make it like init_tabs_form once the tabs proofs are done *)
lemma init_mems_form:
  assumes "s' = init_mems s inst d_inds ds" 
  shows "list_all2 mem_extension (mems s) (mems s')" 
        "\<exists>mems'. s' = s\<lparr>mems := mems'\<rparr>"
proof -
  {
    fix a
    have "s' = foldl (\<lambda>s' (d_ind,d). init_mem s' inst d_ind d) s a \<Longrightarrow> 
          list_all2 mem_extension (mems s) (mems s') \<and> (\<exists>mems'. s' = s\<lparr>mems := mems'\<rparr>)"
    proof (induction a arbitrary:s)
      case Nil
      show ?case using Nil exI[where x="mems s"] unfolding foldl_Nil 
        by(simp add: list_all2_refl mem_extension_refl)  
    next
      case (Cons a1 a2)
      define s_mid where "s_mid = init_mem s inst (fst a1) (snd a1)" 
      then have 1:"s' = foldl (\<lambda>s' (d_ind,d). init_mem s' inst d_ind d) s_mid a2" 
        using Cons foldl_Cons
        by(simp add: case_prod_beta')

      note ind_assms = init_mem_form[OF s_mid_def] Cons(1)[OF 1]

      have "list_all2 mem_extension (mems s) (mems s')" using ind_assms
        list_all2_trans mem_extension_trans
        by blast
      moreover have "\<exists>mems'. s' = s\<lparr>mems := mems'\<rparr>" using ind_assms
        by auto
      ultimately show ?case by auto
    qed 
  }
  note helper = this
  show "list_all2 mem_extension (mems s) (mems s')" using helper assms unfolding init_mems_def
    by presburger 
  show "\<exists>mems'. s' = s\<lparr>mems := mems'\<rparr>" using helper assms unfolding init_mems_def
    by presburger
qed

lemma init_mems_only_modify_mems: 
  assumes "s' = init_mems s inst e_inds es" 
  shows "\<exists>mems'. s' = s\<lparr>mems := mems'\<rparr>"
  using init_mems_form(2)[OF assms] by -


(* while mathematically superfluous, this form makes the following lemmas easier to prove *)
lemma store_extension_intros_with_refl: 
  assumes "funcs s = funcs s' \<or> (\<exists> fs. funcs s @ fs = funcs s')" 
  "tabs s = tabs s' \<or> (\<exists> t1 t2. t1 @ t2 = tabs s' \<and> list_all2 tab_extension (tabs s) t1)"
  "mems s = mems s' \<or> (\<exists> m1 m2. m1 @ m2 = mems s' \<and> list_all2 mem_extension (mems s) m1)" 
  "globs s = globs s' \<or> (\<exists> g1 g2. g1 @ g2 = globs s' \<and> list_all2 global_extension (globs s) g1)" 
  shows "store_extension s s'"
proof -         
  have funcs:"\<exists> fs. funcs s @ fs = funcs s'" using assms(1) by auto
  have tabs: "\<exists> t1 t2. t1 @ t2 = tabs s' \<and> list_all2 tab_extension (tabs s) t1" 
    using assms(2) tab_extension_refl list_all2_refl by (metis append_Nil2) 
  have mems: "\<exists> m1 m2. m1 @ m2 = mems s' \<and> list_all2 mem_extension (mems s) m1" 
    using assms(3) mem_extension_refl list_all2_refl by (metis append_Nil2) 
  have globs: "\<exists> g1 g2. g1 @ g2 = globs s' \<and> list_all2 global_extension (globs s) g1"  
    using assms(4) global_extension_refl list_all2_refl by (metis append_Nil2) 
  show ?thesis using funcs mems tabs globs unfolding store_extension.simps
    by (metis (full_types) unit.exhaust s.surjective) 
qed

lemma init_tabs_preserve_store_extension: 
  assumes "s' = init_tabs s inst e_inds es" 
  shows "store_extension s s'"
  using init_tabs_tab_extension[OF assms] init_tabs_only_modify_tabs[OF assms] 
      store_extension_intros_with_refl
  by (metis append_Nil2 s.ext_inject s.surjective s.update_convs(2))   

lemma init_mems_preserve_store_extension: 
  assumes "s' = init_mems s inst d_inds ds" 
  shows "store_extension s s'"
  using init_mems_form[OF assms] store_extension_intros_with_refl
  by (metis append_Nil2 s.ext_inject s.surjective s.update_convs(3))   

lemma alloc_module_preserve_store_extension:
  assumes "alloc_module s m imps gvs (s',inst,exps)" 
  shows "store_extension s s'"
  using alloc_module_ext_arb[OF assms] 
  store_extension_intros_with_refl list_all2_refl tab_extension_refl mem_extension_refl global_extension_refl
  by metis


definition alloc_func_simple :: "module_func \<Rightarrow> inst \<Rightarrow> cl" where
  "alloc_func_simple m_f inst =
     (case m_f of (i_t, loc_ts, b_es) \<Rightarrow>
        Func_native inst ((types inst)!i_t) loc_ts b_es)"

lemma alloc_func_equiv:"fst (alloc_func s m_f i) = s\<lparr>funcs := funcs s @ [alloc_func_simple m_f i]\<rparr>"
  using alloc_func_def alloc_func_simple_def by(simp split:prod.splits)

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


lemma alloc_module_funcs_only_alloc_func:
  assumes "alloc_module s m imps gvs (s',inst,exps)"
    "alloc_funcs s (m_funcs m) inst = (s1,i_fs)"
  shows "funcs s' = funcs s1" 
  using assms alloc_tabs_range alloc_mems_range alloc_globs_range 
  unfolding alloc_module.simps 
  by force 

lemma alloc_module_funcs_form:
  assumes "alloc_module s m v_imps g_inits (s', inst, v_exps)" 
        "funcs s' = funcs s @ fs"
  shows "fs = alloc_funcs_simple (m_funcs m) inst"
proof -
  define s_mid where s_mid_def:"s_mid = fst (alloc_funcs s (m_funcs m) inst)"
  then have "funcs s' = funcs s_mid" 
    using alloc_module_funcs_only_alloc_func[OF assms(1)]
    by (metis eq_fst_iff) 
  then have "funcs s_mid = funcs s @ fs" using assms(2) by auto
  then show ?thesis using alloc_funcs_equiv s_mid_def by auto
qed

definition alloc_tab_simple :: "tab_t \<Rightarrow> tabinst" where
  "alloc_tab_simple m_t = (replicate (l_min m_t) None, (l_max m_t))"

lemma alloc_tab_equiv:"fst (alloc_tab s m_t) = s\<lparr>tabs := tabs s @ [alloc_tab_simple m_t]\<rparr>"
  using alloc_tab_def alloc_tab_simple_def by simp

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

lemma alloc_tabs_store_agnostic: 
  assumes "tabs s1 = tabs s2"
         "(s1', i1) = alloc_tabs s1 (m_tabs m)"
         "(s2', i2) = alloc_tabs s2 (m_tabs m)"
  shows "tabs s1' = tabs s2' \<and> i1 = i2"
  using alloc_tabs_range(1) assms  alloc_tabs_equiv
  by (metis (no_types, lifting) fst_conv s.select_convs(2) s.surjective s.update_convs(2))
   

lemma alloc_module_tabs_only_alloc_tabs:
  assumes "alloc_module s m imps gvs (s',inst,exps)"
    "alloc_tabs s (m_tabs m) = (s1,i_ts)"
  shows "tabs s' = tabs s1 \<and> inst.tabs inst = (ext_tabs imps)@i_ts"
  using assms alloc_funcs_range fst_conv
    alloc_tabs_store_agnostic alloc_mems_range alloc_globs_range 
  unfolding alloc_module.simps
  by(smt (z3) Pair_inject inst.select_convs(3))
  (*todo: takes like 10 seconds to run*)


lemma alloc_module_tabs_form: 
  assumes "alloc_module s m v_imps g_inits (s', inst, v_exps)" 
          "tabs s' = tabs s @ ts" 
  shows "ts = alloc_tabs_simple (m_tabs m)"
proof - 
  have "tabs s' = tabs (fst (alloc_tabs s (m_tabs m)))" 
    using alloc_module_tabs_only_alloc_tabs[OF assms(1)]
    by (metis eq_fst_iff) 
  then show ?thesis using alloc_tabs_equiv assms(2) by auto
qed

definition alloc_glob_simple :: "(module_glob \<times> v) \<Rightarrow> global" where 
  "alloc_glob_simple m_g_v = 
    (case m_g_v of (m_g, v) \<Rightarrow> \<lparr>g_mut=(tg_mut (module_glob.g_type m_g)), g_val=v\<rparr>)"

lemma alloc_glob_equiv:"fst (alloc_glob s m_g_v) = s\<lparr>globs := globs s @ [alloc_glob_simple m_g_v]\<rparr>"
  using alloc_glob_def alloc_glob_simple_def by(simp split:prod.splits)

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

lemma alloc_globs_store_agnostic: 
  assumes "globs s1 = globs s2"
         "(s1', i1) = alloc_globs s1 (m_globs m) gvs"
         "(s2', i2) = alloc_globs s2 (m_globs m) gvs"
  shows "globs s1' = globs s2' \<and> i1 = i2"
  using alloc_globs_range(1) assms alloc_globs_equiv
  by (metis (no_types, lifting))

lemma alloc_module_globs_only_alloc_globs:
  assumes "alloc_module s m imps gvs (s',inst,exps)"
    "alloc_globs s (m_globs m) gvs = (s1,i_gs)"
  shows "globs s' = globs s1 \<and> inst.globs inst = (ext_globs imps)@i_gs"
  using assms alloc_funcs_range fst_conv
    alloc_tabs_range alloc_mems_range alloc_globs_store_agnostic
  unfolding alloc_module.simps
  by (smt (z3) Pair_inject inst.select_convs(5))
  (*todo: takes like 10 seconds to run*)


lemma alloc_module_globs_form: 
  assumes "alloc_module s m v_imps g_inits (s', inst, v_exps)" 
          "globs s' = globs s @ gs" 
  shows "gs = alloc_globs_simple (m_globs m) g_inits"
proof - 
  have "globs s' = globs (fst (alloc_globs s (m_globs m) g_inits))" 
    using alloc_module_globs_only_alloc_globs[OF assms(1)]
    by (metis eq_fst_iff) 
  then show ?thesis using alloc_globs_equiv assms(2) by auto
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