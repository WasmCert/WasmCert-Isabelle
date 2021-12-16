theory Wasm_Instantiation_Properties imports Wasm_Instantiation Wasm_Properties begin

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


lemma store_extension_intros_with_refl: 
  assumes "funcs s = funcs s' \<or> (\<exists> fs. funcs s @ fs = funcs s')" 
  "tabs s = tabs s' \<or> (\<exists> t1 t2. t1 @ t2 = tabs s' \<and> list_all2 tab_extension (tabs s) t1)"
  "mems s = mems s' \<or> (\<exists> m1 m2. m1 @ m2 = mems s' \<and> list_all2 mem_extension (mems s) m1)" 
  "globs s = globs s' \<or> (\<exists> g1 g2. g1 @ g2 = globs s' \<and> list_all2 global_extension (globs s) g1)" 
  shows "store_extension s s'"
proof -         
  have funcs:"\<exists> fs. funcs s @ fs = funcs s'" using assms(1) by auto

  have tabs: "\<exists> t1 t2. t1 @ t2 = tabs s' \<and> list_all2 tab_extension (tabs s) t1" 
    using assms(2) tab_extension_refl list_all2_refl
    by (metis append_Nil2) 

  have mems: "\<exists> m1 m2. m1 @ m2 = mems s' \<and> list_all2 mem_extension (mems s) m1" 
    using assms(3) mem_extension_refl list_all2_refl
    by (metis append_Nil2) 

  have globs: "\<exists> g1 g2. g1 @ g2 = globs s' \<and> list_all2 global_extension (globs s) g1"  
    using assms(4) global_extension_refl list_all2_refl
    by (metis append_Nil2) 
  
  show ?thesis using funcs mems tabs globs unfolding store_extension.simps
    by (metis (full_types) unit.exhaust s.surjective) 
qed


abbreviation "element_in_bounds s inst e_ind e 
\<equiv> e_ind + (length (e_init e)) \<le> length (fst ((tabs s)!((inst.tabs inst)!(e_tab e))))"

abbreviation "element_funcs_in_bounds s inst e 
\<equiv>list_all (\<lambda>i. (inst.funcs inst)!i < length (s.funcs s)) (e_init e)" 

lemma init_tab_form:
  assumes "s' = init_tab s inst e_ind e" 
  shows "list_all2 tab_extension (tabs s) (tabs s')" 
        "\<exists>tabs'. s' = s\<lparr>tabs := tabs'\<rparr>"
        "element_funcs_in_bounds s inst e
        \<Longrightarrow> element_in_bounds s inst e_ind e
        \<Longrightarrow> list_all2 (\<lambda>t t'. tab_agree s t \<longrightarrow> tab_agree s' t') (tabs s) (tabs s')"
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
      using init_tab_is
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
    then have 4:"tab_agree s (tab_e,max) \<longrightarrow> tab_agree s' (tab'_e, max)" by auto  
    have 5:"\<And>t. tab_agree s t \<longrightarrow> tab_agree s' t" unfolding tab_agree_def 
      using \<open>funcs s = funcs s'\<close> by auto  
    have "list_all2 (\<lambda>t t'. tab_agree s t \<longrightarrow> tab_agree s' t') (tabs s) (tabs s')"
      using 3[OF 4 5] by -  
  }
  then show "element_funcs_in_bounds s inst e \<Longrightarrow> element_in_bounds s inst e_ind e
        \<Longrightarrow> list_all2 (\<lambda>t t'. tab_agree s t \<longrightarrow> tab_agree s' t') (tabs s) (tabs s')" 
   using init_tab_is by (simp add: list_all_length)
qed

lemma tab_extension_trans:"tab_extension a b \<Longrightarrow> tab_extension b c \<Longrightarrow> tab_extension a c" 
  unfolding tab_extension_def by auto


lemma init_tabs_trans_pred: 
  assumes "s' = init_tabs s inst e_inds es" 
          "\<And>a b c. P a b \<Longrightarrow> P b c \<Longrightarrow> P a c"
          "\<And>a. P a a"
          "\<And>s1 s2 e. e \<in> set (zip e_inds es) \<Longrightarrow> s2 = init_tab s1 inst (fst e) (snd e) \<Longrightarrow> P s1 s2"
  shows "P s s'" 
proof -
  {
    fix a
    have "set a \<subseteq> set (zip e_inds es) \<Longrightarrow> s' = foldl (\<lambda>s' (e_ind,e). init_tab s' inst e_ind e) s a \<Longrightarrow> P s s'"
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

      have 2:"a1 \<in> set (zip e_inds es)" using Cons(2) by auto
      have 3:"set a2 \<subseteq> set (zip e_inds es)" using Cons(2) by auto 
      show ?case using assms(2)[OF assms(4)[OF 2 s_mid_def] Cons(1)[OF 3 1]] by auto
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
proof -
  define only_modify_tabs ::  "s \<Rightarrow> s \<Rightarrow> bool"
    where "only_modify_tabs = (\<lambda>s1 s2. \<exists>tabs'. s2 = s1\<lparr>tabs := tabs'\<rparr>)" 
  have 1:"\<And>a b c. only_modify_tabs a b \<Longrightarrow> only_modify_tabs b c \<Longrightarrow> only_modify_tabs a c"
    unfolding only_modify_tabs_def by force 
  have 2:"\<And>a. only_modify_tabs a a" unfolding only_modify_tabs_def
    by (metis s.cases s.update_convs(2)) 
  show ?thesis using init_tabs_trans_pred[OF assms, where P=only_modify_tabs] 1 2 init_tab_form(2)
    unfolding only_modify_tabs_def by metis
qed 


lemma init_tabs_tab_agree:
  assumes "s' = init_tabs s inst e_inds es" 
"list_all (element_funcs_in_bounds s inst) es"
"list_all2 (element_in_bounds s inst) e_inds es"
  shows "list_all2 (\<lambda>t t'. tab_agree s t \<longrightarrow> tab_agree s' t') (tabs s) (tabs s')"
proof - 
  define tab_agree_all2 ::  "s \<Rightarrow> s \<Rightarrow> bool"
    where "tab_agree_all2 = (\<lambda>s1 s2. list_all2 (\<lambda>t t'. tab_agree s1 t \<longrightarrow> tab_agree s2 t') (tabs s1) (tabs s2))" 
  have tab_agree_all2_trans:"\<And>a b c. tab_agree_all2 a b \<Longrightarrow> tab_agree_all2 b c \<Longrightarrow> tab_agree_all2 a c"
    unfolding tab_agree_all2_def using list_all2_trans
    by (smt (verit, best)) 
  have tab_agree_all2_refl:"\<And>a. tab_agree_all2 a a" unfolding tab_agree_all2_def 
    using list_all2_refl by (smt (verit, best)) 

  {
    fix a 
    have "list_all (element_funcs_in_bounds s inst) (map snd a)
      \<Longrightarrow> list_all2 (element_in_bounds s inst) (map fst a) (map snd a)
      \<Longrightarrow> s' = foldl (\<lambda>s' (e_ind,e). init_tab s' inst e_ind e) s a \<Longrightarrow> tab_agree_all2 s s'"
    proof(induct a arbitrary: s)
      case Nil
      then show ?case using tab_agree_all2_refl by auto 
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
        then have 1:"element_in_bounds s inst (fst x) (snd x)" 
          using Cons(3) case_prod_unfold zip_map_fst_snd unfolding list_all2_iff
          by (metis (no_types, lifting) set_subset_Cons subset_code(1))

        have "list_all2 tab_extension (tabs s) (tabs s_mid)" using init_tab_form(1)[OF s_mid_def] by -
        then have 2:"tab_size (s.tabs s ! (inst.tabs inst ! e_tab (snd x))) 
        \<le> tab_size (s.tabs s_mid ! (inst.tabs inst ! e_tab (snd x)))" 
          sorry
         
        have "element_in_bounds s_mid inst (fst x) (snd x)" using 1 2 by auto 
      }
      then have 3:"list_all2 (element_in_bounds s_mid inst) (map fst a2) (map snd a2)"
        unfolding list_all2_iff by auto

      have "element_funcs_in_bounds s inst (snd a1)" using Cons(2) by auto 
      moreover have "element_in_bounds s inst (fst a1) (snd a1)" using Cons(3) by auto 
      ultimately have 4:"tab_agree_all2 s s_mid" 
        using init_tab_form(3)[OF s_mid_def] unfolding tab_agree_all2_def by auto
      
      show ?case using Cons(1)[OF 2 3 1] using 4 tab_agree_all2_trans
        by metis 
    qed
  }
  then have "tab_agree_all2 s s'" using assms unfolding init_tabs_def
    by (metis (no_types, lifting) list_all2_lengthD map_fst_zip map_snd_zip) 
  then show ?thesis unfolding tab_agree_all2_def by -
qed

  

lemma init_tabs_preserve_funcs:
  assumes "s' = init_tabs s inst e_inds es" 
  shows "funcs s' = funcs s"
  using init_tabs_only_modify_tabs[OF assms]
  by auto


lemma init_tabs_preserve_store_extension: 
  assumes "s' = init_tabs s inst e_inds es" 
  shows "store_extension s s'"
  using init_tabs_tab_extension[OF assms] init_tabs_only_modify_tabs[OF assms] 
      store_extension_intros_with_refl
  by (metis append_Nil2 s.ext_inject s.surjective s.update_convs(2))   

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

lemma init_mems_preserve_funcs:
  assumes "s' = init_mems s inst d_inds ds" 
  shows "funcs s' = funcs s"
  using init_mems_form(2)[OF assms]
  by auto

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

lemma alloc_module_funcs_only_alloc_func:
  assumes "alloc_module s m imps gvs (s',inst,exps)"
    "alloc_funcs s (m_funcs m) inst = (s1,i_fs)"
  shows "funcs s' = funcs s1" 
  using assms alloc_tabs_range alloc_mems_range alloc_globs_range 
  unfolding alloc_module.simps 
  by force 

lemma list_all2_in_set:
  assumes "x\<in>set xs" "list_all2 f xs ys" 
  shows "\<exists>y. f x y" 
  using assms 
  by (smt (verit, best) list_all2_conv_all_nth mem_Collect_eq set_conv_nth)



definition alloc_func_fs :: "module_func \<Rightarrow> inst \<Rightarrow> cl" where
  "alloc_func_fs m_f inst =
     (case m_f of (i_t, loc_ts, b_es) \<Rightarrow>
        Func_native inst ((types inst)!i_t) loc_ts b_es)"

lemma alloc_func_equiv:"fst (alloc_func s m_f i) = s\<lparr>funcs := funcs s @ [alloc_func_fs m_f i]\<rparr>"
  using alloc_func_def alloc_func_fs_def by(simp split:prod.splits)

abbreviation "alloc_funcs_fs m_fs i \<equiv> map (\<lambda>m_f. alloc_func_fs m_f i) m_fs"

lemma alloc_funcs_equiv:"fst (alloc_funcs s m_fs i) = s\<lparr>funcs := funcs s @ alloc_funcs_fs m_fs i\<rparr>"
proof(induct m_fs arbitrary: s)
  case Nil
  then show ?case by auto 
next
  case (Cons a m_fs)
  have "fst (alloc_funcs s (a # m_fs) i) = fst (alloc_funcs (fst (alloc_func s a i)) m_fs i)"
    using alloc_Xs.simps(2) by(simp split:prod.splits)

  also have "... = fst (alloc_funcs (s\<lparr>funcs := funcs s @ [alloc_func_fs a i]\<rparr>) m_fs i)" 
    using alloc_func_equiv by simp

  also have "... = s\<lparr>funcs := funcs s @ alloc_funcs_fs (a#m_fs) i\<rparr> " 
    using Cons by auto
  finally show ?case by auto
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
    and "list_all2 (external_typing s) v_imps t_imps"
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

  obtain \<C> fts ds i_opt  ifts igs gts its ts ims ms
    where c_is:"list_all2 (module_func_typing \<C>) (m_funcs m) fts"
    "list_all (module_elem_typing \<C>) (m_elem m)"
    "list_all (module_data_typing \<C>) ds"
    "pred_option (module_start_typing \<C>) i_opt"
    "\<C> = \<lparr>types_t=(m_types m), func_t=ifts@fts, global=igs@gts, table=its@ts, memory=ims@ms, 
          local=[], label=[], return=None\<rparr>"
    using \<open>module_typing m t_imps t_exps\<close> module_typing.simps
    by auto 

  have "funcs s1 = funcs s2" using init_tabs_preserve_funcs s_init_tabs by auto
  also have "... = funcs s'" using init_mems_preserve_funcs s_init_mems by auto
  finally have "funcs s1 = funcs s'" by -

  have "list_all2 (funci_agree (funcs s')) (inst.funcs inst) (func_t \<C>)" sorry
  moreover have "list_all2 (globi_agree (globs s')) (inst.globs inst) (global \<C>)" sorry 
  moreover have "list_all2 (tabi_agree (tabs s')) (inst.tabs inst) (table \<C>)" sorry
  moreover have "list_all2 (memi_agree (mems s')) (inst.mems inst) (memory \<C>)" sorry
  moreover have "types inst = types_t \<C>" 
  proof -
    have "types inst = m_types m" using s_alloc_module unfolding alloc_module.simps 
      by(auto)
    also have "... = types_t \<C>" using c_is by auto
    finally show ?thesis by -
  qed
  moreover have "local \<C> = [] \<and> label \<C> = [] \<and> return \<C> = None" using c_is by auto
  ultimately have "inst_typing s' inst \<C>" using inst_typing.simps
    by (metis (full_types) inst.surjective old.unit.exhaust t_context.surjective) 

  show "store_typing s'"
  proof -
    have 1:"list_all (\<lambda>cl. \<exists>tf. cl_typing s' cl tf) (funcs s')" 
    proof -
        

        obtain fs where "funcs s @ fs = funcs s1" using alloc_module_ext_arb[OF s_alloc_module]
          by metis
        then have "funcs s @ fs = funcs s'" using \<open>funcs s1 = funcs s'\<close> by auto

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

            define s_mid where s_mid_def:"s_mid = fst (alloc_funcs s (m_funcs m) inst)"
            then have "funcs s1 = funcs s_mid" 
              using alloc_module_funcs_only_alloc_func[OF s_alloc_module]
              by (metis eq_fst_iff) 
            then have "funcs s_mid = funcs s @ fs" using \<open>funcs s @ fs = funcs s1\<close> by auto
            then have 0:"alloc_funcs_fs (m_funcs m) inst = fs" 
              using alloc_funcs_equiv s_mid_def by auto
            
            obtain i_t loc_ts b_es where 1:
              "f = Func_native inst ((types inst)!i_t) loc_ts b_es"  
              "(i_t, loc_ts, b_es) \<in> set (m_funcs m)"
              using 0 \<open>f\<in> set fs\<close> unfolding alloc_func_fs_def by auto

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
        ultimately show ?thesis using \<open>funcs s @ fs = funcs s'\<close>
          by (metis list_all_append) 
      qed 
    have 2:"list_all (tab_agree s') (tabs s')"
    proof -
      have "tabs s2 = tabs s'" using init_mems_form(2)[OF s_init_mems] by auto 

      have "list_all2 (funci_agree (funcs s')) (inst.funcs inst) (func_t \<C>)" 
        using \<open>inst_typing s' inst \<C>\<close> unfolding inst_typing.simps by auto
      then have 1:"list_all (\<lambda>i. i< length (funcs s1)) (inst.funcs inst)" 
        using \<open>funcs s1 = funcs s'\<close> unfolding funci_agree_def
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
        using s_element_in_bounds
        by (smt (verit, best) list_all2_map1 list_all2_mono) 

      have "list_all (tab_agree s1) (tabs s1)" sorry 
      moreover have "list_all2 (\<lambda>t t'. tab_agree s1 t \<longrightarrow> tab_agree s2 t') (tabs s1) (tabs s2)"
        using init_tabs_tab_agree[OF s_init_tabs 1 2] by -
      ultimately have "list_all (tab_agree s2) (tabs s2)" 
        by (metis (mono_tags, lifting) list_all2_conv_all_nth list_all_length)
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