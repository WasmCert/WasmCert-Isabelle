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

lemma init_tab_form:
  assumes "s' = init_tab s inst e_ind e" 
  shows "list_all2 tab_extension (tabs s) (tabs s')" 
        "\<exists>tabs'. s' = s\<lparr>tabs := tabs'\<rparr>"
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

  have "length tab_e \<le> length tab'_e" using init_tab_is
    by simp 
  then have "tab_extension ((tabs s)!t_ind) (tab'_e, max)" 
    unfolding tab_extension_def using init_tab_is
    by (metis fst_conv snd_conv) 
  then show "list_all2 tab_extension (tabs s) (tabs s')"  
    using init_tab_is  tab_extension_refl unfolding 1 list_all2_conv_all_nth  
    by (simp, metis nth_list_update_eq nth_list_update_neq)

  show "\<exists>tabs'. s' = s\<lparr>tabs := tabs'\<rparr>" unfolding assms init_tab_def
    by(simp add: Let_def exI split:prod.splits)
qed

lemma tab_extension_trans:"tab_extension a b \<Longrightarrow> tab_extension b c \<Longrightarrow> tab_extension a c" 
  unfolding tab_extension_def by auto


lemma init_tabs_form:
  assumes "s' = init_tabs s inst e_inds es" 
  shows "list_all2 tab_extension (tabs s) (tabs s')" 
        "\<exists>tabs'. s' = s\<lparr>tabs := tabs'\<rparr>"
proof -
  {
    fix a
    have "s' = foldl (\<lambda>s' (e_ind,e). init_tab s' inst e_ind e) s a \<Longrightarrow> 
          list_all2 tab_extension (tabs s) (tabs s') \<and> (\<exists>tabs'. s' = s\<lparr>tabs := tabs'\<rparr>)"
    proof (induction a arbitrary:s)
      case Nil
      show ?case using Nil exI[where x="tabs s"] unfolding foldl_Nil 
        by(simp add: list_all2_refl tab_extension_refl)  
    next
      case (Cons a1 a2)
      define s_mid where "s_mid = init_tab s inst (fst a1) (snd a1)" 
      then have 1:"s' = foldl (\<lambda>s' (e_ind,e). init_tab s' inst e_ind e) s_mid a2" 
        using Cons foldl_Cons
        by(simp add: case_prod_beta')

      note ind_assms = init_tab_form[OF s_mid_def] Cons(1)[OF 1]

      have "list_all2 tab_extension (tabs s) (tabs s')" using ind_assms
        list_all2_trans tab_extension_trans
        by blast
      moreover have "\<exists>tabs'. s' = s\<lparr>tabs := tabs'\<rparr>" using ind_assms
        by auto
      ultimately show ?case by auto
    qed 
  }
  note helper = this
  show "list_all2 tab_extension (tabs s) (tabs s')" using helper assms unfolding init_tabs_def
    by presburger 
  show "\<exists>tabs'. s' = s\<lparr>tabs := tabs'\<rparr>" using helper assms unfolding init_tabs_def
    by presburger
qed

lemma init_tabs_preserve_funcs:
  assumes "s' = init_tabs s inst e_inds es" 
  shows "funcs s' = funcs s"
  using init_tabs_form(2)[OF assms]
  by auto


lemma init_tabs_preserve_store_extension: 
  assumes "s' = init_tabs s inst e_inds es" 
  shows "store_extension s s'"
  using init_tabs_form[OF assms] store_extension_intros_with_refl
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
    "list_all2 (external_typing s) v_imps t_imps"
    and s_alloc_module:"alloc_module s m v_imps g_inits (s1, inst, v_exps)"
    and "f = \<lparr> f_locs = [], f_inst = inst \<rparr>"
    "list_all2 (\<lambda>g v. reduce_trans (s1,f,$*(g_init g)) (s1,f,[$C v])) (m_globs m) g_inits"
    "list_all2 (\<lambda>e c. reduce_trans (s1,f,$*(e_off e)) (s1,f,[$C ConstInt32 c])) (m_elem m) e_offs"
    "list_all2 (\<lambda>d c. reduce_trans (s1,f,$*(d_off d)) (s1,f,[$C ConstInt32 c])) (m_data m) d_offs"
    "list_all2 (\<lambda>e_off e. ((nat_of_int e_off) + (length (e_init e))) \<le> length (fst ((tabs s1)!((inst.tabs inst)!(e_tab e))))) e_offs (m_elem m)"
    "list_all2 (\<lambda>d_off d. ((nat_of_int d_off) + (length (d_init d))) \<le> mem_length ((mems s1)!((inst.mems inst)!(d_data d)))) d_offs (m_data m)"
    "map_option (\<lambda>i_s. ((inst.funcs inst)!i_s)) (m_start m) = start"
    and s_init_tabs:"init_tabs s1 inst (map nat_of_int e_offs) (m_elem m) = s2"
    and s_init_mems:"init_mems s2 inst (map nat_of_int d_offs) (m_data m) = s'" 
    using assms(2) instantiate.simps by auto

  have "store_extension s s1" using alloc_module_preserve_store_extension s_alloc_module by auto
  have "store_extension s1 s2" using init_tabs_preserve_store_extension s_init_tabs by auto 
  have "store_extension s2 s'" using init_mems_preserve_store_extension s_init_mems by auto 

  obtain \<C> fts els ds i_opt where c_is:"list_all2 (module_func_typing \<C>) (m_funcs m) fts"
    "list_all (module_elem_typing \<C>) els"
    "list_all (module_data_typing \<C>) ds"
    "pred_option (module_start_typing \<C>) i_opt"
    using \<open>module_typing m t_imps t_exps\<close> module_typing.simps
    by auto 

  have "inst_typing s1 inst \<C>" sorry

  show "store_typing s'"
  proof -
    have 1:"list_all (\<lambda>cl. \<exists>tf. cl_typing s' cl tf) (funcs s')" 
    proof -
      have s1_cl_typing:"list_all (\<lambda>cl. \<exists>tf. cl_typing s1 cl tf) (funcs s1)" 
      proof - 
        obtain fs where "funcs s1 = funcs s @ fs" using alloc_module_ext_arb[OF s_alloc_module]
          by metis

        have "list_all (\<lambda>cl. \<exists>tf. cl_typing s1 cl tf) (funcs s)" 
          using cl_typing_store_extension_inv[OF \<open>store_extension s s1\<close>] store_typing.simps assms(1)
          by (smt (verit, ccfv_threshold) list_all_length) 
        moreover have "list_all (\<lambda>cl. \<exists>tf. cl_typing s1 cl tf) fs" 
        proof -
          {
            fix f
            assume "f\<in>set fs" 

            define s_mid where s_mid_def:"s_mid = fst (alloc_funcs s (m_funcs m) inst)"
            then have "funcs s1 = funcs s_mid" 
              using alloc_module_funcs_only_alloc_func[OF s_alloc_module]
              by (metis eq_fst_iff) 
            then have "funcs s_mid = funcs s @ fs" using \<open>funcs s1 = funcs s @ fs\<close> by auto
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
              using store_typing_imp_types_eq[OF \<open>inst_typing s1 inst \<C>\<close> 2(1)] by auto

            have "cl_typing s1 f (tn _> tm)" 
              using 1(1) 2 3 
              cl_typing.intros(1)[OF \<open>inst_typing s1 inst \<C>\<close>]
              by presburger 
            then have "\<exists>tf. cl_typing s1 f tf" by auto
          }
          then show ?thesis by (simp add: list_all_iff) 
        qed
        ultimately show ?thesis using \<open>funcs s1 = funcs s @ fs\<close> by auto
      qed 
      have s2_cl_typing:"list_all (\<lambda>cl. \<exists>tf. cl_typing s2 cl tf) (funcs s2)"
      proof -
        have "funcs s1 = funcs s2" using init_tabs_preserve_funcs s_init_tabs by auto
        then show ?thesis using cl_typing_store_extension_inv[OF \<open>store_extension s1 s2\<close>] s1_cl_typing 
          by (smt (verit, best) list_all_length)
      qed  
      show  "list_all (\<lambda>cl. \<exists>tf. cl_typing s' cl tf) (funcs s')" 
      proof -
        have "funcs s2 = funcs s'" using init_mems_preserve_funcs s_init_mems by auto
        then show ?thesis using cl_typing_store_extension_inv[OF \<open>store_extension s2 s'\<close>] s2_cl_typing 
          by (smt (verit, best) list_all_length)
      qed 
    qed
    have 2:"list_all (tab_agree s') (tabs s')"
      sorry
    have 3:"list_all mem_agree (mems s')"
      sorry
    show ?thesis
      using 1 2 3 store_typing.intros
      by blast
  qed

  show "\<exists>\<C>. inst_typing s' inst \<C>"
  proof -
    have "inst_typing s2 inst \<C>" 
      using inst_typing_store_extension_inv[OF \<open>inst_typing s1 inst \<C>\<close>  \<open>store_extension s1 s2\<close>]
      by simp 
    then have "inst_typing s' inst \<C>" 
      using inst_typing_store_extension_inv  \<open>store_extension s2 s'\<close>
      by simp
    then show ?thesis by auto
  qed

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