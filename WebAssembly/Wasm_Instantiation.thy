theory Wasm_Instantiation imports Wasm_Module_Checker Wasm_Interpreter_Properties begin

fun alloc_Xs :: "(s \<Rightarrow> 'a \<Rightarrow> (s \<times> i)) \<Rightarrow> s \<Rightarrow> 'a list \<Rightarrow> (s \<times> i list)" where
  "alloc_Xs f s [] = (s,[])"
| "alloc_Xs f s (m_X#m_Xs) = (let (s'', i_X) = f s m_X in
                              let (s',i_Xs) = alloc_Xs f s'' m_Xs in
                              (s',i_X#i_Xs))"

definition alloc_func :: "s \<Rightarrow> module_func \<Rightarrow> inst \<Rightarrow> (s \<times> i)" where
  "alloc_func s m_f inst =
     (case m_f of (i_t, loc_ts, b_es) \<Rightarrow>
        (s\<lparr>s.funcs := (funcs s)@[Func_native inst ((types inst)!i_t) loc_ts b_es]\<rparr>,length (funcs s)))"

abbreviation "alloc_funcs s m_fs i \<equiv> alloc_Xs (\<lambda>s m_f. alloc_func s m_f i) s m_fs"

definition alloc_tab :: "s \<Rightarrow> tab_t \<Rightarrow> (s \<times> i)" where
  "alloc_tab s m_t = (s\<lparr>s.tabs := (tabs s)@[(replicate (l_min m_t) None, (l_max m_t))]\<rparr>,length (tabs s))"

abbreviation "alloc_tabs \<equiv> alloc_Xs alloc_tab"

definition alloc_mem :: "s \<Rightarrow> mem_t \<Rightarrow> (s \<times> i)" where
  "alloc_mem s m_m = (s\<lparr>s.mems := (mems s)@[mem_mk m_m]\<rparr>,length (mems s))"

abbreviation "alloc_mems \<equiv> alloc_Xs alloc_mem"

definition alloc_glob :: "s \<Rightarrow> (module_glob \<times> v) \<Rightarrow> (s \<times> i)" where
  "alloc_glob s m_g_v = 
    (case m_g_v of (m_g, v) \<Rightarrow>
      (s\<lparr>s.globs := (globs s)@[\<lparr>g_mut=(tg_mut (module_glob.g_type m_g)), g_val=v\<rparr>]\<rparr>,length (globs s)))"

abbreviation "alloc_globs s m_gs vs \<equiv> alloc_Xs alloc_glob s (zip m_gs vs)"

lemma alloc_func_length:
  assumes "alloc_func s m_f i = (s', i_f)"
  shows "length (funcs s) = i_f"
        "length (funcs s') = Suc i_f"
        "\<exists>farb. (funcs s)@[farb] = (funcs s')"
        "(tabs s) = (tabs s')"
        "(mems s) = (mems s')"
        "(globs s) = (globs s')"
  using assms[symmetric]
  unfolding alloc_func_def
  by (simp_all split: prod.splits)

lemma alloc_tab_length:
  assumes "alloc_tab s m_t = (s', i_t)"
  shows "length (tabs s) = i_t"
        "length (tabs s') = Suc i_t"
        "(funcs s) = (funcs s')"
        "\<exists>tarb. (tabs s)@[tarb] = (tabs s')"
        "(mems s) = (mems s')"
        "(globs s) = (globs s')"
  using assms[symmetric]
  unfolding alloc_tab_def
  by (simp_all split: prod.splits)

lemma alloc_mem_length:
  assumes "alloc_mem s m_m = (s', i_m)"
  shows "length (mems s) = i_m"
        "length (mems s') = Suc i_m"
        "(funcs s) = (funcs s')"
        "(tabs s) = (tabs s')"
        "\<exists>marb. (mems s)@[marb] = (mems s')"
        "(globs s) = (globs s')"
  using assms[symmetric]
  unfolding alloc_mem_def
  by (simp_all split: prod.splits)

lemma alloc_glob_length:
  assumes "alloc_glob s (m_g, v) = (s', i_g)"
  shows "length (globs s) = i_g"
        "length (globs s') = Suc i_g"
        "(funcs s) = (funcs s')"
        "(tabs s) = (tabs s')"
        "(mems s) = (mems s')"
        "(globs s)@[\<lparr>g_mut=(tg_mut (module_glob.g_type m_g)), g_val=v\<rparr>] = (globs s')"
  using assms[symmetric]
  unfolding alloc_glob_def
  by (simp_all split: prod.splits)

lemma alloc_funcs_range:
  assumes "alloc_funcs s m_fs i = (s', i_fs)"
  shows "i_fs = [length (funcs s) ..< (length (funcs s) + length m_fs)] \<and>
         (\<exists>farb. (funcs s)@farb = (funcs s')) \<and>
         (tabs s) = (tabs s') \<and>
         (mems s) = (mems s') \<and>
         (globs s) = (globs s')"
  using assms
proof (induction m_fs arbitrary: s i_fs)
  case Nil
  thus ?case
    by simp
next
  case (Cons m_f m_fs)
  obtain s'' i_f' i_fs' where s''_is:"alloc_func s m_f i = (s'', i_f')"
                                     "alloc_funcs s'' m_fs i = (s', i_fs')"
                                     "i_f' # i_fs' = i_fs"
    using Cons(2)
    by (simp split: prod.splits)
  thus ?case
    using Cons(1)[OF s''_is(2)] using alloc_func_length[OF s''_is(1)] upt_rec
    apply (simp split: prod.splits)
    apply (metis append_assoc)
    done
qed

lemma alloc_tabs_range:
  assumes "alloc_tabs s m_ts = (s', i_ts)"
  shows "i_ts = [length (tabs s) ..< (length (tabs s) + length m_ts)] \<and>
         (funcs s) = (funcs s') \<and>
         (\<exists>tarb. (tabs s)@tarb = (tabs s')) \<and>
         (mems s) = (mems s') \<and>
         (globs s) = (globs s')"
  using assms
proof (induction m_ts arbitrary: s i_ts)
  case Nil
  thus ?case
    by simp
next
  case (Cons m_t m_ts)
  obtain s'' i_t' i_ts' where s''_is:"alloc_tab s m_t = (s'', i_t')"
                                     "alloc_tabs s'' m_ts = (s', i_ts')"
                                     "i_t' # i_ts' = i_ts"
    using Cons(2)
    by (simp split: prod.splits)
  thus ?case
    using Cons(1)[OF s''_is(2)] using alloc_tab_length[OF s''_is(1)] upt_rec
    apply (simp split: prod.splits)
    apply (metis append_assoc)
    done
qed

lemma alloc_mems_range:
  assumes "alloc_mems s m_ms = (s', i_ms)"
  shows "i_ms = [length (mems s) ..< (length (mems s) + length m_ms)] \<and>
         (funcs s) = (funcs s') \<and>
         (tabs s) = (tabs s') \<and>
         (\<exists>marb. (mems s)@marb = (mems s')) \<and>
         (globs s) = (globs s')"
  using assms
proof (induction m_ms arbitrary: s i_ms)
  case Nil
  thus ?case
    by simp
next
  case (Cons m_m m_ms)
  obtain s'' i_m' i_ms' where s''_is:"alloc_mem s m_m = (s'', i_m')"
                                     "alloc_mems s'' m_ms = (s', i_ms')"
                                     "i_m' # i_ms' = i_ms"
    using Cons(2)
    by (simp split: prod.splits)
  thus ?case
    using Cons(1)[OF s''_is(2)] using alloc_mem_length[OF s''_is(1)] upt_rec
    apply (simp split: prod.splits)
    apply (metis append_assoc)
    done
qed

lemma alloc_globs_range:
  assumes "alloc_globs s m_gs vs = (s', i_gs)"
  shows "i_gs = [length (globs s) ..< (length (globs s) + min (length m_gs) (length vs))] \<and>
         (funcs s) = (funcs s') \<and>
         (tabs s) = (tabs s') \<and>
         (mems s) = (mems s') \<and>
         ((globs s)@(map2 (\<lambda>m_g v. \<lparr>g_mut=(tg_mut (module_glob.g_type m_g)), g_val=v\<rparr>) m_gs vs) = (globs s'))"
  using assms
proof (induction m_gs arbitrary: s i_gs vs)
  case Nil
  thus ?case
    by simp
next
  case (Cons m_g m_gs)
  note outer_Cons = Cons
  show ?case
  proof (cases vs)
    case Nil
    thus ?thesis
      using Cons
      by simp
  next
    case (Cons v vs')
    then obtain s'' i_g' i_gs' where s''_is:"alloc_glob s (m_g, v) = (s'', i_g')"
                                       "alloc_globs s'' m_gs vs' = (s', i_gs')"
                                       "i_g' # i_gs' = i_gs"
      using outer_Cons(2)
      by (simp split: prod.splits)
    thus ?thesis
      using outer_Cons(1)[OF s''_is(2)] using alloc_glob_length[OF s''_is(1)] upt_rec Cons
      apply (simp)
      apply (metis (no_types, lifting) append_Cons append_assoc self_append_conv2)
      done
  qed
qed

lemma length_alloc_Xs:
  assumes "alloc_Xs f s m_Xs = (s', i_Xs)"
  shows "length i_Xs = length m_Xs"
  using assms
proof (induction m_Xs arbitrary: s i_Xs)
  case Nil
  thus ?case
    by simp
next
  case (Cons m_X m_Xs)
  thus ?case
    by (fastforce split: prod.splits)
qed

lemma alloc_Xs_app:
  assumes  "alloc_Xs f s (m_Xs@m_Ys) = (s', i_XYs)"
  shows "\<exists>s'' i_Xs i_Ys. i_XYs = i_Xs@i_Ys \<and>
              alloc_Xs f s m_Xs = (s'', i_Xs) \<and>
              alloc_Xs f s'' m_Ys = (s', i_Ys)"
  using assms
proof (induction f s "(m_Xs@m_Ys)" arbitrary: m_Xs i_XYs rule: alloc_Xs.induct)
  case (1 f s)
  thus ?case
    by simp
next
  case (2 f s m_X' m_XYs')
  consider (a) "m_Xs = []" "m_X' # m_XYs' = m_Ys"
         | (b) m_Xs' where "m_X' # m_Xs' = m_Xs" "m_XYs' = m_Xs' @ m_Ys"
    using Cons_eq_append_conv[of m_X' m_XYs' m_Xs m_Ys]
          2(2)
    by blast
  thus ?case
  proof cases
    case a
    thus ?thesis
      using 2
      by fastforce
  next
    case b
    obtain s'' i_XY i_XYs' where s''_is:
      "m_Xs = m_X' # m_Xs'"
      "f s m_X' = (s'', i_XY)"
      "alloc_Xs f s'' (m_Xs' @ m_Ys) = (s', i_XYs')"
      "i_XY # i_XYs' = i_XYs"
      using 2(3) b(1)[symmetric]
      by (simp split: prod.splits)
    thus ?thesis
      using 2(1)[OF _ _ b(2) s''_is(3), of _ i_XY]
      by (fastforce split: prod.splits)
  qed
qed

lemma alloc_Xs_snoc:
  assumes  "alloc_Xs f s (m_Xs@[m_X]) = (s', i_XYs)"
  shows "\<exists>s'' i_Xs i_X. i_XYs = i_Xs@[i_X] \<and>
              alloc_Xs f s m_Xs = (s'', i_Xs) \<and>
              f s'' m_X = (s', i_X)"
  using alloc_Xs_app[OF assms]
  apply (simp split: prod.splits)
  apply (metis prod.exhaust_sel)
  done

inductive alloc_module :: "s \<Rightarrow> m \<Rightarrow> v_ext list \<Rightarrow> v list \<Rightarrow> (s \<times> inst \<times> module_export list) \<Rightarrow> bool" where
  "\<lbrakk>inst = \<lparr>types=(m_types m),
           funcs=(ext_funcs imps)@i_fs,
           tabs=(ext_tabs imps)@i_ts,
           mems=(ext_mems imps)@i_ms,
           globs=(ext_globs imps)@i_gs\<rparr>;
    alloc_funcs s (m_funcs m) inst = (s1,i_fs);
    alloc_tabs s1 (m_tabs m) = (s2,i_ts);
    alloc_mems s2 (m_mems m) = (s3,i_ms);
    alloc_globs s3 (m_globs m) gvs = (s',i_gs);
    exps = map (\<lambda>m_exp. \<lparr>E_name=(E_name m_exp), E_desc=(export_get_v_ext inst (E_desc m_exp))\<rparr>) (m_exports m)
     \<rbrakk> \<Longrightarrow> alloc_module s m imps gvs (s',inst,exps)"

definition interp_alloc_module :: "s \<Rightarrow> m \<Rightarrow> v_ext list \<Rightarrow> v list \<Rightarrow> (s \<times> inst \<times> module_export list)" where
  "interp_alloc_module s m imps gvs =
   (let i_fs = [length (funcs s) ..< (length (funcs s) + length (m_funcs m))] in
    let i_ts = [length (tabs s) ..< (length (tabs s) + length (m_tabs m))] in
    let i_ms = [length (mems s) ..< (length (mems s) + length (m_mems m))] in
    let i_gs = [length (globs s) ..< (length (globs s) + min (length (m_globs m)) (length gvs))] in
    let inst = \<lparr>types=(m_types m),
                funcs=(ext_funcs imps)@i_fs,
                tabs=(ext_tabs imps)@i_ts,
                mems=(ext_mems imps)@i_ms,
                globs=(ext_globs imps)@i_gs\<rparr> in
    let (s1,_) = alloc_funcs s (m_funcs m) inst in
    let (s2,_) = alloc_tabs s1 (m_tabs m) in
    let (s3,_) = alloc_mems s2 (m_mems m) in
    let (s',_) = alloc_globs s3 (m_globs m) gvs in
    let exps = map (\<lambda>m_exp. \<lparr>E_name=(E_name m_exp), E_desc=(export_get_v_ext inst (E_desc m_exp))\<rparr>) (m_exports m) in
    (s', inst, exps))"

lemma alloc_module_imp_interp_alloc_module:
  assumes "alloc_module s m imps gvs (s',inst,exps)"
  shows "(interp_alloc_module s m imps gvs = (s',inst,exps))"
proof -
  obtain s1 s2 s3 i_fs i_ts i_ms i_gs where s'_is:
    "inst = \<lparr>types=(m_types m),
             funcs=(ext_funcs imps)@i_fs,
             tabs=(ext_tabs imps)@i_ts,
             mems=(ext_mems imps)@i_ms,
             globs=(ext_globs imps)@i_gs\<rparr>"
    "alloc_funcs s (m_funcs m) inst = (s1,i_fs)"
    "alloc_tabs s1 (m_tabs m) = (s2,i_ts)"
    "alloc_mems s2 (m_mems m) = (s3,i_ms)"
    "alloc_globs s3 (m_globs m) gvs = (s',i_gs)"
    "exps = map (\<lambda>m_exp. \<lparr>E_name=(E_name m_exp), E_desc=(export_get_v_ext inst (E_desc m_exp))\<rparr>) (m_exports m)"
    using assms
    unfolding alloc_module.simps
    by blast
  have "i_fs = [length (funcs s) ..< (length (funcs s) + length (m_funcs m))]"
       "i_ts = [length (tabs s) ..< (length (tabs s) + length (m_tabs m))]"
       "i_ms = [length (mems s) ..< (length (mems s) + length (m_mems m))]"
       "i_gs = [length (globs s) ..< (length (globs s) + min (length (m_globs m)) (length gvs))]"
    using alloc_funcs_range[OF s'_is(2)] alloc_tabs_range[OF s'_is(3)]
          alloc_mems_range[OF s'_is(4)] alloc_globs_range[OF s'_is(5)]
    by auto
  thus ?thesis
    using s'_is
    unfolding interp_alloc_module_def
    by (simp add: Let_def split: prod.splits)
qed

lemma interp_alloc_module_imp_alloc_module:
  assumes "(interp_alloc_module s m imps gvs = (s',inst,exps))"
  shows "alloc_module s m imps gvs (s',inst,exps)"
proof -
  obtain i_fs i_ts i_ms i_gs i_fs' i_ts' i_ms' i_gs' s1 s2 s3 where s'_is:
    "i_fs = [length (funcs s) ..< (length (funcs s) + length (m_funcs m))]"
    "i_ts = [length (tabs s) ..< (length (tabs s) + length (m_tabs m))]"
    "i_ms = [length (mems s) ..< (length (mems s) + length (m_mems m))]"
    "i_gs = [length (globs s) ..< (length (globs s) + min (length (m_globs m)) (length gvs))]"
    "inst = \<lparr>types=(m_types m),
                funcs=(ext_funcs imps)@i_fs,
                tabs=(ext_tabs imps)@i_ts,
                mems=(ext_mems imps)@i_ms,
                globs=(ext_globs imps)@i_gs\<rparr>"
    "(s1,i_fs') = alloc_funcs s (m_funcs m) inst"
    "(s2,i_ts') = alloc_tabs s1 (m_tabs m)"
    "(s3,i_ms') = alloc_mems s2 (m_mems m)"
    "(s',i_gs') = alloc_globs s3 (m_globs m) gvs"
    "exps = map (\<lambda>m_exp. \<lparr>E_name=(E_name m_exp), E_desc=(export_get_v_ext inst (E_desc m_exp))\<rparr>) (m_exports m)"
    using assms
    unfolding interp_alloc_module_def
    by (auto simp add: Let_def split: prod.splits)
  have "i_fs = i_fs'"
       "i_ts = i_ts'"
       "i_ms = i_ms'"
       "i_gs = i_gs'"
    using s'_is(1,2,3,4)
          alloc_funcs_range[OF s'_is(6)[symmetric]]
          alloc_tabs_range[OF s'_is(7)[symmetric]]
          alloc_mems_range[OF s'_is(8)[symmetric]]
          alloc_globs_range[OF s'_is(9)[symmetric]]
    by metis+
  thus ?thesis
    using alloc_module.intros[OF s'_is(5) _ _ _ _ s'_is(10)]
    by (metis (no_types, lifting) s'_is(6,7,8,9))
qed

lemma alloc_module_equiv_interp_alloc_module:
  "alloc_module s m imps gvs (s',inst,exps) = (interp_alloc_module s m imps gvs = (s',inst,exps))"
  using alloc_module_imp_interp_alloc_module interp_alloc_module_imp_alloc_module
  by blast

definition init_tab :: "s \<Rightarrow> inst \<Rightarrow> nat \<Rightarrow> module_elem \<Rightarrow> s" where
  "init_tab s inst e_ind e = (let t_ind = ((inst.tabs inst)!(e_tab e)) in
                               let (tab_e,max) = (tabs s)!t_ind in
                               let e_pay = map (\<lambda>i. Some ((inst.funcs inst)!i)) (e_init e) in
                               let tab'_e = ((take e_ind tab_e) @ e_pay @ (drop (e_ind + length e_pay) tab_e)) in
                               s\<lparr>tabs := (tabs s)[e_ind := (tab'_e,max)]\<rparr>)"

definition init_tabs :: "s \<Rightarrow> inst \<Rightarrow> nat list \<Rightarrow> module_elem list \<Rightarrow> s" where
  "init_tabs s inst e_inds es = foldl (\<lambda>s' (e_ind,e). init_tab s' inst e_ind e) s (zip e_inds es)"

definition init_mem :: "s \<Rightarrow> inst \<Rightarrow> nat \<Rightarrow> module_data \<Rightarrow> s" where
  "init_mem s inst d_ind d = (let m_ind = ((inst.mems inst)!(d_data d)) in
                               let mem = (mems s)!m_ind in
                               let mem' = write_bytes mem d_ind (d_init d) in
                               s\<lparr>mems := (mems s)[m_ind := mem']\<rparr>)"

definition init_mems :: "s \<Rightarrow> inst \<Rightarrow> nat list \<Rightarrow> module_data list \<Rightarrow> s" where
  "init_mems s inst d_inds ds = foldl (\<lambda>s' (d_ind,d). init_mem s' inst d_ind d) s (zip d_inds ds)"

inductive instantiate :: "s \<Rightarrow> m \<Rightarrow> v_ext list \<Rightarrow> ((s \<times> inst \<times> (module_export list)) \<times> (nat option)) \<Rightarrow> bool" where
  "\<lbrakk>module_typing m t_imps t_exps;
    list_all2 (external_typing s) v_imps t_imps;
    alloc_module s m v_imps g_inits (s', inst, v_exps);
    f = \<lparr> f_locs = [], f_inst = inst \<rparr>;
    list_all2 (\<lambda>g v. reduce_trans (s',f,$*(g_init g)) (s',f,[$C v])) (m_globs m) g_inits;
    list_all2 (\<lambda>e c. reduce_trans (s',f,$*(e_off e)) (s',f,[$C ConstInt32 c])) (m_elem m) e_offs;
    list_all2 (\<lambda>d c. reduce_trans (s',f,$*(d_off d)) (s',f,[$C ConstInt32 c])) (m_data m) d_offs;
    list_all2 (\<lambda>e_off e. ((nat_of_int e_off) + (length (e_init e))) \<le> length (fst ((tabs s)!((inst.tabs inst)!(e_tab e))))) e_offs (m_elem m);
    list_all2 (\<lambda>d_off d. ((nat_of_int d_off) + (length (d_init d))) \<le> mem_length ((mems s)!((inst.mems inst)!(d_data d)))) d_offs (m_data m);
    map_option (\<lambda>i_s. ((inst.funcs inst)!i_s)) (m_start m) = start;
    init_tabs s' inst (map nat_of_int e_offs) (m_elem m) = s'';
    init_mems s' inst (map nat_of_int d_offs) (m_data m) = s_end
    \<rbrakk> \<Longrightarrow> instantiate s m v_imps ((s_end, inst, v_exps), start)"

definition interp_get_v :: "s \<Rightarrow> inst \<Rightarrow> b_e list \<Rightarrow> v" where
  "interp_get_v s inst b_es = 
     (case run_v 2 0 (s,\<lparr> f_locs = [], f_inst = inst \<rparr>,$*b_es) of
        (_,RValue [v]) \<Rightarrow> v)"

definition interp_get_i32 :: "s \<Rightarrow> inst \<Rightarrow> b_e list \<Rightarrow> i32" where
  "interp_get_i32 s inst b_es = 
     (case interp_get_v s inst b_es of
        ConstInt32 c \<Rightarrow> c
      | _ \<Rightarrow> 0)"

fun interp_instantiate :: "s \<Rightarrow> m \<Rightarrow> v_ext list \<Rightarrow> ((s \<times> inst \<times> (module_export list)) \<times> (nat option)) option" where
  "interp_instantiate s m v_imps =
     (case (module_type_checker m) of
        Some (t_imps, t_exps) \<Rightarrow>
          if (list_all2 (external_typing s) v_imps t_imps) then
            let g_inits = 
              map (\<lambda>g. interp_get_v s \<lparr>types=[],funcs=[],tabs=[],mems=[],globs=ext_globs v_imps\<rparr> (g_init g)) (m_globs m) in
            let (s', inst, v_exps) = interp_alloc_module s m v_imps g_inits in
            let e_offs = map (\<lambda>e. interp_get_i32 s' inst (e_off e)) (m_elem m) in
            let d_offs = map (\<lambda>d. interp_get_i32 s' inst (d_off d)) (m_data m) in
            if (list_all2 (\<lambda>e_off e. ((nat_of_int e_off) + (length (e_init e))) \<le> length (fst ((tabs s)!((inst.tabs inst)!(e_tab e))))) e_offs (m_elem m) \<and>
                list_all2 (\<lambda>d_off d. ((nat_of_int d_off) + (length (d_init d))) \<le> mem_length ((mems s)!((inst.mems inst)!(d_data d)))) d_offs (m_data m)) then
              let start = map_option (\<lambda>i_s. ((inst.funcs inst)!i_s)) (m_start m) in
              let s'' = init_tabs s' inst (map nat_of_int e_offs) (m_elem m) in
              let s_end = init_mems s' inst (map nat_of_int d_offs) (m_data m) in
              Some ((s_end, inst, v_exps), start)
            else None
          else None
      | _ \<Rightarrow> None)"

lemma const_expr_is:
  assumes "const_expr \<C> b_e"
          "\<C> \<turnstile> [b_e] : (ts _> ts')"
        shows "\<exists>t. (\<C> \<turnstile> [b_e] : ([] _> [t])) \<and> ts' = ts@[t] \<and> 
         ((\<exists>v. b_e = (C v) \<and> typeof v = t) \<or>
         (\<exists>j. b_e = (Get_global j) \<and> j < length (global \<C>) \<and>
              tg_mut ((global \<C>)!j) = T_immut \<and>
              tg_t ((global \<C>)!j) = t))"
  using assms(2,1)
proof (induction "\<C>" "[b_e]" "(ts _> ts')" arbitrary: ts ts' rule: b_e_typing.induct)
  case (const \<C> v)
  thus ?case
    using b_e_typing.const
    by blast
next
  case (get_global i \<C> t)
  thus ?case
    using b_e_typing.get_global const_expr.cases
    by fastforce
next
  case (weakening \<C> t1s t2s ts)
  thus ?case
    by simp
qed (auto simp add: const_expr.simps)

lemma const_exprs_empty:
  assumes "const_exprs \<C> b_es"
          "\<C> \<turnstile> b_es : ([] _> [])"
  shows "b_es = []"
  using assms(2,1)
proof (induction "([] _> [])" rule: b_e_typing.induct)
  case (composition \<C> es t2s e)
  thus ?case
    by (metis (no_types, lifting) Nil_is_append_conv const_expr_is list.pred_inject(2) list_all_append)
next
  case (weakening \<C> es t1s t2s ts)
  thus ?case
    by blast
qed (auto simp add: const_expr.simps)

lemma const_exprs_is:
  assumes "const_exprs \<C> b_es"
          "\<C> \<turnstile> b_es : ([] _> [t])"
  shows "(\<exists>v. b_es = [C v] \<and> typeof v = t) \<or>
         (\<exists>j. b_es = [Get_global j] \<and> j < length (global \<C>) \<and>
              tg_mut ((global \<C>)!j) = T_immut \<and>
              tg_t ((global \<C>)!j) = t)"
  using assms(2,1)
proof (induction "\<C>" "b_es" "([] _> [t])" rule: b_e_typing.induct)
  case (composition \<C> es t2s e)
  have 1:"const_exprs \<C> es" "const_expr \<C> e"
    using composition(5)
    by simp_all
  have "t2s = []" "es = []"
    using const_expr_is[OF 1(2) composition(3)]  composition(1) const_exprs_empty 1(1)
    by auto
  thus ?case
    using composition
    by simp
qed (auto simp add: const_expr.simps)

lemma const_exprs_run_v:
  assumes "const_exprs \<C> b_es"
          "\<C> \<turnstile> b_es : ([] _> [t])"
          "global \<C> = tgs"
          "list_all2 (\<lambda>ig tg. external_typing s (Ext_glob ig) (Te_glob tg)) igs tgs"
          "inst.globs inst = igs@arb"
  shows "\<exists>v. typeof v = t \<and> run_v 2 0 (s, \<lparr> f_locs=[], f_inst=inst \<rparr>,$*b_es) = (s, RValue [v])"
proof -
  consider (1) v where "b_es = [C v] \<and> typeof v = t"
         | (2) j where "b_es = [Get_global j]"
                       "j < length (global \<C>)"
                       "tg_mut (global \<C> ! j) = T_immut"
                       "tg_t (global \<C> ! j) = t"
    using const_exprs_is[OF assms(1,2)]
    by blast
  thus ?thesis
  proof cases
    case 1
    thus ?thesis
      by (auto simp add: const_list_def is_const_def Suc_1[symmetric])
  next
    case 2
    thus ?thesis
      using assms
      unfolding list_all2_conv_all_nth external_typing.simps
      by (auto simp add: const_list_def is_const_def Suc_1[symmetric] glob_typing_def nth_append sglob_def sglob_ind_def sglob_val_def)
  qed
qed

lemma const_exprs_reduce_trans:
  assumes "const_exprs \<C> b_es"
          "\<C> \<turnstile> b_es : ([] _> [t])"
          "reduce_trans (s_r,f,$*b_es) (s',f',[$C v])"
          "global \<C> = tgs"
          "list_all2 (\<lambda>ig tg. external_typing s (Ext_glob ig) (Te_glob tg)) igs tgs"
          "globs s_r = (globs s)@arbg1"
          "globs s_v = (globs s)@arbg2"
          "inst.globs (f_inst f) = igs@arbi1"
          "inst.globs inst_v = igs@arbi2"
  shows "s_r = s' \<and> f = f' \<and> typeof v = t \<and> run_v 2 0 (s_v,\<lparr> f_locs=vs_arb, f_inst=inst_v\<rparr>,$*b_es) = (s_v, RValue [v])"
proof -
  consider (1) v_r where "b_es = [C v_r] \<and> typeof v_r = t"
         | (2) j where "b_es = [Get_global j]"
                       "j < length (global \<C>)"
                       "tg_mut (global \<C> ! j) = T_immut"
                       "tg_t (global \<C> ! j) = t"
    using const_exprs_is[OF assms(1,2)]
    by blast
  thus ?thesis
  proof (cases)
    case 1
    thus ?thesis
      using assms(3) reduce_trans_consts
      apply (simp add: const_list_def is_const_def Suc_1[symmetric])
      apply (metis (mono_tags, lifting) append_Nil2 case_prod_conv list.inject split_vals_e.simps(1,2) split_vals_e_conv_app)
      done
  next
    case 2
    have type_is:"typeof (sglob_val s (f_inst f) j) = t" "j < length igs" "(igs!j) < length (globs s)"
      using assms(4,5,6,8) 2(2,3,4)
      unfolding list_all2_conv_all_nth external_typing.simps
      by (simp_all add: glob_typing_def nth_append sglob_def sglob_ind_def sglob_val_def)
    show ?thesis
      using assms(3)
      unfolding reduce_trans_def
    proof (cases rule: converse_rtranclpE)
      case base
      thus ?thesis
        using 2(1)
        by auto
    next
      case (step y)
      then obtain s_y f_y es_y where y_is:"\<lparr>s_r;f;[$Get_global j]\<rparr> \<leadsto> \<lparr>s_y;f_y;es_y\<rparr>" "y = (s_y, f_y, es_y)"
        using 2
        by fastforce
      hence s_y_is:"s_y = s_r \<and> f_y = f \<and> es_y = [$C sglob_val s (f_inst f) j]"
        using assms(6,8)
      proof (induction s_r f "[$Get_global j]" s_y f_y es_y arbitrary: y rule: reduce.induct)
        case (basic e' s vs i)
        thus ?case
          using lfilled_single
          apply cases
          apply auto
          done
      next
        case (get_global s vs i)
        thus ?case
          using type_is(2,3)
          by (simp_all add: sglob_def sglob_ind_def sglob_val_def nth_append)
      next
        case (label s vs es i s' vs' es' k lholed les')
        thus ?case
          using lfilled_single[OF label(3)]
          by (metis Lfilled_exact.L0 Lfilled_exact_imp_Lfilled e.distinct(5) lfilled_eq reduce_not_nil)
      qed auto
      thus ?thesis
        using step(2) y_is reduce_trans_consts[of s_y f_y "[sglob_val s (f_inst f) j]" s' f' "[v]"] 2 type_is
        apply (simp add: assms nth_append sglob_def sglob_ind_def sglob_val_def reduce_trans_def const_list_def is_const_def Suc_1[symmetric] split: prod.splits)
        using s_y_is type_is(1)
        apply blast
        done
    qed
  qed
qed

lemma ext_globs_ind:
  assumes "i<length (ext_globs v_imps)"
  shows "\<exists>j. j < length v_imps \<and> Ext_glob ((ext_globs v_imps) ! i) = v_imps!j"
  using assms
proof (induction v_imps arbitrary: i)
case Nil
  thus ?case
    by (simp add: map_filter_simps(2))
next
  case (Cons v_imp v_imps)
  consider (1) k where "v_imp = Ext_glob k" | (2) "\<And>k. v_imp \<noteq> Ext_glob k"
    by blast
  thus ?case
  proof (cases)
    case 1
    show ?thesis
    proof (cases i)
      case 0
      thus ?thesis
        using 1
        by (auto simp add: map_filter_def)
    next
      case (Suc i')
      hence Suc1:"i' < length (ext_globs (v_imps))"
        using 1 Cons(2)
        by (simp add: map_filter_def)
      thus ?thesis
        using Cons(1)[OF Suc1] Suc 1
        by (auto simp add: map_filter_def)
    qed
  next
    case 2
    hence a2:"ext_globs v_imps = ext_globs (v_imp#v_imps)"
      apply (cases v_imp)
      apply (simp_all add: map_filter_def)
      done
    hence b2:"i < length (ext_globs (v_imps))"
      using Cons(2)
      by simp
    thus ?thesis
      using Cons(1)[OF b2] a2
      by auto
  qed
qed

lemma alloc_glob_ext_typing:
  assumes "alloc_glob s (m_g, v) = (s', i_g)"
          "typeof v = (tg_t (g_type m_g))"
  shows "external_typing s' (Ext_glob i_g) (Te_glob (g_type m_g))"
  using assms alloc_glob_length[OF assms(1)]
  unfolding alloc_glob_def external_typing.simps glob_typing_def
  apply simp
  apply (metis global.select_convs(1) global.select_convs(2) nth_append_length)
  done

lemma alloc_globs_ext_typing:
  assumes "alloc_globs s m_gs vs = (s', i_gs)"
          "list_all2 (\<lambda>v m_g. typeof v = (tg_t (g_type m_g))) vs m_gs"
  shows "list_all2 (\<lambda>ig tg. external_typing s' (Ext_glob ig) (Te_glob tg)) i_gs (map g_type m_gs)"
  using assms(2,1)
proof (induction arbitrary: s i_gs rule: list_all2_induct)
case Nil
  thus ?case
    by simp
next
  case (Cons x xs y ys)
  obtain i_g i_gs' s'' where i_gs_is:"i_gs = i_g#i_gs'"
                                     "alloc_glob s (y,x) = (s'', i_g)"
                                     "alloc_globs s'' ys xs = (s', i_gs')"
    using Cons(4)
    by (fastforce split: prod.splits)
  have "external_typing s' (Ext_glob i_g) (Te_glob (g_type y))"
    using alloc_glob_ext_typing[OF i_gs_is(2) Cons(1)] alloc_globs_range[OF i_gs_is(3)] list_all2_lengthD[OF Cons(2)]
          nth_append[of "s.globs s''"]
    unfolding external_typing.simps
    apply simp
    apply (metis length_append trans_less_add1)
    done
  thus ?case
    using alloc_glob_ext_typing[OF i_gs_is(2) Cons(1)] Cons(3)[OF i_gs_is(3)] i_gs_is(1)
    by (simp split: prod.splits)
qed

lemma list_all2_external_typing_glob_alloc:
  assumes "list_all2 (\<lambda>i t. external_typing s i t) v_imps t_imps"
  shows "list_all2 (\<lambda>ig tg. external_typing s (Ext_glob ig) (Te_glob tg)) (ext_globs v_imps) (ext_t_globs t_imps)"
  using assms
proof (induction t_imps rule: list_all2_induct)
  case Nil
  thus ?case
    by (simp add: map_filter_simps(2))
next
  case (Cons x xs y ys)
  thus ?case
  proof (cases rule: external_typing.cases)
    case (4 i gt)
    thus ?thesis
      using Cons
      by (simp add: map_filter_def)
  qed (fastforce simp add: map_filter_def)+
qed

lemma alloc_module_ext_arb:
  assumes "alloc_module s m imps gvs (s',inst,exps)"
  shows "\<exists>farbs tarbs marbs garbs.
           (funcs s)@farbs = funcs s' \<and>
           (tabs s)@tarbs = tabs s' \<and>
           (mems s)@marbs = mems s' \<and>
           (globs s)@garbs = globs s'"
proof -
  obtain s1 s2 s3 i_fs i_ts i_ms i_gs where inst_is:
    "inst = \<lparr>types=(m_types m),
           funcs=(ext_funcs imps)@i_fs,
           tabs=(ext_tabs imps)@i_ts,
           mems=(ext_mems imps)@i_ms,
           globs=(ext_globs imps)@i_gs\<rparr>"
    "alloc_funcs s (m_funcs m) inst = (s1,i_fs)"
    "alloc_tabs s1 (m_tabs m) = (s2,i_ts)"
    "alloc_mems s2 (m_mems m) = (s3,i_ms)"
    "alloc_globs s3 (m_globs m) gvs = (s',i_gs)"
    "exps = map (\<lambda>m_exp. \<lparr>E_name=(E_name m_exp), E_desc=(export_get_v_ext inst (E_desc m_exp))\<rparr>) (m_exports m)"
    using assms(1)
    unfolding alloc_module.simps
    by blast
  show ?thesis
    using alloc_funcs_range[OF inst_is(2)]
          alloc_tabs_range[OF inst_is(3)]
          alloc_mems_range[OF inst_is(4)]
          alloc_globs_range[OF inst_is(5)]
    by fastforce
qed

lemma alloc_module_external_typing_preserved:
  assumes "alloc_module s m imps gvs (s',inst,exps)"
          "external_typing s v_imp t_imp"
  shows "external_typing s' v_imp t_imp"
  using assms(2,1)
proof (cases rule: external_typing.cases)
  case (1 i tf)
  thus ?thesis
    using alloc_module_ext_arb[OF assms(1)]
    by (metis add.commute external_typing.intros(1) length_append nth_append trans_less_add2)
next
  case (2 i tt)
  thus ?thesis
    using alloc_module_ext_arb[OF assms(1)]
    by (metis external_typing.intros(2) length_append nth_append trans_less_add1)
next
  case (3 i mt)
  thus ?thesis
    using alloc_module_ext_arb[OF assms(1)]
    by (metis external_typing.intros(3) length_append nth_append trans_less_add1)
next
  case (4 i gt)
  thus ?thesis
    using alloc_module_ext_arb[OF assms(1)]
    by (metis external_typing.intros(4) length_append nth_append trans_less_add1)
qed

lemma g_init_type_interp:
  assumes "interp_get_v s inst (g_init m_g) = gv"
          "(module_glob_typing \<C>) m_g gt"
          "global \<C> = tgs"
          "list_all2 (\<lambda>ig tg. external_typing s (Ext_glob ig) (Te_glob tg)) igs tgs"
          "inst.globs inst = igs@arb"
  shows "typeof gv = tg_t (g_type m_g)"
proof -
  have 1:"const_exprs \<C> (g_init m_g)"
    using assms(2)
    unfolding module_glob_typing.simps
    by fastforce
  have 2:"\<C> \<turnstile> (g_init m_g) : ([] _> [tg_t (g_type m_g)])"
    using assms(2)
    unfolding module_glob_typing.simps
    by fastforce
  show ?thesis
    using const_exprs_run_v[OF 1 2 assms(3,4,5)] assms(1)
    unfolding interp_get_v_def
    by (simp split: prod.splits)
qed

lemma interp_instantiate_imp_instantiate:
  assumes "(interp_instantiate s m v_imps = Some ((s_end, inst, v_exps), start))"
  shows "(instantiate s m v_imps ((s_end, inst, v_exps), start))"
proof -
  obtain t_imps t_exps g_inits s' e_offs d_offs s'' inst' where s_end_is:
    "module_type_checker m = Some (t_imps, t_exps)"
    "(list_all2 (external_typing s) v_imps t_imps)"
    "g_inits = map (\<lambda>g. interp_get_v s inst' (g_init g)) (m_globs m)"
    "(s', inst, v_exps) = interp_alloc_module s m v_imps g_inits"
    "e_offs = map (\<lambda>e. interp_get_i32 s' inst (e_off e)) (m_elem m)"
    "d_offs = map (\<lambda>d. interp_get_i32 s' inst (d_off d)) (m_data m)"
    "list_all2 (\<lambda>e_off e. ((nat_of_int e_off) + (length (e_init e))) \<le> length (fst ((tabs s)!((inst.tabs inst)!(e_tab e))))) e_offs (m_elem m)"
    "list_all2 (\<lambda>d_off d. ((nat_of_int d_off) + (length (d_init d))) \<le> mem_length ((mems s)!((inst.mems inst)!(d_data d)))) d_offs (m_data m)"
    "start = map_option (\<lambda>i_s. ((inst.funcs inst)!i_s)) (m_start m)"
    "s'' = init_tabs s' inst (map nat_of_int e_offs) (m_elem m)"
    "s_end = init_mems s' inst (map nat_of_int d_offs) (m_data m)"
    "inst' = \<lparr>types=[],funcs=[],tabs=[],mems=[],globs=ext_globs v_imps\<rparr>"
    using assms
    by (fastforce simp add: Let_def split: if_splits option.splits prod.splits)

  have 1:"module_typing m t_imps t_exps"
    using s_end_is(1) module_type_checker_imp_module_typing
    by blast
  have 2:"alloc_module s m v_imps g_inits (s', inst, v_exps)"
    using s_end_is(4) interp_alloc_module_imp_alloc_module
    by metis

  obtain fs fts ts ms gs gts els ds i_opt imps exps tfs ifts itts imts igts \<C> \<C>' where m_is:
    "list_all2 (module_func_typing \<C>) fs fts"
    "list_all (module_tab_typing) ts"
    "list_all (module_mem_typing) ms"
    "list_all2 (module_glob_typing \<C>') gs gts"
    "list_all (module_elem_typing \<C>) els"
    "list_all (module_data_typing \<C>) ds"
    "pred_option (module_start_typing \<C>) i_opt"
    "list_all2 (\<lambda>imp. module_import_typing \<C> (I_desc imp)) imps t_imps"
    "list_all2 (\<lambda>exp. module_export_typing \<C> (E_desc exp)) exps t_exps"
    "ifts = ext_t_funcs t_imps"
    "itts = ext_t_tabs t_imps"
    "imts = ext_t_mems t_imps"
    "igts = ext_t_globs t_imps"
    "\<C> = \<lparr>types_t=tfs, func_t=ifts@fts, global=igts@gts, table=itts@ts, memory=imts@ms, local=[], label=[], return=None\<rparr>"
    "\<C>' = \<lparr>types_t=[], func_t=[], global=igts, table=[], memory=[], local=[], label=[], return=None\<rparr>"
    "m = \<lparr>m_types = tfs,
          m_funcs = fs,
          m_tabs = ts,
          m_mems = ms,
          m_globs = gs,
          m_elem = els,
          m_data = ds,
          m_start = i_opt,
          m_imports = imps,
          m_exports = exps\<rparr>"
    using 1
    unfolding module_typing.simps
    by blast

  obtain s1 s2 s3 i_fs i_ts i_ms i_gs where inst_is:
    "inst = \<lparr>types=(m_types m),
           funcs=(ext_funcs v_imps)@i_fs,
           tabs=(ext_tabs v_imps)@i_ts,
           mems=(ext_mems v_imps)@i_ms,
           globs=(ext_globs v_imps)@i_gs\<rparr>"
    "alloc_funcs s (m_funcs m) inst = (s1,i_fs)"
    "alloc_tabs s1 (m_tabs m) = (s2,i_ts)"
    "alloc_mems s2 (m_mems m) = (s3,i_ms)"
    "alloc_globs s3 (m_globs m) g_inits = (s',i_gs)"
    "v_exps = map (\<lambda>m_exp. \<lparr>E_name=(E_name m_exp), E_desc=(export_get_v_ext inst (E_desc m_exp))\<rparr>) (m_exports m)"
    using 2
    unfolding alloc_module.simps
    by blast

  have 12:"list_all2 (\<lambda>ig tg. external_typing s (Ext_glob ig) (Te_glob tg)) (inst.globs inst') (global \<C>')"
    using s_end_is(2,12) m_is(13,15) ext_globs_ind list_all2_external_typing_glob_alloc
    by simp
  have 11:"list_all2 (\<lambda>ig tg. external_typing s' (Ext_glob ig) (Te_glob tg)) (inst.globs inst) (global \<C>)"
  proof -
    have "list_all2 (\<lambda>ig tg. external_typing s' (Ext_glob ig) (Te_glob tg)) (inst.globs inst') (global \<C>')"
      using alloc_module_external_typing_preserved[OF 2] 12
      unfolding list_all2_conv_all_nth
      by fastforce
    moreover
    have 111:"list_all2 (\<lambda>v m_g. typeof v = tg_t (g_type m_g)) g_inits (m_globs m)"
      using s_end_is(3)[symmetric] g_init_type_interp[OF _ _ _ 12, of inst' _ _ \<C>' _ "[]"] m_is(4,16)
      by (auto simp add: list_all2_conv_all_nth)
    have "(gather_m_g_types (m_globs m)) = gts"
      using m_is(4,16)
      unfolding list_all2_conv_all_nth module_glob_typing.simps
      apply simp
      apply (metis length_map module_glob.select_convs(1) nth_equalityI nth_map)
      done
    hence "list_all2 (\<lambda>ig tg. external_typing s' (Ext_glob ig) (Te_glob tg)) i_gs gts"
      using alloc_globs_ext_typing[OF inst_is(5) 111]
      by blast
    ultimately
    show ?thesis
      using list_all2_appendI
      by (fastforce simp add: m_is(14,15) inst_is(1) s_end_is(12))
  qed

  have 3:"list_all2 (\<lambda>g v. reduce_trans (s',\<lparr> f_locs=[], f_inst=inst \<rparr>,$*(g_init g)) (s',\<lparr> f_locs=[], f_inst=inst \<rparr>,[$C v])) (m_globs m) g_inits"
  proof -
    { fix i
      assume local_assms:"length (m_globs m) = length g_inits" "i<length (m_globs m)"
      hence l1:"const_exprs \<C>' (g_init (m_globs m ! i))"
        using m_is(4,16)
        unfolding list_all2_conv_all_nth module_glob_typing.simps
        by auto
      obtain t where l2:"\<C>' \<turnstile> (g_init (m_globs m ! i)) : ([] _> [t])"
        using local_assms m_is(4,16)
        unfolding list_all2_conv_all_nth module_glob_typing.simps
        by auto
      obtain v_r where "run_v 2 0 (s, \<lparr> f_locs=[], f_inst=inst' \<rparr>, $* (g_init (m_globs m ! i))) =  (s, RValue [v_r])"
        using const_exprs_run_v[OF l1 l2 _ 12, of inst']
        by auto
      hence a_runv:"run_v 2 0 (s,\<lparr> f_locs=[], f_inst=inst'\<rparr>,$*(g_init ((m_globs m)!i))) = (s,RValue [(g_inits!i)])"
        using s_end_is(3) local_assms
        by (simp add: interp_get_v_def split: v.splits)
      obtain f_temp where f_temp_is:
        "reduce_trans (s, \<lparr>f_locs = [], f_inst = inst'\<rparr>, $* g_init (m_globs m ! i)) (s, f_temp, $$* [g_inits ! i])"
        using run_v_sound[OF a_runv]
        by blast
      hence l3:"reduce_trans (s,\<lparr> f_locs=[], f_inst=inst' \<rparr>,$*(g_init ((m_globs m)!i))) (s,\<lparr> f_locs=[], f_inst=inst' \<rparr>,[$C (g_inits!i)])"
        using reduce_trans_length_locals[OF f_temp_is] reduce_trans_inst_is[OF f_temp_is]
        apply simp
        apply (metis (full_types) f.surjective unit.exhaust)
        done
      obtain arbg arbi where arbgi:"(globs s)@arbg = (globs s')"
                                   "inst.globs inst = inst.globs inst' @ arbi"
        using alloc_module_ext_arb[OF 2] 2 s_end_is(12)
        unfolding alloc_module.simps
        by auto
      have run_v_is:"run_v 2 0 (s', \<lparr> f_locs=[], f_inst=inst \<rparr>, $* g_init (m_globs m ! i)) = (s', RValue [g_inits ! i])"
        using const_exprs_reduce_trans[OF l1 l2 l3] _ 12 _ arbgi(1)[symmetric] _ arbgi(2)
        by fastforce
      obtain f_temp where  "reduce_trans (s',\<lparr> f_locs=[], f_inst=inst \<rparr>,$*(g_init ((m_globs m)!i))) (s',f_temp,[$C (g_inits!i)])"
        using run_v_sound[OF run_v_is]
        by auto
      hence "reduce_trans (s',\<lparr> f_locs=[], f_inst=inst \<rparr>,$*(g_init ((m_globs m)!i))) (s',\<lparr> f_locs=[], f_inst=inst \<rparr>,[$C (g_inits!i)])"
        using reduce_trans_length_locals reduce_trans_inst_is
        by (metis (full_types) f.select_convs(1) f.surjective length_greater_0_conv unit.exhaust)
    }
    thus ?thesis
      using s_end_is(3)
      unfolding list_all2_conv_all_nth
      by fastforce
  qed

  have 4:"list_all2 (\<lambda>e c. reduce_trans (s',\<lparr> f_locs=[], f_inst=inst \<rparr>,$*(e_off e)) (s',\<lparr> f_locs=[], f_inst=inst \<rparr>,[$C ConstInt32 c])) (m_elem m) e_offs"
  proof -
    { fix i
      assume local_assms:"length (m_elem m) = length e_offs" "i<length (m_elem m)"
      hence l1:"const_exprs \<C> (e_off (m_elem m ! i))"
        by (metis m_is(5,16) list_all_length m.select_convs(6) module_elem.select_convs(2) module_elem_typing.cases)
      have l2:"\<C> \<turnstile> (e_off (m_elem m ! i)) : ([] _> [T_i32])"
        using local_assms
        by (metis m_is(5,16) list_all_length m.select_convs(6) module_elem.select_convs(2) module_elem_typing.cases)
      obtain c_r where "run_v 2 0 (s', \<lparr> f_locs=[], f_inst=inst \<rparr>, $* e_off (m_elem m ! i)) =  (s', RValue [ConstInt32 c_r])"
        using const_exprs_run_v[OF l1 l2 _ 11, of inst "[]"] typeof_i32
        by auto
      hence run_v_is:"run_v 2 0 (s', \<lparr> f_locs=[], f_inst=inst \<rparr>, $* e_off (m_elem m ! i)) = (s', RValue [ConstInt32 (e_offs ! i)])"
        using s_end_is(5) local_assms
        by (simp add: interp_get_i32_def interp_get_v_def split: v.splits)
      obtain f_temp where "reduce_trans (s', \<lparr> f_locs=[], f_inst=inst \<rparr>, $* e_off (m_elem m ! i)) (s', f_temp, [$C ConstInt32 (e_offs ! i)])"
        using run_v_sound[OF run_v_is]
        by auto
      hence "reduce_trans (s', \<lparr> f_locs=[], f_inst=inst \<rparr>, $* e_off (m_elem m ! i)) (s', \<lparr> f_locs=[], f_inst=inst \<rparr>, [$C ConstInt32 (e_offs ! i)])"
        using reduce_trans_length_locals reduce_trans_inst_is
        by (metis (full_types) f.select_convs(1) f.surjective length_greater_0_conv old.unit.exhaust)
    }
    thus ?thesis
      using s_end_is(5)
      unfolding list_all2_conv_all_nth
      by fastforce
  qed
  have 5:"list_all2 (\<lambda>d c. reduce_trans (s',\<lparr> f_locs=[], f_inst=inst \<rparr>,$*(d_off d)) (s',\<lparr> f_locs=[], f_inst=inst \<rparr>,[$C ConstInt32 c])) (m_data m) d_offs"
  proof -
    { fix i
      assume local_assms:"length (m_data m) = length d_offs" "i<length (m_data m)"
      hence l1:"const_exprs \<C> (d_off (m_data m ! i))"
        by (metis list_all_length m.select_convs(7) m_is(6,16) module_data.select_convs(2) module_data_typing.simps)
      have l2:"\<C> \<turnstile> (d_off (m_data m ! i)) : ([] _> [T_i32])"
        using local_assms
        by (metis list_all_length m.select_convs(7) m_is(6,16) module_data.select_convs(2) module_data_typing.simps)
      obtain c_r where "run_v 2 0 (s', \<lparr> f_locs=[], f_inst=inst \<rparr>, $* d_off (m_data m ! i)) =  (s', RValue [ConstInt32 c_r])"
        using const_exprs_run_v[OF l1 l2 _ 11, of inst "[]"] typeof_i32
        by auto
      hence run_v_is:"run_v 2 0 (s', \<lparr> f_locs=[], f_inst=inst \<rparr>, $* d_off (m_data m ! i)) = (s', RValue [ConstInt32 (d_offs ! i)])"
        using s_end_is(6) local_assms
        by (simp add: interp_get_i32_def interp_get_v_def split: v.splits)
      obtain f_temp where "reduce_trans (s', \<lparr> f_locs=[], f_inst=inst \<rparr>, $* d_off (m_data m ! i)) (s', f_temp, [$C ConstInt32 (d_offs ! i)])"
        using run_v_sound[OF run_v_is]
        by auto
      hence "reduce_trans (s', \<lparr> f_locs=[], f_inst=inst \<rparr>, $* d_off (m_data m ! i)) (s', \<lparr> f_locs=[], f_inst=inst \<rparr>, [$C ConstInt32 (d_offs ! i)])"
        using reduce_trans_length_locals reduce_trans_inst_is
        by (metis (full_types) f.select_convs(1) f.surjective length_greater_0_conv old.unit.exhaust)
    }
    thus ?thesis
      using s_end_is(6)
      unfolding list_all2_conv_all_nth
      by fastforce
   qed
   show ?thesis
     using instantiate.intros
           1 s_end_is(2) 2 3 4 5 s_end_is(7,8) s_end_is(9,10,11)[symmetric]
      by blast
qed

lemma map_intro_length:
  assumes "\<And>i. i < length ls \<Longrightarrow> F (ls!i) = fls!i"
          "length ls = length fls"
  shows "map F ls = fls"
  using assms
  by (metis length_map nth_equalityI nth_map)

lemma instantiate_imp_interp_instantiate:
  assumes "(instantiate s m v_imps ((s_end, inst, v_exps), start))"
  shows "(interp_instantiate s m v_imps = Some ((s_end, inst, v_exps), start))"
proof -
  obtain fs ts ms gs els ds i_opt imps exps tfs where m_is:
    "m = \<lparr>m_types = tfs,
          m_funcs = fs,
          m_tabs = ts,
          m_mems = ms,
          m_globs = gs,
          m_elem = els,
          m_data = ds,
          m_start = i_opt,
          m_imports = imps,
          m_exports = exps\<rparr>"
    using m.cases
    by blast
  obtain inst' where inst'_is:
    "inst' = \<lparr>types=[],funcs=[],tabs=[],mems=[],globs=ext_globs v_imps\<rparr>"
    using inst.cases
    by blast

  obtain t_imps t_exps g_inits s' e_offs d_offs s'' f where s_end_is:
    "module_typing m t_imps t_exps"
    "list_all2 (external_typing s) v_imps t_imps"
    "alloc_module s m v_imps g_inits (s', inst, v_exps)"
    "list_all2 (\<lambda>g v. reduce_trans (s',f,$*(g_init g)) (s',f,[$C v])) gs g_inits"
    "list_all2 (\<lambda>e c. reduce_trans (s',f,$*(e_off e)) (s',f,[$C ConstInt32 c])) els e_offs"
    "list_all2 (\<lambda>d c. reduce_trans (s',f,$*(d_off d)) (s',f,[$C ConstInt32 c])) ds d_offs"
    "list_all2 (\<lambda>e_off e. ((nat_of_int e_off) + (length (e_init e))) \<le> length (fst ((tabs s)!((inst.tabs inst)!(e_tab e))))) e_offs els"
    "list_all2 (\<lambda>d_off d. ((nat_of_int d_off) + (length (d_init d))) \<le> mem_length ((mems s)!((inst.mems inst)!(d_data d)))) d_offs ds"
    "map_option (\<lambda>i_s. ((inst.funcs inst)!i_s)) i_opt = start"
    "init_tabs s' inst (map nat_of_int e_offs) els = s''"
    "init_mems s' inst (map nat_of_int d_offs) ds = s_end"
    "f = \<lparr> f_locs=[], f_inst=inst \<rparr>"
    using assms m_is
    unfolding instantiate.simps
    by fastforce

  obtain fts gts ifts itts imts igts \<C> \<C>' where m_is_2:
    "list_all2 (module_func_typing \<C>) fs fts"
    "list_all (module_tab_typing) ts"
    "list_all (module_mem_typing) ms"
    "list_all2 (module_glob_typing \<C>') gs gts"
    "list_all (module_elem_typing \<C>) els"
    "list_all (module_data_typing \<C>) ds"
    "pred_option (module_start_typing \<C>) i_opt"
    "list_all2 (\<lambda>imp. module_import_typing \<C> (I_desc imp)) imps t_imps"
    "list_all2 (\<lambda>exp. module_export_typing \<C> (E_desc exp)) exps t_exps"
    "ifts = ext_t_funcs t_imps"
    "itts = ext_t_tabs t_imps"
    "imts = ext_t_mems t_imps"
    "igts = ext_t_globs t_imps"
    "\<C> = \<lparr>types_t=tfs, func_t=ifts@fts, global=igts@gts, table=itts@ts, memory=imts@ms, local=[], label=[], return=None\<rparr>"
    "\<C>' = \<lparr>types_t=[], func_t=[], global=igts, table=[], memory=[], local=[], label=[], return=None\<rparr>"
    using s_end_is(1) m_is
    unfolding module_typing.simps
    by blast

  obtain s1 s2 s3 i_fs i_ts i_ms i_gs where inst_is:
    "inst = \<lparr>types=(m_types m),
           funcs=(ext_funcs v_imps)@i_fs,
           tabs=(ext_tabs v_imps)@i_ts,
           mems=(ext_mems v_imps)@i_ms,
           globs=(ext_globs v_imps)@i_gs\<rparr>"
    "alloc_funcs s fs inst = (s1,i_fs)"
    "alloc_tabs s1 ts = (s2,i_ts)"
    "alloc_mems s2 ms = (s3,i_ms)"
    "alloc_globs s3 gs g_inits = (s',i_gs)"
    "v_exps = map (\<lambda>m_exp. \<lparr>E_name=(E_name m_exp), E_desc=(export_get_v_ext inst (E_desc m_exp))\<rparr>) (m_exports m)"
    using s_end_is(3) m_is
    unfolding alloc_module.simps
    by fastforce

  have 12:"list_all2 (\<lambda>ig tg. external_typing s (Ext_glob ig) (Te_glob tg)) (inst.globs inst') (global \<C>')"
    using ext_globs_ind list_all2_external_typing_glob_alloc
    by (simp add: inst'_is m_is_2(13,15) s_end_is(2))
  have 11:"list_all2 (\<lambda>ig tg. external_typing s' (Ext_glob ig) (Te_glob tg)) (inst.globs inst) (global \<C>)"
  proof -
    have "list_all2 (\<lambda>ig tg. external_typing s' (Ext_glob ig) (Te_glob tg)) (inst.globs inst') (global \<C>')"
      using alloc_module_external_typing_preserved[OF s_end_is(3)] 12
      unfolding list_all2_conv_all_nth
      by fastforce
    moreover
    have 111:"list_all2 (\<lambda>v m_g. typeof v = tg_t (g_type m_g)) g_inits gs"
    proof -
      { fix i
        assume local_assms: "i < length gs"
        have l2:"\<C>' \<turnstile> (g_init (gs ! i)) : ([] _> [tg_t (g_type (gs!i))])"
                "const_exprs \<C>' (g_init (gs ! i))"
          using local_assms m_is m_is m_is_2(4,15)
          unfolding list_all2_conv_all_nth module_glob_typing.simps
          by auto
        have l1:"reduce_trans (s',f,$*(g_init (gs!i))) (s',f,[$C (g_inits!i)])"
          using s_end_is(4) local_assms
          unfolding list_all2_conv_all_nth
          by blast
        have "typeof (g_inits!i) = tg_t (g_type (gs!i))"
          using local_assms const_exprs_reduce_trans[OF l2(2,1) l1 _ 12]
              alloc_module_ext_arb[OF s_end_is(3)] s_end_is(3)
          unfolding alloc_module.simps s_end_is(12)
          apply simp
          apply (metis (mono_tags, lifting) inst'_is inst.select_convs(5))
          done
      }
      thus ?thesis
        using s_end_is(4)
        unfolding list_all2_conv_all_nth
        by metis
    qed
    have "(gather_m_g_types gs) = gts"
      using m_is_2(4,15)
      unfolding list_all2_conv_all_nth module_glob_typing.simps
      apply simp
      apply (metis length_map module_glob.select_convs(1) nth_equalityI nth_map)
      done
    hence "list_all2 (\<lambda>ig tg. external_typing s' (Ext_glob ig) (Te_glob tg)) i_gs gts"
      using alloc_globs_ext_typing[OF inst_is(5) 111]
      by blast
    ultimately
    show ?thesis
      using list_all2_appendI inst'_is
      by (fastforce simp add: m_is_2(14,15) inst_is(1) s_end_is(11))
  qed

  have "(module_type_checker m) = Some (t_imps, t_exps)"
    using s_end_is(1) module_typing_equiv_module_type_checker
    by blast
  moreover
  have "g_inits = map (\<lambda>g. interp_get_v s inst' (g_init g)) gs"
  proof -
    { fix i
      assume local_assms: "i < length gs"
      obtain t where l2:"\<C>' \<turnstile> (g_init (gs ! i)) : ([] _> [t])"
                        "const_exprs \<C>' (g_init (gs ! i))"
        using local_assms m_is m_is m_is_2(4,15)
        unfolding list_all2_conv_all_nth module_glob_typing.simps
        by auto
      have l1:"reduce_trans (s',f,$*(g_init (gs!i))) (s',f,[$C (g_inits!i)])"
        using s_end_is(4) local_assms
        unfolding list_all2_conv_all_nth
        by blast
      have "run_v 2 0 (s,\<lparr> f_locs=[], f_inst=inst' \<rparr>,$*(g_init (gs!i))) = (s,RValue [g_inits!i])"
        using const_exprs_reduce_trans[OF l2(2,1) l1 _ 12, of _ s "[]" _ inst' "[]"]
              alloc_module_ext_arb[OF s_end_is(3)] s_end_is(3)
        unfolding alloc_module.simps s_end_is(12)
        apply simp
        apply (metis (mono_tags, lifting) inst'_is inst.select_convs(5))
        done
      hence "interp_get_v s inst' (g_init (gs!i)) = g_inits!i"
        unfolding interp_get_v_def
        by fastforce
    }
    thus ?thesis
      using map_intro_length[symmetric, of gs "(\<lambda>g. interp_get_v s inst' (g_init g))" g_inits]
            list_all2_lengthD[OF s_end_is(4)]
      by fastforce
  qed
  moreover
  have "interp_alloc_module s m v_imps g_inits = (s', inst, v_exps)"
    using s_end_is(3) alloc_module_equiv_interp_alloc_module
    by blast
  moreover
  have "e_offs = map (\<lambda>e. interp_get_i32 s' inst (e_off e)) els"
  proof -
    { fix i
      assume local_assms: "i < length els"
      have l2:"const_exprs \<C> (e_off (els ! i))"
              "\<C> \<turnstile> e_off (els ! i) : ([] _> [T_i32])"
        using m_is_2(5)
        by (metis list_all_length local_assms module_elem.select_convs(2) module_elem_typing.cases)+
      have l1:"reduce_trans (s',f,$*(e_off (els!i))) (s',f,[$C ConstInt32 (e_offs!i)])"
        using s_end_is(5) local_assms
        unfolding list_all2_conv_all_nth
        by blast
      have "run_v 2 0 (s',f,$*(e_off (els!i))) = (s',RValue [ConstInt32 (e_offs!i)])"
        using const_exprs_reduce_trans[OF l2(1,2) l1 _ 11]
        unfolding s_end_is(12)
        by fastforce
      hence "interp_get_i32 s' inst (e_off (els!i)) = e_offs!i"
        unfolding interp_get_i32_def interp_get_v_def s_end_is(12)
        by fastforce
    }
    thus ?thesis
      using map_intro_length[symmetric, of els "(\<lambda>e. interp_get_i32 s' inst (e_off e))" e_offs]
            list_all2_lengthD[OF s_end_is(5)]
      by fastforce
  qed
  moreover
  have "d_offs = map (\<lambda>d. interp_get_i32 s' inst (d_off d)) ds"
  proof -
    { fix i
      assume local_assms: "i < length ds"
      have l2:"const_exprs \<C> (d_off (ds ! i))"
              "\<C> \<turnstile> d_off (ds ! i) : ([] _> [T_i32])"
        using m_is_2(6)
        by (metis list_all_length local_assms module_data.select_convs(2) module_data_typing.cases)+
      have l1:"reduce_trans (s',f,$*(d_off (ds!i))) (s',f,[$C ConstInt32 (d_offs!i)])"
        using s_end_is(6) local_assms
        unfolding list_all2_conv_all_nth
        by blast
      have "run_v 2 0 (s',f,$*(d_off (ds!i))) = (s',RValue [ConstInt32 (d_offs!i)])"
        using const_exprs_reduce_trans[OF l2(1,2) l1 _ 11]
        unfolding s_end_is(12)
        by fastforce
      hence "interp_get_i32 s' inst (d_off (ds!i)) = d_offs!i"
        unfolding interp_get_i32_def interp_get_v_def s_end_is(12)
        by fastforce
    }
    thus ?thesis
      using map_intro_length[symmetric, of ds "(\<lambda>e. interp_get_i32 s' inst (d_off e))" d_offs]
            list_all2_lengthD[OF s_end_is(6)]
      by fastforce
  qed
  ultimately
  show ?thesis
    using s_end_is(2,7,8,9,10,11) m_is inst'_is
    by simp
qed

theorem instantiate_equiv_interp_instantiate:
  "(instantiate s m v_imps ((s_end, inst, v_exps), start)) = (interp_instantiate s m v_imps = Some ((s_end, inst, v_exps), start))"
  using instantiate_imp_interp_instantiate interp_instantiate_imp_instantiate
  by blast
end