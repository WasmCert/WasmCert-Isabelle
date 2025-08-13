theory Wasm_Instantiation 
imports Wasm_Module_Checker Wasm_Interpreter_Properties "../libs/Misc_Generic_Lemmas"
begin

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
  "alloc_tab s t_t = (s\<lparr>s.tabs := (tabs s)@[(t_t, (replicate (l_min (tab_t_lim t_t)) (ConstNull (tab_t_reftype t_t))))]\<rparr>,length (tabs s))"

abbreviation "alloc_tabs \<equiv> alloc_Xs alloc_tab"

definition alloc_mem :: "s \<Rightarrow> mem_t \<Rightarrow> (s \<times> i)" where
  "alloc_mem s m_m = (s\<lparr>s.mems := (mems s)@[mem_mk m_m]\<rparr>,length (mems s))"

abbreviation "alloc_mems \<equiv> alloc_Xs alloc_mem"

definition alloc_glob :: "s \<Rightarrow> (module_glob \<times> v) \<Rightarrow> (s \<times> i)" where
  "alloc_glob s m_g_v = 
    (case m_g_v of (m_g, v) \<Rightarrow>
      (s\<lparr>s.globs := (globs s)@[\<lparr>g_mut=(tg_mut (module_glob.g_type m_g)), g_val=v\<rparr>]\<rparr>,length (globs s)))"

abbreviation "alloc_globs s m_gs vs \<equiv> alloc_Xs alloc_glob s (zip m_gs vs)"

definition alloc_elem :: "s \<Rightarrow> (module_elem \<times> v_ref list) => (s \<times> i)" where
  "alloc_elem s m_el_v_rs = (case m_el_v_rs of (m_el, v_rs) \<Rightarrow> (s\<lparr>s.elems := (elems s)@[(e_type m_el, v_rs)]\<rparr>,length (elems s)))"

abbreviation "alloc_elems s t_rs v_rs \<equiv> alloc_Xs alloc_elem s (zip t_rs v_rs)"

definition alloc_data :: "s \<Rightarrow> module_data => (s \<times> i)" where
  "alloc_data s m_d = (s\<lparr>s.datas := (datas s)@[d_init m_d]\<rparr>,length (datas s))"

abbreviation "alloc_datas \<equiv> alloc_Xs alloc_data"

lemma alloc_func_length:
  assumes "alloc_func s m_f i = (s', i_f)"
  shows "length (funcs s) = i_f"
        "length (funcs s') = Suc i_f"
        "\<exists>farb. (funcs s)@[farb] = (funcs s')"
        "(tabs s) = (tabs s')"
        "(mems s) = (mems s')"
        "(globs s) = (globs s')"
        "(elems s) = (elems s')"
        "(datas s) = (datas s')"
  using assms[symmetric]
  unfolding alloc_func_def
  by (simp_all split: prod.splits)

lemma alloc_tab_length:
  assumes "alloc_tab s t_ts = (s', i_t)"
  shows "length (tabs s) = i_t"
        "length (tabs s') = Suc i_t"
        "(funcs s) = (funcs s')"
        "\<exists>tarb. (tabs s)@[tarb] = (tabs s')"
        "(mems s) = (mems s')"
        "(globs s) = (globs s')"
        "(elems s) = (elems s')"
        "(datas s) = (datas s')"
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
        "(elems s) = (elems s')"
        "(datas s) = (datas s')"
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
        "(elems s) = (elems s')"
        "(datas s) = (datas s')"
  using assms[symmetric]
  unfolding alloc_glob_def
  by (simp_all split: prod.splits)

lemma alloc_elem_length:
  assumes "alloc_elem s (m_el, v_rs) = (s', i_e)"
  shows "length (elems s) = i_e"
        "length (elems s') = Suc i_e"
        "(funcs s) = (funcs s')"
        "(tabs s) = (tabs s')"
        "(mems s) = (mems s')"
        "(globs s) = (globs s')"
        "(elems s)@[(e_type m_el, v_rs)] = (elems s')"
        "(datas s) = (datas s')"
  using assms[symmetric]
  unfolding alloc_elem_def
  by (simp_all split: prod.splits)

lemma alloc_data_length:
  assumes "alloc_data s m_d = (s', i_d)"
  shows "length (datas s) = i_d"
        "length (datas s') = Suc i_d"
        "(funcs s) = (funcs s')"
        "(tabs s) = (tabs s')"
        "(mems s) = (mems s')"
        "(globs s) = (globs s')"
        "(elems s) = (elems s')"
        "(datas s)@[d_init m_d] = (datas s')"
  using assms[symmetric]
  unfolding alloc_data_def
  by (simp_all split: prod.splits)

lemma alloc_funcs_range:
  assumes "alloc_funcs s m_fs i = (s', i_fs)"
  shows "i_fs = [length (funcs s) ..< (length (funcs s) + length m_fs)] \<and>
         (\<exists>farb. (funcs s)@farb = (funcs s')) \<and>
         (tabs s) = (tabs s') \<and>
         (mems s) = (mems s') \<and>
         (globs s) = (globs s') \<and>
         (elems s) = (elems s') \<and>
         (datas s) = (datas s')"
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
  assumes "alloc_tabs s t_ts = (s', i_ts)"
  shows "i_ts = [length (tabs s) ..< (length (tabs s) + length t_ts)] \<and>
         (funcs s) = (funcs s') \<and>
         (\<exists>tarb. (tabs s)@tarb = (tabs s')) \<and>
         (mems s) = (mems s') \<and>
         (globs s) = (globs s') \<and>
         (elems s) = (elems s') \<and>
         (datas s) = (datas s')"
  using assms
proof (induction t_ts arbitrary: s i_ts)
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
         (globs s) = (globs s') \<and>
         (elems s) = (elems s') \<and>
         (datas s) = (datas s')"
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
         ((globs s)@(map2 (\<lambda>m_g v. \<lparr>g_mut=(tg_mut (module_glob.g_type m_g)), g_val=v\<rparr>) m_gs vs) = (globs s')) \<and>
         (elems s) = (elems s') \<and>
         (datas s) = (datas s')"
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

lemma alloc_elems_range:
  assumes "alloc_elems s m_els v_rss  = (s', i_es)"
  shows "i_es = [length (elems s) ..< length (elems s) + min (length (m_els)) (length v_rss)] \<and>
         (funcs s) = (funcs s') \<and>
         (tabs s) = (tabs s') \<and>
         (mems s) = (mems s') \<and>
         (globs s) = (globs s') \<and>
         (elems s)@(zip (map e_type m_els) v_rss) = (elems s') \<and>
         (datas s) = (datas s')"
  using assms
proof (induction m_els arbitrary: s i_es v_rss)
  case Nil
  thus ?case
    by simp
next
  case (Cons m_el' m_els')
  note outer_Cons = Cons
  show ?case
  proof (cases v_rss)
    case Nil
    thus ?thesis
      using Cons
      by simp
  next
    case (Cons v_rs' v_rss')
    then obtain s'' i_e' i_es' where s''_is:"alloc_elem s (m_el', v_rs') = (s'', i_e')"
                                       "alloc_elems s'' m_els' v_rss' = (s', i_es')"
                                  
                                       "i_e' # i_es' = i_es"
      using outer_Cons(2)
      by (simp split: prod.splits)
    thus ?thesis
      using outer_Cons(1)[OF s''_is(2)] using alloc_elem_length[OF s''_is(1)] upt_rec Cons
      apply (simp)
      apply (metis (no_types, lifting) append_Cons append_assoc self_append_conv2)
      done
  qed
qed

lemma alloc_datas_range:
  assumes "alloc_datas s m_ds = (s', i_ds)"
  shows "i_ds = [length (datas s) ..< (length (datas s) + length m_ds)] \<and>
         (funcs s) = (funcs s') \<and>
         (tabs s) = (tabs s') \<and>
         (mems s) = (mems s') \<and>
         (globs s) = (globs s') \<and>
         (elems s) = (elems s') \<and>
         ((datas s)@(map d_init m_ds) = (datas s'))"
  using assms
proof (induction m_ds arbitrary: s i_ds )
  case Nil
  thus ?case
    by auto
next
  case (Cons m_d' m_ds')
  obtain s'' i_d' i_ds' where s''_is:"alloc_data s m_d' = (s'', i_d')"
                                     "alloc_datas s'' m_ds' = (s', i_ds')"
                                     "i_d' # i_ds' = i_ds"
    using Cons(2)
    by (simp split: prod.splits)
  show ?case
    using Cons(1)[OF s''_is(2)] alloc_data_length[OF s''_is(1)] s''_is(3)
    apply (auto simp add: le_def split: if_splits)
    using upt_rec
    by (simp, metis append_Cons append_Nil2 append_assoc same_append_eq)
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

inductive alloc_module :: "s \<Rightarrow> m \<Rightarrow> v_ext list \<Rightarrow> v list \<Rightarrow> (v_ref list) list \<Rightarrow> (s \<times> inst \<times> module_export list) \<Rightarrow> bool" where
  "\<lbrakk>inst = \<lparr>types=(m_types m),
           funcs=(ext_funcs imps)@i_fs,
           tabs=(ext_tabs imps)@i_ts,
           mems=(ext_mems imps)@i_ms,
           globs=(ext_globs imps)@i_gs,
           elems=i_es,
           datas=i_ds\<rparr>;
    alloc_funcs s (m_funcs m) inst = (s1,i_fs);
    alloc_tabs s1 (m_tabs m) = (s2,i_ts);
    alloc_mems s2 (m_mems m) = (s3,i_ms);
    alloc_globs s3 (m_globs m) gvs = (s4,i_gs);
    alloc_elems s4 (m_elems m) el_inits = (s5,i_es);
    alloc_datas s5 (m_datas m) = (s', i_ds);
    exps = map (\<lambda>m_exp. \<lparr>E_name=(E_name m_exp), E_desc=(export_get_v_ext inst (E_desc m_exp))\<rparr>) (m_exports m)
     \<rbrakk> \<Longrightarrow> alloc_module s m imps gvs el_inits (s',inst,exps)"

definition interp_alloc_module :: "s \<Rightarrow> m \<Rightarrow> v_ext list \<Rightarrow> v list \<Rightarrow> (v_ref list) list \<Rightarrow> (s \<times> inst \<times> module_export list)" where
  "interp_alloc_module s m imps gvs el_inits =
   (let i_fs = [length (funcs s) ..< (length (funcs s) + length (m_funcs m))] in
    let i_ts = [length (tabs s) ..< (length (tabs s) + length (m_tabs m))] in
    let i_ms = [length (mems s) ..< (length (mems s) + length (m_mems m))] in
    let i_gs = [length (globs s) ..< (length (globs s) + min (length (m_globs m)) (length gvs))] in
    let i_es = [length (elems s) ..< length (elems s) + min (length (m_elems m)) (length el_inits)] in
    let i_ds = [length (datas s) ..< length (datas s) + length (m_datas m)] in
    let inst = \<lparr>types=(m_types m),
                funcs=(ext_funcs imps)@i_fs,
                tabs=(ext_tabs imps)@i_ts,
                mems=(ext_mems imps)@i_ms,
                globs=(ext_globs imps)@i_gs,
                elems = i_es,
                datas = i_ds\<rparr> in
    let (s1,_) = alloc_funcs s (m_funcs m) inst in
    let (s2,_) = alloc_tabs s1 (m_tabs m) in
    let (s3,_) = alloc_mems s2 (m_mems m) in
    let (s4,_) = alloc_globs s3 (m_globs m) gvs in
    let (s5,_) = alloc_elems s4 (m_elems m) el_inits in
    let (s',_) = alloc_datas s5 (m_datas m) in
    let exps = map (\<lambda>m_exp. \<lparr>E_name=(E_name m_exp), E_desc=(export_get_v_ext inst (E_desc m_exp))\<rparr>) (m_exports m) in
    (s', inst, exps))"

lemma alloc_module_imp_interp_alloc_module:
  assumes "alloc_module s m imps gvs el_inits (s',inst,exps)"
  shows "(interp_alloc_module s m imps gvs el_inits = (s',inst,exps))"
proof -
  obtain s1 s2 s3 s4 s5 i_fs i_ts i_ms i_gs i_es i_ds where s'_is:
    "inst = \<lparr>types=(m_types m),
             funcs=(ext_funcs imps)@i_fs,
             tabs=(ext_tabs imps)@i_ts,
             mems=(ext_mems imps)@i_ms,
             globs=(ext_globs imps)@i_gs,
             elems=i_es,
             datas=i_ds\<rparr>"
    "alloc_funcs s (m_funcs m) inst = (s1,i_fs)"
    "alloc_tabs s1 (m_tabs m) = (s2,i_ts)"
    "alloc_mems s2 (m_mems m) = (s3,i_ms)"
    "alloc_globs s3 (m_globs m) gvs = (s4,i_gs)"
    "alloc_elems s4 (m_elems m) el_inits = (s5, i_es)"
    "alloc_datas s5 (m_datas m) = (s', i_ds)"
    "exps = map (\<lambda>m_exp. \<lparr>E_name=(E_name m_exp), E_desc=(export_get_v_ext inst (E_desc m_exp))\<rparr>) (m_exports m)"
    using assms
    unfolding alloc_module.simps
    by blast
  have "i_fs = [length (funcs s) ..< (length (funcs s) + length (m_funcs m))]"
       "i_ts = [length (tabs s) ..< (length (tabs s) + length (m_tabs m))]"
       "i_ms = [length (mems s) ..< (length (mems s) + length (m_mems m))]"
       "i_gs = [length (globs s) ..< (length (globs s) + min (length (m_globs m)) (length gvs))]"
       "i_es = [length (elems s) ..< length (elems s) + min (length (m_elems m)) (length el_inits)]"
       "i_ds = [length (datas s) ..< length (datas s) + length (m_datas m)]"
    using alloc_funcs_range[OF s'_is(2)]
          alloc_tabs_range[OF s'_is(3)]
          alloc_mems_range[OF s'_is(4)]
          alloc_globs_range[OF s'_is(5)]
          alloc_elems_range[OF s'_is(6)]
          alloc_datas_range[OF s'_is(7)]
    by auto
  thus ?thesis
    using s'_is
    unfolding interp_alloc_module_def
    by (simp add: Let_def split: prod.splits)
qed

lemma interp_alloc_module_imp_alloc_module:
  assumes "(interp_alloc_module s m imps gvs el_inits = (s',inst,exps))"
  shows "alloc_module s m imps gvs el_inits (s',inst,exps)"
proof -
  obtain i_fs i_ts i_ms i_gs i_es i_ds i_fs' i_ts' i_ms' i_gs' i_es' i_ds' s1 s2 s3 s4 s5 where s'_is:
    "i_fs = [length (funcs s) ..< (length (funcs s) + length (m_funcs m))]"
    "i_ts = [length (tabs s) ..< (length (tabs s) + length (m_tabs m))]"
    "i_ms = [length (mems s) ..< (length (mems s) + length (m_mems m))]"
    "i_gs = [length (globs s) ..< (length (globs s) + min (length (m_globs m)) (length gvs))]"
    "i_es = [length (elems s) ..< length (elems s) + min (length (m_elems m)) (length el_inits)]"
    "i_ds = [length (datas s) ..< length (datas s) + length (m_datas m)]"
    "inst = \<lparr>types=(m_types m),
                funcs=(ext_funcs imps)@i_fs,
                tabs=(ext_tabs imps)@i_ts,
                mems=(ext_mems imps)@i_ms,
                globs=(ext_globs imps)@i_gs,
                elems=i_es,
                datas=i_ds\<rparr>"
    "(s1,i_fs') = alloc_funcs s (m_funcs m) inst"
    "(s2,i_ts') = alloc_tabs s1 (m_tabs m)"
    "(s3,i_ms') = alloc_mems s2 (m_mems m)"
    "(s4,i_gs') = alloc_globs s3 (m_globs m) gvs"
    "(s5,i_es') = alloc_elems s4 (m_elems m) el_inits"
    "(s',i_ds') = alloc_datas s5 (m_datas m)"
    "exps = map (\<lambda>m_exp. \<lparr>E_name=(E_name m_exp), E_desc=(export_get_v_ext inst (E_desc m_exp))\<rparr>) (m_exports m)"
    using assms
    unfolding interp_alloc_module_def
    by (auto simp add: Let_def split: prod.splits)
  have "i_fs = i_fs'"
       "i_ts = i_ts'"
       "i_ms = i_ms'"
       "i_gs = i_gs'"
       "i_es = i_es'"
       "i_ds = i_ds'"
    using s'_is(1,2,3,4,5,6)
          alloc_funcs_range[OF s'_is(8)[symmetric]]
          alloc_tabs_range[OF s'_is(9)[symmetric]]
          alloc_mems_range[OF s'_is(10)[symmetric]]
          alloc_globs_range[OF s'_is(11)[symmetric]]
          alloc_elems_range[OF s'_is(12)[symmetric]]
          alloc_datas_range[OF s'_is(13)[symmetric]]
    by auto
  thus ?thesis
    using alloc_module.intros[OF s'_is(7) _ _ _ _ _ _ s'_is(14)]
    by (metis (no_types, lifting) s'_is(8,9,10,11,12,13))
qed

lemma alloc_module_equiv_interp_alloc_module:
  "alloc_module s m imps gvs els (s',inst,exps) = (interp_alloc_module s m imps gvs els = (s',inst,exps))"
  using alloc_module_imp_interp_alloc_module interp_alloc_module_imp_alloc_module
  by blast

definition run_elem :: "module_elem \<Rightarrow> i \<Rightarrow> b_e list" where
"run_elem m_e i = (case (e_mode m_e) of
  Em_passive \<Rightarrow> []
| Em_active x offset \<Rightarrow> offset@[EConstNum (ConstInt32 0), EConstNum (ConstInt32 (int_of_nat (length (e_init m_e)))), Table_init x i, Elem_drop i]
| Em_declarative \<Rightarrow> [ Elem_drop i])"

definition run_elems :: "module_elem list \<Rightarrow> e list" where
"run_elems m_es = $* concat (map2 run_elem (m_es) [0 ..< length m_es])"

definition run_data :: "module_data \<Rightarrow> i \<Rightarrow> b_e list" where
"run_data m_d i = (case (d_mode m_d) of
  Dm_passive \<Rightarrow> []
| Dm_active x offset \<Rightarrow> offset@[EConstNum (ConstInt32 0), EConstNum (ConstInt32 (int_of_nat (length (d_init m_d)))), Memory_init i, Data_drop i])"

definition run_datas :: "module_data list \<Rightarrow> e list" where
"run_datas m_ds = $* concat (map2 run_data (m_ds) [0 ..< length m_ds])"

inductive instantiate :: "s \<Rightarrow> m \<Rightarrow> v_ext list \<Rightarrow> ((s \<times> inst \<times> (module_export list)) \<times> (e list)) \<Rightarrow> bool" where
  "\<lbrakk>module_typing m t_imps t_exps;
    list_all2 (external_typing s) v_imps t_imps;
    alloc_module s m v_imps g_inits el_inits (s', inst, v_exps);
    f = \<lparr> f_locs = [], f_inst = inst \<rparr>;
    list_all2 (\<lambda>g v. reduce_trans (s',f,$*(g_init g)) (s',f,[$C v])) (m_globs m) g_inits;
    list_all2 (\<lambda>el vs. list_all2 (\<lambda> el_init v. reduce_trans (s',f,$*(el_init)) (s',f,[$C (V_ref v)])) (e_init el) vs) (m_elems m) el_inits;
    (case (m_start m) of None \<Rightarrow> [] | Some i_s \<Rightarrow> [Invoke ((inst.funcs inst)!i_s)]) = start
    \<rbrakk> \<Longrightarrow> instantiate s m v_imps ((s', inst, v_exps), (run_elems (m_elems m))@(run_datas (m_datas m))@start)"

(* TODO: Move these to better places! *)    
    
abbreviation "is_first_fun_idx exps i \<equiv> 
  \<exists>exp. is_first_elem_with_prop (is_Ext_func o E_desc) exps exp
    \<and> i = v_ext.the_idx (E_desc exp)
"  

abbreviation "type_of_fun_idx s i \<equiv> cl_type (s.funcs s ! i)" (* TODO:  No guarantee that index is in bounds *)

definition make_params :: "s \<Rightarrow> i \<Rightarrow> (v list) option \<Rightarrow> (v list) option" where
 "make_params s i vs_opt \<equiv> case vs_opt of
  Some vs \<Rightarrow> Some (rev vs)
| None \<Rightarrow> n_zeros (tf.dom (type_of_fun_idx s i))"

definition "instantiate_config s inst es \<equiv> (s, \<lparr>f_locs = [], f_inst = inst\<rparr>, es)"

definition "run_fuzz_abs s m v_imps vs_opt  s' vs \<equiv> \<exists>s\<^sub>1 s\<^sub>2 inst exps init_es i vs_params. 
    instantiate s m v_imps ((s\<^sub>1,inst,exps),init_es)
  \<and> computes (instantiate_config s\<^sub>1 inst init_es) s\<^sub>2 []
  \<and> is_first_fun_idx exps i
  \<and> Some vs_params = (make_params s\<^sub>2 i vs_opt)
  \<and> computes (invoke_config s\<^sub>2 vs_params i) s' vs"  
    
(*
TODO: instantiate can trap, too! Missing abstract predicate for trapping instantiate!
definition "run_fuzz_abs_traps s m v_imps vs_opt s' \<equiv> \<exists>s\<^sub>1 s\<^sub>2 inst exps init_es i. 
    instantiate s m v_imps ((s\<^sub>1,inst,exps),init_es)
  \<and> (
        traps (instantiate_config s\<^sub>1 inst init_es) s\<^sub>2
    \<or>
        computes (instantiate_config s\<^sub>1 inst init_es) s\<^sub>2 []
      \<and> is_first_fun_idx exps i  
      \<and> traps (invoke_config s\<^sub>2 (make_params s\<^sub>2 i vs_opt) i) s
    )"
*)    
    
definition interp_get_v :: "s \<Rightarrow> inst \<Rightarrow> b_e list \<Rightarrow> v" where
  "interp_get_v s inst b_es = 
     (case run_v 2 0 (s,\<lparr> f_locs = [], f_inst = inst \<rparr>,b_es) of
        (_,RValue [v]) \<Rightarrow> v)"

definition interp_get_i32 :: "s \<Rightarrow> inst \<Rightarrow> b_e list \<Rightarrow> i32" where
  "interp_get_i32 s inst b_es = 
     (case interp_get_v s inst b_es of
        V_num (ConstInt32 c) \<Rightarrow> c
      | _ \<Rightarrow> 0)"

definition interp_get_v_ref :: "s \<Rightarrow> inst \<Rightarrow> b_e list \<Rightarrow> v_ref" where
  "interp_get_v_ref s inst b_es = 
     (case interp_get_v s inst b_es of
        V_ref v \<Rightarrow> v)"

definition interp_get_v_refs :: "s \<Rightarrow> inst \<Rightarrow> (b_e list) list \<Rightarrow> v_ref list" where
  "interp_get_v_refs s inst b_ess = map (interp_get_v_ref s inst) b_ess"

datatype res_inst =
    RI_crash res_error
  | RI_trap String.literal
  | RI_res inst "module_export list" "e list"

fun interp_instantiate :: "s \<Rightarrow> m \<Rightarrow> v_ext list \<Rightarrow> (s \<times> res_inst)" where
  "interp_instantiate s m v_imps =
     (case (module_type_checker m) of
        Some (t_imps, t_exps) \<Rightarrow>
          if (list_all2 (external_typing s) v_imps t_imps) then
            let inst_init_funcs = (ext_funcs v_imps)@[length (funcs s) ..< (length (funcs s) + length (m_funcs m))] in
            let inst_init = \<lparr>types=[],funcs=inst_init_funcs,tabs=[],mems=[],globs=ext_globs v_imps, elems=[], datas=[]\<rparr> in
            let g_inits = 
              map (\<lambda>g. interp_get_v s inst_init (g_init g)) (m_globs m) in
            let el_inits =
              map (\<lambda> el. interp_get_v_refs s inst_init (e_init el)) (m_elems m) in
            let (s', inst, v_exps) = interp_alloc_module s m v_imps g_inits el_inits in
            let start = (case (m_start m) of None \<Rightarrow> [] | Some i_s \<Rightarrow> [Invoke ((inst.funcs inst)!i_s)]) in
            (s', RI_res inst v_exps ((run_elems (m_elems m))@(run_datas (m_datas m))@start))
          else (s, RI_trap (STR ''invalid import''))
      | _ \<Rightarrow> (s, RI_trap (STR ''invalid module'')))"

lemma const_expr_is:
  assumes "const_expr \<C> b_e"
          "\<C> \<turnstile> [b_e] : (ts _> ts')"
        shows "\<exists>t. (\<C> \<turnstile> [b_e] : ([] _> [t])) \<and> ([] _> [t] <ti: ts _> ts') \<and> 
         ((\<exists>v. $b_e = ($C v) \<and> typeof v = t) \<or>
         (\<exists>j. b_e = (Global_get j) \<and> j < length (global \<C>) \<and>
              tg_mut ((global \<C>)!j) = T_immut \<and>
              tg_t ((global \<C>)!j) = t) \<or>
         (\<exists> j. b_e = (Ref_func j) \<and> (j < length (func_t \<C>)) \<and> t = T_ref T_func_ref) \<or>
         (\<exists> t_r. b_e = (Ref_null t_r) \<and> t = T_ref t_r) ) "
  using assms(2,1)
proof (induction "\<C>" "[b_e]" "(ts _> ts')" arbitrary: ts ts' rule: b_e_typing.induct)
  case (const_num \<C> v)
  then show ?case
    using b_e_typing.const_num const_expr.cases instr_subtyping_refl  typeof_num_def v_to_e_def typeof_def
    by (metis v.simps(10))
next
  case (const_vec \<C> v)
  then show ?case
    using b_e_typing.const_vec const_expr.cases typeof_vec_def v_to_e_def typeof_def instr_subtyping_refl
    by (fastforce split: v.splits v_vec.splits)
next
  case (ref_null \<C> t)
  then show ?case using b_e_typing.ref_null instr_subtyping_refl const_expr.cases by blast
next
  case (ref_func j \<C>)
  then show ?case using b_e_typing.ref_func instr_subtyping_refl const_expr.cases by blast
next
  case (global_get i \<C> t)
  then show ?case using b_e_type_global_get[OF b_e_typing.global_get[OF global_get(1,2)]]
    by (metis b_e.distinct(1529) b_e.distinct(1531) b_e.distinct(1543) b_e.distinct(1547) b_e_typing.global_get const_expr.cases)
next
  case (composition \<C> es t1s t2s e t3s)
  then obtain t where t_defs: "\<C> \<turnstile> [b_e] : [] _> [t]"
        "[] _> [t] <ti: t2s _> t3s"
        "e = b_e" "es = []"
    by (metis append1_eq_conv self_append_conv2)
  then show ?case
    using composition instr_subtyping_comp by blast
next
  case (subsumption \<C> tf1 tf2 tf1' tf2')
  then show ?case using instr_subtyping_trans by blast
qed (auto simp add: const_expr.simps)

lemma const_exprs_empty:
  assumes "const_exprs \<C> b_es"
          "\<C> \<turnstile> b_es : ([] _> [])"
        shows "b_es = []"
proof -
  have "\<And> ts ts'. \<C> \<turnstile> b_es : (ts _> ts') \<Longrightarrow> const_exprs \<C> b_es \<Longrightarrow> [] _> [] = ts _> ts' \<Longrightarrow> b_es = []"
  proof -
    fix ts ts'
    show "\<C> \<turnstile> b_es : (ts _> ts') \<Longrightarrow> const_exprs \<C> b_es \<Longrightarrow> [] _> [] = ts _> ts' \<Longrightarrow> b_es = []"
    proof(induction \<C> b_es "ts _> ts'" arbitrary: ts ts' rule: b_e_typing.induct)
      case (composition \<C> es t1s t2s e t3s)
      then show ?case
        using const_expr_is instr_subtyping_def t_list_subtyping_def by auto
    next
      case (subsumption \<C> es tf1 tf2 tf1' tf2')
      then show ?case
        using const_expr_is instr_subtyping_def t_list_subtyping_def by auto
    qed (auto simp add: const_expr.simps const_expr_is instr_subtyping_def t_list_subtyping_def)
  qed
  then show ?thesis
    using assms(1) assms(2) by blast
qed

lemma const_exprs_is:
  assumes "const_exprs \<C> b_es"
          "\<C> \<turnstile> b_es : ([] _> [t])"
  shows "((\<exists>v. $* b_es = [$C v] \<and> typeof v = t) \<or>
         (\<exists>j t'. t' <t: t \<and> b_es = [Global_get j] \<and> j < length (global \<C>) \<and>
              tg_mut ((global \<C>)!j) = T_immut \<and>
              tg_t ((global \<C>)!j) = t')  \<or>
         (\<exists> j. b_es = [Ref_func j] \<and> (j < length (func_t \<C>)) \<and> t = T_ref T_func_ref) \<or>
         (\<exists> t_r. b_es = [Ref_null t_r] \<and> t = T_ref t_r))"
proof -
  let ?goal = "((\<exists>v. $* b_es = [$C v] \<and> typeof v = t) \<or>
         (\<exists>j t'. t' <t: t \<and> b_es = [Global_get j] \<and> j < length (global \<C>) \<and>
              tg_mut ((global \<C>)!j) = T_immut \<and>
              tg_t ((global \<C>)!j) = t')  \<or>
         (\<exists> j. b_es = [Ref_func j] \<and> (j < length (func_t \<C>)) \<and> t = T_ref T_func_ref) \<or>
         (\<exists> t_r. b_es = [Ref_null t_r] \<and> t = T_ref t_r))"
  have "\<And> ts ts'. \<C> \<turnstile> b_es : (ts _> ts') \<Longrightarrow> const_exprs \<C> b_es \<Longrightarrow> [] _> [t] = ts _> ts' \<Longrightarrow> ?goal"
  proof -
    fix ts ts'
    show "\<C> \<turnstile> b_es : (ts _> ts') \<Longrightarrow> const_exprs \<C> b_es \<Longrightarrow> [] _> [t] = ts _> ts' \<Longrightarrow> ?goal"
    proof(induction \<C> b_es "ts _> ts'" arbitrary: ts ts' t rule: b_e_typing.induct)
      case (const_num \<C> v)
      then show ?case
        by (metis const_typeof_num to_e_list_1 typeof_def types_agree_imp_e_typing v.simps(10) v_to_e_def v_typing.simps) 
    next
      case (const_vec \<C> v)
      then show ?case using typeof_def typeof_vec_def v_to_e_def by (auto split: v.splits v_vec.splits)
    next
      case (ref_null \<C> t_ref t)
      then show ?case by blast
    next
      case (ref_func j \<C>)
      then show ?case by blast
    next
      case (global_get i \<C> t t')
      then show ?case
        using const_expr.cases t_subtyping_refl by auto
    next
      case (composition \<C> es t1s t2s e t3s)
      then have 1: "const_exprs \<C> [e]"
        by auto
      then obtain t'' where t''_def: "[] _> [t''] = t2s _> t3s" "t1s = []" "t'' <t: t"
        by (metis t_subtyping_def composition.hyps(3) composition.prems(2) const_expr_is instr_subtyping_append1 instr_subtyping_def list_all2_Nil list_all2_Nil2 list_all_simps(1) self_append_conv2 t_list_subtyping_def tf.sel(1) tf.sel(2))
      have 2: "const_expr \<C> e"
        using 1
        by simp
      
      show ?case
        using composition(4)[OF 1 t''_def(1)] t''_def(3)
        using const_exprs_empty local.composition(1) local.composition(5) local.composition(6) t''_def(1) by auto
    next
      case (subsumption \<C> es tf1 tf2 tf1' tf2')
      obtain t'' where t''_def: "tf2 = [t'']" "t'' <t: t" "[] _> [t''] = tf1 _> tf2"
        using subsumption(3,5)
        by (metis Nil_is_append_conv instr_subtyping_def list_all2_Cons2 list_all2_Nil list_all2_Nil2 self_append_conv2 t_list_subtyping_def tf.sel(1) tf.sel(2))
      consider
          (a) v where "$* es = [$C v] \<and> typeof v = t''"
        | (b) j t' where "t' <t: t'' \<and>
        es = [Global_get j] \<and> j < length (global \<C>) \<and> tg_mut (global \<C> ! j) = T_immut \<and> tg_t (global \<C> ! j) = t'"
        | (c) j where "es = [Ref_func j] \<and> j < length (func_t \<C>) \<and> t'' = T_ref T_func_ref"
        | (d) t_r where "es = [Ref_null t_r] \<and> t'' = T_ref t_r"
        using subsumption(2)[OF subsumption(4) t''_def(3)] by auto
      thus ?case
      proof(cases)
        case a
        then show ?thesis using subsumption(1)
          by (metis const_typeof e_typing_thread_typing.intros(1) e_typing_thread_typing.intros(3) subsumption.hyps(3) subsumption.prems(2))
      next
        case b
        then show ?thesis
          using t''_def(2) t_subtyping_trans by blast
      next
        case c
        then show ?thesis
          using t''_def(2) t_subtyping_def by auto
      next
        case d
        then show ?thesis
          using t''_def(2) t_subtyping_def by auto
      qed
    qed (auto simp add: const_expr.simps const_expr_is instr_subtyping_def t_list_subtyping_def)
  qed
  then show ?thesis
    using assms(1) assms(2) by metis
qed

lemma const_exprs_run_v:
  assumes "const_exprs \<C> b_es"
          "\<C> \<turnstile> b_es : ([] _> [t])"
          "global \<C> = tgs"
          "list_all2 (\<lambda>ig tg. external_typing s (Ext_glob ig) (Te_glob tg)) igs tgs"
          "inst.globs inst = igs@arb"
   shows "\<exists>v. typeof v = t \<and> run_v 2 0 (s, \<lparr> f_locs=[], f_inst=inst \<rparr>,b_es) = (s, RValue [v])"
proof -
  consider
      (1) v where "$* b_es = [$C v] \<and> typeof v = t"
    | (2) j t' where "t' <t: t"
                     "b_es = [Global_get j]"
                     "j < length (global \<C>)"
                     "tg_mut (global \<C> ! j) = T_immut"
                     "tg_t (global \<C> ! j) = t'"
   | (3) j where "b_es = [Ref_func j] \<and> j < length (func_t \<C>) \<and> t = T_ref T_func_ref"
   | (4) t_r where "b_es = [Ref_null t_r] \<and> t = T_ref t_r"
    using const_exprs_is[OF assms(1,2)]
    by auto
  thus ?thesis
  proof cases
    case 1
    thus ?thesis
      using v_to_e_def typeof_def
      apply (auto simp add: const_list_def is_const_def Suc_1[symmetric] split: v.splits v_num.splits)
      by  blast+
  next
    case 2
    then have "list_all2 (\<lambda>ig tg. external_typing s (Ext_glob ig) (Te_glob tg)) igs (global \<C>)"
      using assms(3) assms(4) by fastforce
    then have "external_typing s (Ext_glob (igs!j)) (Te_glob (global \<C>!j))"
      by (simp add: "2"(3) list_all2_conv_all_nth)
    then have "(igs!j) < length (globs s)" "glob_typing ((globs s)!(igs!j)) (global \<C>!j)"
      unfolding external_typing.simps
      by fastforce+
    then have "t' = typeof (g_val ((globs s)!(igs!j)))"
      using glob_typing_def "2"(5) by blast
    then have "t' = t"
      using 2(1) typeof_not_bot t_subtyping_def
      by simp
    thus ?thesis
      using 2 assms
      unfolding list_all2_conv_all_nth external_typing.simps
      by (auto simp add: Let_def const_list_def is_const_def Suc_1[symmetric] glob_typing_def nth_append sglob_def sglob_ind_def sglob_val_def app_s_f_v_s_global_get_def)
  next
    case 3
    then obtain v where "v = V_ref (ConstRefFunc (inst.funcs inst ! j))" "run_v 2 0 (s, \<lparr>f_locs = [], f_inst = inst\<rparr>, b_es) = (s, RValue [v])" "typeof v = T_ref T_func_ref"
      using app_f_v_s_ref_func_def typeof_def typeof_ref_def
      by (auto simp add: Let_def Suc_1[symmetric] split:   v_ref.splits)
    thus ?thesis using 3 by blast
  next
    case 4
    then obtain v where "v = V_ref (ConstNull t_r)" "run_v 2 0 (s, \<lparr>f_locs = [], f_inst = inst\<rparr>, b_es) = (s, RValue [v])" "typeof v = T_ref t_r"
      using app_v_s_ref_null_def typeof_def typeof_ref_def
      by (auto simp add: Let_def Suc_1[symmetric] split: prod.splits  v_ref.splits)
    thus ?thesis using 4 by blast
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
          "func_t \<C> = tfs"
          "length fis = length tfs"
          "inst.funcs (f_inst f) = fis@arbfi1"
          "inst.funcs inst_v = fis@arbfi2"
  shows "s_r = s' \<and> f = f' \<and> typeof v = t \<and> run_v 2 0 (s_v,\<lparr> f_locs=vs_arb, f_inst=inst_v\<rparr>,b_es) = (s_v, RValue [v])"
proof -
  consider
      (1) v' where "$* b_es = [$C v'] \<and> typeof v' = t"
    | (2) j t' where "t' <t: t"
                     "b_es = [Global_get j]"
                     "j < length (global \<C>)"
                     "tg_mut (global \<C> ! j) = T_immut"
                     "tg_t (global \<C> ! j) = t'"
   | (3) j where "b_es = [Ref_func j] \<and> j < length (func_t \<C>) \<and> t = T_ref T_func_ref"
   | (4) t_r where "b_es = [Ref_null t_r] \<and> t = T_ref t_r"
    using const_exprs_is[OF assms(1,2)]
    by auto
  thus ?thesis
  proof (cases)
    case 1
    consider (a) v_n where "b_es = [EConstNum v_n]" "v' = V_num v_n" | (b)  v_v where "b_es = [EConstVec v_v]" "v' = V_vec v_v"
      using 1 typeof_def v_to_e_def
      by (auto split: v_num.splits v.splits)
    thus ?thesis
    proof(cases)
      case a
      then show ?thesis
        using 1 assms(3)  reduce_trans_consts[of s_r f "[v']" s' f' "[v]"] v_to_e_def typeof_num_def
        by (simp add: Let_def const_list_def is_const_def Suc_1[symmetric])
    next
      case b
      then show ?thesis
        using 1 assms(3)  reduce_trans_consts[of s_r f "[v']" s' f' "[v]"] v_to_e_def typeof_num_def
        by (simp add: Let_def const_list_def is_const_def Suc_1[symmetric])
    qed
  next
    case 2
    have type_is:"typeof (sglob_val s (f_inst f) j) = t'" "j < length igs" "(igs!j) < length (globs s)" "t' = t"
      using assms(4,5,6,8) 2(1,2,3,4,5) typeof_not_bot t_subtyping_def
      unfolding list_all2_conv_all_nth external_typing.simps
      by (auto simp add: glob_typing_def nth_append sglob_def sglob_ind_def sglob_val_def)
    show ?thesis
      using assms(3)
      unfolding reduce_trans_def
    proof (cases rule: converse_rtranclpE)
      case base
      thus ?thesis
        using 2(2) v_to_e_def
        by (auto split: v.splits)
    next
      case (step y)
      then obtain s_y f_y es_y where y_is:"\<lparr>s_r;f;[$Global_get j]\<rparr> \<leadsto> \<lparr>s_y;f_y;es_y\<rparr>" "y = (s_y, f_y, es_y)"
        using 2
        by fastforce
      hence s_y_is:"s_y = s_r \<and> f_y = f \<and> es_y = [$C sglob_val s (f_inst f) j]"
        using assms(6,8)
      proof (induction s_r f "[$Global_get j]" s_y f_y es_y arbitrary: y rule: reduce.induct)
        case (basic e' s vs i)
        thus ?case
          using lfilled_single
          apply cases
          apply auto
          done
      next
        case (global_get s vs i)
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
        using step(2) y_is reduce_trans_consts[of s_y f_y "[sglob_val s (f_inst f) j]" s' f' "[v]"] 2 type_is s_y_is v_to_e_def assms(8)
        by (simp add: Let_def assms nth_append sglob_def sglob_ind_def sglob_val_def reduce_trans_def const_list_def is_const_def Suc_1[symmetric] app_s_f_v_s_global_get_def split: prod.splits v.splits)
    qed
  next
    case 3
    have c:  "j < length (inst.funcs (f_inst f))" "j < length (inst.funcs (inst_v))"
      using "3" assms(10,11,12,13)  list_all2_lengthD by fastforce+

    show ?thesis
      using assms(3) 
      unfolding reduce_trans_def
    proof (cases rule: converse_rtranclpE)
      case base
      then show ?thesis
        using 3 v_to_e_def
        by (auto split: v.splits)
    next
      case (step y)
      then obtain s_y f_y es_y where y_is:"\<lparr>s_r;f;[$Ref_func j]\<rparr> \<leadsto> \<lparr>s_y;f_y;es_y\<rparr>" "y = (s_y, f_y, es_y)"
        using 3
        by fastforce
      hence s_y_is:"s_y = s_r \<and> f_y = f \<and> es_y = [$C (V_ref (ConstRefFunc (inst.funcs (f_inst f) ! j)))]"
        using assms(6,8)
      proof (induction s_r f "[$Ref_func j]" s_y f_y es_y arbitrary: y rule: reduce.induct)
        case (basic e' s f)
        then show ?case
          using lfilled_single
          apply cases
          by auto
      next
        case (ref_func fa f s)
        then show ?case using v_to_e_def by simp
      next
        case (label s vs es i s' vs' es' k lholed les')
        thus ?case
          using lfilled_single[OF label(3)]
          by (metis Lfilled_exact.L0 Lfilled_exact_imp_Lfilled e.distinct(5) lfilled_eq reduce_not_nil)
      qed auto
      moreover have "s_r = s' \<and> f = f' \<and> v = V_ref (ConstRefFunc (inst.funcs (f_inst f) ! j))"
        using  step(1,2)
        s_y_is y_is  3 c split_vals_e_conv_app
        reduce_trans_consts[of s f "[(V_ref (ConstRefFunc (inst.funcs (f_inst f) ! j)))]" s_y f_y "[v]"]
        reduce_trans_consts[of s_r f "[(V_ref (ConstRefFunc (inst.funcs (f_inst f) ! j)))]" s' f']
        apply (auto simp add: Let_def assms nth_append reduce_trans_def  const_list_def is_const_def Suc_1[symmetric] app_f_v_s_ref_func_def  split: list.splits v_num.splits v_ref.splits  v.splits)
        apply (metis (no_types, lifting) Nil_is_map_conv list.simps(9))
        apply (metis (no_types, lifting) Nil_is_map_conv list.simps(9))
        by (metis (no_types, lifting) Nil_is_map_conv list.inject list.simps(9) local.step(2))
      ultimately show ?thesis
        using  step(1,2) v_to_e_def typeof_def typeof_ref_def 3
        apply (auto simp add: Let_def app_f_v_s_ref_func_def Suc_1[symmetric])
        using assms(10) assms(11) assms(12) assms(13) by (metis nth_append)
    qed
  next
    case 4
    show ?thesis
      using assms(3) 
      unfolding reduce_trans_def
    proof (cases rule: converse_rtranclpE)
      case base
      then show ?thesis
        using typeof_def typeof_ref_def v_to_e_def 4
        by (auto simp add: const_expr.simps const_expr.cases Let_def const_list_def is_const_def Suc_1[symmetric] app_v_s_ref_null_def split: v.splits t.splits t_ref.splits)
    next
      case (step y)
      then obtain s_y f_y es_y where y_is:"\<lparr>s_r;f;[$Ref_null t_r]\<rparr> \<leadsto> \<lparr>s_y;f_y;es_y\<rparr>" "y = (s_y, f_y, es_y)"
        using 4
        by fastforce
      hence s_y_is:"s_y = s_r \<and> f_y = f \<and> es_y = [$C (V_ref (ConstNull t_r))]"
        using assms(6,8)
      proof (induction s_r f "[$Ref_null t_r]" s_y f_y es_y arbitrary: y rule: reduce.induct)
        case (basic e' s f)
        then show ?case
          using lfilled_single v_to_e_def
          apply cases
          by auto
      next
        case (label s f es s' f' es' k lholed les')
        then show ?case
          by (metis Lfilled.L0 Nil_is_map_conv append_Nil2 e.distinct(5) eq_Nil_appendI lfilled_deterministic lfilled_single reduce_not_nil)
      qed auto
      moreover have "s_r = s' \<and> f = f' \<and> v = V_ref (ConstNull t_r)"
        by (metis (no_types, lifting) s_y_is append1_eq_conv list.simps(8) list.simps(9) local.step(2) reduce_trans_consts reduce_trans_def y_is(2))
      ultimately show ?thesis using 4 typeof_def typeof_ref_def
        by (auto simp add: Let_def app_v_s_ref_null_def Suc_1[symmetric])
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

lemma ext_funcs_ind:
  assumes "i<length (ext_funcs v_imps)"
  shows "\<exists>j. j < length v_imps \<and> Ext_func ((ext_funcs v_imps) ! i) = v_imps!j"
  using assms
proof (induction v_imps arbitrary: i)
case Nil
  thus ?case
    by (simp add: map_filter_simps(2))
next
  case (Cons v_imp v_imps)
  consider (1) k where "v_imp = Ext_func k" | (2) "\<And>k. v_imp \<noteq> Ext_func k"
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
      hence Suc1:"i' < length (ext_funcs (v_imps))"
        using 1 Cons(2)
        by (simp add: map_filter_def)
      thus ?thesis
        using Cons(1)[OF Suc1] Suc 1
        by (auto simp add: map_filter_def)
    qed
  next
    case 2
    hence a2:"ext_funcs v_imps = ext_funcs (v_imp#v_imps)"
      apply (cases v_imp)
      apply (simp_all add: map_filter_def)
      done
    hence b2:"i < length (ext_funcs (v_imps))"
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
    using alloc_glob_ext_typing[OF i_gs_is(2) Cons(2)] alloc_globs_range[OF i_gs_is(3)] list_all2_lengthD[OF Cons(1)]
          nth_append[of "s.globs s''"]
    unfolding external_typing.simps
    apply simp
    apply (metis length_append trans_less_add1)
    done
  thus ?case
    using alloc_glob_ext_typing[OF i_gs_is(2) Cons(2)] Cons(3)[OF i_gs_is(3)] i_gs_is(1)
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
  show ?case
    using Cons(2,1,3)
  proof (cases rule: external_typing.cases)
    case (4 i gt)
    thus ?thesis
      using Cons
      by (simp add: map_filter_def)
  qed (fastforce simp add: map_filter_def)+
qed

lemma list_all2_external_typing_funcs:
  assumes "list_all2 (\<lambda>i t. external_typing s i t) v_imps t_imps"
  shows "list_all2 (\<lambda>im_f tf. external_typing s (Ext_func im_f) (Te_func tf)) (ext_funcs v_imps) (ext_t_funcs t_imps)"
  using assms
proof (induction t_imps rule: list_all2_induct)
  case Nil
  thus ?case
    by (simp add: map_filter_simps(2))
next
  case (Cons x xs y ys)
  show ?case
    using Cons(2,1,3)
  proof (cases rule: external_typing.cases)
    case (1 i tf)
    then show ?thesis
      using Cons
      by (simp add: map_filter_def)
  qed (fastforce simp add: map_filter_def)+
qed

lemma alloc_module_ext_arb:
  assumes "alloc_module s m imps gvs els (s',inst,exps)"
  shows "\<exists>farbs tarbs marbs garbs elarbs darbs.
           (funcs s)@farbs = funcs s' \<and>
           (tabs s)@tarbs = tabs s' \<and>
           (mems s)@marbs = mems s' \<and>
           (globs s)@garbs = globs s' \<and>
           (elems s)@elarbs = elems s' \<and>
           (datas s)@darbs = datas s'"
proof -
  obtain s1 s2 s3 s4 s5 i_fs i_ts i_ms i_gs i_es i_ds where inst_is:
    "inst = \<lparr>types=(m_types m),
           funcs=(ext_funcs imps)@i_fs,
           tabs=(ext_tabs imps)@i_ts,
           mems=(ext_mems imps)@i_ms,
           globs=(ext_globs imps)@i_gs,
           elems=i_es,
           datas=i_ds\<rparr>"
    "alloc_funcs s (m_funcs m) inst = (s1,i_fs)"
    "alloc_tabs s1 (m_tabs m) = (s2,i_ts)"
    "alloc_mems s2 (m_mems m) = (s3,i_ms)"
    "alloc_globs s3 (m_globs m) gvs = (s4,i_gs)"
    "alloc_elems s4 (m_elems m) els = (s5,i_es)"
    "alloc_datas s5 (m_datas m) = (s',i_ds)"
    "exps = map (\<lambda>m_exp. \<lparr>E_name=(E_name m_exp), E_desc=(export_get_v_ext inst (E_desc m_exp))\<rparr>) (m_exports m)"
    using assms(1)
    unfolding alloc_module.simps
    by blast
  show ?thesis
    using alloc_funcs_range[OF inst_is(2)]
          alloc_tabs_range[OF inst_is(3)]
          alloc_mems_range[OF inst_is(4)]
          alloc_globs_range[OF inst_is(5)]
          alloc_elems_range[OF inst_is(6)]
          alloc_datas_range[OF inst_is(7)]
    by fastforce
qed

lemma alloc_module_external_typing_preserved:
  assumes "alloc_module s m imps gvs els (s',inst,exps)"
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

lemma alloc_func_typing:
  assumes
    "alloc_func s m_f inst = (s', i)"
    "module_func_typing \<C> m_f tf"
    "(types inst)!(fst m_f) = tf"
  shows "i = length (funcs s) \<and> cl_type (funcs s'!i) = tf"
proof(cases m_f)
  case (fields i_t t_locs b_es)
  then have "i_t < length (types_t \<C>)"
    using assms
    using module_func_typing.simps by auto
  have 1: "s' = s\<lparr>s.funcs := (funcs s)@[Func_native inst ((types inst)!i_t) t_locs b_es]\<rparr>" "i = length (funcs s)"
    using fields assms
    unfolding alloc_func_def
    by auto
  then have "((types inst)!i_t) = tf"
    using assms(3) fields by auto
  then have "cl_type (funcs s'!i) = tf" using 1 cl_type_def by auto
  then show ?thesis using 1 by auto
qed

lemma alloc_funcs_typing:
  assumes
    "alloc_funcs s m_fs inst = (s', i_fs)"
    "list_all2 (module_func_typing \<C>) m_fs tfs"
    "list_all2 (\<lambda> m_f tf. (types inst)!(fst m_f) = tf) m_fs tfs"
  shows "list_all2 (\<lambda> i tf. i < length (funcs s') \<and> cl_type (funcs s'!i) = tf) i_fs tfs"
  using assms
proof(induction m_fs arbitrary: s tfs s' i_fs)
  case Nil
  then show ?case by simp
next
  case (Cons m_f m_fs)
  obtain i_f' i_fs' tf' tfs' where i_tf_splits: "i_fs = i_f'#i_fs'" "tfs = tf'#tfs'"
    using length_alloc_Xs[OF Cons(2)] Cons(3)
    by (metis Suc_length_conv list_all2_lengthD)
  then obtain s'' where alloc_func_split:
    "alloc_func s m_f inst = (s'', i_f')"
    "alloc_funcs s'' m_fs inst = (s', i_fs')"
    using Cons.prems(1)
    by (auto split:prod.splits)
  have a: "module_func_typing \<C> m_f tf'"
    using Cons.prems(2) i_tf_splits(2) by blast 
  have b: "(types inst)!(fst m_f) = tf'"
    using Cons.prems(3) i_tf_splits(2) by blast
  have "i_f' < length (funcs s'') \<and> cl_type (funcs s''!i_f') = tf'"
    using alloc_func_typing[OF alloc_func_split(1) a b]
    using alloc_func_length(2) alloc_func_split(1) by auto
  then have "i_f' < length (funcs s') \<and> cl_type (funcs s'!i_f') = tf'"
    using alloc_funcs_range[OF alloc_func_split(2)]
    by (metis length_append nth_append trans_less_add1)
  moreover have "list_all2 (\<lambda> i tf. i < length (funcs s') \<and> cl_type (funcs s'!i) = tf) i_fs' tfs'"
    using Cons(1)[OF alloc_func_split(2)]
    using Cons.prems(2) Cons.prems(3) i_tf_splits(2) by blast
  ultimately show ?case using i_tf_splits
    by blast
qed

lemma interp_instantiate_imp_instantiate:
  assumes "(interp_instantiate s m v_imps = (s', RI_res inst v_exps init_es))"
  shows "(instantiate s m v_imps ((s', inst, v_exps), init_es))"
proof -
  obtain t_imps t_exps inst_init_funcs inst_init g_inits el_inits start  where s_end_is:
    "module_type_checker m = Some (t_imps, t_exps)"
    "(list_all2 (external_typing s) v_imps t_imps)"
    "inst_init_funcs = (ext_funcs v_imps)@[length (funcs s) ..< (length (funcs s) + length (m_funcs m))]"
    "inst_init = \<lparr>types=[],funcs=inst_init_funcs,tabs=[],mems=[],globs=ext_globs v_imps, elems=[], datas=[]\<rparr>"
    "g_inits = map (\<lambda>g. interp_get_v s inst_init (g_init g)) (m_globs m)"
    "el_inits = map (\<lambda> el. interp_get_v_refs s inst_init (e_init el)) (m_elems m)"
    "(s', inst, v_exps) = interp_alloc_module s m v_imps g_inits el_inits"
    "start = (case (m_start m) of None \<Rightarrow> [] | Some i_s \<Rightarrow> [Invoke ((inst.funcs inst)!i_s)])"
    "init_es = ((run_elems (m_elems m))@(run_datas (m_datas m))@start)"
    using assms
    by (fastforce simp add: Let_def split: if_splits option.splits prod.splits)

  have 1:"module_typing m t_imps t_exps"
    using s_end_is(1) module_type_checker_imp_module_typing
    by blast
  have 2:"alloc_module s m v_imps g_inits el_inits (s', inst, v_exps)"
    using s_end_is(7) interp_alloc_module_imp_alloc_module
    by metis

  obtain fs fts ts ms gs gts els rts ds dts i_opt imps exps tfs ifts itts imts igts \<C> \<C>' where m_is:
    "list_all2 (module_func_typing \<C>) fs fts"
    "list_all (module_tab_typing) ts"
    "list_all (module_mem_typing) ms"
    "list_all2 (module_glob_typing \<C>') gs gts"
    "list_all2 (module_elem_typing \<C>') els rts"
    "list_all (module_data_typing \<C>') ds"
    "length dts = length ds"
    "pred_option (module_start_typing \<C>) i_opt"
    "list_all2 (\<lambda>imp. module_import_typing \<C> (I_desc imp)) imps t_imps"
    "list_all2 (\<lambda>exp. module_export_typing \<C> (E_desc exp)) exps t_exps"
    "ifts = ext_t_funcs t_imps"
    "itts = ext_t_tabs t_imps"
    "imts = ext_t_mems t_imps"
    "igts = ext_t_globs t_imps"
    "\<C> = \<lparr>types_t=tfs,
       func_t=ifts@fts,
       global=igts@gts,
       elem=rts,
       data=dts,
       table=itts@ts,
       memory=imts@ms,
       local=[],
       label=[],
       return=None,
       refs=collect_funcidxs_module (m\<lparr>m_funcs := [], m_start := None\<rparr>)\<rparr>"
    "\<C>' = \<C>\<lparr>global := igts\<rparr>"
    "m = \<lparr>m_types = tfs,
          m_funcs = fs,
          m_tabs = ts,
          m_mems = ms,
          m_globs = gs,
          m_elems = els,
          m_datas = ds,
          m_start = i_opt,
          m_imports = imps,
          m_exports = exps\<rparr>"
    using 1
    unfolding module_typing.simps
    by blast

  obtain s1 s2 s3 s4 s5 i_fs i_ts i_ms i_gs i_es i_ds where inst_is:
    "inst = \<lparr>types=(m_types m),
           funcs=(ext_funcs v_imps)@i_fs,
           tabs=(ext_tabs v_imps)@i_ts,
           mems=(ext_mems v_imps)@i_ms,
           globs=(ext_globs v_imps)@i_gs,
           elems=i_es,
           datas=i_ds\<rparr>"
    "alloc_funcs s (m_funcs m) inst = (s1,i_fs)"
    "alloc_tabs s1 (m_tabs m) = (s2,i_ts)"
    "alloc_mems s2 (m_mems m) = (s3,i_ms)"
    "alloc_globs s3 (m_globs m) g_inits = (s4,i_gs)"
    "alloc_elems s4 (m_elems m) el_inits = (s5, i_es)"
    "alloc_datas s5 (m_datas m) = (s', i_ds)"
    "v_exps = map (\<lambda>m_exp. \<lparr>E_name=(E_name m_exp), E_desc=(export_get_v_ext inst (E_desc m_exp))\<rparr>) (m_exports m)"
    using 2
    unfolding alloc_module.simps
    by blast

  have 12:"list_all2 (\<lambda>ig tg. external_typing s (Ext_glob ig) (Te_glob tg)) (inst.globs inst_init) (global \<C>')"
    using s_end_is(2,4) m_is(14,16) ext_globs_ind list_all2_external_typing_glob_alloc
    by simp
  have 11:"list_all2 (\<lambda>ig tg. external_typing s' (Ext_glob ig) (Te_glob tg)) (inst.globs inst) (global \<C>)"
  proof -
    have "list_all2 (\<lambda>ig tg. external_typing s' (Ext_glob ig) (Te_glob tg)) (inst.globs inst_init) (global \<C>')"
      using alloc_module_external_typing_preserved[OF 2] 12
      unfolding list_all2_conv_all_nth
      by fastforce
    moreover
    have 111:"list_all2 (\<lambda>v m_g. typeof v = tg_t (g_type m_g)) g_inits (m_globs m)"
      using s_end_is(5)[symmetric] g_init_type_interp[OF _ _ _ 12, of inst_init _ _ \<C>' _ "[]"] m_is(4,17)
      by (auto simp add: list_all2_conv_all_nth)
    have "(gather_m_g_types (m_globs m)) = gts"
      using m_is(4,17)
      unfolding list_all2_conv_all_nth module_glob_typing.simps
      apply simp
      apply (metis length_map module_glob.select_convs(1) nth_equalityI nth_map)
      done
    hence "list_all2 (\<lambda>ig tg. external_typing s' (Ext_glob ig) (Te_glob tg)) i_gs gts"
      using alloc_globs_ext_typing[OF inst_is(5) 111]
      using alloc_datas_range alloc_elems_range external_typing.simps inst_is(6) inst_is(7) by fastforce
    ultimately
    show ?thesis
      using list_all2_appendI
      by (fastforce simp add: m_is inst_is(1) s_end_is)
  qed

  have 13: "length ((ext_funcs v_imps)@[length (funcs s) ..< (length (funcs s) + length (m_funcs m))]) = length (ifts@fts)"
  proof -
    have "length ((ext_funcs v_imps)) = length (ifts)"
      using list_all2_external_typing_funcs list_all2_lengthD m_is(11) s_end_is(2) by blast
    moreover
    have "length ([length (funcs s) ..< (length (funcs s) + length (m_funcs m))]) = length (fts)"
      using list_all2_conv_all_nth m_is(1) m_is(17) by auto
    ultimately show ?thesis by auto
  qed
  have fs_prop1: "func_t \<C>' = ifts@fts"
    using m_is(15,16)
    by auto
  have fs_prop2: "inst.funcs inst_init = ext_funcs v_imps @ [length (s.funcs s)..<length (s.funcs s) + length (m_funcs m)]"
    by (simp add: s_end_is(3) s_end_is(4))
  then have fs_prop3: "inst.funcs inst = ext_funcs v_imps @ [length (s.funcs s)..<length (s.funcs s) + length (m_funcs m)]"
    using inst_is alloc_funcs_range by fastforce

  obtain arbg arbi where arbgi:"(globs s)@arbg = (globs s')"
                                   "inst.globs inst = inst.globs inst_init @ arbi"
      using alloc_module_ext_arb[OF 2] 2 s_end_is(4)
      unfolding alloc_module.simps
      by auto

  have 3:"list_all2 (\<lambda>g v. reduce_trans (s',\<lparr> f_locs=[], f_inst=inst \<rparr>,$*(g_init g)) (s',\<lparr> f_locs=[], f_inst=inst \<rparr>,[$C v])) (m_globs m) g_inits"
  proof -
    { fix i
      assume local_assms:"length (m_globs m) = length g_inits" "i<length (m_globs m)"
      hence l1:"const_exprs \<C>' (g_init (m_globs m ! i))"
        using m_is(4,17)
        unfolding list_all2_conv_all_nth module_glob_typing.simps
        by auto
      obtain t where l2:"\<C>' \<turnstile> (g_init (m_globs m ! i)) : ([] _> [t])"
        using local_assms m_is(4,17)
        unfolding list_all2_conv_all_nth module_glob_typing.simps
        by auto
      obtain v_r where v_r_def: "run_v 2 0 (s, \<lparr> f_locs=[], f_inst=inst_init \<rparr>, (g_init (m_globs m ! i))) =  (s, RValue [v_r])"
        using const_exprs_run_v[OF l1 l2 _ 12, of inst_init]
        by auto
      hence a_runv:"run_v 2 0 (s,\<lparr> f_locs=[], f_inst=inst_init\<rparr>,(g_init ((m_globs m)!i))) = (s,RValue [(g_inits!i)])"
        using s_end_is(5) local_assms
        by (simp add: interp_get_v_def split: v.splits)
      obtain f_temp where f_temp_is:
        "reduce_trans (s, \<lparr>f_locs = [], f_inst = inst_init\<rparr>, $* g_init (m_globs m ! i)) (s, f_temp, $C* [g_inits ! i])"
        using run_v_sound[OF a_runv]
        by fastforce
      hence l3:"reduce_trans (s,\<lparr> f_locs=[], f_inst=inst_init \<rparr>,$*(g_init ((m_globs m)!i))) (s,\<lparr> f_locs=[], f_inst=inst_init \<rparr>,[$C (g_inits!i)])"
        using reduce_trans_length_locals[OF f_temp_is] reduce_trans_inst_is[OF f_temp_is]
        apply simp
        apply (metis (full_types) f.surjective unit.exhaust)
        done

      have run_v_is:"run_v 2 0 (s', \<lparr> f_locs=[], f_inst=inst \<rparr>, g_init (m_globs m ! i)) = (s', RValue [g_inits ! i])"
        using const_exprs_reduce_trans[OF l1 l2 l3 _ 12  _ arbgi(1)[symmetric] _ arbgi(2)  fs_prop1 13] fs_prop2 fs_prop3
        by auto
        
      obtain f_temp where  "reduce_trans (s',\<lparr> f_locs=[], f_inst=inst \<rparr>,$*(g_init ((m_globs m)!i))) (s',f_temp,[$C (g_inits!i)])"
        using run_v_sound[OF run_v_is]
        by auto
      hence "reduce_trans (s',\<lparr> f_locs=[], f_inst=inst \<rparr>,$*(g_init ((m_globs m)!i))) (s',\<lparr> f_locs=[], f_inst=inst \<rparr>,[$C (g_inits!i)])"
        using reduce_trans_length_locals reduce_trans_inst_is
        by (metis (full_types) f.select_convs(1) f.surjective length_greater_0_conv unit.exhaust)
    }
    thus ?thesis
      using s_end_is(5)
      unfolding list_all2_conv_all_nth
      by fastforce
  qed

  have 4: "list_all2
     (\<lambda>m_el el_init. list_all2
            (\<lambda>el_init v.
                reduce_trans (s', \<lparr>f_locs = [], f_inst = inst\<rparr>, $* el_init) (s', \<lparr>f_locs = [], f_inst = inst\<rparr>, [$C V_ref v]))
            (e_init m_el) el_init)
     (m_elems m) el_inits"
  proof -
    { fix i j
      assume assms: "i < length (m_elems m)" "j < length (e_init (m_elems m!i))"
      
      obtain m_el where m_el_def: "m_el = m_elems m!i" by simp
      hence l1:"const_exprs \<C>' (e_init m_el!j)"
        using m_is(5,17)
        unfolding list_all2_conv_all_nth module_elem_typing.simps assms
        by (metis assms(1) assms(2) list_all_length m.select_convs(6) module_elem.select_convs(2))
      obtain tr where l2:"\<C>' \<turnstile> (e_init m_el!j) : ([] _> [T_ref tr])"
        using assms  m_is(5,17)
        unfolding list_all2_conv_all_nth module_elem_typing.simps
        by (metis m_el_def list_all_length m.select_convs(6) module_elem.select_convs(2))
      obtain v_r where v_r_def: "run_v 2 0 (s, \<lparr> f_locs=[], f_inst=inst_init \<rparr>, (e_init m_el!j)) =  (s, RValue [v_r])"
        using const_exprs_run_v[OF l1 l2 _ 12, of inst_init]
        by auto
      have "el_inits!i!j = interp_get_v_ref s inst_init ((e_init (m_elems m!i))!j)"
        using s_end_is(6) interp_get_v_refs_def
        assms(1,2) by simp
      then have a_runv:"run_v 2 0 (s,\<lparr> f_locs=[], f_inst=inst_init\<rparr>,((e_init m_el!j))) = (s,RValue [V_ref (el_inits!i!j)])"
        using s_end_is(6) assms(1,2) m_el_def v_r_def typeof_def const_exprs_run_v[OF l1 l2 _ 12, of inst_init]
        by (auto simp add: interp_get_v_refs_def interp_get_v_ref_def interp_get_v_def split:  config.splits  v.splits)
      obtain f_temp where f_temp_is:
        "reduce_trans (s, \<lparr>f_locs = [], f_inst = inst_init\<rparr>, $* ((e_init m_el!j))) (s, f_temp, $C* [V_ref (el_inits!i!j)])"
        using run_v_sound[OF a_runv]
        by fastforce
      hence l3:"reduce_trans (s,\<lparr> f_locs=[], f_inst=inst_init \<rparr>,$*((e_init m_el!j))) (s,\<lparr> f_locs=[], f_inst=inst_init \<rparr>,[$C (V_ref (el_inits!i!j))])"
        using reduce_trans_length_locals[OF f_temp_is] reduce_trans_inst_is[OF f_temp_is]
        apply simp
        apply (metis (full_types) f.surjective unit.exhaust)
        done
 
      have run_v_is:"run_v 2 0 (s', \<lparr> f_locs=[], f_inst=inst \<rparr>, ((e_init m_el!j))) = (s', RValue [V_ref (el_inits!i!j)])"
        using const_exprs_reduce_trans[OF l1 l2 l3 _ 12  _ arbgi(1)[symmetric] _ arbgi(2)  fs_prop1 13] fs_prop2 fs_prop3
        by auto
        
      obtain f_temp where  "reduce_trans (s',\<lparr> f_locs=[], f_inst=inst \<rparr>,$*((e_init m_el!j))) (s',f_temp,[$C (V_ref (el_inits!i!j))])"
        using run_v_sound[OF run_v_is]
        by auto
      hence "reduce_trans (s',\<lparr> f_locs=[], f_inst=inst \<rparr>,$*((e_init m_el!j))) (s',\<lparr> f_locs=[], f_inst=inst \<rparr>,[$C (V_ref (el_inits!i!j))])"
        using reduce_trans_length_locals reduce_trans_inst_is
        by (metis (full_types) f.select_convs(1) f.surjective length_greater_0_conv unit.exhaust)
      hence "reduce_trans (s',\<lparr> f_locs=[], f_inst=inst \<rparr>,$*(((e_init ((m_elems m)!i)))!j)) (s',\<lparr> f_locs=[], f_inst=inst \<rparr>,[$C V_ref ((el_inits!i)!j)])"
        using m_el_def by fastforce
    }
    then show ?thesis using s_end_is(6)
      unfolding list_all2_conv_all_nth
      by (simp add: interp_get_v_refs_def)
  qed

  show ?thesis
    using instantiate.intros[OF 1 s_end_is(2) 2 _ 3 4 s_end_is(8)[symmetric]] s_end_is(9)
    by simp
qed

lemma map_intro_length:
  assumes "\<And>i. i < length ls \<Longrightarrow> F (ls!i) = fls!i"
          "length ls = length fls"
  shows "map F ls = fls"
  using assms
  by (metis length_map nth_equalityI nth_map)

lemma instantiate_imp_interp_instantiate:
  assumes "(instantiate s m v_imps ((s', inst, v_exps), init_es))"
  shows "(interp_instantiate s m v_imps = (s', RI_res inst v_exps init_es))"
proof -
  obtain fs ts ms gs els ds i_opt imps exps tfs where m_is:
    "m = \<lparr>m_types = tfs,
          m_funcs = fs,
          m_tabs = ts,
          m_mems = ms,
          m_globs = gs,
          m_elems = els,
          m_datas = ds,
          m_start = i_opt,
          m_imports = imps,
          m_exports = exps\<rparr>"
    using m.cases
    by blast
  obtain inst_init inst_init_funcs where inst_init_is:
    "inst_init = \<lparr>types=[],funcs=inst_init_funcs,tabs=[],mems=[],globs=ext_globs v_imps, elems=[], datas=[]\<rparr>"
    "inst_init_funcs = (ext_funcs v_imps)@[length (funcs s) ..< (length (funcs s) + length (m_funcs m))]"
    using inst.cases
    by blast

  obtain t_imps t_exps g_inits el_inits f start where s_end_is:
    "module_typing m t_imps t_exps"
    "list_all2 (external_typing s) v_imps t_imps"
    "alloc_module s m v_imps g_inits el_inits (s', inst, v_exps)"
    "list_all2 (\<lambda>g v. reduce_trans (s',f,$*(g_init g)) (s',f,[$C v])) gs g_inits"
    "list_all2 (\<lambda>el vs. list_all2 (\<lambda> el_init v. reduce_trans (s',f,$*(el_init)) (s',f,[$C (V_ref v)])) (e_init el) vs) els el_inits"
    "(case (m_start m) of None \<Rightarrow> [] | Some i_s \<Rightarrow> [Invoke ((inst.funcs inst)!i_s)]) = start"
    "f = \<lparr> f_locs=[], f_inst=inst \<rparr>"
    "init_es = (run_elems (m_elems m))@(run_datas (m_datas m))@start"
    using assms m_is
    unfolding instantiate.simps
    by fastforce

  obtain fts gts rts dts ifts itts imts igts \<C> \<C>' where m_is_2:
    "list_all2 (module_func_typing \<C>) fs fts"
    "list_all (module_tab_typing) ts"
    "list_all (module_mem_typing) ms"
    "list_all2 (module_glob_typing \<C>') gs gts"
    "list_all2 (module_elem_typing \<C>') els rts"
    "list_all (module_data_typing \<C>') ds"
    "length dts = length ds"
    "pred_option (module_start_typing \<C>) i_opt"
    "list_all2 (\<lambda>imp. module_import_typing \<C> (I_desc imp)) imps t_imps"
    "list_all2 (\<lambda>exp. module_export_typing \<C> (E_desc exp)) exps t_exps"
    "ifts = ext_t_funcs t_imps"
    "itts = ext_t_tabs t_imps"
    "imts = ext_t_mems t_imps"
    "igts = ext_t_globs t_imps"
    "\<C> = \<lparr>types_t=tfs, func_t=ifts@fts, global=igts@gts, elem=rts, data=dts, table=itts@ts, memory=imts@ms, local=[], label=[], return=None,
       refs=collect_funcidxs_module (m\<lparr>m_funcs := [], m_start := None\<rparr>)\<rparr>"
    "\<C>' = \<C>\<lparr>global := igts\<rparr>"
    using s_end_is(1) m_is
    unfolding module_typing.simps
    by blast

  obtain s1 s2 s3 s4 s5 i_fs i_ts i_ms i_gs i_es i_ds where inst_is:
    "inst = \<lparr>types=(m_types m),
           funcs=(ext_funcs v_imps)@i_fs,
           tabs=(ext_tabs v_imps)@i_ts,
           mems=(ext_mems v_imps)@i_ms,
           globs=(ext_globs v_imps)@i_gs,
           elems=i_es,
           datas=i_ds\<rparr>"
    "alloc_funcs s fs inst = (s1,i_fs)"
    "alloc_tabs s1 ts = (s2,i_ts)"
    "alloc_mems s2 ms = (s3,i_ms)"
    "alloc_globs s3 gs g_inits = (s4,i_gs)"
    "alloc_elems s4 (m_elems m) el_inits = (s5, i_es)"
    "alloc_datas s5 (m_datas m) = (s', i_ds)"
    "v_exps = map (\<lambda>m_exp. \<lparr>E_name=(E_name m_exp), E_desc=(export_get_v_ext inst (E_desc m_exp))\<rparr>) (m_exports m)"
    using s_end_is(3) m_is
    unfolding alloc_module.simps
    by fastforce



  have fs_prop1: "func_t \<C>' = ifts@fts"
    by (simp add: m_is_2(15) m_is_2(16))
  have fs_prop2: "inst.funcs inst_init = ext_funcs v_imps @ [length (s.funcs s)..<length (s.funcs s) + length (m_funcs m)]"
    by (simp add: inst_init_is(1) inst_init_is(2))
  then have fs_prop3: "inst.funcs inst = ext_funcs v_imps @ [length (s.funcs s)..<length (s.funcs s) + length (m_funcs m)]"
    using inst_is inst_init_is alloc_funcs_range
    by (simp add: m_is)

  have 13: "length ((ext_funcs v_imps)@[length (funcs s) ..< (length (funcs s) + length (m_funcs m))]) = length (ifts@fts)"
  proof -
    have "length ((ext_funcs v_imps)) = length (ifts)"
      using list_all2_external_typing_funcs list_all2_lengthD m_is_2(11) s_end_is(2) by blast
    moreover
    have "length ([length (funcs s) ..< (length (funcs s) + length (m_funcs m))]) = length (fts)"
      using list_all2_lengthD m_is m_is_2(1) by auto
    ultimately show ?thesis by auto
  qed
  
  obtain arbg arbi where arbgi:"(globs s)@arbg = (globs s')"
                                "inst.globs inst = inst.globs inst_init @ arbi"
                               "inst.globs (f_inst f) = inst.globs inst_init @ arbi"
      using alloc_module_ext_arb[OF s_end_is(3)]
      unfolding alloc_module.simps
      using inst_init_is(1) inst_is(1) s_end_is(7) by auto

  have 12:"list_all2 (\<lambda>ig tg. external_typing s (Ext_glob ig) (Te_glob tg)) (inst.globs inst_init) (global \<C>')"
    using ext_globs_ind list_all2_external_typing_glob_alloc
    by (simp add: inst_init_is m_is_2(14,16) s_end_is(2))
  have 11:"list_all2 (\<lambda>ig tg. external_typing s' (Ext_glob ig) (Te_glob tg)) (inst.globs inst) (global \<C>)"
  proof -
    have "list_all2 (\<lambda>ig tg. external_typing s' (Ext_glob ig) (Te_glob tg)) (inst.globs inst_init) (global \<C>')"
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

        obtain arbg arbi where arbgi:"(globs s)@arbg = (globs s')"
                                   "inst.globs inst = inst.globs inst_init @ arbi"
          using alloc_module_ext_arb[OF s_end_is(3)]  s_end_is(3,4)
          unfolding alloc_module.simps
          using inst_init_is(1) by fastforce
        have "typeof (g_inits!i) = tg_t (g_type (gs!i))"
          using local_assms const_exprs_reduce_trans[OF l2(2,1) l1 _ 12 arbgi(1)[symmetric] arbgi(1)[symmetric] _ _ fs_prop1 13] fs_prop2 fs_prop3
              alloc_module_ext_arb[OF s_end_is(3)] s_end_is(4)
          unfolding alloc_module.simps
          apply simp
          by (metis append_Nil2 arbgi(2) f.select_convs(2) s_end_is(7))
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
      using alloc_globs_ext_typing[OF inst_is(5) 111] alloc_elems_range[OF inst_is(6)] alloc_datas_range[OF inst_is(7)]
        external_typing.simps by auto
    ultimately
    show ?thesis
      using list_all2_appendI inst_init_is
      by (fastforce simp add: m_is_2(15,16) inst_is(1) s_end_is(8))
  qed

  have "(module_type_checker m) = Some (t_imps, t_exps)"
    using s_end_is(1) module_typing_equiv_module_type_checker
    by blast
  moreover
  have "g_inits = map (\<lambda>g. interp_get_v s inst_init (g_init g)) gs"
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
  
      have "run_v 2 0 (s,\<lparr> f_locs=[], f_inst=inst_init \<rparr>,(g_init (gs!i))) = (s,RValue [g_inits!i])"
        using const_exprs_reduce_trans[OF l2(2,1) l1 _ 12 arbgi(1)[symmetric] _ arbgi(3)  _ fs_prop1 13] fs_prop2 fs_prop3
              alloc_module_ext_arb[OF s_end_is(3)] s_end_is(3) s_end_is(7)
        unfolding alloc_module.simps
        using inst_init_is
        by (simp split: prod.splits del: run_v.simps)
      hence "interp_get_v s inst_init (g_init (gs!i)) = g_inits!i"
        unfolding interp_get_v_def
        by fastforce
    }
    thus ?thesis
      using map_intro_length[symmetric, of gs "(\<lambda>g. interp_get_v s inst_init (g_init g))" g_inits]
            list_all2_lengthD[OF s_end_is(4)]
      by fastforce
  qed
  moreover
  have "interp_alloc_module s m v_imps g_inits el_inits = (s', inst, v_exps)"
    using s_end_is(3) alloc_module_equiv_interp_alloc_module
    by blast
  moreover
  have "el_inits = map (\<lambda> el. interp_get_v_refs s inst_init (e_init el)) els"
  proof -
    { fix i
      assume local_assms1: "i < length els"
      
      have "interp_get_v_refs s inst_init (e_init (els ! i)) = el_inits ! i"
      proof -
        { fix j
          assume local_assms2: "j < length (e_init (els!i))"
          obtain tr where l2:"\<C>' \<turnstile> (e_init (els ! i))!j : ([] _> [T_ref tr])"
                            "const_exprs \<C>' ((e_init (els ! i))!j)"
            using local_assms1 local_assms2  m_is_2(5,15,16)
            unfolding list_all2_conv_all_nth  module_elem_typing.simps
            by (metis list_all_length module_elem.select_convs(2))
          have l1:"reduce_trans (s',f,$*((e_init (els ! i))!j)) (s',f,[$C (V_ref (el_inits!i!j))])"
            using s_end_is(5) local_assms1 local_assms2
            unfolding list_all2_conv_all_nth
            by blast
          obtain arbg arbi where arbgi:"(globs s)@arbg = (globs s')"
                                       "inst.globs inst = inst.globs inst_init @ arbi"
                                       "inst.globs (f_inst f) = inst.globs inst_init @ arbi"
              using alloc_module_ext_arb[OF s_end_is(3)]  s_end_is(3,4) inst_init_is(1) inst_is(1)
              unfolding alloc_module.simps
              using inst_init_is(1)
              using s_end_is(7) by fastforce
          obtain arbf where arbf_def: "funcs s' = funcs s@arbf"
            by (metis s_end_is(3) alloc_module_ext_arb)
          have "run_v 2 0 (s,\<lparr> f_locs=[], f_inst=inst_init \<rparr>,((e_init (els ! i))!j)) = (s,RValue [V_ref (el_inits!i!j)])"
            using const_exprs_reduce_trans[OF l2(2,1) l1 _ 12 arbgi(1)[symmetric] _ arbgi(3)  _ fs_prop1 13] fs_prop2 fs_prop3
                  alloc_module_ext_arb[OF s_end_is(3)] s_end_is(3) s_end_is(7)
            unfolding alloc_module.simps
            using inst_init_is
            by (simp split: prod.splits del: run_v.simps)

          hence "interp_get_v_ref s inst_init ((e_init (els ! i))!j) = el_inits ! i ! j"
            unfolding interp_get_v_ref_def interp_get_v_def
            using const_exprs_run_v[OF l2(2,1) _ 12, of inst_init "[]"]
            by(auto split: v.splits) 
        }
        then show ?thesis using map_intro_length[symmetric, of "(e_init (els ! i))" "interp_get_v_ref s inst_init" "el_inits ! i" ]
          by (metis (no_types, lifting) interp_get_v_refs_def list_all2_conv_all_nth local_assms1 s_end_is(5)) 
      qed
    }
    thus ?thesis
      using map_intro_length[symmetric, of els "(\<lambda>el. interp_get_v_refs s inst_init (e_init el))" el_inits]
            list_all2_lengthD[OF s_end_is(5)]
      by fastforce
  qed
  ultimately show ?thesis using s_end_is m_is inst_init_is
    by (auto simp add: Let_def)
qed

theorem instantiate_equiv_interp_instantiate:
  "(instantiate s m v_imps ((s', inst, v_exps), init_es)) = (interp_instantiate s m v_imps = (s', RI_res inst v_exps init_es))"
  using instantiate_imp_interp_instantiate interp_instantiate_imp_instantiate
  by blast

definition interp_instantiate_init :: "s \<Rightarrow> m \<Rightarrow> v_ext list \<Rightarrow> (s \<times> res_inst)" where
  "interp_instantiate_init s m v_imps = (case (interp_instantiate s m v_imps) of
                                       (s', RI_res inst v_exps init_es) \<Rightarrow>
                                         (case (run_instantiate (2^63) 300 (s', inst, init_es)) of
                                           (s'', RCrash r) \<Rightarrow> (s'', RI_crash r)
                                         | (s'', RTrap r) \<Rightarrow> (s'', RI_trap r)
                                         | (s'', RValue []) \<Rightarrow> (s'', RI_res inst v_exps [])
                                         | (s'', RValue (x#xs)) \<Rightarrow> (s'', RI_crash (Error_invalid (STR ''start function''))))
                                     | x \<Rightarrow> x)"
                                     
                                     
(* TODO: Naming should be run_fuzz, and run_fuzz_m for the monadic version. 
  But name run_fuzz fixed for code-export, so not changing it now! *)
definition run_fuzz' :: "fuel \<Rightarrow> depth \<Rightarrow> s \<Rightarrow> m \<Rightarrow> v_ext list \<Rightarrow> (v list) option \<Rightarrow> (s \<times> res)" where
  "run_fuzz' n d s m v_imps opt_vs = (let
   i_res = interp_instantiate_init s m v_imps in
   case i_res of
     (s', RI_res inst v_exps init_es) \<Rightarrow>
     (case (List.find (\<lambda>exp. case (E_desc exp) of Ext_func i \<Rightarrow> True | _ \<Rightarrow> False) v_exps) of
        Some exp \<Rightarrow> (case (E_desc exp) of Ext_func i \<Rightarrow> (
                       case make_params s' i opt_vs of
                          Some params \<Rightarrow>  run_invoke_v n d (s', params, i)
                       |  None \<Rightarrow> (s', RCrash (Error_invariant (STR ''could not make parameters for a function with given type signature'')))))
      | None \<Rightarrow> (s', RCrash (Error_invariant (STR ''no import to invoke''))))
  | (s', RI_crash res) \<Rightarrow> (s', RCrash res)
  | (s', RI_trap msg) \<Rightarrow> (s', RTrap msg))"

definition run_fuzz_entry' :: "fuel \<Rightarrow> m \<Rightarrow> (v list) option \<Rightarrow> s \<times> res" where
  "run_fuzz_entry' n m vs_opt = run_fuzz' n 300 empty_store m [] vs_opt"
                                     
end