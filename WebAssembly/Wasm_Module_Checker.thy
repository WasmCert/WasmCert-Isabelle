theory Wasm_Module_Checker imports Wasm_Module Wasm_Checker_Properties begin

code_pred (modes: i \<Rightarrow> i \<Rightarrow> bool as limit_type_checker_p) limit_typing .

fun module_func_type_checker :: "t_context \<Rightarrow> module_func \<Rightarrow> bool" where
"module_func_type_checker \<C> (i, t_locs, b_es) =
  ((i < length (types_t \<C>)) \<and>
     (case (types_t \<C>)!i of
       (tn _> tm) \<Rightarrow>
         b_e_type_checker (\<C>\<lparr>local := tn @ t_locs, label := ([tm] @ (label \<C>)), return := Some tm\<rparr>) b_es ([] _> tm)))"

lemma module_func_typing_equiv_module_func_type_checker:
  "module_func_typing \<C> m_f tf = (module_func_type_checker \<C> m_f \<and>
                                   ((types_t \<C>)!(fst m_f) = tf))"
  apply (cases m_f)
  apply (auto simp add: module_func_typing.simps b_e_typing_equiv_b_e_type_checker split: tf.splits)
  done

abbreviation "module_tab_type_checker \<equiv> module_tab_typing"
abbreviation "module_mem_type_checker \<equiv> module_mem_typing"

fun module_glob_type_checker :: "t_context \<Rightarrow> module_glob \<Rightarrow> bool" where
  "module_glob_type_checker \<C> \<lparr>g_type=tg, g_init=es\<rparr> =
     (const_exprs \<C> es \<and> b_e_type_checker \<C> es ([] _> [tg_t tg]))"

lemma module_glob_typing_equiv_module_glob_type_checker:
  "module_glob_typing \<C> m_g tg = (module_glob_type_checker \<C> m_g \<and>
                                   (module_glob.g_type m_g) = tg)"
  apply (cases m_g)
  apply (auto simp add: module_glob_typing.simps b_e_typing_equiv_b_e_type_checker)
  done

fun module_elem_type_checker :: "t_context \<Rightarrow> module_elem \<Rightarrow> bool" where
  "module_elem_type_checker \<C> \<lparr>e_tab=t, e_off=es, e_init=is\<rparr> =
     (const_exprs \<C> es \<and> b_e_type_checker \<C> es ([] _> [T_i32]) \<and> t < length (table \<C>) \<and> list_all (\<lambda>i. i < length (func_t \<C>)) is)"

lemma module_elem_typing_equiv_module_elem_type_checker:
  "module_elem_typing \<C> m_e = module_elem_type_checker \<C> m_e"
  apply (cases m_e)
  apply (auto simp add: module_elem_typing.simps b_e_typing_equiv_b_e_type_checker)
  done

fun module_data_type_checker :: "t_context \<Rightarrow> module_data \<Rightarrow> bool" where
  "module_data_type_checker \<C> \<lparr>d_data=d, d_off=es, d_init=bs\<rparr> =
     (const_exprs \<C> es \<and> b_e_type_checker \<C> es ([] _> [T_i32]) \<and> d < length (memory \<C>))"

lemma module_data_typing_equiv_module_data_type_checker:
  "module_data_typing \<C> m_e = module_data_type_checker \<C> m_e"
  apply (cases m_e)
  apply (auto simp add: module_data_typing.simps b_e_typing_equiv_b_e_type_checker)
  done

code_pred (modes: i \<Rightarrow> i \<Rightarrow> bool as module_start_type_checker_p) module_start_typing .

abbreviation "module_start_type_checker \<equiv> module_start_typing"

fun module_import_typer :: "tf list \<Rightarrow> imp_desc \<Rightarrow> extern_t option" where
  "module_import_typer tfs (Imp_func i) = (if i < length tfs then Some (Te_func (tfs!i)) else None)"
| "module_import_typer tfs (Imp_tab tt) = (if module_tab_typing tt then Some (Te_tab tt) else None)"
| "module_import_typer tfs (Imp_mem mt) = (if module_mem_typing mt then Some (Te_mem mt) else None)"
| "module_import_typer tfs (Imp_glob gt) =  Some (Te_glob gt)"

lemma module_import_typing_equiv_module_import_typer:
  "(module_import_typing \<C> imp e_t) = (module_import_typer (types_t \<C>) imp = Some e_t)"
  apply (cases imp)
  apply (auto simp add: module_import_typing.simps)
  done

fun module_export_typer :: "t_context \<Rightarrow> exp_desc \<Rightarrow> extern_t option" where
  "module_export_typer \<C> (Ext_func i) = (if i < length (func_t \<C>) then Some (Te_func ((func_t \<C>)!i)) else None)"
| "module_export_typer \<C> (Ext_tab i) = (if i < length (table \<C>) then Some (Te_tab ((table \<C>)!i)) else None)"
| "module_export_typer \<C> (Ext_mem i) = (if i < length (memory \<C>) then Some (Te_mem ((memory \<C>)!i)) else None)"
| "module_export_typer \<C> (Ext_glob i) = (if i < length (global \<C>) then Some (Te_glob ((global \<C>)!i)) else None)"

lemma module_export_typing_equiv_module_export_typer:
  "(module_export_typing \<C> exp e_t) = (module_export_typer \<C> exp = Some e_t)"
  apply (cases exp)
  apply (auto simp add: module_export_typing.simps)
  done

abbreviation "module_imports_typer tfs imps \<equiv> List.those (List.map (\<lambda>imp. module_import_typer tfs (I_desc imp)) imps)"
abbreviation "module_exports_typer \<C> exps \<equiv> List.those (List.map (\<lambda>exp. module_export_typer \<C> (E_desc exp)) exps)"

lemma list_all2_module_imports_typer:
  "list_all2 (\<lambda>imp. module_import_typing \<C> (I_desc imp)) imps impts = (module_imports_typer (types_t \<C>) imps = Some impts)"
proof (induction imps arbitrary:impts)
  case Nil
  thus ?case
    by auto
next
  case (Cons imp imps)
  thus ?case
  proof (cases impts)
    case Nil
    thus ?thesis
      by (simp split: option.splits)
  next
    case (Cons impt impts')
    thus ?thesis
      using module_import_typing_equiv_module_import_typer[of \<C> "(I_desc imp)" impt]
            Cons.IH
      by (auto split: option.splits)
  qed
qed

lemma list_all2_module_exports_typer:
  "list_all2 (\<lambda>exp. module_export_typing \<C> (E_desc exp)) exps expts = (module_exports_typer \<C> exps = Some expts)"
proof (induction exps arbitrary:expts)
  case Nil
  thus ?case
    by auto
next
  case (Cons exp exps)
  thus ?case
  proof (cases expts)
    case Nil
    thus ?thesis
      by (simp split: option.splits)
  next
    case (Cons expt expts')
    thus ?thesis
      using module_export_typing_equiv_module_export_typer[of \<C> "(E_desc exp)" expt]
            Cons.IH
      by (auto split: option.splits)
  qed
qed

definition gather_m_f_type :: "tf list \<Rightarrow> module_func \<Rightarrow> tf option" where
  "gather_m_f_type tfs m_f \<equiv> if (fst m_f < length tfs) then Some (tfs!(fst m_f)) else None"

abbreviation gather_m_f_types :: "tf list \<Rightarrow> module_func list \<Rightarrow> (tf list) option" where
  "gather_m_f_types tfs m_fs \<equiv> List.those (List.map (gather_m_f_type tfs) m_fs)"

lemma module_func_typing_imp_gather_m_f_type:
  assumes "module_func_typing \<C> fs ft"
  shows "gather_m_f_type (types_t \<C>) fs = Some ft"
  using assms
  unfolding module_func_typing.simps gather_m_f_type_def
  by (auto split: if_splits)

lemma module_func_typing_imp_gather_m_f_types:
  assumes "list_all2 (module_func_typing \<C>) fs fts"
  shows "gather_m_f_types (types_t \<C>) fs = Some fts"
  using assms
proof (induction fs arbitrary: fts)
  case Nil
  thus ?case
    by auto
next
  case (Cons a fs)
  thus ?case
    using module_func_typing_imp_gather_m_f_type
    unfolding list_all2_Cons1
    by fastforce
qed

lemma gather_m_f_types_length:
  assumes "gather_m_f_types (types_t \<C>) fs = Some fts"
  shows "length fs = length fts"
  using assms
proof (induction fs arbitrary: fts)
case Nil
  thus ?case
    by simp
next
  case (Cons a fs)
  thus ?case
    by (auto split: option.splits)
qed

lemma gather_m_f_type_imp_module_func_typing:
  assumes "gather_m_f_type (types_t \<C>) f = Some ft"
          "module_func_type_checker \<C> f"
  shows "module_func_typing \<C> f ft"
  using assms
  unfolding gather_m_f_type_def
  by (simp add: module_func_typing_equiv_module_func_type_checker split: if_splits)

lemma gather_m_f_types_imp_module_func_typing:
  assumes "gather_m_f_types (types_t \<C>) fs = Some fts"
          "list_all (module_func_type_checker \<C>) fs"
  shows "list_all2 (module_func_typing \<C>) fs fts"
  using assms
proof (induction fs arbitrary: fts)
  case Nil
  thus ?case
    by simp
next
  case (Cons f fs')
  note outer_Cons = Cons
  show ?case
  proof (cases fts)
    case Nil
    thus ?thesis
      using Cons(2)
      by (simp split: option.splits)
  next
    case (Cons ft fts')
    thus ?thesis
      using outer_Cons gather_m_f_type_imp_module_func_typing
      by (auto split: option.splits)
  qed
qed

abbreviation gather_m_g_types :: "module_glob list \<Rightarrow> tg list" where
  "gather_m_g_types \<equiv> map module_glob.g_type"

fun module_type_checker :: "m \<Rightarrow> (extern_t list \<times> extern_t list) option" where
  "module_type_checker \<lparr>m_types = tfs,
                        m_funcs = fs,
                        m_tabs = ts,
                        m_mems = ms,
                        m_globs = gs,
                        m_elem = els,
                        m_data = ds,
                        m_start = i_opt,
                        m_imports = imps,
                        m_exports = exps\<rparr> =
  (case (gather_m_f_types tfs fs, module_imports_typer tfs imps) of
     (Some fts, Some impts) \<Rightarrow>
       let ifts = ext_t_funcs impts in
       let its = ext_t_tabs impts in
       let ims = ext_t_mems impts in
       let igs = ext_t_globs impts in
       let gts = gather_m_g_types gs in
       let \<C> = \<lparr>types_t=tfs, func_t=ifts@fts, global=igs@gts, table=its@ts, memory=ims@ms, local=[], label=[], return=None\<rparr> in
       let \<C>' = \<lparr>types_t=[], func_t=[], global=igs, table=[], memory=[], local=[], label=[], return=None\<rparr> in
       if (list_all (\<lambda>tf. case tf of (tn _> tm) \<Rightarrow> length tm \<le> 1) tfs \<and> \<comment> \<open>\<open>MVP restriction\<close>\<close>
           list_all (module_func_type_checker \<C>) fs \<and>
           list_all (module_tab_type_checker) ts \<and>
           list_all (module_mem_type_checker) ms \<and>
           list_all (module_glob_type_checker \<C>') gs \<and>
           list_all (module_elem_type_checker \<C>) els \<and>
           list_all (module_data_type_checker \<C>) ds \<and>
           pred_option (module_start_type_checker \<C>) i_opt \<and>
           module_exports_distinct exps \<and>
         length (its@ts) \<le> 1 \<and> \<comment> \<open>\<open>MVP restriction\<close>\<close>
         length (ims@ms) \<le> 1   \<comment> \<open>\<open>MVP restriction\<close>\<close>) then
         case (module_exports_typer \<C> exps) of
           Some expts \<Rightarrow> Some (impts, expts)
         | _ \<Rightarrow> None
       else None
     | _ \<Rightarrow> None
  )"

lemma module_typing_imp_module_type_checker:
  assumes "module_typing m impts expts"
  shows "module_type_checker m = Some (impts, expts)"
proof -
  obtain tfs fs ts ms gs els ds i_opt imps exps where m_def:
    "m =\<lparr>m_types = tfs,
         m_funcs = fs,
         m_tabs = ts,
         m_mems = ms,
         m_globs = gs,
         m_elem = els,
         m_data = ds,
         m_start = i_opt,
         m_imports = imps,
         m_exports = exps\<rparr>"
    using module_type_checker.cases
    by blast
  obtain \<C> \<C>' fts gts ifts its ims igs where module_typing_is:
    "list_all (\<lambda>tf. case tf of (tn _> tm) \<Rightarrow> length tm \<le> 1) tfs"
    "list_all2 (module_func_typing \<C>) fs fts"
    "list_all (module_tab_typing) ts"
    "list_all (module_mem_typing) ms"
    "list_all2 (module_glob_typing \<C>') gs gts"
    "list_all (module_elem_typing \<C>) els"
    "list_all (module_data_typing \<C>) ds"
    "pred_option (module_start_typing \<C>) i_opt"
    "list_all2 (\<lambda>imp. module_import_typing \<C> (I_desc imp)) imps impts"
    "list_all2 (\<lambda>exp. module_export_typing \<C> (E_desc exp)) exps expts"
    "ifts = ext_t_funcs impts"
    "its = ext_t_tabs impts"
    "ims = ext_t_mems impts"
    "igs = ext_t_globs impts"
    "module_exports_distinct exps"
    "length (its@ts) \<le> 1"
    "length (ims@ms) \<le> 1"
    "\<C> = \<lparr>types_t=tfs, func_t=ifts@fts, global=igs@gts, table=its@ts, memory=ims@ms, local=[], label=[], return=None\<rparr>"
    "\<C>' = \<lparr>types_t=[], func_t=[], global=igs, table=[], memory=[], local=[], label=[], return=None\<rparr>"
    using assms
    unfolding m_def
    apply (simp only: module_typing.simps)
    apply blast
    done

  have "gather_m_f_types tfs fs = Some fts"
    using module_typing_is(2,18) module_func_typing_imp_gather_m_f_types
    by fastforce
  moreover
  have "gather_m_g_types gs = gts"
    using module_typing_is(5)
    unfolding list_all2_conv_all_nth module_glob_typing.simps
    by (metis length_map module_glob.select_convs(1) nth_equalityI nth_map)
  moreover
  have "module_imports_typer tfs imps = Some impts"
    using module_typing_is(9)
    by (simp add: list_all2_module_imports_typer module_typing_is(18))
  moreover
  have "module_exports_typer \<C> exps = Some expts"
    using module_typing_is(10)
    by (simp add: list_all2_module_exports_typer)
  moreover
  have "list_all (module_func_type_checker \<C>) fs"
       "list_all (module_tab_type_checker) ts"
       "list_all (module_mem_type_checker) ms"
       "list_all (module_glob_type_checker \<C>') gs"
       "list_all (module_elem_type_checker \<C>) els"
       "list_all (module_data_type_checker \<C>) ds"
       "pred_option (module_start_type_checker \<C>) i_opt"
       "module_exports_distinct exps"
    using module_typing_is(2-8,15)
          module_func_typing_equiv_module_func_type_checker
          module_glob_typing_equiv_module_glob_type_checker
          module_elem_typing_equiv_module_elem_type_checker
          module_data_typing_equiv_module_data_type_checker
    by (simp_all add: list_all2_conv_all_nth list_all_length)
  ultimately
  show ?thesis
    using module_typing_is
    unfolding m_def
    by simp
qed

lemma module_type_checker_imp_module_typing:
  assumes "module_type_checker m = Some (impts, expts)"
  shows "module_typing m impts expts"
proof -
  obtain tfs fs ts ms gs els ds i_opt imps exps where m_def:
    "m =\<lparr>m_types = tfs,
         m_funcs = fs,
         m_tabs = ts,
         m_mems = ms,
         m_globs = gs,
         m_elem = els,
         m_data = ds,
         m_start = i_opt,
         m_imports = imps,
         m_exports = exps\<rparr>"
    using module_type_checker.cases
    by blast
  obtain fts ifts its ims igs gts \<C> \<C>' where module_type_checker_is:
    "gather_m_f_types tfs fs = Some fts"
    "module_imports_typer tfs imps = Some impts"
    "ifts = ext_t_funcs impts"
    "its = ext_t_tabs impts"
    "ims = ext_t_mems impts"
    "igs = ext_t_globs impts"
    "gts = gather_m_g_types gs"
    "\<C> = \<lparr>types_t=tfs, func_t=ifts@fts, global=igs@gts, table=its@ts, memory=ims@ms, local=[], label=[], return=None\<rparr>"
    "\<C>' = \<lparr>types_t=[], func_t=[], global=igs, table=[], memory=[], local=[], label=[], return=None\<rparr>"
    "list_all (\<lambda>tf. case tf of (tn _> tm) \<Rightarrow> length tm \<le> 1) tfs"
    "list_all (module_func_type_checker \<C>) fs"
    "list_all (module_tab_type_checker) ts"
    "list_all (module_mem_type_checker) ms"
    "list_all (module_glob_type_checker \<C>') gs"
    "list_all (module_elem_type_checker \<C>) els"
    "list_all (module_data_type_checker \<C>) ds"
    "pred_option (module_start_type_checker \<C>) i_opt"
    "module_exports_distinct exps"
    "length (its@ts) \<le> 1"
    "length (ims@ms) \<le> 1"
    "module_exports_typer \<C> exps = Some expts"
    using assms m_def
    by (simp add: Let_def split: option.splits if_splits)
  have "list_all2 (module_func_typing \<C>) fs fts"
    using gather_m_f_types_imp_module_func_typing
          module_type_checker_is(1,8,11)
    by fastforce
  moreover
  have "list_all (module_tab_typing) ts"
       "list_all (module_mem_typing) ms"
       "list_all2 (module_glob_typing \<C>') gs gts"
       "list_all (module_elem_typing \<C>) els"
       "list_all (module_data_typing \<C>) ds"
       "pred_option (module_start_typing \<C>) i_opt"
    using module_type_checker_is
          module_glob_typing_equiv_module_glob_type_checker
          module_elem_typing_equiv_module_elem_type_checker
          module_data_typing_equiv_module_data_type_checker
    by (simp_all add: list_all2_conv_all_nth list_all_length)
  moreover
  have "list_all2 (\<lambda>imp. module_import_typing \<C> (I_desc imp)) imps impts"
    using list_all2_module_imports_typer[symmetric]
          module_type_checker_is(2,8)
    by fastforce
  moreover
  have "list_all2 (\<lambda>exp. module_export_typing \<C> (E_desc exp)) exps expts"
    using list_all2_module_exports_typer[symmetric]
          module_type_checker_is(21,8)
    by fastforce
  ultimately
  show ?thesis
    using m_def module_type_checker_is
    by (fastforce simp add: module_typing.simps)
qed

theorem module_typing_equiv_module_type_checker:
  "module_typing m impts expts = (module_type_checker m = Some (impts, expts))"
  using module_typing_imp_module_type_checker
        module_type_checker_imp_module_typing
  by blast

(*
lemma[code]: "pred_option P None = True"
  by auto
lemmas[code] = option.pred_inject(2)


export_code module_type_checker in OCaml
module_name Example file_prefix "example.ml"
*)
end