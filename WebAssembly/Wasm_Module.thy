theory Wasm_Module imports Wasm begin

record module_glob =
  g_type :: tg
  g_init :: "b_e list"

record module_elem =
  e_tab :: i
  e_off :: "b_e list"
  e_init :: "i list"

record module_data =
  d_data :: i
  d_off :: "b_e list"
  d_init :: "byte list"

type_synonym module_func = \<comment> \<open>function\<close>
  "i \<times> t list \<times> b_e list"

datatype imp_desc =
  Imp_func i
| Imp_tab tab_t
| Imp_mem mem_t
| Imp_glob tg

datatype v_ext =
  Ext_func i
| Ext_tab i
| Ext_mem i
| Ext_glob i

type_synonym exp_desc = v_ext

record module_import =
  I_module :: String.literal
  I_name :: String.literal
  I_desc :: imp_desc

record module_export =
  E_name :: String.literal
  E_desc :: exp_desc

datatype extern_t =
  Te_func tf
| Te_tab tab_t
| Te_mem mem_t
| Te_glob tg

definition export_get_v_ext :: "inst \<Rightarrow> exp_desc \<Rightarrow> v_ext" where
  "export_get_v_ext inst exp =
     (case exp of
        Ext_func i \<Rightarrow> Ext_func ((inst.funcs inst)!i)
      | Ext_tab i \<Rightarrow> Ext_tab ((inst.tabs inst)!i)
      | Ext_mem i \<Rightarrow> Ext_mem ((inst.mems inst)!i)
      | Ext_glob i \<Rightarrow> Ext_glob ((inst.globs inst)!i))"

abbreviation "ext_funcs \<equiv> List.map_filter (\<lambda>x. case x of Ext_func i \<Rightarrow> Some i | _ \<Rightarrow> None)"
abbreviation "ext_tabs \<equiv> List.map_filter (\<lambda>x. case x of Ext_tab i \<Rightarrow> Some i | _ \<Rightarrow> None)" 
abbreviation "ext_mems \<equiv> List.map_filter (\<lambda>x. case x of Ext_mem i \<Rightarrow> Some i | _ \<Rightarrow> None)" 
abbreviation "ext_globs \<equiv> List.map_filter (\<lambda>x. case x of Ext_glob i \<Rightarrow> Some i | _ \<Rightarrow> None)"

abbreviation "ext_t_funcs \<equiv> List.map_filter (\<lambda>x. case x of Te_func tf \<Rightarrow> Some tf | _ \<Rightarrow> None)"
abbreviation "ext_t_tabs \<equiv> List.map_filter (\<lambda>x. case x of Te_tab t \<Rightarrow> Some t | _ \<Rightarrow> None)" 
abbreviation "ext_t_mems \<equiv> List.map_filter (\<lambda>x. case x of Te_mem m \<Rightarrow> Some m | _ \<Rightarrow> None)" 
abbreviation "ext_t_globs \<equiv> List.map_filter (\<lambda>x. case x of Te_glob g \<Rightarrow> Some g | _ \<Rightarrow> None)" 

inductive const_expr :: "t_context \<Rightarrow> b_e \<Rightarrow> bool" where \<comment> \<open>constant expression\<close>
  "const_expr \<C> (C v)"
| "\<lbrakk>k < length (global \<C>); tg_mut ((global \<C>)!k) = T_immut \<rbrakk> \<Longrightarrow> const_expr \<C> (Get_global k)"

code_pred (modes: i \<Rightarrow> i \<Rightarrow> bool as const_expr_p) const_expr .

abbreviation "const_exprs \<C> es \<equiv> list_all (const_expr \<C>) es"

inductive limit_typing :: "limit_t \<Rightarrow> nat \<Rightarrow> bool" where
  "\<lbrakk>k \<le> 2^32; n \<le> k; pred_option (\<lambda>m. m \<le> k) m_opt; pred_option (\<lambda>m. n \<le> m) m_opt\<rbrakk>
     \<Longrightarrow> limit_typing \<lparr>l_min = n, l_max = m_opt\<rparr> k"

inductive module_func_typing :: "t_context \<Rightarrow> module_func \<Rightarrow> tf \<Rightarrow> bool" where
  "\<lbrakk>i < length (types_t \<C>);
    (types_t \<C>)!i = (tn _> tm);
    \<C>\<lparr>local := tn @ t_locs, label := ([tm] @ (label \<C>)), return := Some tm\<rparr> \<turnstile> b_es : ([] _> tm)\<rbrakk>
     \<Longrightarrow> module_func_typing \<C> (i, t_locs, b_es) (tn _> tm)"

abbreviation "module_tab_typing t \<equiv> limit_typing t (2^32)"
abbreviation "module_mem_typing t \<equiv> limit_typing t (2^16)"

inductive module_glob_typing :: "t_context \<Rightarrow> module_glob \<Rightarrow> tg \<Rightarrow> bool" where
  "\<lbrakk>const_exprs \<C> es; \<C> \<turnstile> es : ([] _> [tg_t tg])\<rbrakk> \<Longrightarrow> module_glob_typing \<C> \<lparr>g_type=tg, g_init=es\<rparr> tg"

inductive module_elem_typing :: "t_context \<Rightarrow> module_elem \<Rightarrow> bool" where
  "\<lbrakk>const_exprs \<C> es;
    \<C> \<turnstile> es : ([] _> [T_i32]);
    t < length (table \<C>);
    list_all (\<lambda>i. i < length (func_t \<C>)) is\<rbrakk> \<Longrightarrow> module_elem_typing \<C> \<lparr>e_tab=t, e_off=es, e_init=is\<rparr>"

inductive module_data_typing :: "t_context \<Rightarrow> module_data \<Rightarrow> bool" where
  "\<lbrakk>const_exprs \<C> es;
    \<C> \<turnstile> es : ([] _> [T_i32]);
    d < length (memory \<C>)\<rbrakk> \<Longrightarrow> module_data_typing \<C> \<lparr>d_data=d, d_off=es, d_init=bs\<rparr>"

inductive module_start_typing :: "t_context \<Rightarrow> i \<Rightarrow> bool" where
  "\<lbrakk>i < length (func_t \<C>); (func_t \<C>)!i = ([] _> [])\<rbrakk> \<Longrightarrow> module_start_typing \<C> i"

abbreviation "module_exports_distinct exps \<equiv> List.distinct (List.map E_name exps)"

inductive module_import_typing :: "t_context \<Rightarrow> imp_desc \<Rightarrow> extern_t \<Rightarrow> bool" where
  "\<lbrakk>i < length (types_t \<C>); (types_t \<C>)!i = tf\<rbrakk> \<Longrightarrow> module_import_typing \<C> (Imp_func i) (Te_func tf)"
| "\<lbrakk>module_tab_typing tt\<rbrakk> \<Longrightarrow> module_import_typing \<C> (Imp_tab tt) (Te_tab tt)"
| "\<lbrakk>module_mem_typing mt\<rbrakk> \<Longrightarrow> module_import_typing \<C> (Imp_mem mt) (Te_mem mt)"
| "module_import_typing \<C> (Imp_glob gt) (Te_glob gt)"

inductive module_export_typing :: "t_context \<Rightarrow> exp_desc \<Rightarrow> extern_t \<Rightarrow> bool" where
  "\<lbrakk>i < length (func_t \<C>); (func_t \<C>)!i = tf\<rbrakk> \<Longrightarrow> module_export_typing \<C> (Ext_func i) (Te_func tf)"
| "\<lbrakk>i < length (table \<C>); (table \<C>)!i = tt\<rbrakk> \<Longrightarrow> module_export_typing \<C> (Ext_tab i) (Te_tab tt)"
| "\<lbrakk>i < length (memory \<C>); (memory \<C>)!i = mt\<rbrakk> \<Longrightarrow> module_export_typing \<C> (Ext_mem i) (Te_mem mt)"
| "\<lbrakk>i < length (global \<C>); (global \<C>)!i = gt\<rbrakk> \<Longrightarrow> module_export_typing \<C> (Ext_glob i) (Te_glob gt)"

inductive external_typing :: "s \<Rightarrow> v_ext \<Rightarrow> extern_t \<Rightarrow> bool" where
  "\<lbrakk>i < length (funcs s); cl_type ((funcs s)!i) = tf\<rbrakk> \<Longrightarrow> external_typing s (Ext_func i) (Te_func tf)"
| "\<lbrakk>i < length (tabs s); tab_typing ((tabs s)!i) tt\<rbrakk> \<Longrightarrow> external_typing s (Ext_tab i) (Te_tab tt)"
| "\<lbrakk>i < length (mems s); mem_typing ((mems s)!i) mt\<rbrakk> \<Longrightarrow> external_typing s (Ext_mem i) (Te_mem mt)"
| "\<lbrakk>i < length (globs s); glob_typing ((globs s)!i) gt\<rbrakk> \<Longrightarrow> external_typing s (Ext_glob i) (Te_glob gt)"

record m = \<comment> \<open>module\<close>
  m_types :: "tf list"
  m_funcs :: "module_func list"
  m_tabs :: "tab_t list"
  m_mems :: "mem_t list"
  m_globs :: "module_glob list"
  m_elem :: "module_elem list"
  m_data :: "module_data list"
  m_start :: "i option"
  m_imports :: "module_import list"
  m_exports :: "module_export list"

inductive module_typing :: "m \<Rightarrow> extern_t list \<Rightarrow> extern_t list \<Rightarrow> bool" where
"\<lbrakk>list_all (\<lambda>tf. case tf of (tn _> tm) \<Rightarrow> length tm \<le> 1) tfs; \<comment> \<open>\<open>MVP restriction\<close>\<close>
  list_all2 (module_func_typing \<C>) fs fts;
  list_all (module_tab_typing) ts;
  list_all (module_mem_typing) ms;
  list_all2 (module_glob_typing \<C>') gs gts;
  list_all (module_elem_typing \<C>) els;
  list_all (module_data_typing \<C>) ds;
  pred_option (module_start_typing \<C>) i_opt;
  module_exports_distinct exps;
  list_all2 (\<lambda>imp. module_import_typing \<C> (I_desc imp)) imps impts;
  list_all2 (\<lambda>exp. module_export_typing \<C> (E_desc exp)) exps expts;
  ifts = ext_t_funcs impts;
  its = ext_t_tabs impts;
  ims = ext_t_mems impts;
  igs = ext_t_globs impts;
  length (its@ts) \<le> 1; \<comment> \<open>\<open>MVP restriction\<close>\<close>
  length (ims@ms) \<le> 1; \<comment> \<open>\<open>MVP restriction\<close>\<close>
  \<C> = \<lparr>types_t=tfs, func_t=ifts@fts, global=igs@gts, table=its@ts, memory=ims@ms, local=[], label=[], return=None\<rparr>;
  \<C>' = \<lparr>types_t=[], func_t=[], global=igs, table=[], memory=[], local=[], label=[], return=None\<rparr>\<rbrakk>
  \<Longrightarrow> module_typing \<lparr>m_types = tfs,
                     m_funcs = fs,
                     m_tabs = ts,
                     m_mems = ms,
                     m_globs = gs,
                     m_elem = els,
                     m_data = ds,
                     m_start = i_opt,
                     m_imports = imps,
                     m_exports = exps\<rparr> impts expts"

end