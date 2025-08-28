theory Wasm_Module imports Wasm begin

record module_glob =
  g_type :: tg
  g_init :: "b_e list"

datatype elem_mode =
  Em_passive
| Em_active i "(b_e list)"
| Em_declarative

record module_elem =
  e_type :: t_ref
  e_init :: "(b_e list) list"
  e_mode :: elem_mode

datatype data_mode =
  Dm_passive
| Dm_active i "(b_e list)"

record module_data =
  d_init :: "bytes"
  d_mode :: data_mode

type_synonym module_func = \<comment> \<open>function\<close>
  "i \<times> t list \<times> b_e list"

datatype imp_desc =
  Imp_func i
| Imp_tab tab_t
| Imp_mem mem_t
| Imp_glob tg

datatype v_ext =
  Ext_func (the_idx: i)
| Ext_tab (the_idx: i)
| Ext_mem (the_idx: i)
| Ext_glob (the_idx: i)
hide_const (open) v_ext.the_idx

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
  "const_expr \<C> (EConstNum v_n)"
| "const_expr \<C> (EConstVec v_v)"
| "const_expr \<C> (Ref_func x)"
| "const_expr \<C> (Ref_null t_r)"
| "\<lbrakk>k < length (global \<C>); tg_mut ((global \<C>)!k) = T_immut \<rbrakk> \<Longrightarrow> const_expr \<C> (Global_get k)"

code_pred (modes: i \<Rightarrow> i \<Rightarrow> bool as const_expr_p) const_expr .

abbreviation "const_exprs \<C> es \<equiv> list_all (const_expr \<C>) es"

inductive limit_typing :: "limit_t \<Rightarrow> nat \<Rightarrow> bool" where
  "\<lbrakk>k \<le> 2^32; n \<le> k; pred_option (\<lambda>m. m \<le> k) m_opt; pred_option (\<lambda>m. n \<le> m) m_opt\<rbrakk>
     \<Longrightarrow> limit_typing \<lparr>l_min = n, l_max = m_opt\<rparr> k"

inductive module_func_typing :: "t_context \<Rightarrow> module_func \<Rightarrow> tf \<Rightarrow> bool" where
  "\<lbrakk>i < length (types_t \<C>);
    (types_t \<C>)!i = (tn _> tm);
    \<C>\<lparr>local := tn @ t_locs, label := ([tm] @ (label \<C>)), return := Some tm\<rparr> \<turnstile> b_es : ([] _> tm);
    n_zeros t_locs \<noteq> None\<rbrakk>
     \<Longrightarrow> module_func_typing \<C> (i, t_locs, b_es) (tn _> tm)"

inductive module_tab_typing :: "tab_t \<Rightarrow> bool" where
  "limit_typing lims (2^32 - 1) \<Longrightarrow> module_tab_typing (T_tab lims reftype)"

abbreviation "module_mem_typing t \<equiv> limit_typing t (2^16)"

inductive module_glob_typing :: "t_context \<Rightarrow> module_glob \<Rightarrow> tg \<Rightarrow> bool" where
  "\<lbrakk>const_exprs \<C> es; \<C> \<turnstile> es : ([] _> [tg_t tg])\<rbrakk> \<Longrightarrow> module_glob_typing \<C> \<lparr>g_type=tg, g_init=es\<rparr> tg"

inductive elem_mode_typing :: "t_context \<Rightarrow> elem_mode \<Rightarrow> t_ref \<Rightarrow> bool" where
  pasive: "elem_mode_typing \<C> Em_passive tr"
| active: "\<lbrakk>x < length (table \<C>); T_tab lims tr = table \<C>!x; \<C> \<turnstile> es : ([] _> [T_num T_i32]); const_exprs \<C> es\<rbrakk> \<Longrightarrow> elem_mode_typing \<C> (Em_active x es) tr"
| declarative: "elem_mode_typing \<C> Em_declarative tr"

inductive module_elem_typing :: "t_context \<Rightarrow> module_elem \<Rightarrow> t_ref \<Rightarrow> bool" where
  "\<lbrakk>list_all (const_exprs \<C>) es;
    list_all (\<lambda>e. (\<C> \<turnstile> e : ([] _> [T_ref tr]))) es;
    elem_mode_typing \<C> em tr\<rbrakk> \<Longrightarrow> module_elem_typing \<C> \<lparr>e_type=tr, e_init=es, e_mode=em\<rparr> tr"

inductive data_mode_typing :: "t_context \<Rightarrow> data_mode \<Rightarrow> bool" where
  pasive: "data_mode_typing \<C> Dm_passive"
| active: "\<lbrakk>x < length (memory \<C>); lims = memory \<C>!x; \<C> \<turnstile> es : ([] _> [T_num T_i32]); const_exprs \<C> es\<rbrakk> \<Longrightarrow> data_mode_typing \<C> (Dm_active x es)"

inductive module_data_typing :: "t_context \<Rightarrow> module_data \<Rightarrow> bool" where
  "data_mode_typing \<C> dm \<Longrightarrow> module_data_typing \<C> \<lparr>d_init=es, d_mode=dm\<rparr>"

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

(* TODO: review whether validity needs to be checked *)
(* This is not needed in module definition but is used later in instantion *)
inductive external_typing :: "s \<Rightarrow> v_ext \<Rightarrow> extern_t \<Rightarrow> bool" where
  "\<lbrakk>i < length (funcs s); cl_type ((funcs s)!i) = tf\<rbrakk> \<Longrightarrow> external_typing s (Ext_func i) (Te_func tf)"
| "\<lbrakk>i < length (tabs s); tab_subtyping (fst ((tabs s)!i)) tt\<rbrakk> \<Longrightarrow> external_typing s (Ext_tab i) (Te_tab tt)"
| "\<lbrakk>i < length (mems s); mem_subtyping (fst ((mems s)!i)) mt\<rbrakk> \<Longrightarrow> external_typing s (Ext_mem i) (Te_mem mt)"
| "\<lbrakk>i < length (globs s); glob_typing ((globs s)!i) gt\<rbrakk> \<Longrightarrow> external_typing s (Ext_glob i) (Te_glob gt)"

record m = \<comment> \<open>module\<close>
  m_types :: "tf list"
  m_funcs :: "module_func list"
  m_tabs :: "tab_t list"
  m_mems :: "mem_t list"
  m_globs :: "module_glob list"
  m_elems :: "module_elem list"
  m_datas :: "module_data list"
  m_start :: "i option"
  m_imports :: "module_import list"
  m_exports :: "module_export list"

fun extract_funcidx_b_e :: "b_e  \<Rightarrow> i option" where
  "extract_funcidx_b_e (Ref_func x) = Some x"
| "extract_funcidx_b_e _ = None"

fun collect_funcidxs_b_e_list :: "b_e list \<Rightarrow> i list" where
  "collect_funcidxs_b_e_list es = List.map_filter extract_funcidx_b_e es"

fun collect_funcidxs_module_func :: "module_func \<Rightarrow> i list" where
  "collect_funcidxs_module_func (_, _, es) = List.map_filter extract_funcidx_b_e es"

fun collect_funcidxs_elem_mode :: "elem_mode \<Rightarrow> i list" where
  "collect_funcidxs_elem_mode (Em_active _ es) = collect_funcidxs_b_e_list es"
| "collect_funcidxs_elem_mode _ = []"

fun collect_funcidxs_module_elem :: "module_elem \<Rightarrow> i list" where
  "collect_funcidxs_module_elem me = concat (collect_funcidxs_elem_mode (e_mode me)#(map collect_funcidxs_b_e_list (e_init me)))"

fun collect_funcidxs_module_data :: "module_data \<Rightarrow> i list" where
  "collect_funcidxs_module_data \<lparr>d_init=es, d_mode=dm\<rparr> = (case dm of
      Dm_active x es \<Rightarrow> collect_funcidxs_b_e_list es
    | _ \<Rightarrow> [])"

fun collect_funcidxs_module_glob :: "module_glob \<Rightarrow> i list" where
  "collect_funcidxs_module_glob glob = List.map_filter extract_funcidx_b_e (g_init glob)"

fun collect_funcidxs_module_import :: "module_import \<Rightarrow> i list" where
  "collect_funcidxs_module_import me = (case I_desc me of
    Imp_func i \<Rightarrow> [i]
  | _ \<Rightarrow> [])"

fun collect_funcidxs_module_export :: "module_export \<Rightarrow> i list" where
  "collect_funcidxs_module_export me = (case E_desc me of
    Ext_func i \<Rightarrow> [i]
  | _ \<Rightarrow> [])"

fun collect_funcidxs_module :: "m \<Rightarrow> i list" where
  "collect_funcidxs_module module = (let
      from_funcs = concat (map collect_funcidxs_module_func (m_funcs module));
      from_globs = concat (map collect_funcidxs_module_glob (m_globs module));
      from_start = (case (m_start module) of
          Some x \<Rightarrow> [x]
        | None \<Rightarrow> []);
      from_elems = concat (map collect_funcidxs_module_elem (m_elems module));
      from_datas = concat (map collect_funcidxs_module_data (m_datas module));
      from_imports = concat (map collect_funcidxs_module_import (m_imports module));
      from_exports = concat (map collect_funcidxs_module_export (m_exports module))
    in remdups (concat [from_funcs, from_globs, from_start, from_elems, from_datas, from_imports, from_exports]))"

inductive module_typing :: "m \<Rightarrow> extern_t list \<Rightarrow> extern_t list \<Rightarrow> bool" where
"\<lbrakk>list_all2 (module_func_typing \<C>) fs fts;
  list_all (module_mem_typing) ms;
  list_all (module_tab_typing) ts;
  list_all2 (module_glob_typing \<C>') gs gts;
  list_all2 (module_elem_typing \<C>') els rts;
  list_all (module_data_typing \<C>') ds;
  length dts = length ds;
  pred_option (module_start_typing \<C>) i_opt;
  module_exports_distinct exps;
  list_all2 (\<lambda>imp. module_import_typing \<C> (I_desc imp)) imps impts;
  list_all2 (\<lambda>exp. module_export_typing \<C> (E_desc exp)) exps expts;
  ifts = ext_t_funcs impts;
  its = ext_t_tabs impts;
  ims = ext_t_mems impts;
  igs = ext_t_globs impts;
  length (ims@ms) \<le> 1;
  \<C> = \<lparr>types_t=tfs,
       func_t=ifts@fts,
       global=igs@gts,
       elem=rts,
       data=dts,
       table=its@ts,
       memory=ims@ms,
       local=[],
       label=[],
       return=None,
       refs=collect_funcidxs_module (module\<lparr>m_funcs := [], m_start := None\<rparr>)\<rparr>;
  \<C>' = \<C>\<lparr>global := igs\<rparr>;
  module = \<lparr>m_types = tfs,
                     m_funcs = fs,
                     m_tabs = ts,
                     m_mems = ms,
                     m_globs = gs,
                     m_elems = els,
                     m_datas = ds,
                     m_start = i_opt,
                     m_imports = imps,
                     m_exports = exps\<rparr>
\<rbrakk> \<Longrightarrow> module_typing module impts expts"

end