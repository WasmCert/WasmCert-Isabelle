theory Wasm_Instantiation_Monad imports Wasm_Instantiation Wasm_Interpreter_Monad begin

instance v_ext :: countable
  by countable_datatype

instance v_ext :: heap ..

instance extern_t :: countable
  by countable_datatype

instance extern_t :: heap ..

fun tab_typing_m :: "tabinst_m \<Rightarrow> tab_t \<Rightarrow> bool Heap" where
  "tab_typing_m t tt = do {
   t_min \<leftarrow> Array.len (fst t);
   return (limits_compat \<lparr>l_min=t_min,l_max=(snd t)\<rparr> tt) }"

fun mem_typing_m :: "mem_m \<Rightarrow> mem_t \<Rightarrow> bool Heap" where
  "mem_typing_m m mt = do {
   m_min \<leftarrow> Array.len (fst m);
   return (limits_compat \<lparr>l_min=m_min,l_max=(snd m)\<rparr> mt) }"

fun external_typing_m :: "s_m \<Rightarrow> v_ext \<Rightarrow> extern_t \<Rightarrow> bool Heap" where
  "external_typing_m s_m (Ext_func i) (Te_func tf) = do {
   f_len \<leftarrow> Array.len (s_m.funcs s_m);
   (if (i < f_len) then do {
      f \<leftarrow> Array.nth (s_m.funcs s_m) i;
      return (cl_m_type f = tf)
    }
    else return False) }"

| "external_typing_m s_m (Ext_tab i) (Te_tab tt) = do {
   t_len \<leftarrow> Array.len (s_m.tabs s_m);
   (if (i < t_len) then do {
      t \<leftarrow> Array.nth (s_m.tabs s_m) i;
      tab_typing_m t tt
    }
    else return False) }"

| "external_typing_m s_m (Ext_mem i) (Te_mem mt) = do {
   m_len \<leftarrow> Array.len (s_m.mems s_m);
   (if (i < m_len) then do {
      m \<leftarrow> Array.nth (s_m.mems s_m) i;
      mem_typing_m m mt
    }
    else return False) }"

| "external_typing_m s_m (Ext_glob i) (Te_glob gt) = do {
   g_len \<leftarrow> Array.len (s_m.globs s_m);
   (if (i < g_len) then do {
      g \<leftarrow> Array.nth (s_m.globs s_m) i;
      return (glob_typing g gt)
    }
    else return False) }"

| "external_typing_m s_m _ _ = return False"

definition export_get_v_ext_m :: "inst_m \<Rightarrow> exp_desc \<Rightarrow> v_ext Heap" where
  "export_get_v_ext_m inst exp =
     (case exp of
        Ext_func i \<Rightarrow> do { x \<leftarrow> Array.nth (inst_m.funcs inst) i; return (Ext_func x) }
      | Ext_tab i \<Rightarrow>  do { x \<leftarrow> Array.nth (inst_m.tabs inst) i; return (Ext_tab x) }
      | Ext_mem i \<Rightarrow>  do { x \<leftarrow> Array.nth (inst_m.mems inst) i; return (Ext_mem x) }
      | Ext_glob i \<Rightarrow>   do { x \<leftarrow> Array.nth (inst_m.globs inst) i; return (Ext_glob x) })"

definition interp_alloc_module_m :: "s_m \<Rightarrow> m \<Rightarrow> v_ext list \<Rightarrow> v list \<Rightarrow> (s_m \<times> inst_m \<times> module_export list) Heap" where
  "interp_alloc_module_m s_m m imps gvs = do {
   length_funcs_s \<leftarrow> Array.len (s_m.funcs s_m);
   length_tabs_s \<leftarrow> Array.len (s_m.tabs s_m);
   length_mems_s \<leftarrow> Array.len (s_m.mems s_m);
   length_globs_s \<leftarrow> Array.len (s_m.globs s_m);
   let i_fs = [length_funcs_s ..< (length_funcs_s + length (m_funcs m))];
   let i_ts = [length_tabs_s ..< (length_tabs_s + length (m_tabs m))];
   let i_ms = [length_mems_s ..< (length_mems_s + length (m_mems m))];
   let i_gs = [length_globs_s ..< (length_globs_s + min (length (m_globs m)) (length gvs))];
   inst_types \<leftarrow> Array.of_list (m_types m);
   inst_funcs \<leftarrow> Array.of_list ((ext_funcs imps)@i_fs);
   inst_tabs \<leftarrow> Array.of_list ((ext_tabs imps)@i_ts);
   inst_mems \<leftarrow> Array.of_list ((ext_mems imps)@i_ms);
   inst_globs \<leftarrow> Array.of_list ((ext_globs imps)@i_gs);
   let inst_m = \<lparr> types = inst_types,
                  funcs = inst_funcs,
                  tabs = inst_tabs,
                  mems = inst_mems,
                  globs = inst_globs \<rparr>;
    empty_inst \<leftarrow> make_empty_inst_m;
    empty_tab \<leftarrow> Array.of_list [];
    empty_mem \<leftarrow> Array.of_list [];
    let dummy_func = (Func_native empty_inst ([] _> []) [] []);
    let dummy_tab = (empty_tab, None);
    let dummy_mem = (empty_mem, None);
    let dummy_glob = \<lparr>g_mut = T_mut, g_val = ConstInt32 0\<rparr>;
    s_funcs \<leftarrow> Array.new (length_funcs_s + length (m_funcs m)) dummy_func;
    s_tabs \<leftarrow> Array.new (length_tabs_s + length (m_tabs m)) dummy_tab;
    s_mems \<leftarrow> Array.new (length_mems_s + length (m_mems m)) dummy_mem;
    s_globs \<leftarrow> Array.new (length_globs_s + length (m_globs m)) dummy_glob;
    array_blit (s_m.funcs s_m) 0 s_funcs 0 length_funcs_s;
    array_blit (s_m.tabs s_m) 0 s_tabs 0 length_tabs_s;
    array_blit (s_m.mems s_m) 0 s_mems 0 length_mems_s;
    array_blit (s_m.globs s_m) 0 s_globs 0 length_globs_s;
    array_blit_map (m_funcs m)
      (\<lambda>(i, tlocs, b_es). do { ft \<leftarrow> Array.nth inst_types i; return (Func_native inst_m ft tlocs b_es) })
      s_funcs
      length_funcs_s;
    array_blit_map (m_tabs m)
      (\<lambda>tt. do { t' \<leftarrow> Array.new (l_min tt) None; return (t', (l_max tt)) })
      s_tabs
      length_tabs_s;
    array_blit_map (m_mems m)
      (\<lambda>mt. do { m' \<leftarrow> Array.new (l_min mt * Ki64) zero_byte; return (m', (l_max mt)) })
      s_mems
      length_mems_s;
    array_blit_map (zip (m_globs m) gvs)
      (\<lambda>(m_g, v). return \<lparr>g_mut=(tg_mut (module_glob.g_type m_g)), g_val=v\<rparr>)
      s_globs
      length_globs_s;
    exps \<leftarrow> Heap_Monad.fold_map
              (\<lambda>m_exp. do { desc \<leftarrow> (export_get_v_ext_m inst_m (E_desc m_exp));
                            return \<lparr>E_name=(E_name m_exp), E_desc=desc\<rparr> })
              (m_exports m);
    let s_res = \<lparr>s_m.funcs=s_funcs, s_m.tabs=s_tabs, s_m.mems=s_mems, s_m.globs=s_globs\<rparr>;
    return (s_res, inst_m, exps)
    }"

fun list_all2_m :: "('a \<Rightarrow> 'b \<Rightarrow> bool Heap) \<Rightarrow> 'a::heap list \<Rightarrow> 'b::heap list \<Rightarrow> bool Heap" where
  "list_all2_m R [] []  = return True"
| "list_all2_m R (x#xs) [] = return False"
| "list_all2_m R [] (y#ys) = return False"
| "list_all2_m R (x#xs) (y#ys) = do { b \<leftarrow> R x y; b' \<leftarrow> list_all2_m R xs ys; return (b \<and> b') }"

definition interp_get_v_m :: "s_m \<Rightarrow> inst_m \<Rightarrow> b_e list \<Rightarrow> v Heap" where
  "interp_get_v_m s inst b_es = do {
     f_locs1 \<leftarrow> Array.of_list [];
     res \<leftarrow> run_v_m 2 0 (s, f_locs1, inst, b_es);
     case res of (_,RValue [v]) \<Rightarrow> return v }"

definition interp_get_i32_m :: "s_m \<Rightarrow> inst_m \<Rightarrow> b_e list \<Rightarrow> i32 Heap" where
  "interp_get_i32_m s inst b_es = do {
     v \<leftarrow> interp_get_v_m s inst b_es;
      (case v of ConstInt32 c \<Rightarrow> return c | _ \<Rightarrow> return 0) }"

definition init_tab_m :: "s_m \<Rightarrow> inst_m \<Rightarrow> nat \<Rightarrow> module_elem \<Rightarrow> unit Heap" where
  "init_tab_m s inst e_ind e =
     do {
       t_ind \<leftarrow> Array.nth (inst_m.tabs inst) (e_tab e);
       (tab_e,max) \<leftarrow> Array.nth (s_m.tabs s) t_ind;
       array_blit_map (e_init e) (\<lambda>i. do { i_cl \<leftarrow> Array.nth (inst_m.funcs inst) i; return (Some i_cl) }) tab_e e_ind }"

definition init_mem_m :: "s_m \<Rightarrow> inst_m \<Rightarrow> nat \<Rightarrow> module_data \<Rightarrow> unit Heap" where
  "init_mem_m s inst d_ind d =
     do {
       m_ind \<leftarrow> Array.nth (inst_m.mems inst) (d_data d);
       mem \<leftarrow> Array.nth (s_m.mems s) m_ind;
       write_bytes_m mem d_ind (d_init d) }"

definition init_tabs_m :: "s_m \<Rightarrow> inst_m \<Rightarrow> nat list \<Rightarrow> module_elem list \<Rightarrow> unit Heap" where
  "init_tabs_m s inst e_inds es = do {Heap_Monad.fold_map (\<lambda>(e_ind,e). init_tab_m s inst e_ind e) (zip e_inds es); return () }"

definition init_mems_m :: "s_m \<Rightarrow> inst_m \<Rightarrow> nat list \<Rightarrow> module_data list \<Rightarrow> unit Heap" where
  "init_mems_m s inst d_inds ds = do {Heap_Monad.fold_map (\<lambda>(d_ind,d). init_mem_m s inst d_ind d) (zip d_inds ds); return () }"

definition get_start_m :: "inst_m \<Rightarrow> nat option \<Rightarrow> (nat option) Heap" where
  "get_start_m inst i_s =
   (case i_s of
      None \<Rightarrow> return None
    | Some i_s' \<Rightarrow> do { i_s_s \<leftarrow> Array.nth (inst_m.funcs inst) i_s'; return (Some i_s_s) })"

fun interp_instantiate_m :: "s_m \<Rightarrow> m \<Rightarrow> v_ext list \<Rightarrow> (((s_m \<times> inst_m \<times> (module_export list)) \<times> (nat option)) option) Heap" where
  "interp_instantiate_m s_m m v_imps =
     (case (module_type_checker m) of
        Some (t_imps, t_exps) \<Rightarrow> do {
          exps_well_typed \<leftarrow> list_all2_m (external_typing_m s_m) v_imps t_imps;
          if (exps_well_typed) then do {
            g_inits \<leftarrow> Heap_Monad.fold_map
                         (\<lambda>g. do {
                                i_types \<leftarrow> Array.of_list [];
                                i_funcs \<leftarrow> Array.of_list [];
                                i_tabs \<leftarrow> Array.of_list [];
                                i_mems \<leftarrow> Array.of_list [];
                                i_globs \<leftarrow> Array.of_list (ext_globs v_imps);
                                let inst_m = \<lparr>types=i_types, funcs=i_funcs, tabs=i_tabs, mems=i_mems, globs=i_globs\<rparr>;
                                v \<leftarrow> interp_get_v_m s_m inst_m (g_init g);
                                return v })
                          (m_globs m);
            (s_m', inst_m, v_exps) \<leftarrow> interp_alloc_module_m s_m m v_imps g_inits;
            e_offs \<leftarrow> Heap_Monad.fold_map (\<lambda>e. interp_get_i32_m s_m' inst_m (e_off e)) (m_elem m);
            d_offs \<leftarrow> Heap_Monad.fold_map (\<lambda>d. interp_get_i32_m s_m' inst_m (d_off d)) (m_data m);
            start \<leftarrow> get_start_m inst_m (m_start m);
            init_tabs_m s_m' inst_m (map nat_of_int e_offs) (m_elem m);
            init_mems_m s_m' inst_m (map nat_of_int d_offs) (m_data m);
            return (Some ((s_m', inst_m, v_exps), start)) }
          else
            return None
        }
      | _ \<Rightarrow> return None)"

end