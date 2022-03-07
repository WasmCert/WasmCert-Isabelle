theory Wasm_Instantiation_Monad_Properties 
  imports "../libs/Misc_Generic_Lemmas" "../libs/List_Assn" 
    Wasm_Instantiation_Monad Wasm_Monad_Assertions Wasm_Instantiation_Properties     
    Wasm_Interpreter_Monad_Properties
    
begin

lemma list_blit_array_triple:
  "<a \<mapsto>\<^sub>a la> 
  list_blit_array l a n
  <\<lambda>r. \<up>(fits_at_in l n la) 
    * a \<mapsto>\<^sub>a insert_at_in l n la>"
proof(induct l arbitrary:a la n)
case Nil
  then show ?case by sep_auto
next
  case (Cons a l)
  show ?case 
    supply [simp del] = list_blit_array.simps
    apply(subst list_blit_array.simps)
    apply(sep_auto heap:Cons split:list.splits simp: take_update_last)
    done
qed

lemma fold_map_decon:
  assumes "list_all R xs"
  assumes "\<And> x. R x \<Longrightarrow> <P> f x <\<lambda>r. Q x r * P>"
  assumes "\<And>ys. list_assn Q xs ys * P \<Longrightarrow>\<^sub>A Q' ys"
  shows 
    "<P> Heap_Monad.fold_map f xs <Q'>"
  using assms
proof(induct xs arbitrary:P Q')
  case Nil
  then show ?case by sep_auto
next
  case (Cons a xs)
  {
    fix y ys
    have "list_assn Q xs ys * ( Q a y * P) \<Longrightarrow>\<^sub>A  Q' (y#ys)" using Cons(4)[of "y#ys"] 
      by (simp add: assn_times_assoc star_aci(3))
  }
  note 1 = this

  have 2:"R a" and 3:"list_all R xs" using Cons(2) by auto

  show ?case  
    apply(sep_auto heap:Cons(3)[OF 2] Cons(1)[OF 3 Cons(3)])
    using 1 star_aci(2) star_aci(3) by auto
qed


lemma fold_map_decon':
  assumes "\<And> x. <P> f x <\<lambda>r. Q x r * P>"
  assumes "\<And>ys. list_assn Q xs ys * P \<Longrightarrow>\<^sub>A Q' ys"
  shows 
    "<P> Heap_Monad.fold_map f xs <Q'>"
  using fold_map_decon[where R="\<lambda>x. True", simplified, OF _ assms]
  by (simp add: list.pred_True)

lemma array_blit_map_decon:
  assumes "P \<Longrightarrow>\<^sub>A a \<mapsto>\<^sub>a la * F"
  assumes "\<And> x. <F> f x <\<lambda>r. Q x r * F>"
  assumes "\<And>ys. fits_at_in xs n la \<Longrightarrow> 
    a \<mapsto>\<^sub>a insert_at_in ys n la * list_assn Q xs ys * F \<Longrightarrow>\<^sub>A Q' ()"
  shows 
    "<P> 
    array_blit_map xs f a n
    <Q'>"
  supply [simp del] = Heap_Monad.fold_map.simps list_blit_array.simps
  apply (rule cons_pre_rule[OF assms(1)])  
  apply (sep_auto)
   apply (vcg heap:fold_map_decon'[OF assms(2)])
   apply(solve_entails)
  apply(extract_pre_pure)
  apply(sep_auto heap:list_blit_array_triple)
  subgoal using assms(3) by auto
  by (metis assms(3))

abbreviation "module_func_to_cl inst inst_types \<equiv> 
  (\<lambda>(i_t, loc_ts, b_es). cl.Func_native inst (inst_types!i_t) loc_ts b_es)"

abbreviation "module_func_to_cl_m inst_m inst_types \<equiv> 
  (\<lambda>(i_t, loc_ts, b_es). cl_m.Func_native inst_m (inst_types!i_t) loc_ts b_es)"

abbreviation "alloc_funcs_simple' m_fs inst inst_types \<equiv> 
  map (\<lambda>m_f. module_func_to_cl inst inst_types m_f) m_fs" 

lemma alloc_funcs_simple_conv:
  "alloc_funcs_simple m_fs inst = alloc_funcs_simple' m_fs inst (inst.types inst)" 
  unfolding alloc_func_simple_def by simp

lemma list_assn_map1:"list_assn P (map f xs) ys = list_assn (\<lambda>x y. P (f x) y) xs ys"
  by(induct "(\<lambda>x y. P (f x) y)"  xs ys rule: list_assn.induct, auto)

lemma list_assn_pure:"list_assn (\<lambda>x y. \<up>(P x y)) xs ys = \<up>(list_all2 P xs ys)"
  by(induct "\<lambda>x y. \<up>(P x y)"  xs ys rule: list_assn.induct, auto)

lemma alloc_funcs_m_triple:
  "< s_funcs \<mapsto>\<^sub>a fs * inst_types \<mapsto>\<^sub>a m_tfs> 
  alloc_funcs_m s_funcs n m_fs inst_m inst_types
  <\<lambda>r.\<exists>\<^sub>Ays. \<up>(fits_at_in m_fs n fs)
  *  s_funcs \<mapsto>\<^sub>a insert_at_in ys n fs
  *  \<up>(list_all2 (cl_m_agree ([inst], [inst_m])) (alloc_funcs_simple' m_fs inst m_tfs) ys)
  *  inst_types \<mapsto>\<^sub>a m_tfs>"
  unfolding alloc_funcs_m_def 
  supply [simp del] = array_blit_map.simps
  apply(vcg 
      decon:array_blit_map_decon[where Q="\<lambda>m_f r. \<up>(r = module_func_to_cl_m inst_m m_tfs m_f)"])
    apply(solve_entails)
   apply(sep_auto)
  apply(sep_auto simp:list_assn_pure)
  by(simp add: list_all2_map1 list_all2_conv_all_nth cl_m_agree_j_def inst_at_def split:prod.splits)


lemma alloc_tabs_m_triple: 
  "< s_tabs \<mapsto>\<^sub>a ts> 
  alloc_tabs_m s_tabs n m_ts
  <\<lambda>r.\<exists>\<^sub>Ays. \<up>(fits_at_in m_ts n ts)
  *  s_tabs \<mapsto>\<^sub>a insert_at_in ys n ts
  *  list_assn tabinst_m_assn (alloc_tabs_simple m_ts) ys>"
  unfolding alloc_tabs_m_def 
  supply [simp del] = array_blit_map.simps
  apply(vcg decon: array_blit_map_decon
      [where F=emp and Q="\<lambda>tt t_m. tabinst_m_assn (alloc_tab_simple tt) t_m"])
    apply solve_entails
   apply (sep_auto simp:tabinst_m_assn_def alloc_tab_simple_def)
  apply (sep_auto simp:list_assn_map1)
  done


lemma alloc_mems_m_triple: 
  "< s_mems \<mapsto>\<^sub>a ms> 
  alloc_mems_m s_mems n m_ms
  <\<lambda>r.\<exists>\<^sub>Ays. \<up>(fits_at_in m_ms n ms)
  *  s_mems \<mapsto>\<^sub>a insert_at_in ys n ms
  *  list_assn mem_m_assn (alloc_mems_simple m_ms) ys>"
  unfolding alloc_mems_m_def
  supply [simp del] = array_blit_map.simps
  apply(vcg decon: array_blit_map_decon
      [where F=emp and Q="\<lambda>mt m_m. mem_m_assn (alloc_mem_simple mt) m_m"])
    apply(solve_entails)
   apply(sep_auto)
   apply(sep_auto simp:mem_m_assn_def alloc_mem_simple_def mem_mk_def mem_rep_mk_def 
      bytes_replicate_def zero_byte_def mem_rep.Abs_mem_rep_inverse)
  apply(sep_auto simp:list_assn_map1)
  done

lemma list_all2_eq_map_conv:"(list_all2 (\<lambda>x y. f x = g y) xs ys) = (map f xs = map g ys)"
  unfolding list_all2_conv_all_nth
  by (metis length_map map_intro_length nth_map)

(* todo: learn how to make this nicer *)
lemma alloc_globs_m_triple': 
  "< s_globs \<mapsto>\<^sub>a gs> 
  alloc_globs_m s_globs n m_gs gvs 
  <\<lambda>r.\<up>(fits_at_in (zip m_gs gvs) n gs)
  *  s_globs \<mapsto>\<^sub>a insert_at_in (alloc_globs_simple m_gs gvs) n gs>"
  unfolding alloc_globs_m_def 
  supply [simp del] = array_blit_map.simps
  apply(vcg decon: array_blit_map_decon
      [where F=emp and Q="\<lambda>m_g_v g_m. \<up>(alloc_glob_simple m_g_v = g_m)"])
    apply(solve_entails)
   apply(sep_auto simp:alloc_glob_simple_def)
  apply(sep_auto simp:list_assn_pure)
  apply(simp add:list_all2_eq_map_conv)
  done

lemma alloc_globs_m_triple: 
  "< s_globs \<mapsto>\<^sub>a gs> 
  alloc_globs_m s_globs n m_gs gvs 
  <\<lambda>r. \<up>(fits_at_in (zip m_gs gvs) n gs)
  *  s_globs \<mapsto>\<^sub>a insert_at_in (alloc_globs_simple m_gs gvs) n gs>"
  by(rule cons_post_rule[OF alloc_globs_m_triple'], sep_auto)

abbreviation "get_exports inst m_exps \<equiv> 
  map (\<lambda>m_exp. \<lparr>E_name=(E_name m_exp), E_desc=(export_get_v_ext inst (E_desc m_exp))\<rparr>) m_exps"

lemma get_exports_m_triple: 
  "<inst_m_assn inst inst_m> 
  get_exports_m inst_m m_exps 
  <\<lambda>r. \<up>(r = get_exports inst m_exps) * inst_m_assn inst inst_m>"
  unfolding get_exports_m_def 
  supply [simp del] = Heap_Monad.fold_map.simps
  apply(vcg decon del:sep_decon_rules decon:fold_map_decon'[where Q=
        "\<lambda>m_exp r. \<up>(\<lparr>E_name = E_name m_exp, E_desc = export_get_v_ext inst (E_desc m_exp)\<rparr> = r)"])
   apply(sep_auto simp:export_get_v_ext_m_def export_get_v_ext_def 
      inst_m_assn_def split:v_ext.splits)
  apply(sep_auto simp:list_assn_pure list_all2_eq_map_conv)
  done

lemma alloc_funcs_equiv_full:"alloc_funcs s m_fs i
  = (s\<lparr>s.funcs := s.funcs s @ alloc_funcs_simple m_fs i\<rparr>, 
     [length (s.funcs s)..<length (s.funcs s) + length m_fs])"
  using alloc_funcs_equiv alloc_funcs_range
  by (metis surjective_pairing) 

lemma alloc_tabs_equiv_full:"alloc_tabs s m_ts
  = (s\<lparr>s.tabs := s.tabs s @ alloc_tabs_simple m_ts\<rparr>, 
     [length (s.tabs s)..<length (s.tabs s) + length m_ts])"
  using alloc_tabs_equiv alloc_tabs_range
  by (metis surjective_pairing) 

lemma alloc_mems_equiv_full:"alloc_mems s m_ms
  = (s\<lparr>s.mems := s.mems s @ alloc_mems_simple m_ms\<rparr>, 
     [length (s.mems s)..<length (s.mems s) + length m_ms])"
  using alloc_mems_equiv alloc_mems_range
  by (metis surjective_pairing) 

lemma alloc_globs_equiv_full:"alloc_globs s m_gs gvs
  = (s\<lparr>s.globs := s.globs s @ alloc_globs_simple m_gs gvs\<rparr>, 
     [length (s.globs s)..<length (s.globs s) + min (length m_gs) (length gvs)])"
  using alloc_globs_equiv alloc_globs_range
  by (metis surjective_pairing) 

lemma cl_m_agree_set_extend: 
  assumes "cl_m_agree i_s' cl cl_m" "inst_store_subset i_s' i_s" 
  shows "cl_m_agree i_s cl cl_m" 
  using assms(1) inst_store_extend_preserve_contains[OF _ assms(2)] 
  unfolding cl_m_agree_j_def  
  by (auto, simp split:cl.splits cl_m.splits)

lemma cl_m_agree_extend: 
  assumes "cl_m_agree (is, i_ms) cl cl_m" 
  shows "length is = length i_ms   \<Longrightarrow> cl_m_agree (is@is', i_ms@i_ms') cl cl_m"
        "length is' = length i_ms' \<Longrightarrow> cl_m_agree (is'@is, i_ms'@i_ms) cl cl_m"
proof -
  obtain j where j_def:"cl_m_agree_j (is, i_ms) j cl cl_m" using assms(1) by auto
  
  have "length is = length i_ms \<Longrightarrow> cl_m_agree_j (is@is', i_ms@i_ms') j cl cl_m"
    using assms(1) j_def unfolding cl_m_agree_j_def 
    by (simp add: inst_at_def split:cl.splits cl_m.splits) 
  then show 
    "length is = length i_ms \<Longrightarrow> cl_m_agree (is@is', i_ms@i_ms') cl cl_m" by auto

  have "length is' = length i_ms' \<Longrightarrow> cl_m_agree_j (is'@is, i_ms'@i_ms) (j+length is') cl cl_m" 
    using assms(1) j_def unfolding cl_m_agree_j_def 
    by (simp add: inst_at_def split:cl.splits cl_m.splits add:nth_append) 
  then show 
    "length is' = length i_ms' \<Longrightarrow> cl_m_agree (is'@is, i_ms'@i_ms) cl cl_m" by auto
qed



lemma list_assn_split:"list_assn P xs1 ys1 * list_assn P xs2 ys2
   \<Longrightarrow>\<^sub>A list_assn P (xs1 @ xs2) (ys1 @ ys2) "
  by (extract_pre_pure, sep_auto)



lemma interp_alloc_module_m_triple:
  "< s_m_assn (is', i_ms') s s_m * inst_store_assn (is, i_ms)>
  interp_alloc_module_m s_m m imps gvs
  <\<lambda>(s_m', i_m, exps_m). let (s', i, exps) = interp_alloc_module s m imps gvs in 
  \<up>(exps=exps_m) * inst_store_assn (i#is, i_m#i_ms) * s_m_assn (i#is', i_m#i_ms') s' s_m' >\<^sub>t"
proof - 
  have list_all2_extract_length:
    "\<And>P xs ys. list_all2 P xs ys = (length xs = length ys \<and> list_all2 P xs ys)"
    using list_all2_lengthD by auto

  show ?thesis
  unfolding s_m_assn_def funcs_m_assn_def tabs_m_assn_def 
    mems_m_assn_def globs_m_assn_def inst_m_assn_def inst_store_assn_def
    (* unfolding and simplifying interp_alloc_module immediately
    to reduce the load on sep_auto later *)
    interp_alloc_module_def alloc_funcs_equiv_full alloc_funcs_simple_conv 
      alloc_tabs_equiv_full alloc_mems_equiv_full alloc_globs_equiv_full
  apply(sep_auto simp:Let_def)

    (* now proceeding with vcg steps *)
  supply [simp del] = array_blit_map.simps
  unfolding interp_alloc_module_m_def make_empty_inst_m_def
    (* each line separately to have it look less stuck *)
  apply(sep_auto heap:alloc_funcs_m_triple)
   apply(sep_auto heap:alloc_tabs_m_triple)
   apply(sep_auto heap:alloc_mems_m_triple)
   apply(sep_auto heap:alloc_globs_m_triple)
    (*todo: find a nicer way of splitting the get_exports_m_triple *)
  apply(sep_auto, sep_auto heap: get_exports_m_triple
    [of "\<lparr>inst.types = _, funcs = _, tabs = _, mems = _ , globs = _ \<rparr>"
      "\<lparr>inst_m.types = _, funcs = _, tabs = _, mems = _ , globs = _ \<rparr>", 
      simplified inst_m_assn_def inst.simps inst_m.simps])
  apply(extract_pre_pure)
    (* todo: find a better way of extracting length information from the hypotheses *)
  apply(subst (asm) (1) list_all2_extract_length)  

  apply(sep_auto) (* takes a while *)

  (* deal with the list_all2 schematic goals 
    todo: possibly a better way *)
   apply(rule list_all2_appendI)
    apply(rule_tac list_all2_mono[of "cl_m_agree (is', i_ms')"])
     apply(auto)
    apply(rule cl_m_agree_extend(2)[of _ _ _ _"[_]" "[_]", simplified])
    apply(auto)
  
   apply(rule_tac list_all2_mono[of "cl_m_agree ([_], [_])"])
    apply(auto)
   apply(rule cl_m_agree_extend(1)[of "[_]" "[_]", simplified])
  apply(auto)

  apply(subst (asm) (1) list_all2_extract_length, auto)
    (* split the list_assn containing @ *)
  apply(ent_backward_all r:list_assn_split)
  apply(sep_auto)
  done
qed

lemma list_all2_m_decon: 
  assumes "\<And> x y. <P> f_m x y <\<lambda>r. \<up>(r = f x y) * P>"
  assumes "P \<Longrightarrow>\<^sub>A Q' (list_all2 f xs ys)"
  shows 
    "<P> list_all2_m f_m xs ys <Q'>"
  using assms
proof(induct xs ys arbitrary:P Q' rule:list_induct2')
  case 1
  then show ?case by sep_auto
next
  case (2 x xs) then show ?case by sep_auto
next
  case (3 y ys) then show ?case by sep_auto
next
  case (4 x xs y ys)

  show ?case 
  apply(sep_auto)
    apply(sep_auto heap:4(2))
    apply(sep_auto heap:4(1)[where Q'="\<lambda>r. Q' (f x y \<and> r) ",OF 4(2) 4(3)[simplified]])
    done
qed

abbreviation "external_typing_m_triple_abbv i_s s s_m v_imp t_imp \<equiv> 
  < s_m_assn i_s s s_m > 
  external_typing_m s_m v_imp t_imp 
  <\<lambda>r. \<up>(r = external_typing s v_imp t_imp) * s_m_assn i_s s s_m>"

lemma external_typing_m_func_triple:
  "external_typing_m_triple_abbv i_s s s_m (Ext_func i) (Te_func tf)"
  unfolding s_m_assn_def funcs_m_assn_def external_typing.simps list_all2_conv_all_nth
  apply(sep_auto)
    apply(metis cl_m_agree_type)
   apply(metis cl_m_agree_type)
  apply(sep_auto)
  done

lemma external_typing_m_tab_triple:
  "external_typing_m_triple_abbv i_s s s_m (Ext_tab i) (Te_tab tt)"
  unfolding s_m_assn_def tabs_m_assn_def  external_typing.simps list_assn_conv_idx
  apply(sep_auto)
    apply(extract_pre_pure)
    apply(extract_list_idx i)
    apply(sep_auto)
   apply(extract_pre_pure)
   apply(sep_auto)
     apply(sep_auto simp:tab_typing_def tabinst_m_assn_def split:prod.splits)
    apply(sep_auto simp:tab_typing_def tabinst_m_assn_def split:prod.splits)
   apply(reinsert_list_idx i, sep_auto)
  apply(extract_pre_pure, sep_auto)
  done    

lemma external_typing_m_mem_triple:
  "external_typing_m_triple_abbv i_s s s_m (Ext_mem i) (Te_mem mt)"
  unfolding s_m_assn_def mems_m_assn_def external_typing.simps list_assn_conv_idx
  apply(sep_auto)
    apply(extract_pre_pure)
    apply(extract_list_idx i)
    apply(sep_auto)
   apply(extract_pre_pure)
   apply(sep_auto)
     apply(sep_auto simp:mem_typing_def mem_m_assn_def mem_size_def mem_length_def mem_rep_length_def
    mem_max_def split:prod.splits)
    apply(sep_auto simp:mem_typing_def mem_m_assn_def mem_size_def mem_length_def mem_rep_length_def
    mem_max_def split:prod.splits)
   apply(reinsert_list_idx i, sep_auto)
  apply(extract_pre_pure, sep_auto)
  done

lemma external_typing_m_glob_triple:
  "external_typing_m_triple_abbv i_s s s_m (Ext_glob i) (Te_glob gt)"
  unfolding s_m_assn_def globs_m_assn_def external_typing.simps by sep_auto

fun v_ext_extern_t_agree :: "v_ext \<Rightarrow> extern_t \<Rightarrow> bool" where 
  "v_ext_extern_t_agree (Ext_func i) (Te_func tf) = True" 
| "v_ext_extern_t_agree (Ext_tab i) (Te_tab tt)   = True" 
| "v_ext_extern_t_agree (Ext_mem i) (Te_mem mt)   = True" 
| "v_ext_extern_t_agree (Ext_glob i) (Te_glob gt) = True" 
| "v_ext_extern_t_agree _ _                       = False" 

lemma external_typing_m_triple: 
  "external_typing_m_triple_abbv i_s s s_m v_imp t_imp"
proof(cases "v_ext_extern_t_agree v_imp t_imp")
  case True
  show ?thesis 
    supply [sep_heap_rules] = external_typing_m_func_triple external_typing_m_tab_triple
    external_typing_m_mem_triple external_typing_m_glob_triple
    and [simp del] = external_typing_m.simps
    by(insert True, cases v_imp, (cases t_imp, sep_auto+)+)
next
  case False
  show ?thesis 
    supply [simp] = external_typing.simps
    by(insert False, cases v_imp, (cases t_imp, sep_auto+)+)
qed



lemma funcs_m_assn_extend: 
  "length is = length i_ms \<Longrightarrow> 
  funcs_m_assn (is, i_ms) fs fs_m \<Longrightarrow>\<^sub>A funcs_m_assn (is@is', i_ms@i_ms') fs fs_m"
  "length is' = length i_ms' \<Longrightarrow> 
  funcs_m_assn (is, i_ms) fs fs_m \<Longrightarrow>\<^sub>A funcs_m_assn (is'@is, i_ms'@i_ms) fs fs_m"
  unfolding funcs_m_assn_def list_all2_conv_all_nth
  by (sep_auto, simp add: cl_m_agree_extend)+


lemma s_m_assn_extend: 
  "length is = length i_ms \<Longrightarrow>
  s_m_assn (is, i_ms) s s_m \<Longrightarrow>\<^sub>A s_m_assn (is@is', i_ms@i_ms') s s_m"
  "length is' = length i_ms' \<Longrightarrow>
  s_m_assn (is, i_ms) s s_m \<Longrightarrow>\<^sub>A s_m_assn (is'@is, i_ms'@i_ms) s s_m"
  unfolding s_m_assn_def
  by ((rule fr_refl)+, rule funcs_m_assn_extend, simp)+


abbreviation "cfg_m_no_realloc cfg_m cfg_m' \<equiv> (
  case cfg_m of Config_m d s_m fc fcs \<Rightarrow>
  case cfg_m' of Config_m d' s_m' fc' fcs' \<Rightarrow> s_m = s_m')"

lemma run_step_b_e_m_triple_const:
    assumes "const_expr \<C> b_e"
    shows "<cfg_m_assn i_s i_s' cfg cfg_m> 
    run_step_b_e_m b_e cfg_m 
    <\<lambda>(cfg_m', res). \<up>(cfg_m_no_realloc cfg_m cfg_m') * 
    cfg_m_pair_assn i_s i_s' (run_step_b_e b_e cfg) (cfg_m', res)>\<^sub>t" 
  using assms unfolding const_expr.simps
  apply(simp split:b_e.splits)
  unfolding cfg_m_assn_def s_m_assn_def fc_m_assn_def 
  apply(sep_auto split:config.splits config_m.splits frame_context_m.splits frame_context.splits 
      redex.splits heap:get_global_triple)
  done


lemma run_step_e_m_triple_const:
    assumes "const_expr \<C> b_e"
    shows "<cfg_m_assn i_s i_s' cfg cfg_m> 
    run_step_e_m (Basic b_e) cfg_m 
    <\<lambda>(cfg_m', res). \<up>(cfg_m_no_realloc cfg_m cfg_m') * 
    cfg_m_pair_assn i_s i_s' (run_step_b_e b_e cfg) (cfg_m', res)>\<^sub>t" 
  using assms unfolding const_expr.simps 
  supply [simp del] = run_step_b_e_m.simps
  apply(simp split:e.splits)
  apply(rule config_m.induct )
  apply(rule config.induct)
  apply(sep_auto split: frame_context.splits frame_context_m.splits redex.splits
      heap:run_step_b_e_m_triple_const[OF assms])
  done

lemma split_v_s_b_s_aux_preserve_const: 
  assumes "const_exprs \<C> b_es" "split_v_s_b_s_aux v_s b_es = (v_s', b_es')"
  shows "const_exprs \<C>  b_es'"
  using assms 
proof(induct b_es arbitrary: v_s)
  case Nil
  then show ?case by auto
next
  case (Cons a b_es)
  then show ?case 
    by (metis const_expr.simps list.pred_inject(2) prod.sel(2) split_v_s_b_s_aux.simps(1) split_v_s_b_s_aux.simps(19))
qed

lemma run_iter_m_triple_const:
  assumes "inst_at i_s (inst, f_inst2) j" "inst_store_subset i_s' i_s" "const_exprs \<C> b_es"
  shows "< s_m_assn i_s' s s_m * inst_store_assn i_s * locs_m_assn locs f_locs1>
  run_iter_m n (Config_m d s_m (Frame_context_m (Redex v_s [] b_es) [] 0 f_locs1 f_inst2) [])
  <\<lambda>(cfg_m', res_m). let (cfg', res) = 
   run_iter n (Config d s (Frame_context (Redex v_s [] b_es) [] 0 
 \<lparr> f_locs = locs, f_inst = inst\<rparr>) [])
  in \<up>(case cfg_m' of Config_m d' s_m' fc' fcs' \<Rightarrow> s_m' = s_m) * 
    cfg_m_pair_assn i_s i_s' (cfg', res) (cfg_m', res_m) >\<^sub>t"
  using assms
proof(induct n arbitrary:v_s b_es f_locs1 f_inst2 j inst locs)
  case 0
  then show ?case unfolding cfg_m_assn_def fc_m_assn_def fcs_m_assn_def using assms
    by sep_auto
next
  note 1 = cfg_m_assn_def fc_m_assn_def fcs_m_assn_def
  note 2 = run_step_b_e_m_triple_const[of _ _ _ _
      "Config _ _ (Frame_context _ _ _ \<lparr>f_locs = _, f_inst = _\<rparr>) []" 
      "Config_m _ _ (Frame_context_m _ _ _ _ _) []",
      simplified 1 config.case config_m.case frame_context.case frame_context_m.case
      list_assn.simps star_aci]

  case (Suc n)
  show ?case
    supply [simp del] = run_step_b_e_m.simps
    apply(sep_auto)
    using Suc(2) assms(2) apply(sep_auto simp:1)
      apply(sep_auto)
     apply(sep_auto)
    apply(sep_auto)
     apply(sep_auto heap:Suc) 

    apply(insert Suc(4))
    apply(simp del:list.pred_inject)
     apply(match premises in C:"const_exprs _ _" and I:"split_v_s_b_s_aux _ _ = _" \<Rightarrow>
        \<open>insert split_v_s_b_s_aux_preserve_const[OF C I]\<close>)
    apply(sep_auto)
     apply(rule cons_pre_rule[OF _ 2])
    using Suc(2) assms(2) apply(auto)
     apply(sep_auto)
    apply(simp add:const_expr.simps, auto)
      apply(sep_auto heap:Suc simp:1 split:prod.splits res_step.splits
    config_m.splits frame_context_m.splits)+
    done
qed


lemma run_v_m_triple_const:
  assumes "inst_at i_s (inst, f_inst2) j"  "inst_store_subset i_s' i_s" "const_exprs \<C> b_es"
  shows "< s_m_assn i_s' s s_m * inst_store_assn i_s * locs_m_assn locs f_locs1>
  run_v_m n d (s_m, f_locs1, f_inst2, b_es)
  <\<lambda>(s_m', res_m). let (s', res) = 
   run_v n d (s, \<lparr> f_locs = locs, f_inst = inst\<rparr>, b_es)
  in \<up>(s_m' = s_m \<and> res_m = res) * s_m_assn i_s' s' s_m' * inst_store_assn i_s >\<^sub>t"
  by(sep_auto heap:run_iter_m_triple_const[OF assms] 
        split:config_m.splits config.splits prod.splits
        simp:cfg_m_assn_def)

abbreviation "interp_get_v_m_triple s s_m i_s i_s' inst inst_m b_es \<equiv> 
  < s_m_assn i_s' s s_m * inst_store_assn i_s  * inst_m_assn inst inst_m > 
  interp_get_v_m s_m inst_m b_es
  <\<lambda>r.\<up>(r = interp_get_v s inst b_es) 
  * s_m_assn i_s' s s_m * inst_store_assn i_s * inst_m_assn inst inst_m >\<^sub>t"

lemma interp_get_v_m_triple:
  assumes  
    "const_exprs \<C> b_es" "\<C> \<turnstile> b_es : ([] _> [t])" 
    "list_all2 (\<lambda>ig tg. external_typing s (Ext_glob ig) (Te_glob tg)) igs (global \<C>)"
    "inst.globs inst = igs @ arb"
    "inst_store_subset i_s' i_s" 
  shows "interp_get_v_m_triple s s_m i_s i_s' inst inst_m b_es"
proof -
  obtain iss i_ms where i_s:"i_s = (iss, i_ms)" by fastforce 

  have 1:"s_m_assn i_s' s s_m * inst_store_assn i_s  * inst_m_assn inst inst_m
    \<Longrightarrow>\<^sub>A s_m_assn i_s' s s_m * inst_store_assn (inst#iss, inst_m#i_ms)"
    unfolding i_s inst_store_assn_def by sep_auto

  have 2:"inst_at (inst#iss, inst_m#i_ms) (inst, inst_m) 0" unfolding inst_at_def by auto

  have 3:"inst_store_subset i_s' (inst#iss, inst_m#i_ms)" 
    using assms(5) unfolding inst_store_subset_def i_s by auto

  note 4 = run_v_m_triple_const
    [simplified locs_m_assn_def,
      OF 2 3 assms(1)]

  obtain v where 5:"run_v 2 0 (s, \<lparr>f_locs = [], f_inst = inst\<rparr>, b_es) = (s, RValue [v])" 
    using const_exprs_run_v[OF assms(1) assms(2) _ assms(3) assms(4)] by auto
  show ?thesis 
    unfolding interp_get_v_m_def interp_get_v_def
    supply [simp del] = run_v_m.simps run_v.simps
    apply(rule cons_pre_rule[OF 1])
    apply(sep_auto heap:4)
    apply(sep_auto split:res.splits prod.splits simp:inst_store_assn_def i_s 5)
    done 
qed


lemma interp_get_v_m_triple_glob: 
  assumes "module_glob_typing \<C> g gt"  
    "global \<C> = ext_t_globs t_imps"
    "list_all2 (external_typing s) v_imps t_imps" 
    "inst.globs inst = ext_globs v_imps "
    "inst_store_subset i_s' i_s" 
  shows 
    "interp_get_v_m_triple s s_m i_s i_s' inst inst_m (g_init g)"
proof - 
  have 1:"const_exprs \<C> (g_init g)" and 2:"\<C> \<turnstile> (g_init g) : ([] _> [tg_t gt])"  
    using assms(1) unfolding module_glob_typing.simps by auto

  have 3:
    "list_all2 (\<lambda>ig tg. external_typing s (Ext_glob ig) (Te_glob tg)) (ext_globs v_imps) (global \<C>)"
    unfolding assms(2) 
    using ext_typing_imp_globi_agree[OF assms(3)]
    unfolding globi_agree_def external_typing.simps
    by auto

  have 4:"inst.globs inst = (ext_globs v_imps) @ []" using assms(4) by auto

  show ?thesis using interp_get_v_m_triple[OF 1 2 3 4 assms(5)] by -
qed

lemma interp_get_v_m_triple':
  assumes  "module_typing m t_imps t_exps" "list_all2 (external_typing s) v_imps t_imps" 
    "inst.globs inst = ext_globs v_imps "
  shows "< s_m_assn i_s' s s_m * inst_store_assn i_s  * inst_m_assn inst inst_m > 
  interp_get_v_m s_m inst_m b_es
  <\<lambda>r.\<up>(r = interp_get_v s inst b_es) 
  * s_m_assn i_s' s s_m * inst_store_assn i_s * inst_m_assn inst inst_m >\<^sub>t"
proof -
  show ?thesis sorry
qed



lemma list_assn_star:"list_assn (\<lambda>x y. P x y * Q x y) xs ys = list_assn P xs ys * list_assn Q xs ys" 
  apply(induct "(\<lambda>x y. P x y * Q x y)"  xs ys rule: list_assn.induct, auto)
  using assn_times_assoc star_aci(3) by presburger

lemma list_assn_true:"list_assn (\<lambda>x y. true) xs ys = 
  \<up>(length xs = length ys) * (if length xs > 0 then true else emp)" 
  by(induct xs ys rule:list_induct2', auto)

lemma list_assn_true':"list_assn (\<lambda>x y. true) xs ys \<Longrightarrow>\<^sub>A true"
  by simp 


lemma interp_get_i32_m_triple:
  assumes  "module_typing m t_imps t_exps" "list_all2 (external_typing s) v_imps t_imps" 
    "inst.globs inst = ext_globs v_imps "
  shows "< s_m_assn i_s' s s_m * inst_store_assn i_s  * inst_m_assn inst inst_m > 
  interp_get_i32_m s_m inst_m b_es
  <\<lambda>r.\<up>(r = interp_get_i32 s inst b_es) 
  * s_m_assn i_s' s s_m * inst_store_assn i_s * inst_m_assn inst inst_m >\<^sub>t"
  sorry


lemma interp_instantiate_m_triple: 
  "< s_m_assn (is, i_ms)  s s_m * inst_store_assn (is, i_ms)  > 
  interp_instantiate_m s_m m v_imps 
  <\<lambda>(s_m', res_m). let (s', res) = interp_instantiate s m v_imps in 
  \<exists>\<^sub>Ai_s'. s_m_assn i_s' s' s_m' * inst_store_assn i_s'  >"
proof - 
  note 1 = interp_get_v_m_triple_glob
    [where inst="\<lparr>inst.types = _, funcs = _, tabs = _, mems = _, globs = _\<rparr>"
      and inst_m="\<lparr>inst_m.types = _, funcs = _, tabs = _, mems = _, globs = _\<rparr>",
      simplified inst_m_assn_def inst.simps inst_m.simps]


  show ?thesis
  supply [simp del] = list_all2_m.simps

  apply(sep_auto)
    apply(vcg decon:list_all2_m_decon[where Q'="\<lambda>r. _ * \<up>(r = _)"])
     apply(sep_auto heap:external_typing_m_triple)
    apply(solve_entails)

   apply(match premises in  I:"module_type_checker _ = _" 
      \<Rightarrow> \<open>insert module_type_checker_imp_module_typing[OF I]\<close>)

     apply(sep_auto simp:module_typing.simps)
      apply(match premises in I:"list_all2 (module_glob_typing _) _ _" 
        \<Rightarrow> \<open>insert list_all2_forget[OF I]\<close>)

      apply(vcg decon:fold_map_decon
        [where R="\<lambda>x. \<exists>y. module_glob_typing _ x y" and 
          Q="\<lambda>g r.\<up>(interp_get_v s _ (g_init g) = r) * true"])
       apply(sep_auto heap:1 simp:inst_store_subset_def)
      apply(solve_entails)

     apply(sep_auto)
      apply(simp add:list_assn_star list_assn_pure list_all2_eq_map_conv)
      apply(sep_auto heap:interp_alloc_module_m_triple)
    apply(sep_auto split:prod.splits)
   

  sorry
qed
end