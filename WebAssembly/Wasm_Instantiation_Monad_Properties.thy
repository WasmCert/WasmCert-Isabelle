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
  assumes "\<And> x. <P> f x <\<lambda>r. Q x r * P>"
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
    have "list_assn Q xs ys * ( Q a y * P) \<Longrightarrow>\<^sub>A  Q' (y#ys)" using Cons(3)[of "y#ys"] 
      by (simp add: assn_times_assoc star_aci(3))
  }
  note 1 = this
  show ?case  
    apply(sep_auto heap:Cons(2) Cons(1)[OF Cons(2)])
    using 1 star_aci(2) star_aci(3) by auto
qed

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
   apply (vcg heap:fold_map_decon[OF assms(2)])
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
  by(simp add: list_all2_map1 list_all2_conv_all_nth cl_m_agree_j_def split:prod.splits)


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
  apply(vcg decon del:sep_decon_rules decon:fold_map_decon[where Q=
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

lemma cl_m_agree_extend: 
  assumes "cl_m_agree (is, i_ms) cl cl_m" 
  shows "length is = length i_ms   \<Longrightarrow> cl_m_agree (is@is', i_ms@i_ms') cl cl_m"
        "length is' = length i_ms' \<Longrightarrow> cl_m_agree (is'@is, i_ms'@i_ms) cl cl_m"
proof -
  obtain j where j_def:"cl_m_agree_j (is, i_ms) j cl cl_m" using assms(1) by auto
  
  have "length is = length i_ms \<Longrightarrow> cl_m_agree_j (is@is', i_ms@i_ms') j cl cl_m"
    using assms(1) j_def unfolding cl_m_agree_j_def by (simp split:cl.splits cl_m.splits) 
  then show 
    "length is = length i_ms \<Longrightarrow> cl_m_agree (is@is', i_ms@i_ms') cl cl_m" by auto

  have "length is' = length i_ms' \<Longrightarrow> cl_m_agree_j (is'@is, i_ms'@i_ms) (j+length is') cl cl_m" 
    using assms(1) j_def unfolding cl_m_agree_j_def 
    by (simp split:cl.splits cl_m.splits add:nth_append) 
  then show 
    "length is' = length i_ms' \<Longrightarrow> cl_m_agree (is'@is, i_ms'@i_ms) cl cl_m" by auto
qed


lemma list_assn_split:"list_assn P xs1 ys1 * list_assn P xs2 ys2
   \<Longrightarrow>\<^sub>A list_assn P (xs1 @ xs2) (ys1 @ ys2) "
  by (extract_pre_pure, sep_auto)


lemma interp_alloc_module_m_triple:"< s_m_assn (is, i_ms) s s_m * inst_store_assn (is, i_ms)>
  interp_alloc_module_m s_m m imps gvs
  <\<lambda>(s_m', i_m, exps_m). let (s', i, exps) = interp_alloc_module s m imps gvs in 
  \<up>(exps=exps_m) * inst_store_assn (is@[i], i_ms@[i_m]) * s_m_assn (is@[i], i_ms@[i_m]) s' s_m' >\<^sub>t"
proof - 
  have list_all2_extract_length:
    "\<And>P xs ys. list_all2 P xs ys = (length xs = length ys \<and> list_all2 P xs ys)"
    using list_all2_lengthD by auto

  have post_star_assoc:"\<And>A P Q R. (A \<Longrightarrow>\<^sub>A P * (Q * R)) \<Longrightarrow> (A \<Longrightarrow>\<^sub>A P * Q * R)"
    by (simp add: assn_aci(9))

  have post_rule:"\<And>A P Q1 Q2 R. (Q1 \<Longrightarrow>\<^sub>A Q2) \<Longrightarrow> (A \<Longrightarrow>\<^sub>A P * Q1 * R) \<Longrightarrow> (A \<Longrightarrow>\<^sub>A P * Q2 * R)"
    by (meson ent_refl ent_star_mono ent_trans)

  show ?thesis
  unfolding s_m_assn_def funcs_m_assn_def tabs_m_assn_def 
    mems_m_assn_def globs_m_assn_def inst_m_assn_def
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
    apply(rule_tac list_all2_mono[of "cl_m_agree (is, i_ms)"])
     apply(auto simp add:cl_m_agree_extend(1))
   apply(rule_tac list_all2_mono[of "cl_m_agree ([_], [_])"])
    apply (auto, metis (no_types, lifting) cl_m_agree_extend(2))

  apply(subst (asm) (1) list_all2_extract_length, auto)
    (* split the list_assn containing @ *)
  apply(rule post_rule[OF list_assn_split] | rule post_star_assoc)+
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


lemma interp_get_v_m_triple:
  "< s_m_assn is s s_m * inst_m_assn inst inst_m > 
  interp_get_v_m s_m inst_m b_es
  <\<lambda>r.\<up>(r = interp_get_v s inst b_es) * s_m_assn is s s_m * inst_m_assn inst inst_m >"
proof - 
  note 1 = run_iter_m_triple[of _ 
      "Config _ _ (Frame_context (Redex [] [] b_es) [] 0 _) _"
      "Config_m _ _ (Frame_context_m (Redex [] [] b_es) [] 0 _ inst_m) _", 
      simplified cfg_m_assn_def fc_m_assn_def 
      config.case config_m.case frame_context.case frame_context_m.case]

  show ?thesis
  unfolding interp_get_v_m_def
  apply(sep_auto)
  
  sorry

qed 

lemma interp_instantiate_m_triple: 
  "< s_m_assn i_s s s_m * inst_store_assn i_s > 
  interp_instantiate_m s_m m v_imps 
  <\<lambda>(s_m', res_m). let (s', res) = interp_instantiate s m v_imps in 
  \<exists>\<^sub>Ai_s'. s_m_assn i_s' s' s_m' * inst_store_assn i_s'  >"
  supply [simp del] = list_all2_m.simps
  apply(sep_auto)
    apply(vcg decon:list_all2_m_decon)
     apply(sep_auto heap:external_typing_m_triple)
    apply(solve_entails)
  apply(sep_auto)
  sorry

end
