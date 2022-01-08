theory Wasm_Interpreter_Monad_Properties imports "../libs/List_Assn" Wasm_Interpreter_Monad begin

term app_s_f_v_s_mem_size_m
term app_s_f_v_s_mem_size

definition "mem_m_assn \<equiv> \<lambda>(mr,mm) (mri,mmi). mri \<mapsto>\<^sub>a Rep_mem_rep mr * \<up>(mmi=mm)"

definition "inst_m_assn i ii \<equiv> 
    inst_m.types ii \<mapsto>\<^sub>a inst.types i
  * inst_m.funcs ii \<mapsto>\<^sub>a inst.funcs i  
  * inst_m.tabs  ii \<mapsto>\<^sub>a inst.tabs  i 
  * inst_m.mems  ii \<mapsto>\<^sub>a inst.mems  i 
  * inst_m.globs ii \<mapsto>\<^sub>a inst.globs i"
     
lemma [sep_heap_rules]: "<mem_m_assn m mi> Array.len (fst mi) <\<lambda>r. mem_m_assn m mi * \<up>(r=length (Rep_mem_rep (fst m)))>"
  unfolding mem_m_assn_def
  by (sep_auto split: prod.splits)

method extract_list_idx for i :: nat =
  (subst listI_assn_extract[of i], (simp;fail), (simp;fail))
  
method reinsert_list_idx for i :: nat =
  rule listI_assn_reinsert[where i=i] listI_assn_reinsert'[where i=i],
  (frame_inference; fail),
  (simp;fail),
  (simp;fail)
  
lemma "< mi \<mapsto>\<^sub>a mis * (list_assn mem_m_assn) ms mis * inst_m_assn (f_inst i) ii > 
    app_s_f_v_s_mem_size_m mi ii vs 
  <\<lambda>r. \<up>(r = app_s_f_v_s_mem_size ms i vs) *
   mi \<mapsto>\<^sub>a mis * (list_assn mem_m_assn) ms mis * inst_m_assn (f_inst i) ii>"
  unfolding app_s_f_v_s_mem_size_m_def inst_m_assn_def list_assn_conv_idx
  apply extract_pre_pure
  apply sep_auto
  apply (extract_list_idx "inst.mems (f_inst i) ! 0")
  apply (sep_auto)
  apply (reinsert_list_idx "inst.mems (f_inst i) ! 0")
  apply (sep_auto)
  subgoal by (auto simp add: app_s_f_v_s_mem_size_def smem_ind_def mem_size_def mem_length_def mem_rep_length_def split: option.split list.split)  
  apply (sep_auto)
  done
    
find_theorems app_s_f_v_s_mem_size

lemma run_step_b_e_m_run_step_b_e_Unreachable:
  assumes "execute (run_step_b_e_m Unreachable cfg_m) h = Some ((cfg_m', res), h')"
  shows "run_step_b_e Unreachable (config_m_to_config h cfg_m) = ((config_m_to_config h' cfg_m'), res)"
  using assms
  by (auto simp add: Heap_Monad.return_def Heap_Monad.heap_def config_m_to_config_def split: frame_context_m.splits frame_context.splits config_m.splits redex.splits prod.splits)

lemma run_step_b_e_m_run_step_b_e:
  assumes "execute (run_step_b_e_m b_e cfg_m) h = Some ((cfg_m', res), h')"
  shows "run_step_b_e b_e (config_m_to_config h cfg_m) = ((config_m_to_config h' cfg_m'), res)"
  using assms
  sorry

lemma run_step_e_m_run_step_e:
  assumes "execute (run_step_e_m e cfg_m) h = Some ((cgf_m', res), h')"
  shows "run_step_e e (config_m_to_config h cfg_m) = ((config_m_to_config h' cfg_m'), res)"
  sorry

lemma run_iter_m_run_iter:
  assumes "execute (run_iter_m n cfg_m) h = Some ((cgf_m', res), h')"
  shows "run_iter n (config_m_to_config h cfg_m) = ((config_m_to_config h' cfg_m'), res)"
  sorry
end