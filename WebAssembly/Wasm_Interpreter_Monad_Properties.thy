theory Wasm_Interpreter_Monad_Properties imports "../libs/Misc_Generic_Lemmas" "../libs/List_Assn" Wasm_Interpreter_Monad begin

lemma load_fX_from_uiX_bs_helper:
  assumes "n*8 = LENGTH('a::len)"
          "length bs \<le> n"
  shows "((word_rsplit_rev::'a word \<Rightarrow> _) (word_rcat_rev (map Rep_uint8 bs))) = (map Rep_uint8 (takefill 0 n bs))"
proof -
  have 3:"(word_rcat_rev :: _ \<Rightarrow> 'a word) (map Rep_uint8 bs) = (word_rcat_rev :: _ \<Rightarrow> 'a word) (takefill 0 n (map Rep_uint8 bs))"
    using word_rcat_rev_is_word_rcat_rev_takefill[of n "(map Rep_uint8 bs)"]
    apply standard
    apply (auto simp add: assms)
    done
  hence "((word_rsplit_rev::'a word \<Rightarrow> _) (word_rcat_rev (map Rep_uint8 bs))) = takefill 0 n (map Rep_uint8 bs)"
    using assms word_split_rcat_rev_size
    by (force simp add: word_size)
  thus ?thesis
    unfolding map_takefill
    by (simp add: zero_uint8.rep_eq)
qed

lemma load_f32_from_ui32_bs:
  assumes "length bs \<le> 4"
  shows "(serialise_i32 (i32_impl_abs (Abs_uint32' (word_rcat_rev (map Rep_uint8' bs))))) = takefill 0 4 bs"
proof -
  have 1:"(word_rsplit_rev::32 word \<Rightarrow> _) (word_rcat_rev ((map Rep_uint8 bs))) = (map Rep_uint8 (takefill 0 4 bs))"
    using load_fX_from_uiX_bs_helper[OF _ assms]
    by force
  have 2:"Abs_uint8' \<circ> Rep_uint8 = id"
    unfolding Abs_uint8'_def map_fun_def
    by (simp add: Rep_uint8_inverse fun_comp_eq_conv)
  show ?thesis
    using 1 2
    unfolding serialise_i32_def i32_impl_abs_def
    by (auto simp add: I32.rep_abs Abs_uint32'.abs_eq Abs_uint32_inverse)
qed

lemma load_f64_from_ui64_bs:
  assumes "length bs \<le> 8"
  shows "(serialise_i64 (i64_impl_abs (Abs_uint64' (word_rcat_rev (map Rep_uint8' bs))))) = takefill 0 8 bs"
proof -
  have 1:"(word_rsplit_rev::64 word \<Rightarrow> _) (word_rcat_rev ((map Rep_uint8 bs))) = (map Rep_uint8 (takefill 0 8 bs))"
    using load_fX_from_uiX_bs_helper[OF _ assms]
    by force
  have 2:"Abs_uint8' \<circ> Rep_uint8 = id"
    unfolding Abs_uint8'_def map_fun_def
    by (simp add: Rep_uint8_inverse fun_comp_eq_conv)
  show ?thesis
    using 1 2
    unfolding serialise_i64_def i64_impl_abs_def
    by (auto simp add: I64.rep_abs Abs_uint64'.abs_eq Abs_uint64_inverse)
qed

lemma word_list_sign_extend_Rep_uint8:
  assumes "length bs > 0"
  shows "(word_list_sign_extend n (map Rep_uint8 bs)) = map Rep_uint8 (Wasm_Base_Defs.sign_extend S n bs)"
proof -
  have "msb (last bs) = (msb (last (map Rep_uint8 bs)))"
    using assms
    apply (induction bs)
    apply (simp_all add: msb_uint8.rep_eq)
    done
  thus ?thesis
    unfolding msb_byte_def msbyte_def word_list_sign_extend_def sign_extend_def negone_byte_def zero_byte_def bytes_takefill_def
    by (simp add: map_takefill one_uint8.rep_eq uminus_uint8.rep_eq zero_uint8.rep_eq)
qed

lemma load_fX_from_siX_bs_helper:
  assumes "n*8 = LENGTH('a::len)"
          "length bs \<le> n"
          "length bs > 0"
  shows "(word_rsplit_rev::'a word \<Rightarrow> _) (word_rcat_rev (word_list_sign_extend n (map Rep_uint8 bs))) = map Rep_uint8 (Wasm_Base_Defs.sign_extend S n bs)"
proof -
  have 1:"(word_rsplit_rev::'a word \<Rightarrow> _) ((word_rcat_rev :: _ \<Rightarrow> 'a word) (map Rep_uint8 (Wasm_Base_Defs.sign_extend S n bs))) = (map Rep_uint8 (Wasm_Base_Defs.sign_extend S n bs))"
    using word_split_rcat_rev_size
    apply standard
    apply (auto simp add: assms word_size Wasm_Base_Defs.sign_extend_def bytes_takefill_def)
    done
  thus ?thesis
    using word_list_sign_extend_Rep_uint8 assms(3)
    by simp
qed

lemma load_f32_from_si32_bs:
  assumes "length bs > 0" "length bs \<le> 4"
  shows "(serialise_i32 (i32_impl_abs (Abs_uint32' (word_rcat_rev (word_list_sign_extend 4 (map Rep_uint8' bs)))))) = sign_extend S 4 bs"
proof -
  have 1:"(word_rsplit_rev::32 word \<Rightarrow> _) (word_rcat_rev (word_list_sign_extend 4 (map Rep_uint8 bs))) =
            map Rep_uint8 (Wasm_Base_Defs.sign_extend S 4 bs)"
    using load_fX_from_siX_bs_helper assms
    by force
  have 2:"Abs_uint8' \<circ> Rep_uint8 = id"
    unfolding Abs_uint8'_def map_fun_def
    by (simp add: Rep_uint8_inverse fun_comp_eq_conv)
  show ?thesis
    using 1 2
    unfolding serialise_i32_def i32_impl_abs_def
    by (auto simp add: I32.rep_abs Abs_uint32'.abs_eq Abs_uint32_inverse)
qed

lemma load_f64_from_si64_bs:
  assumes "length bs > 0" "length bs \<le> 8"
  shows "(serialise_i64 (i64_impl_abs (Abs_uint64' (word_rcat_rev (word_list_sign_extend 8 (map Rep_uint8' bs)))))) = sign_extend S 8 bs"
proof -
  have 1:"(word_rsplit_rev::64 word \<Rightarrow> _) (word_rcat_rev (word_list_sign_extend 8 (map Rep_uint8 bs))) =
            map Rep_uint8 (Wasm_Base_Defs.sign_extend S 8 bs)"
    using load_fX_from_siX_bs_helper assms
    by force
  have 2:"Abs_uint8' \<circ> Rep_uint8 = id"
    unfolding Abs_uint8'_def map_fun_def
    by (simp add: Rep_uint8_inverse fun_comp_eq_conv)
  show ?thesis
    using 1 2
    unfolding serialise_i64_def i64_impl_abs_def
    by (auto simp add: I64.rep_abs Abs_uint64'.abs_eq Abs_uint64_inverse)
qed

lemma store_f32_to_i32_bs:
  assumes "length bs = 4"
  shows "(map Abs_uint8' (takefill (0::8 word) n (word_rsplit_rev (Rep_uint32' (i32_impl_rep (deserialise_i32 bs)))))) = takefill (0::uint8) n bs"
proof -
  have 1:"(((word_rsplit_rev :: 32 word \<Rightarrow> _)
         (Rep_i32 (deserialise_i32 bs)))) = map Rep_uint8 bs"
    using word_split_rcat_rev_size[of "(map Rep_uint8 bs)"] assms
    unfolding deserialise_i32_def
    by (force simp add: word_size Abs_i32_inverse)
  have 2:"Abs_uint8' \<circ> Rep_uint8 = id"
    unfolding Abs_uint8'_def map_fun_def
    by (simp add: Rep_uint8_inverse fun_comp_eq_conv)
  show ?thesis
    using 1 2
    unfolding i32_impl_rep_def
    by (simp add: Abs_uint32_inverse map_takefill Abs_uint8'.abs_eq zero_uint8.abs_eq)
qed

lemma store_f64_to_i64_bs:
  assumes "length bs = 8"
  shows "(map Abs_uint8' (takefill (0::8 word) n (word_rsplit_rev (Rep_uint64' (i64_impl_rep (deserialise_i64 bs)))))) = takefill (0::uint8) n bs"
proof -
  have 1:"(((word_rsplit_rev :: 64 word \<Rightarrow> _)
         (Rep_i64 (deserialise_i64 bs)))) = map Rep_uint8 bs"
    using word_split_rcat_rev_size[of "(map Rep_uint8 bs)"] assms
    unfolding deserialise_i64_def
    by (force simp add: word_size Abs_i64_inverse)
  have 2:"Abs_uint8' \<circ> Rep_uint8 = id"
    unfolding Abs_uint8'_def map_fun_def
    by (simp add: Rep_uint8_inverse fun_comp_eq_conv)
  show ?thesis
    using 1 2
    unfolding i64_impl_rep_def
    by (simp add: Abs_uint64_inverse map_takefill Abs_uint8'.abs_eq zero_uint8.abs_eq)
qed
  
  term app_s_f_v_s_mem_size_m
term app_s_f_v_s_mem_size

definition "mem_m_assn \<equiv> \<lambda>(mr,mm) (mri,mmi). mri \<mapsto>\<^sub>b\<^sub>a Rep_mem_rep mr * \<up>(mmi=mm)"

definition "inst_m_assn i ii \<equiv> 
    inst_m.types ii \<mapsto>\<^sub>a inst.types i
  * inst_m.funcs ii \<mapsto>\<^sub>a inst.funcs i  
  * inst_m.tabs  ii \<mapsto>\<^sub>a inst.tabs  i 
  * inst_m.mems  ii \<mapsto>\<^sub>a inst.mems  i 
  * inst_m.globs ii \<mapsto>\<^sub>a inst.globs i"
     
lemma [sep_heap_rules]: "<mem_m_assn m mi> len_byte_array (fst mi) 
<\<lambda>r. mem_m_assn m mi * \<up>(r=length (Rep_mem_rep (fst m)))>"
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
  subgoal by (auto simp add: app_s_f_v_s_mem_size_def smem_ind_def mem_size_def 
        mem_length_def mem_rep_length_def split: option.split list.split)  
  apply (sep_auto)
  done
    
find_theorems app_s_f_v_s_mem_size

lemma run_step_b_e_m_run_step_b_e_Unreachable:
  assumes "execute (run_step_b_e_m Unreachable cfg_m) h = Some ((cfg_m', res), h')"
  shows "run_step_b_e Unreachable (config_m_to_config h cfg_m) = 
    ((config_m_to_config h' cfg_m'), res)"
  using assms
  by (auto simp add: Heap_Monad.return_def Heap_Monad.heap_def config_m_to_config_def 
      split: frame_context_m.splits frame_context.splits config_m.splits redex.splits prod.splits)

lemmas splits = 
  frame_context_m.splits frame_context.splits config_m.splits redex.splits prod.splits

lemmas defs =  
  Heap_Monad.return_def Heap_Monad.heap_def 
  config_m_to_config_def frame_context_m_to_frame_context_def

lemma run_step_b_e_m_run_step_b_e:
  assumes "execute (run_step_b_e_m b_e cfg_m) h = Some ((cfg_m', res), h')"
  shows "run_step_b_e b_e (config_m_to_config h cfg_m) = ((config_m_to_config h' cfg_m'), res)"
  using assms
proof(cases b_e)
  case Unreachable show ?thesis using assms by (auto simp add: defs Unreachable split: splits)
next
  case Nop show ?thesis using assms by (auto simp add: defs Nop split: splits)
next
  case Drop show ?thesis using assms by (auto simp add: defs Drop split: splits)
next
  case Select show ?thesis using assms by (auto simp add: defs Select split: splits)
next
  case (Block tf b_ebs)
  show ?thesis using assms unfolding Block by (auto simp add: defs Let_def split: splits tf.split)
next
  case (Loop tf b_els)
  show ?thesis using assms unfolding Loop by (auto simp add: defs Let_def split: splits tf.split)
next
  case (If tf es1 es2) show ?thesis using assms by (auto simp add: defs If split: splits)
next
  case (Br_if k) show ?thesis using assms by (auto simp add: defs Br_if split: splits)
next
  case (Br_table ks k) show ?thesis using assms by (auto simp add: defs Br_table split: splits)
next
  case (Tee_local k) show ?thesis using assms by (auto simp add: defs Tee_local split: splits)
next
  case (EConst k) show ?thesis using assms by (auto simp add: defs EConst split: splits)
next
  case (Unop t op) show ?thesis using assms by (auto simp add: defs Unop split: splits)
next
  case (Binop t op) show ?thesis using assms by (auto simp add: defs Binop split: splits)
next
  case (Testop t op) show ?thesis using assms by(auto simp add: defs Testop split: splits)
next
  case (Relop t op) show ?thesis using assms by(auto simp add: defs Relop split: splits)
next
  case (Cvtop t2 op t1 sx) show ?thesis using assms by (auto simp add: defs Cvtop split: splits)
next
  case Return
  (* why are those defined twice? *)
  have 1:"\<And>r v. Wasm_Interpreter.update_redex_return r v 
    = Wasm_Interpreter_Monad.update_redex_return r v"
    by (metis Wasm_Interpreter.update_redex_return.elims 
        Wasm_Interpreter_Monad.update_redex_return.simps)
  show ?thesis using assms unfolding Return 
    by (auto simp add: defs 1 split: splits frame_context_m.split list.split)
next
  case (Br k)
  show ?thesis using assms unfolding Br
    apply (auto simp add: defs Let_def split: splits label_context.split) sorry
next
  case (Call k)
  show ?thesis using assms unfolding Call 
    apply (auto simp add: defs split: splits) sorry
next
  case (Call_indirect k)
  show ?thesis using assms unfolding Call_indirect 
    apply (auto simp add: defs split: splits) sorry
next
  case (Get_local k)
  then show ?thesis sorry
next
  case (Set_local k)
  then show ?thesis sorry
next
  case (Get_global k)
  then show ?thesis sorry
next
  case (Set_global k)
  then show ?thesis sorry
next
  case (Load x191 x192 x193 x194)
  then show ?thesis sorry
next
  case (Store x201 x202 x203 x204)
  then show ?thesis sorry
next
  case Current_memory
  then show ?thesis sorry
next
  case Grow_memory
  then show ?thesis sorry
qed

lemma run_step_e_m_run_step_e:
  assumes "execute (run_step_e_m e cfg_m) h = Some ((cfg_m', res), h')"
  shows "run_step_e e (config_m_to_config h cfg_m) = ((config_m_to_config h' cfg_m'), res)"
proof(cases e)
  case (Basic b_e)
  have 1:"run_step_e_m e cfg_m = run_step_b_e_m b_e cfg_m" unfolding Basic
    by(rule config_m.induct, auto simp add: defs split: splits)
  have "run_step_e e (config_m_to_config h cfg_m) = run_step_b_e b_e (config_m_to_config h cfg_m)"
    unfolding Basic by(rule config.induct, auto simp add: defs split: splits) 
  also have "... = ((config_m_to_config h' cfg_m'), res)" 
    using assms run_step_b_e_m_run_step_b_e unfolding 1 by simp
  finally show ?thesis by -
next
  case (Invoke i_cl)
  then show ?thesis sorry
next
  case Trap
  show ?thesis using assms by (auto simp add: defs Trap split: splits)
next
  case (Label x41 x42 x43)
  show ?thesis using assms by (auto simp add: defs Label split: splits)
next
  case (Frame x51 x52 x53)
  show ?thesis using assms by (auto simp add: defs Frame split: splits)
qed

lemma run_iter_m_run_iter:
  "execute (run_iter_m n cfg_m) h = Some ((cfg_m', res), h')
 \<Longrightarrow> run_iter n (config_m_to_config h cfg_m) = ((config_m_to_config h' cfg_m'), res)"
proof(induct n)
  case 0
  show ?case using 0 by (auto simp add: defs split: splits)
next
  case (Suc n)
  then show ?case sorry
qed
end