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

lemma serialise_deserialise_i32:
  assumes "length x = 4"
  shows "serialise_i32 (deserialise_i32 x) = x"
proof -
  have "(word_rsplit_rev :: (32 word \<Rightarrow> _))
       (word_rcat_rev (map Rep_uint8 x)) = (map Rep_uint8 x)"
  using assms takefill_same[of 0 x]
  by (simp add: Abs_i32_inverse load_fX_from_uiX_bs_helper)
  moreover have "Abs_uint8' \<circ> Rep_uint8 = id"
    unfolding Abs_uint8'_def map_fun_def
    by (simp add: Rep_uint8_inverse fun_comp_eq_conv)
  ultimately show ?thesis
    unfolding serialise_i32_def deserialise_i32_def
    by (simp add: I32.rep_abs)
qed

lemma serialise_deserialise_i64:
  assumes "length x = 8"
  shows "serialise_i64 (deserialise_i64 x) = x"
proof -
  have "(word_rsplit_rev :: (64 word \<Rightarrow> _))
       (word_rcat_rev (map Rep_uint8 x)) = (map Rep_uint8 x)"
  using assms takefill_same[of 0 x]
  by (simp add: Abs_i64_inverse load_fX_from_uiX_bs_helper)
  moreover have "Abs_uint8' \<circ> Rep_uint8 = id"
    unfolding Abs_uint8'_def map_fun_def
    by (simp add: Rep_uint8_inverse fun_comp_eq_conv)
  ultimately show ?thesis
    unfolding serialise_i64_def deserialise_i64_def
    by (simp add: I64.rep_abs)
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


definition "mem_m_assn \<equiv> \<lambda>(mr,mm) (mr_m,mm_m). mr_m \<mapsto>\<^sub>b\<^sub>aRep_mem_rep mr * \<up>(mm_m=mm)"

method extract_list_idx for i :: nat =
  (subst listI_assn_extract[of i], (simp;fail), (simp;fail))
  
method reinsert_list_idx for i :: nat =
  rule listI_assn_reinsert[where i=i] listI_assn_reinsert'[where i=i],
  (frame_inference; fail),
  (simp;fail),
  (simp;fail)

method knock_down for i :: nat = 
 extract_pre_pure?, extract_list_idx i, sep_auto, extract_pre_pure?, reinsert_list_idx i

term app_s_f_v_s_mem_size_m
term app_s_f_v_s_mem_size


definition "inst_m_assn i i_m \<equiv> 
    inst_m.types i_m \<mapsto>\<^sub>a inst.types i
  * inst_m.funcs i_m \<mapsto>\<^sub>a inst.funcs i  
  * inst_m.tabs  i_m \<mapsto>\<^sub>a inst.tabs  i 
  * inst_m.mems  i_m \<mapsto>\<^sub>a inst.mems  i 
  * inst_m.globs i_m \<mapsto>\<^sub>a inst.globs i"

lemma [sep_heap_rules]: "<mem_m_assn m mi> len_byte_array (fst mi) 
<\<lambda>r. mem_m_assn m mi * \<up>(r=length (Rep_mem_rep (fst m)))>"
  unfolding mem_m_assn_def
  by (sep_auto split: prod.splits)

type_synonym inst_store = "(inst list \<times> inst_m list)"

abbreviation "inst_store_assn \<equiv> \<lambda>(is, i_ms). list_assn inst_m_assn is i_ms"

abbreviation "inst_at \<equiv> \<lambda>(is, i_ms) (i, i_m) j. j < length is \<and> is!j = i \<and> i_ms!j = i_m"

abbreviation "contains_inst_assn i_s i \<equiv> \<exists>\<^sub>A j. \<up>(inst_at i_s i j)"

definition mems_m_assn :: "mem list \<Rightarrow> mem_m array \<Rightarrow> assn" where
  "mems_m_assn ms ms_m = (\<exists>\<^sub>A ms_i. ms_m \<mapsto>\<^sub>a ms_i  * list_assn mem_m_assn ms ms_i)"

definition cl_m_assn :: "inst_store \<Rightarrow> cl \<Rightarrow> cl_m \<Rightarrow> assn" where 
  "cl_m_assn i_s cl cl_m = (case cl of 
  cl.Func_native i tf ts b_es \<Rightarrow> 
    (case cl_m of 
    cl_m.Func_native i_m tf_m ts_m b_es_m \<Rightarrow> 
     contains_inst_assn i_s (i, i_m) * \<up>(tf = tf_m \<and> ts = ts_m \<and> b_es = b_es_m) 
  | cl_m.Func_host tf_m host_m \<Rightarrow> false)
| cl.Func_host tf host \<Rightarrow> 
    (case cl_m of 
    cl_m.Func_native i_m tf_m ts_m b_es_m \<Rightarrow> false 
  | cl_m.Func_host tf_m host_m \<Rightarrow> \<up>(tf = tf_m \<and> host = host_m))
)"

lemma ex_assn_pure_conv:"(\<exists>\<^sub>Ax. \<up>(P x)) = \<up>(\<exists>x. P x)"
  by (smt (z3) ent_ex_preI ent_iffI ent_pure_pre_iff_sng ent_refl triv_exI)

lemma cl_m_assn_pure:"is_pure_assn (cl_m_assn i_s cl cl_m)"
  unfolding cl_m_assn_def 
  by(simp split: cl.split cl_m.split add:ex_assn_pure_conv)
  

lemma cl_m_assn_type:
  assumes "h \<Turnstile> cl_m_assn i_s cl cl_m" 
  shows "cl_type cl = cl_m_type cl_m"
  using assms
  unfolding cl_m_assn_def cl_type_def cl_m_type_def
  by(simp split:cl.splits cl_m.splits)

definition funcs_m_assn :: "inst_store \<Rightarrow> cl list \<Rightarrow> cl_m array \<Rightarrow> assn" where
  "funcs_m_assn i_s fs fs_m = (\<exists>\<^sub>A fs_i. fs_m \<mapsto>\<^sub>a fs_i * list_assn (cl_m_assn i_s) fs fs_i)"

definition tabinst_m_assn :: "tabinst \<Rightarrow> tabinst_m \<Rightarrow> assn" where 
  "tabinst_m_assn = (\<lambda>(tr,tm) (tr_m,tm_m). tr_m \<mapsto>\<^sub>a tr * \<up>(tm = tm_m))"

definition tabs_m_assn :: "tabinst list \<Rightarrow> tabinst_m array \<Rightarrow> assn" where
 "tabs_m_assn ts ts_m = (\<exists>\<^sub>A ts_i. ts_m \<mapsto>\<^sub>a ts_i * list_assn tabinst_m_assn ts ts_i)"

definition "globs_m_assn gs gs_m \<equiv> gs_m \<mapsto>\<^sub>a gs"

definition s_m_assn :: "inst_store \<Rightarrow> s \<Rightarrow> s_m \<Rightarrow> assn" where 
  "s_m_assn i_s s s_m = 
  funcs_m_assn i_s (s.funcs s) (s_m.funcs s_m)
* tabs_m_assn  (s.tabs s)  (s_m.tabs s_m)
* mems_m_assn  (s.mems s)  (s_m.mems s_m)
* globs_m_assn (s.globs s) (s_m.globs s_m)"

definition locs_m_assn :: "v list \<Rightarrow> v array \<Rightarrow> assn" where 
  "locs_m_assn locs locs_m = locs_m \<mapsto>\<^sub>a locs"

definition fc_m_assn :: "inst_store \<Rightarrow> frame_context \<Rightarrow> frame_context_m \<Rightarrow> assn" where 
  "fc_m_assn i_s fc fc_m = (
  case fc of Frame_context redex lcs nf f \<Rightarrow> 
  case fc_m of Frame_context_m redex_m lcs_m nf_m f_locs1 f_inst2 \<Rightarrow>
  \<up>(redex = redex_m \<and> lcs = lcs_m \<and> nf = nf_m)
  * contains_inst_assn i_s (f_inst f, f_inst2)
  * locs_m_assn (f_locs f) f_locs1
)"

definition "fcs_m_assn i_s fcs fcs_m \<equiv> list_assn (fc_m_assn i_s) fcs fcs_m"

lemma [simp]:"fcs_m_assn i_s (fc#fcs) (fc_m#fcs_m) = 
  fc_m_assn i_s fc fc_m * fcs_m_assn i_s fcs fcs_m"
  unfolding fcs_m_assn_def by simp

definition cfg_m_assn :: "inst_store \<Rightarrow> config \<Rightarrow> config_m \<Rightarrow> assn" where
  "cfg_m_assn i_s cfg cfg_m = (
  case cfg of Config d s fc fcs \<Rightarrow>
  case cfg_m of Config_m d_m s_m fc_m fcs_m \<Rightarrow> 
  \<up>(d=d_m) * s_m_assn i_s s s_m * fc_m_assn i_s fc fc_m * fcs_m_assn i_s fcs fcs_m
   * inst_store_assn i_s
)"     

lemma mem_size_triple:
  assumes "inst_at (is, i_ms) (f_inst f, f_inst2) j" 
  shows 
  "< ms_m \<mapsto>\<^sub>a ms_i * list_assn mem_m_assn ms ms_i * inst_store_assn (is, i_ms) > 
    app_s_f_v_s_mem_size_m ms_m f_inst2 v_s 
  <\<lambda>r. \<up>(r = app_s_f_v_s_mem_size ms f v_s) *
   ms_m \<mapsto>\<^sub>a ms_i * (list_assn mem_m_assn) ms ms_i * inst_store_assn (is, i_ms)>"
  using assms
  unfolding app_s_f_v_s_mem_size_m_def inst_m_assn_def list_assn_conv_idx
  apply sep_auto
   apply (knock_down j)
  apply(sep_auto)
  apply(knock_down "inst.mems (f_inst f) ! 0")
   apply (sep_auto)
  subgoal by (auto simp add: app_s_f_v_s_mem_size_def smem_ind_def mem_size_def 
        mem_length_def mem_rep_length_def split: option.split list.split)  
  apply (sep_auto)
  done



lemma get_local_triple: 
  "<locs_m_assn (f_locs f) f_locs1> 
  app_f_v_s_get_local_m k f_locs1 v_s 
  <\<lambda>r. \<up>(r = app_f_v_s_get_local k f v_s) * locs_m_assn (f_locs f) f_locs1>"
  unfolding locs_m_assn_def app_f_v_s_get_local_m_def app_f_v_s_get_local_def
  by sep_auto


lemma get_global_triple:
  assumes "inst_at (is, i_ms) (f_inst f, f_inst2) j"
  shows "<globs_m_assn gs gs_m * inst_store_assn (is, i_ms)>
  app_s_f_v_s_get_global_m k gs_m f_inst2 v_s
  <\<lambda>r.\<up>(r = app_s_f_v_s_get_global k gs f v_s)
  * globs_m_assn gs gs_m * inst_store_assn (is, i_ms)>"
  using assms
  unfolding globs_m_assn_def inst_m_assn_def app_s_f_v_s_get_global_m_def app_s_f_v_s_get_global_def
    sglob_ind_def list_assn_conv_idx
  apply (sep_auto)
   apply (knock_down j)
  apply (sep_auto)
  done

lemma set_local_triple: 
  assumes "inst_at (is, i_ms) (f_inst f, f_inst2) j"
  shows "<locs_m_assn (f_locs f) f_locs1 * inst_store_assn (is, i_ms)> 
  app_f_v_s_set_local_m k f_locs1 v_s
  <\<lambda>r. let (f', v_s', res) = (app_f_v_s_set_local k f v_s) in 
  \<up>(r = (v_s', res) \<and> inst_at (is, i_ms) (f_inst f', f_inst2) j) 
  * locs_m_assn (f_locs f') f_locs1 * inst_store_assn (is, i_ms)>"
  using assms
  unfolding locs_m_assn_def app_f_v_s_set_local_m_def app_f_v_s_set_local_def
  by(sep_auto)


(*unfortunately I have to phrase it as (is, i_ms), otherwise sep_auto gets confused*)
lemma set_global_triple: 
  assumes "inst_at (is, i_ms) (f_inst f, f_inst2) j"
  shows "<globs_m_assn gs gs_m * inst_store_assn (is, i_ms)> 
  app_s_f_v_s_set_global_m k gs_m f_inst2 v_s
  <\<lambda>r. let (gs', v_s', res) = (app_s_f_v_s_set_global k gs f v_s) in 
  \<up>(r = (v_s', res)) 
  * globs_m_assn gs' gs_m * inst_store_assn (is, i_ms)>"
  using assms
  unfolding app_s_f_v_s_set_global_m_def inst_m_assn_def globs_m_assn_def list_assn_conv_idx
  apply (sep_auto simp: app_s_f_v_s_set_global_def update_glob_def sglob_ind_def Let_def
      split: prod.split)
   apply (knock_down j)
  apply(sep_auto)
  done


(* app_s_f_v_s_set_global_def update_glob_def sglob_ind_def Let_def *)

lemma call_triple: 
  assumes "inst_at (is, i_ms) (f_inst f, f_inst2) j"
  shows
 "<inst_store_assn (is, i_ms)> 
  app_f_call_m k f_inst2 
  <\<lambda>r. \<up>(r = app_f_call k f) * inst_store_assn (is, i_ms)>"
  using assms
  unfolding inst_m_assn_def app_f_call_m_def app_f_call_def sfunc_ind_def list_assn_conv_idx
  apply(sep_auto)
   apply(knock_down j)
  apply(sep_auto)
  done


lemmas is_complex_goal = asm_rl[of "< _ > _ < _ >"] asm_rl[of "_ \<Longrightarrow>\<^sub>A _"]

method_setup then_else = \<open>let
in
  Method.text_closure -- Method.text_closure -- Method.text_closure >>
    (fn ((textb, textt), texte) => fn ctxt => fn using => fn st =>
      let
        val bmethod = Method.evaluate_runtime textb ctxt using;
        val tmethod = Method.evaluate_runtime textt ctxt using;
        val emethod = Method.evaluate_runtime texte ctxt using;
      in
        (case try (fn st => bmethod st |> Seq.pull) st of
          SOME (SOME (Seq.Result st,_)) => tmethod st
        | _ => emethod st)
      end)
end     
\<close>

method defer_vcg = then_else \<open>rule is_complex_goal\<close> \<open>fail\<close> 
  \<open>find_goal \<open>rule is_complex_goal\<close>, 
  (rule is_complex_goal | tactic \<open>defer_tac 1\<close>)\<close>

method sep_auto_all = (defer_vcg | (rule is_complex_goal, sep_auto))+

lemma [sep_heap_rules]: "<tabinst_m_assn t t_m> 
    Array.len (fst t_m) 
    <\<lambda>r. tabinst_m_assn t t_m * \<up>(r=length (fst t))>"
  unfolding tabinst_m_assn_def
  by (sep_auto split: prod.splits)

lemma [sep_heap_rules]: "<tabinst_m_assn t t_m> 
    Array.nth (fst t_m) x
    <\<lambda>r. tabinst_m_assn t t_m * \<up>(r=(fst t)!x)>"
  unfolding tabinst_m_assn_def
  by (sep_auto split: prod.splits)

lemma funcs_nth_type_triple:"<funcs_m_assn i_s cls cls_m> 
    Array.nth cls_m i  
    <\<lambda>r. \<up>(cl_m_type r = cl_type (cls!i)) * funcs_m_assn i_s cls cls_m>" 
  unfolding funcs_m_assn_def list_assn_conv_idx
  apply(sep_auto heap del:nth_rule)
  apply(extract_pre_pure)
  apply(sep_auto)
  apply(simp add: listI_assn_extract[of i])
  using cl_m_assn_type 
  by (metis mod_starD)

lemma call_indirect_triple:
  assumes "inst_at (is, i_ms) (f_inst f, f_inst2) j"
  shows 
  "<tabs_m_assn ts ts_m * funcs_m_assn i_s fs fs_m * inst_store_assn (is, i_ms)> 
  app_s_f_v_s_call_indirect_m k ts_m fs_m f_inst2 v_s
  <\<lambda>r. \<up>(r = app_s_f_v_s_call_indirect k ts fs f v_s) 
* tabs_m_assn ts ts_m * funcs_m_assn i_s fs fs_m * inst_store_assn (is, i_ms)>"
  using assms
  unfolding app_s_f_v_s_call_indirect_m_def 
  supply [split] = v.splits option.splits
  apply(sep_auto)
  unfolding inst_m_assn_def tabs_m_assn_def list_assn_conv_idx
   apply(sep_auto_all)
       apply(knock_down j)
      apply sep_auto_all
      apply(knock_down "inst.tabs (f_inst f) ! 0")
      apply(sep_auto_all)
      apply(knock_down "inst.tabs (f_inst f) ! 0")
       apply(sep_auto_all)
         apply(sep_auto heap: funcs_nth_type_triple)
        apply(sep_auto_all)
         apply(knock_down j)
        apply(sep_auto_all)
         apply(simp_all add:app_s_f_v_s_call_indirect_def Let_def split:list.splits)
     apply(auto simp add:stypes_def tab_cl_ind_def)
  done


find_theorems app_s_f_v_s_mem_size

lemmas splits = 
  frame_context_m.splits frame_context.splits config.splits config_m.splits redex.splits prod.splits

lemmas defs =  
  Heap_Monad.return_def Heap_Monad.heap_def 
  config_m_to_config_def frame_context_m_to_frame_context_def


abbreviation cfg_m_pair_assn where 
  "cfg_m_pair_assn i_s p p_m \<equiv> 
  let (cfg, res) = p in 
  let (cfg_m, res_m) = p_m in 
  cfg_m_assn i_s cfg cfg_m * \<up>(res = res_m)"

  
lemma run_step_b_e_m_triple:
    "<cfg_m_assn i_s cfg cfg_m> 
    run_step_b_e_m b_e cfg_m 
    <\<lambda>r. cfg_m_pair_assn i_s (run_step_b_e b_e cfg) r>\<^sub>t"
proof - 
  obtain d s fc fcs where config:"cfg = Config d s fc fcs"
    by(erule config.exhaust)
  obtain redex lcs nf f where frame:"fc = Frame_context redex lcs nf f" 
    by(erule frame_context.exhaust)
  obtain v_s es b_es where redex:"redex = Redex v_s es b_es" 
    by(erule redex.exhaust)

  obtain d_m s_m fc_m fcs_m where config_m:"cfg_m = Config_m d_m s_m fc_m fcs_m" 
    by(erule config_m.exhaust)  
  obtain redex_m lcs_m nf_m f_locs1 f_inst2 
    where frame_m:"fc_m = Frame_context_m redex_m lcs_m nf_m f_locs1 f_inst2" 
    by(erule frame_context_m.exhaust)
  obtain v_s_m es_m b_es_m where redex_m:"redex_m = Redex v_s_m es_m b_es_m" 
    by(erule redex.exhaust)

  note unfold_vars_m = config_m frame_m redex_m

  note unfold_vars = config frame redex unfold_vars_m

  note unfold_vars_assns = unfold_vars cfg_m_assn_def fc_m_assn_def

  show ?thesis
  proof (cases b_e)
    case (Tee_local k)
    then show ?thesis unfolding unfold_vars_assns by sep_auto
  next
    case (Set_global k)
    then show ?thesis unfolding unfold_vars_assns s_m_assn_def 
      (*comment on instability*)
      by (sep_auto heap:set_global_triple split:prod.splits)
  next
    case (Load t tp_sx a off)
    then show ?thesis sorry
  next
    case (Store t tp a off)
    then show ?thesis sorry
  next
    case Grow_memory
    then show ?thesis sorry
  next
    case Current_memory
    then show ?thesis 
      unfolding unfold_vars_assns s_m_assn_def mems_m_assn_def 
      by(sep_auto heap:mem_size_triple split:prod.splits)
  next
    case (Set_local k)
    then show ?thesis 
      unfolding unfold_vars_assns
      by (sep_auto heap: set_local_triple[of _ _ f f_inst2] split:prod.splits)
  next
    case (Get_local k)
    then show ?thesis 
      unfolding unfold_vars_assns by (sep_auto heap:get_local_triple)
  next
    case (Get_global k)
    then show ?thesis 
      unfolding unfold_vars_assns s_m_assn_def by (sep_auto heap:get_global_triple split:prod.splits)
  next
    case (Call k)
    then show ?thesis 
      unfolding unfold_vars_assns by (sep_auto heap:call_triple split:prod.splits)
  next
    case (Call_indirect k)
    then show ?thesis 
      unfolding unfold_vars_assns s_m_assn_def by (sep_auto heap:call_indirect_triple split:prod.splits)
  next
    case Return (* this case relies on garbage collection *)

    show ?thesis
      unfolding Return unfold_vars_assns fcs_m_assn_def
      by (sep_auto split:splits list.split)
  next
    case (Block tf b_ebs)
    then show ?thesis unfolding unfold_vars_assns by(sep_auto split:tf.splits)
  next
    case (Loop tfs b_els)
    then show ?thesis unfolding unfold_vars_assns by(sep_auto split:tf.splits)
  next
    case (Br k)
    then show ?thesis unfolding unfold_vars_assns by(sep_auto split:label_context.splits)
  next
    case Unreachable
    then show ?thesis unfolding unfold_vars_assns by sep_auto
  next
    case Nop
    then show ?thesis unfolding unfold_vars_assns by sep_auto
  next
    case Drop 
    then show ?thesis unfolding unfold_vars_assns by sep_auto
  next
    case Select 
    then show ?thesis unfolding unfold_vars_assns by sep_auto
  next
    case (If tf es1 es2) 
    then show ?thesis unfolding unfold_vars_assns by sep_auto
  next
    case (Br_if k)
    then show ?thesis unfolding unfold_vars_assns by sep_auto
  next
    case (Br_table ks k)
    then show ?thesis unfolding unfold_vars_assns by sep_auto
  next
    case (EConst k)
    then show ?thesis unfolding unfold_vars_assns by sep_auto
  next
    case (Unop t op)
    then show ?thesis unfolding unfold_vars_assns by sep_auto
  next
    case (Binop t op)
    then show ?thesis unfolding unfold_vars_assns by sep_auto
  next
    case (Testop t op)
    then show ?thesis unfolding unfold_vars_assns by sep_auto
  next
    case (Relop t op)
    then show ?thesis unfolding unfold_vars_assns by sep_auto
  next
    case (Cvtop t2 op t1 sx)
    then show ?thesis unfolding unfold_vars_assns by sep_auto
  qed
qed

abbreviation "s_m_vs_pair_assn i_s \<equiv> \<lambda>(s, vs) (s_m, vs_m). s_m_assn i_s s s_m * \<up>(vs=vs_m)"

abbreviation "s_m_vs_opt_assn i_s a a_m s s_m \<equiv> (case a of 
   Some s_vs \<Rightarrow> (case a_m of Some s_vs_m \<Rightarrow> s_m_vs_pair_assn i_s s_vs s_vs_m | None \<Rightarrow> false) 
 | None \<Rightarrow> (case a_m of Some s_vs_m \<Rightarrow> false | None \<Rightarrow> s_m_assn i_s s s_m)) "

lemma host_apply_impl_m_triple:
 "< s_m_assn i_s s s_m>
 host_apply_impl_m s_m tf h vs
 <\<lambda>r. s_m_vs_opt_assn i_s (host_apply_impl s tf h vs) r s s_m>"
  sorry

lemma host_apply_impl_m_triple':
 "< funcs_m_assn i_s (s.funcs s) (s_m.funcs s_m) 
* tabs_m_assn (s.tabs s) (s_m.tabs s_m) * mems_m_assn (s.mems s) (s_m.mems s_m) 
* globs_m_assn (s.globs s) (s_m.globs s_m)>
 host_apply_impl_m s_m tf h vs
 <\<lambda>r. s_m_vs_opt_assn i_s (host_apply_impl s tf h vs) r s s_m>"
  sorry

lemma host_apply_impl_m_triple'':
 "< s_m.funcs s_m \<mapsto>\<^sub>a fs_i * list_assn (cl_m_assn i_s) (s.funcs s) fs_i
* tabs_m_assn (s.tabs s) (s_m.tabs s_m) * mems_m_assn (s.mems s) (s_m.mems s_m) 
* globs_m_assn (s.globs s) (s_m.globs s_m)>
 host_apply_impl_m s_m tf h vs
 <\<lambda>r. s_m_vs_opt_assn i_s (host_apply_impl s tf h vs) r s s_m>"
  sorry


lemma ent_triple_preI:
  assumes "\<And>h. h\<Turnstile>P \<Longrightarrow> P \<Longrightarrow>\<^sub>A Q"
  shows "P \<Longrightarrow>\<^sub>A Q"
  using assms unfolding entails_def by auto

method extract_pre_pure' uses dest =
  (rule hoare_triple_preI | rule ent_triple_preI | drule asm_rl[of "_\<Turnstile>_"]),
  (determ \<open>elim mod_starE dest[elim_format] extract_pure_rules[elim_format]\<close>)?,
  ((determ \<open>thin_tac "_ \<Turnstile> _"\<close>)+)?,
  (simp (no_asm) only: triv_forall_equality)?

lemma pure_dup:
  assumes "is_pure_assn P" 
  shows "P = P*P" 
  using assms unfolding is_pure_assn_def
  by auto


lemma [sep_heap_rules]:
  "< fs_m\<mapsto>\<^sub>a fs_i * list_assn (cl_m_assn i_s) fs fs_i> 
  Array.nth fs_m i 
  <\<lambda>r. \<up>(i < length fs_i \<and> r = fs_i!i) 
  * cl_m_assn i_s (fs!i) r * fs_m \<mapsto>\<^sub>a fs_i * list_assn (cl_m_assn i_s) fs fs_i>"
  unfolding funcs_m_assn_def list_assn_conv_idx 
  apply(sep_auto)
  apply(extract_pre_pure')
  apply(extract_list_idx i)
  apply(subst pure_dup[OF cl_m_assn_pure])
  apply(reinsert_list_idx i)
  apply(sep_auto)
  done


lemma run_step_e_m_triple:
    "<cfg_m_assn i_s cfg cfg_m> 
    run_step_e_m e cfg_m 
    <\<lambda>r. cfg_m_pair_assn i_s (run_step_e e cfg) r>\<^sub>t"
proof -
  obtain d s fc fcs where config:"cfg = Config d s fc fcs"
    by(erule config.exhaust)
  obtain redex lcs nf f where frame:"fc = Frame_context redex lcs nf f" 
    by(erule frame_context.exhaust)
  obtain v_s es b_es where redex:"redex = Redex v_s es b_es" 
    by(erule redex.exhaust)
  obtain d_m s_m fc_m fcs_m where config_m:"cfg_m = Config_m d_m s_m fc_m fcs_m" 
    by(erule config_m.exhaust)  
  obtain redex_m lcs_m nf_m f_locs1 f_inst2 
    where frame_m:"fc_m = Frame_context_m redex_m lcs_m nf_m f_locs1 f_inst2" 
    by(erule frame_context_m.exhaust)
  obtain v_s_m es_m b_es_m where redex_m:"redex_m = Redex v_s_m es_m b_es_m" 
    by(erule redex.exhaust)
  note unfold_vars_m = config_m frame_m redex_m
  note unfold_vars = config frame redex unfold_vars_m
  note unfold_vars_assns = unfold_vars cfg_m_assn_def fc_m_assn_def

  show ?thesis 
  proof (cases e)
    case (Basic b_e)
    have 1:"run_step_e_m (Basic b_e) cfg_m = run_step_b_e_m b_e cfg_m"
      unfolding unfold_vars_m by simp
    have 2:"run_step_e (Basic b_e) cfg = run_step_b_e b_e cfg"
      unfolding unfold_vars by simp 
    show ?thesis unfolding Basic 1 2 by(sep_auto heap:run_step_b_e_m_triple)
  next
    case (Invoke i_cl)

    show ?thesis unfolding Invoke unfold_vars_assns 
      supply [simp] = Let_def and 
        [split] = splits v.splits option.splits cl.splits cl_m.splits tf.splits nat.splits
      and [sep_heap_rules] = host_apply_impl_m_triple''
      apply(sep_auto simp:s_m_assn_def funcs_m_assn_def heap del: nth_rule)
      supply [simp] = cl_m_assn_def locs_m_assn_def s_m_assn_def funcs_m_assn_def fc_m_assn_def 
                apply(sep_auto_all)
      apply (sep_auto)
      done
  next
    case Trap
    then show ?thesis unfolding unfold_vars by sep_auto
  next
    case (Label x41 x42 x43)
    then show ?thesis unfolding unfold_vars by sep_auto
  next
    case (Frame x51 x52 x53)
    then show ?thesis unfolding unfold_vars by sep_auto
  qed
qed 

lemma run_step_e_m_run_step_e:
  assumes 
    "execute (run_step_e_m e cfg_m) h = Some ((cfg_m', res), h')"
  shows 
    "run_step_e e (config_m_to_config h cfg_m) = ((config_m_to_config h' cfg_m'), res)"
proof(cases e)
  case (Basic b_e)
  have 1:"run_step_e_m e cfg_m = run_step_b_e_m b_e cfg_m" unfolding Basic
    by(rule config_m.induct, auto simp add: defs split: splits)
  have "run_step_e e (config_m_to_config h cfg_m) = run_step_b_e b_e (config_m_to_config h cfg_m)"
    unfolding Basic by(rule config.induct, auto simp add: defs split: splits) 
  also have "... = ((config_m_to_config h' cfg_m'), res)" 
    using assms sorry
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