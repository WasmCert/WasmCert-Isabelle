theory Wasm_Monad_Assertions 
  imports Wasm_Interpreter_Monad "../libs/Misc_Generic_Lemmas" "../libs/List_Assn" begin
(* separation logic methods *)

method extract_list_idx for i :: nat =
  (subst listI_assn_extract[of i], (simp;fail), (simp;fail))
  
method reinsert_list_idx for i :: nat =
  rule listI_assn_reinsert[where i=i] listI_assn_reinsert'[where i=i],
  (frame_inference; fail),
  (simp;fail),
  (simp;fail)

method knock_down for i :: nat = 
 extract_pre_pure?, extract_list_idx i, sep_auto, extract_pre_pure?, reinsert_list_idx i

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



abbreviation "expect_assn A B x_opt y_opt \<equiv> (case x_opt of 
  Some x \<Rightarrow> (case y_opt of Some y \<Rightarrow> A x y | None \<Rightarrow> false)
  | None \<Rightarrow> (case y_opt of Some y \<Rightarrow> false | None \<Rightarrow> B)
  )"


(* assertions *) 

definition "inst_m_assn i i_m \<equiv> 
    inst_m.types i_m \<mapsto>\<^sub>a inst.types i
  * inst_m.funcs i_m \<mapsto>\<^sub>a inst.funcs i  
  * inst_m.tabs  i_m \<mapsto>\<^sub>a inst.tabs  i 
  * inst_m.mems  i_m \<mapsto>\<^sub>a inst.mems  i 
  * inst_m.globs i_m \<mapsto>\<^sub>a inst.globs i"

type_synonym inst_store = "(inst list \<times> inst_m list)"

definition "inst_store_assn \<equiv> \<lambda>(is, i_ms). list_assn inst_m_assn is i_ms"

definition "inst_at \<equiv> \<lambda>(is, i_ms) (i, i_m) j. j < min (length is) (length i_ms) 
  \<and> is!j = i \<and> i_ms!j = i_m"

abbreviation "contains_inst i_s i \<equiv> \<exists> j. inst_at i_s i j"

definition "inst_store_subset \<equiv> \<lambda>(is1, i_ms1) (is2, i_ms2). 
  set (zip is1 i_ms1) \<subseteq> set (zip is2 i_ms2)"

lemma inst_store_extend_preserve_contains:
  assumes "inst_at i_s' i j" "inst_store_subset i_s' i_s" 
  shows "contains_inst i_s i"
  using assms unfolding inst_store_subset_def inst_at_def
  apply(simp split:prod.splits) 
  by (metis in_set_zip prod.sel(1) prod.sel(2) subset_code(1))

definition cl_m_agree_j :: "inst_store \<Rightarrow> nat \<Rightarrow> cl \<Rightarrow> cl_m \<Rightarrow> bool" where 
  "cl_m_agree_j i_s j cl cl_m = (case cl of 
  cl.Func_native i tf ts b_es \<Rightarrow> 
    (case cl_m of 
    cl_m.Func_native i_m tf_m ts_m b_es_m \<Rightarrow> 
    inst_at i_s (i, i_m) j \<and> tf = tf_m \<and> ts = ts_m \<and> b_es = b_es_m
  | cl_m.Func_host tf_m host_m \<Rightarrow> False)
| cl.Func_host tf host \<Rightarrow> 
    (case cl_m of 
    cl_m.Func_native i_m tf_m ts_m b_es_m \<Rightarrow> False 
  | cl_m.Func_host tf_m host_m \<Rightarrow> tf = tf_m \<and> host = host_m)
)"

abbreviation "cl_m_agree i_s cl cl_m \<equiv> \<exists>j. cl_m_agree_j i_s j cl cl_m"

definition funcs_m_assn :: "inst_store \<Rightarrow> cl list \<Rightarrow> cl_m array \<Rightarrow> assn" where
  "funcs_m_assn i_s fs fs_m = (\<exists>\<^sub>A fs_i. fs_m \<mapsto>\<^sub>a fs_i *\<up>(list_all2 (cl_m_agree i_s)  fs fs_i))"

definition tabinst_m_assn :: "tabinst \<Rightarrow> tabinst_m \<Rightarrow> assn" where 
  "tabinst_m_assn = (\<lambda>(tr,tm) (tr_m,tm_m). tr_m \<mapsto>\<^sub>a tr * \<up>(tm = tm_m))"

definition "mem_m_assn \<equiv> \<lambda>(mr,mm) (mr_m,mm_m). mr_m \<mapsto>\<^sub>b\<^sub>aRep_mem_rep mr * \<up>(mm_m=mm)"

definition mems_m_assn :: "mem list \<Rightarrow> mem_m array \<Rightarrow> assn" where
  "mems_m_assn ms ms_m = (\<exists>\<^sub>A ms_i. ms_m \<mapsto>\<^sub>a ms_i  * list_assn mem_m_assn ms ms_i)"

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
  \<up>(redex = redex_m \<and> lcs = lcs_m \<and> nf = nf_m \<and> contains_inst i_s (f_inst f, f_inst2))
  * locs_m_assn (f_locs f) f_locs1
)"

definition "fcs_m_assn i_s fcs fcs_m \<equiv> list_assn (fc_m_assn i_s) fcs fcs_m"

definition cfg_m_assn :: "inst_store \<Rightarrow> inst_store \<Rightarrow> config \<Rightarrow> config_m \<Rightarrow> assn" where
  "cfg_m_assn i_s i_s' cfg cfg_m = (
  case cfg of Config d s fc fcs \<Rightarrow>
  case cfg_m of Config_m d_m s_m fc_m fcs_m \<Rightarrow> 
  \<up>(d=d_m \<and> inst_store_subset i_s' i_s) 
  * s_m_assn i_s' s s_m * fc_m_assn i_s fc fc_m * fcs_m_assn i_s fcs fcs_m
  * inst_store_assn i_s
)"     



lemma cl_m_agree_type: "cl_m_agree i_s cl cl_m \<Longrightarrow> cl_type cl = cl_m_type cl_m"
  unfolding cl_m_agree_j_def cl_type_def cl_m_type_def
  by (auto, simp split:cl.splits cl_m.splits)


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

lemma [sep_heap_rules]: "<mem_m_assn m mi> 
    len_byte_array (fst mi) 
    <\<lambda>r. mem_m_assn m mi * \<up>(r=length (Rep_mem_rep (fst m)))>"
  unfolding mem_m_assn_def
  by (sep_auto split: prod.splits)

(* misc triples *)

abbreviation "fits_at_in l n la \<equiv> (length l > 0 \<longrightarrow> n+length l \<le> length la)"

abbreviation "insert_at_in l n la \<equiv> take n la @ l @ drop (n+length l) la"

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

end