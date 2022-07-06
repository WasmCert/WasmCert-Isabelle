theory Wasm_Interpreter_Monad_Config imports  Wasm_Countable Wasm_Interpreter 
  "HOL-Imperative_HOL.Array" 
  "../libs/Byte_Array"   "../libs/List_Assn" begin 

instance uint8 :: heap ..
instance tf :: heap ..
instance v :: heap ..
instance global_ext :: (heap) heap ..

type_synonym mem_m = "(byte_array) \<times> nat option"

record inst_m = \<comment> \<open>instances\<close>
  types :: "tf array"
  funcs :: "i array"
  tabs :: "i array"
  mems :: "i array"
  globs :: "i array"

instance inst_m_ext :: (countable) countable
proof(rule countable_classI[of "\<lambda>i. to_nat (inst_m.types i, inst_m.funcs i, inst_m.tabs i, inst_m.mems i, inst_m.globs i, inst_m.more i)"])
qed auto

datatype cl_m = \<comment> \<open>function closures\<close>
  Func_native inst_m (cl_m_type:tf) "t list" "b_e list"
| Func_host (cl_m_type:tf) host

instance cl_m :: countable
  by (countable_datatype)

instance cl_m :: heap ..

type_synonym tabinst_m = "(i option) array \<times> nat option"

record s_m = \<comment> \<open>store\<close>
  funcs :: "cl_m array"
  tabs :: "tabinst_m array"
  mems :: "mem_m array"
  globs :: "global array"

instance s_m_ext :: (countable) countable
proof(rule countable_classI[of "\<lambda>i. to_nat (s_m.funcs i, s_m.tabs i, s_m.mems i, s_m.globs i, s_m.more i)"])
qed auto

instance s_m_ext :: (heap) heap ..

(* 0: redex, 1: label contexts, 2: frame arity, 3: frame *)
datatype frame_context_m = Frame_context_m redex "label_context list" (frame_arity:nat) (f_locs_m:"v array") (f_inst_m:"inst_m")

datatype config_m = Config_m depth s_m frame_context_m "frame_context_m list"



(* assertions *) 

definition "inst_m_assn i i_m \<equiv> 
    inst_m.types i_m \<mapsto>\<^sub>a inst.types i
  * inst_m.funcs i_m \<mapsto>\<^sub>a inst.funcs i  
  * inst_m.tabs  i_m \<mapsto>\<^sub>a inst.tabs  i 
  * inst_m.mems  i_m \<mapsto>\<^sub>a inst.mems  i 
  * inst_m.globs i_m \<mapsto>\<^sub>a inst.globs i"

type_synonym inst_assocs = "(inst list \<times> inst_m list)"

definition inst_assocs_assn :: "inst_assocs \<Rightarrow> assn" where
  "inst_assocs_assn \<equiv> \<lambda>(is, i_ms). list_assn inst_m_assn is i_ms"

definition inst_at :: "inst_assocs \<Rightarrow> (inst \<times> inst_m) \<Rightarrow> nat \<Rightarrow> bool " where 
  "inst_at \<equiv> \<lambda>(is, i_ms) (i, i_m) j. j < min (length is) (length i_ms) 
  \<and> is!j = i \<and> i_ms!j = i_m"

abbreviation "contains_inst i_s i \<equiv> \<exists> j. inst_at i_s i j"

definition inst_assocs_extension :: "inst_assocs \<Rightarrow> inst_assocs \<Rightarrow> bool" where
  "inst_assocs_extension \<equiv> \<lambda>(is, i_ms) (is', i_ms'). 
  length is = length i_ms \<and> (\<exists>a b. is' = is @ a \<and> i_ms' = i_ms @ b)"

lemma inst_assocs_extension_preserves_inst_at:
  assumes "inst_assocs_extension ias ias'" "inst_at ias i j"
  shows "inst_at ias' i j"
  using assms unfolding inst_at_def inst_assocs_extension_def
  by auto

lemma inst_assocs_assn_extension_id:
  "h \<Turnstile> inst_assocs_assn ias \<Longrightarrow> inst_assocs_extension ias ias"
  unfolding inst_assocs_assn_def inst_assocs_extension_def
  apply(sep_auto)
  apply(extract_pre_pure)
  done

definition cl_m_agree_j :: "inst_assocs \<Rightarrow> nat \<Rightarrow> cl \<Rightarrow> cl_m \<Rightarrow> bool" where 
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

definition "cl_m_agree i_s cl cl_m \<equiv> \<exists>j. cl_m_agree_j i_s j cl cl_m"

definition funcs_m_assn :: "inst_assocs \<Rightarrow> cl list \<Rightarrow> cl_m array \<Rightarrow> assn" where
  "funcs_m_assn i_s fs fs_m = (\<exists>\<^sub>A fs_i. fs_m \<mapsto>\<^sub>a fs_i *\<up>(list_all2 (cl_m_agree i_s)  fs fs_i))"

definition tabinst_m_assn :: "tabinst \<Rightarrow> tabinst_m \<Rightarrow> assn" where 
  "tabinst_m_assn = (\<lambda>(tr,tm) (tr_m,tm_m). tr_m \<mapsto>\<^sub>a tr * \<up>(tm = tm_m))"

definition "mem_m_assn \<equiv> \<lambda>(mr,mm) (mr_m,mm_m). mr_m \<mapsto>\<^sub>b\<^sub>aRep_mem_rep mr * \<up>(mm_m=mm)"

definition mems_m_assn :: "mem list \<Rightarrow> mem_m array \<Rightarrow> assn" where
  "mems_m_assn ms ms_m = (\<exists>\<^sub>A ms_i. ms_m \<mapsto>\<^sub>a ms_i  * list_assn mem_m_assn ms ms_i)"

definition tabs_m_assn :: "tabinst list \<Rightarrow> tabinst_m array \<Rightarrow> assn" where
 "tabs_m_assn ts ts_m = (\<exists>\<^sub>A ts_i. ts_m \<mapsto>\<^sub>a ts_i * list_assn tabinst_m_assn ts ts_i)"

definition "globs_m_assn gs gs_m \<equiv> gs_m \<mapsto>\<^sub>a gs"

definition s_m_assn :: "inst_assocs \<Rightarrow> s \<Rightarrow> s_m \<Rightarrow> assn" where 
  "s_m_assn i_s s s_m = 
  funcs_m_assn i_s (s.funcs s) (s_m.funcs s_m)
* tabs_m_assn  (s.tabs s)  (s_m.tabs s_m)
* mems_m_assn  (s.mems s)  (s_m.mems s_m)
* globs_m_assn (s.globs s) (s_m.globs s_m)"

definition locs_m_assn :: "v list \<Rightarrow> v array \<Rightarrow> assn" where 
  "locs_m_assn locs locs_m = locs_m \<mapsto>\<^sub>a locs"

definition fc_m_assn :: "inst_assocs \<Rightarrow> frame_context \<Rightarrow> frame_context_m \<Rightarrow> assn" where 
  "fc_m_assn i_s fc fc_m = (
  case fc of Frame_context redex lcs nf f \<Rightarrow> 
  case fc_m of Frame_context_m redex_m lcs_m nf_m f_locs1 f_inst2 \<Rightarrow>
  \<up>(redex = redex_m \<and> lcs = lcs_m \<and> nf = nf_m \<and> contains_inst i_s (f_inst f, f_inst2))
  * locs_m_assn (f_locs f) f_locs1
)"

lemma inst_assocs_extension_preserves_fc_m_assn:
  assumes "inst_assocs_extension ias ias'" 
  shows "fc_m_assn ias fc fc_m \<Longrightarrow>\<^sub>A fc_m_assn ias' fc fc_m"
  using inst_assocs_extension_preserves_inst_at[OF assms] 
  unfolding fc_m_assn_def
  by (sep_auto split:frame_context.splits frame_context_m.splits)

definition "fcs_m_assn i_s fcs fcs_m \<equiv> list_assn (fc_m_assn i_s) fcs fcs_m"

lemma inst_assocs_extension_preserves_fcs_m_assn:
  assumes "inst_assocs_extension ias ias'" 
  shows "fcs_m_assn ias fcs fcs_m \<Longrightarrow>\<^sub>A fcs_m_assn ias' fcs fcs_m"
  using inst_assocs_extension_preserves_fc_m_assn[OF assms] 
  unfolding fcs_m_assn_def
  by (rule list_assn_mono)

definition cfg_m_assn :: "inst_assocs \<Rightarrow> config \<Rightarrow> config_m \<Rightarrow> assn" where
  "cfg_m_assn i_s cfg cfg_m = (
  case cfg of Config d s fc fcs \<Rightarrow>
  case cfg_m of Config_m d_m s_m fc_m fcs_m \<Rightarrow> 
  \<up>(d=d_m) 
  * s_m_assn i_s s s_m * fc_m_assn i_s fc fc_m * fcs_m_assn i_s fcs fcs_m
  * inst_assocs_assn i_s
)"     



abbreviation "expect_assn A B x_opt y_opt \<equiv> (case x_opt of 
  Some x \<Rightarrow> (case y_opt of Some y \<Rightarrow> A x y | None \<Rightarrow> false)
  | None \<Rightarrow> (case y_opt of Some y \<Rightarrow> false | None \<Rightarrow> B)
  )"


end