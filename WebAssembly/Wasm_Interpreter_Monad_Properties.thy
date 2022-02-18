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

(* TODO: the lemmas below should probably appear earlier in the development *)
(* however they depend on more_more_word *)
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

abbreviation "inst_store_assn \<equiv> \<lambda>(is, i_ms). list_assn inst_m_assn is i_ms"

abbreviation "inst_at \<equiv> \<lambda>(is, i_ms) (i, i_m) j. j < length is \<and> is!j = i \<and> i_ms!j = i_m"

abbreviation "contains_inst_assn i_s i \<equiv> \<exists>\<^sub>A j. \<up>(inst_at i_s i j)"

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

definition funcs_m_assn :: "inst_store \<Rightarrow> cl list \<Rightarrow> cl_m array \<Rightarrow> assn" where
  "funcs_m_assn i_s fs fs_m = (\<exists>\<^sub>A fs_i. fs_m \<mapsto>\<^sub>a fs_i * list_assn (cl_m_assn i_s) fs fs_i)"

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
  \<up>(redex = redex_m \<and> lcs = lcs_m \<and> nf = nf_m)
  * contains_inst_assn i_s (f_inst f, f_inst2)
  * locs_m_assn (f_locs f) f_locs1
)"

definition "fcs_m_assn i_s fcs fcs_m \<equiv> list_assn (fc_m_assn i_s) fcs fcs_m"

definition cfg_m_assn :: "inst_store \<Rightarrow> config \<Rightarrow> config_m \<Rightarrow> assn" where
  "cfg_m_assn i_s cfg cfg_m = (
  case cfg of Config d s fc fcs \<Rightarrow>
  case cfg_m of Config_m d_m s_m fc_m fcs_m \<Rightarrow> 
  \<up>(d=d_m) * s_m_assn i_s s s_m * fc_m_assn i_s fc fc_m * fcs_m_assn i_s fcs fcs_m
   * inst_store_assn i_s
)"     



(*  heap rules, lemmas etc. about the assertions above *)

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

lemma pure_dup:
  assumes "is_pure_assn P" 
  shows "P = P*P" 
  using assms unfolding is_pure_assn_def
  by auto

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

lemma [sep_heap_rules]: "<mem_m_assn m mi> 
    len_byte_array (fst mi) 
    <\<lambda>r. mem_m_assn m mi * \<up>(r=length (Rep_mem_rep (fst m)))>"
  unfolding mem_m_assn_def
  by (sep_auto split: prod.splits)

definition "fc_m_assn_pure fc fc_m \<equiv> (
  case fc of Frame_context redex lcs nf f \<Rightarrow> 
  case fc_m of Frame_context_m redex_m lcs_m nf_m f_locs1 f_inst2 \<Rightarrow>
  redex = redex_m \<and> lcs = lcs_m \<and> nf = nf_m)"

lemma extract_pre_fc_m_assn[extract_pure_rules]: 
  "h \<Turnstile> fc_m_assn i_s fc fc_m \<Longrightarrow> fc_m_assn_pure fc fc_m"
  unfolding fc_m_assn_def fc_m_assn_pure_def 
  by (sep_auto split:frame_context.splits frame_context_m.splits)

lemma [simp]:"fcs_m_assn i_s (fc#fcs) (fc_m#fcs_m) = 
  fc_m_assn i_s fc fc_m * fcs_m_assn i_s fcs fcs_m"
  unfolding fcs_m_assn_def by simp

definition "cfg_m_assn_pure cfg cfg_m = (
  case cfg of Config d s fc fcs \<Rightarrow>
  case cfg_m of Config_m d_m s_m fc_m fcs_m \<Rightarrow> 
  d=d_m \<and> fc_m_assn_pure fc fc_m \<and> length fcs = length fcs_m
)"     

lemma extract_pre_cfg_m_assn[extract_pure_rules]: 
  "h \<Turnstile> cfg_m_assn i_s cfg cfg_m \<Longrightarrow> cfg_m_assn_pure cfg cfg_m"
  unfolding cfg_m_assn_def cfg_m_assn_pure_def fcs_m_assn_def
  apply (sep_auto split:config.splits config_m.splits)
  subgoal by (metis mod_starE extract_pre_fc_m_assn)
  by (metis mod_starE extract_pre_list_assn_lengthD) 

lemma array_fold_map_triple:
  assumes "length l = length l'"
          "((length l)+1) = length Ps"
          "\<And>i. \<lbrakk>i < length l\<rbrakk> \<Longrightarrow> <Ps!i> f (l!i) <\<lambda>x. \<up>(x = l'!i) * Ps!(i+1)>"
  shows "<Ps!0> Heap_Monad.fold_map f l <\<lambda>res. \<up>(res = l') * Ps!(length l) >"
  using assms
proof(induct l arbitrary: l' Ps)
case Nil
  thus ?case
    by sep_auto
next
  case (Cons x xl)
  obtain y yl where l'_is:"l' = y#yl" "length xl = length yl"
    using Cons(2)
    by (metis length_Suc_conv)
  have 1:"length xl + 1 = length (tl Ps)"
         "Ps \<noteq> []"
    using Cons(3)
    by auto
  have "(\<And>i. i < length xl \<Longrightarrow>
          <tl Ps ! i> f (xl ! i)
          <\<lambda>x. \<up> (x = yl ! i) *
               tl Ps ! (i + 1)>)"
    using Cons(4) Misc.nth_tl[OF 1(2)] l'_is(1)
    by simp (metis Suc_mono nth_Cons_Suc)
  hence "<Ps ! 1> Heap_Monad.fold_map f xl
  <\<lambda>res. \<up> (res = yl) * Ps ! (length xl + 1)>"
    using Cons(1)[OF l'_is(2) 1(1)] Misc.nth_tl[OF 1(2)]
    by simp
  moreover
  have " <Ps ! 0> f x <\<lambda>x. \<up>(x = l'!0) * Ps!1>"
    using Cons(4)[of 0]
    by simp
  ultimately
  show ?case
    using l'_is(1)
    by sep_auto
qed

lemma list_blit_array_triple:
  assumes "length l + n \<le> length la"
  shows "<a \<mapsto>\<^sub>a la> 
           list_blit_array l a n
         <\<lambda>r. a \<mapsto>\<^sub>a (take n la @ l @ drop (n+length l) la)>"
  using assms
proof (induct l arbitrary: la n)
  case Nil
  thus ?case
    by sep_auto
next
  case (Cons x xl)
  have 1:"length xl + (Suc n) \<le> length (list_update la n x)"
    using Cons(2)
    by auto
  have 2:"<a \<mapsto>\<^sub>a (list_update la n x)>
            list_blit_array xl a (Suc n)
          <\<lambda>r. a \<mapsto>\<^sub>a
            (take (Suc n) (list_update la n x) @
             xl @ drop ((Suc n) + length xl) (list_update la n x))>"
    using Cons(1)[OF 1]
    by blast
  have 3:"take n la @
             x #
             xl @
             drop (Suc (n + length xl)) la = (take (Suc n) (list_update la n x) @
             xl @ drop ((Suc n) + length xl) (list_update la n x))"
    by simp (metis 1 Suc_le_eq add_leD2 length_list_update take_update_last)
  show ?case
    apply sep_auto
    using upd_conv_take_nth_drop[of n la x] Cons(2) apply simp
    using 2 3 apply simp apply (metis append_Cons append_assoc empty_append_eq_id)
    done
qed

lemma array_blit_map_triple:
  assumes  "length l = length l'"
           "length l + n \<le> length la"
           "<P> Heap_Monad.fold_map f l <\<lambda>res. \<up>(res = l') * Q >"
  shows " <a \<mapsto>\<^sub>a la * P> 
            array_blit_map l f a n
          <\<lambda>r. a \<mapsto>\<^sub>a (take n la @ l' @ drop (n+length l') la) * Q >"
proof -
  have 1:"length l' + n \<le> length la"
    using assms
    by auto
  show ?thesis
    by (sep_auto simp del: list_blit_array.simps heap: list_blit_array_triple[OF 1] assms(3))
qed

(* hoare triples for run_step_b_e_m *)

lemma mem_size_triple:
  assumes "inst_at (is, i_ms) (f_inst f, f_inst2) j" 
  shows 
  "< mems_m_assn ms ms_m * inst_store_assn (is, i_ms) > 
    app_s_f_v_s_mem_size_m ms_m f_inst2 v_s 
  <\<lambda>r. \<up>(r = app_s_f_v_s_mem_size ms f v_s) *
   mems_m_assn ms ms_m * inst_store_assn (is, i_ms)>"
  using assms
  unfolding app_s_f_v_s_mem_size_m_def inst_m_assn_def mems_m_assn_def list_assn_conv_idx
  apply sep_auto
   apply (knock_down j)
  apply(sep_auto)
  apply(knock_down "inst.mems (f_inst f) ! 0")
   apply (sep_auto)
  apply (auto simp add: app_s_f_v_s_mem_size_def smem_ind_def mem_size_def 
        mem_length_def mem_rep_length_def split: option.split list.split)  
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

(* memory stuff *)

lemma [sep_heap_rules]: 
    "< mem_m_assn m m_m > 
      grow_zeroed_byte_array (fst m_m) n 
    <\<lambda>r. mem_m_assn (mem_append m n 0) (r,snd m_m)>\<^sub>t"
  unfolding mem_m_assn_def mem_append_def mem_rep_append_def
  by(sep_auto split:prod.splits simp:Abs_mem_rep_inverse)

lemma mem_grow_triple:
  assumes "inst_at (is, i_ms) (f_inst f, f_inst2) j" 
  shows 
  "< mems_m_assn ms ms_m * inst_store_assn (is, i_ms) > 
    app_s_f_v_s_mem_grow_m ms_m f_inst2 v_s 
  <\<lambda>r. let (ms', v_s', res) = app_s_f_v_s_mem_grow ms f v_s in
   \<up>(r = (v_s', res)) * mems_m_assn ms' ms_m * inst_store_assn (is, i_ms)>\<^sub>t"
proof - 
  note expand = smem_ind_def mem_grow_def Let_def mem_size_def mem_length_def
        mem_rep_length_def mem_max_def
  note expand_with_assn = expand mem_m_assn_def mem_append_def
  note splits = option.splits list.splits if_splits prod.splits

  (* the "sep_auto simp:expand split:splits" list eliminate subgoals 
    by finding contradictions in their assumptions *)
  show ?thesis
    using assms 
    unfolding app_s_f_v_s_mem_grow_m_def app_s_f_v_s_mem_grow_def 
      inst_m_assn_def mems_m_assn_def
      list_assn_conv_idx
    apply(sep_auto split: v.splits)
        apply(knock_down "j")
       apply(sep_auto)
        apply(extract_list_idx "inst.mems (f_inst f) ! 0") 
        (* not reinserting immediately -- the extracted mem_m_assn keeps being necessary *)
        apply(sep_auto) 
       apply(sep_auto simp:expand split:splits) 
          apply(rule listI_assn_reinsert_upd, frame_inference, simp, simp)
          apply(sep_auto simp:mem_append_def zero_byte_def)
         apply(sep_auto simp:expand_with_assn split:splits)
        apply(sep_auto)
         apply(sep_auto simp:expand_with_assn split:splits) 
        apply(sep_auto simp:expand_with_assn split:splits) 
       apply(rule listI_assn_reinsert', frame_inference, simp, simp)
       apply(sep_auto)
      apply(sep_auto_all)
    done
qed

named_theorems load_rules

abbreviation "load32_mem_triple fl sx t_len m m_m n \<equiv> 
   <mem_m_assn m m_m> 
  fl (fst m_m) n         
   <\<lambda>r. \<up>(i32_impl_abs r = (deserialise_i32 \<circ> (case sx of S \<Rightarrow> sign_extend S 4 | U \<Rightarrow> id)) 
  (read_bytes m n t_len) 
  \<and> n + t_len \<le> mem_length m) 
  * mem_m_assn m m_m>" 

lemma [load_rules]: 
  "load32_mem_triple load_uint32           U 4 m m_m n"
  "load32_mem_triple load_uint32_of_uint8  U 1 m m_m n"
  "load32_mem_triple load_uint32_of_sint8  S 1 m m_m n"
  "load32_mem_triple load_uint32_of_uint16 U 2 m m_m n"
  "load32_mem_triple load_uint32_of_sint16 S 2 m m_m n"
  unfolding mem_m_assn_def i32_impl_abs_def deserialise_i32_def
    read_bytes_def mem_rep_read_bytes_def t_length_def mem_length_def mem_rep_length_def
  by (sep_auto simp:Abs_uint32'.rep_eq word_list_sign_extend_Rep_uint8 split:prod.splits)+

abbreviation "load64_mem_triple fl sx t_len m m_m n \<equiv> 
   <mem_m_assn m m_m> 
  fl (fst m_m) n         
   <\<lambda>r. \<up>(i64_impl_abs r = (deserialise_i64 \<circ> (case sx of S \<Rightarrow> sign_extend S 8 | U \<Rightarrow> id)) 
  (read_bytes m n t_len) 
  \<and> n + t_len \<le> mem_length m) 
  * mem_m_assn m m_m>" 

lemma [load_rules]: 
  "load64_mem_triple load_uint64           U 8 m m_m n"
  "load64_mem_triple load_uint64_of_uint8  U 1 m m_m n"
  "load64_mem_triple load_uint64_of_sint8  S 1 m m_m n"
  "load64_mem_triple load_uint64_of_uint16 U 2 m m_m n"
  "load64_mem_triple load_uint64_of_sint16 S 2 m m_m n"
  "load64_mem_triple load_uint64_of_uint32 U 4 m m_m n"
  "load64_mem_triple load_uint64_of_sint32 S 4 m m_m n"
  unfolding mem_m_assn_def i64_impl_abs_def deserialise_i64_def
    read_bytes_def mem_rep_read_bytes_def t_length_def mem_length_def mem_rep_length_def
  by (sep_auto simp:Abs_uint64'.rep_eq word_list_sign_extend_Rep_uint8 split:prod.splits)+

lemma load_triple: 
  "<mem_m_assn m m_m>
  load_m_v m_m n off t
  <\<lambda>r_opt. expect_assn (\<lambda>r r_m. \<up>(r_m = wasm_deserialise r t)) true 
  (load m n off (t_length t)) r_opt
  * mem_m_assn m m_m>"
  unfolding load_m_v_def load_def wasm_deserialise_def 
  by(sep_auto heap:load_rules split:t.splits simp:mem_length_def mem_rep_length_def
      read_bytes_def mem_rep_read_bytes_def t_length_def 
serialise_deserialise_i32 serialise_deserialise_i64)

lemma sign_extend_id: 
  "sign_extend sx (length bs) bs = bs"
  unfolding sign_extend_def
  by(simp add:msb_byte_def msbyte_def bytes_takefill_def)

lemma read_bytes_length:"n+l \<le> mem_length m \<Longrightarrow> length (read_bytes m n l) = l" 
  unfolding mem_length_def mem_rep_length_def read_bytes_def mem_rep_read_bytes_def
  by simp

lemma deserialise_i32_absorb_sign_extend: 
  "length bs \<le> 4 \<Longrightarrow> deserialise_i32 (sign_extend U 4 bs) = deserialise_i32 bs"
  unfolding deserialise_i32_def word_rcat_rev_def sign_extend_def bytes_takefill_def
    takefill_def zero_byte_def
  apply(simp split:list.splits)
  apply(auto)
     apply (simp add: zero_uint8.rep_eq)+
  done

lemma deserialise_i64_absorb_sign_extend: 
  "length bs \<le> 8 \<Longrightarrow> deserialise_i64 (sign_extend U 8 bs) = deserialise_i64 bs"
  unfolding deserialise_i64_def word_rcat_rev_def sign_extend_def bytes_takefill_def
    takefill_def zero_byte_def
  apply(simp split:list.splits)
  apply(auto)
     apply (simp add: zero_uint8.rep_eq)+
  done

lemma [load_rules]:
 "<mem_m_assn m m_m> 
  load_uint32_packed (fst m_m) n tp sx        
   <\<lambda>r. \<up>(i32_impl_abs r = (deserialise_i32 \<circ> sign_extend sx 4) (read_bytes m n (tp_length tp)) 
  \<and> n + 1 \<le> mem_length m) 
  * mem_m_assn m m_m>"
  unfolding load_uint32_packed_def 
  supply [simp] = tp_length_def t_length_def
  apply(sep_auto split:tp.splits sx.splits)
       apply(sep_auto heap:load_rules)+
  subgoal  using read_bytes_length sign_extend_id
    by metis
    apply(sep_auto heap:load_rules, 
      simp add:read_bytes_length deserialise_i32_absorb_sign_extend )+
  done 

lemma [load_rules]:
 "<mem_m_assn m m_m> 
  load_uint64_packed (fst m_m) n tp sx        
   <\<lambda>r. \<up>(i64_impl_abs r = (deserialise_i64 \<circ> sign_extend sx 8) (read_bytes m n (tp_length tp)) 
  \<and> n + 1 \<le> mem_length m) 
  * mem_m_assn m m_m>"
  unfolding load_uint64_packed_def 
  supply [simp] = tp_length_def t_length_def
  apply(sep_auto split:tp.splits sx.splits)
       apply(sep_auto heap:load_rules, 
        (simp add:read_bytes_length deserialise_i64_absorb_sign_extend)?)+
  done 

(* Note to self: had issues with sep_auto instantiating the postcondition by dropping the pure precondition *)

lemma load_packed_triple: 
  "<mem_m_assn m m_m>
  load_packed_m_v m_m n off t tp sx
  <\<lambda>r_opt. expect_assn (\<lambda>r r_m. \<up>(r_m = wasm_deserialise r t)) true
      (load_packed sx m n off (tp_length tp) (t_length t)) r_opt
  * mem_m_assn m m_m>"
  unfolding load_packed_m_v_def load_packed_def 
  supply [simp] = t_length_def load_def wasm_deserialise_def mem_length_def mem_rep_length_def
    and [sep_heap_rules] = load_rules
    and [split] = option.splits t.splits
  apply(sep_auto)
     apply(sep_auto simp: sign_extend_def bytes_takefill_def serialise_deserialise_i32) 
    apply(sep_auto)
   apply(sep_auto simp: sign_extend_def bytes_takefill_def serialise_deserialise_i64) 
   apply(sep_auto)
  done

lemma load_maybe_packed_triple:
  assumes "inst_at (is, i_ms) (f_inst f, f_inst2) j"
  shows "<mems_m_assn ms ms_m * inst_store_assn (is, i_ms)>
  app_s_f_v_s_load_maybe_packed_m t tp_sx off ms_m f_inst2 v_s
  <\<lambda>r.\<up>(r = app_s_f_v_s_load_maybe_packed t tp_sx off ms f v_s)
  * mems_m_assn ms ms_m * inst_store_assn (is, i_ms)>\<^sub>t"
proof -
  note expand = smem_ind_def Let_def mem_size_def mem_length_def
        mem_rep_length_def mem_max_def
  note splits = option.splits list.splits if_splits prod.splits

  show ?thesis
    using assms 
    unfolding app_s_f_v_s_load_maybe_packed_m_def app_s_f_v_s_load_maybe_packed_def 
      app_s_f_v_s_load_packed_def app_s_f_v_s_load_def
      inst_m_assn_def mems_m_assn_def
      list_assn_conv_idx
    supply [sep_heap_rules] = load_triple load_packed_triple
    apply(sep_auto split:v.splits)
     apply(sep_auto split:option.splits)
    apply(sep_auto split:v.splits)
        apply(knock_down j)
       apply(sep_auto split:option.splits)    
               apply(sep_auto?, knock_down "inst.mems (f_inst f) ! 0",
        sep_auto simp:expand split:splits)+ (*takes a moment*)   
      apply(sep_auto split:splits)+
    done
qed

named_theorems store_rules

abbreviation "store32_mem_triple fs t_len m m_m n v \<equiv> 
   <mem_m_assn m m_m> 
  fs (fst m_m) n (i32_impl_rep v)
   <\<lambda>r. \<up>(n + t_len \<le> mem_length m) 
  * mem_m_assn (write_bytes m n (bytes_takefill zero_byte t_len (serialise_i32 v))) m_m>" 

lemma [store_rules]:
  "store32_mem_triple store_uint32           4 m m_m n v"
  "store32_mem_triple store_uint8_of_uint32  1 m m_m n v"
  "store32_mem_triple store_uint16_of_uint32 2 m m_m n v"
  unfolding mem_m_assn_def 
  by(sep_auto split:prod.splits 
      simp:write_bytes_def mem_rep_write_bytes_def mem_length_def mem_rep_length_def
      Abs_mem_rep_inverse serialise_i32_def word_rsplit_rev_def 
      i32_impl_rep.rep_eq bytes_takefill_def numeral_Bit0)+

abbreviation "store64_mem_triple fs t_len m m_m n v \<equiv> 
   <mem_m_assn m m_m> 
  fs (fst m_m) n (i64_impl_rep v)
   <\<lambda>r. \<up>(n + t_len \<le> mem_length m) 
  * mem_m_assn (write_bytes m n (bytes_takefill zero_byte t_len (serialise_i64 v))) m_m>" 

lemma [store_rules]:
  "store64_mem_triple store_uint64           8 m m_m n v"
  "store64_mem_triple store_uint8_of_uint64  1 m m_m n v"
  "store64_mem_triple store_uint16_of_uint64 2 m m_m n v"
  "store64_mem_triple store_uint32_of_uint64 4 m m_m n v"
  unfolding mem_m_assn_def 
  by(sep_auto split:prod.splits 
      simp:write_bytes_def mem_rep_write_bytes_def mem_length_def mem_rep_length_def
      Abs_mem_rep_inverse serialise_i64_def word_rsplit_rev_def 
      i64_impl_rep.rep_eq bytes_takefill_def numeral_Bit0)+

lemma store_triple: 
  "<mem_m_assn m m_m>
  store_m_v m_m n off v
  <\<lambda>r_opt. expect_assn (\<lambda>m' r_m. mem_m_assn m' m_m) (mem_m_assn m m_m)
    (store m n off (bits v) (t_length (typeof v))) r_opt>"
  unfolding store_m_v_def
  apply(sep_auto split:v.splits heap:store_rules 
      simp: serialise_deserialise_i32 serialise_f32_len 
      serialise_deserialise_i64 serialise_f64_len 
      store_def bits_def t_length_def typeof_def mem_length_def mem_rep_length_def)
  done

lemma [store_rules]:
 "<mem_m_assn m m_m> 
  store_uint32_packed (fst m_m) n (i32_impl_rep v) tp
   <\<lambda>r.\<up>(n + (tp_length tp) \<le> mem_length m) * 
   mem_m_assn (write_bytes m n (bytes_takefill zero_byte (tp_length tp) (serialise_i32 v))) m_m >"
  unfolding store_uint32_packed_def 
  by(sep_auto simp:tp_length_def split:tp.splits heap:store_rules)

lemma [store_rules]:
 "<mem_m_assn m m_m> 
  store_uint64_packed (fst m_m) n (i64_impl_rep v) tp
   <\<lambda>r. \<up>(n + (tp_length tp) \<le> mem_length m) *
   mem_m_assn  (write_bytes m n (bytes_takefill zero_byte (tp_length tp) (serialise_i64 v))) m_m >"
  unfolding store_uint64_packed_def 
  by(sep_auto simp:tp_length_def split:tp.splits heap:store_rules)

lemma store_packed_triple: 
  "<mem_m_assn m m_m>
  store_packed_m_v m_m n off v tp
  <\<lambda>r_opt. expect_assn (\<lambda>m' r_m. mem_m_assn m' m_m) (mem_m_assn m m_m)
    (store_packed m n off (bits v) (tp_length tp)) r_opt>" 
  unfolding store_packed_m_v_def 
  by (sep_auto split:v.splits heap:store_rules 
      simp:store_packed_def store_def bits_def
      mem_length_def mem_rep_length_def 
      serialise_deserialise_i32 serialise_f32_len
      serialise_deserialise_i64 serialise_f64_len)

lemma store_maybe_packed_triple:
  assumes "inst_at (is, i_ms) (f_inst f, f_inst2) j"
  shows "<mems_m_assn ms ms_m * inst_store_assn (is, i_ms)>
  app_s_f_v_s_store_maybe_packed_m t tp_sx off ms_m f_inst2 v_s
  <\<lambda>r. let (ms', v_s', res) = app_s_f_v_s_store_maybe_packed t tp_sx off ms f v_s in 
  \<up>(r = (v_s', res))
  * mems_m_assn ms' ms_m * inst_store_assn (is, i_ms)>\<^sub>t" 
proof -
  note expand = smem_ind_def mem_grow_def Let_def mem_size_def mem_length_def
        mem_rep_length_def mem_max_def types_agree_def
  note splits = option.splits list.splits if_splits prod.splits

  show ?thesis
    using assms
    unfolding 
      app_s_f_v_s_store_maybe_packed_m_def app_s_f_v_s_store_maybe_packed_def
      app_s_f_v_s_store_def app_s_f_v_s_store_packed_def
      inst_m_assn_def mems_m_assn_def
      list_assn_conv_idx
    apply(sep_auto)
     apply(sep_auto split:option.splits prod.splits simp:app_s_f_v_s_store_packed_def) 
    apply(sep_auto split:list.splits)
     apply(sep_auto split:option.splits prod.splits simp:app_s_f_v_s_store_packed_def)
    apply(sep_auto split:v.splits)

         apply(knock_down j)
        apply(cases tp_sx) 
         apply(sep_auto)
          apply(extract_list_idx "inst.mems (f_inst f) ! 0")
          apply(sep_auto heap:store_triple)
         apply(sep_auto simp:expand split:splits)
          apply(rule listI_assn_reinsert, frame_inference, simp, simp, sep_auto)
         apply(sep_auto simp:expand split:splits)
         apply(rule listI_assn_reinsert_upd, frame_inference, simp, simp, sep_auto)

        apply(sep_auto)
          apply(extract_list_idx "inst.mems (f_inst f) ! 0")
          apply(sep_auto heap:store_packed_triple)
         apply(sep_auto simp:expand split:splits)
          apply(rule listI_assn_reinsert, frame_inference, simp, simp, sep_auto)
         apply(sep_auto simp:expand split:splits)
        apply(rule listI_assn_reinsert_upd, frame_inference, simp, simp, sep_auto)
       apply(sep_auto simp:expand split:splits)+
    done
qed

lemma init_mem_triple: 
  "<mem_m_assn m m_m>
  init_mem_m_v m_m n bs
  <\<lambda>r_opt. expect_assn (\<lambda>m' r_m. mem_m_assn m' m_m) (mem_m_assn m m_m)
    (store m n 0 bs (length bs)) r_opt>"
  by(sep_auto split:v.splits prod.splits list.splits heap:store_rules 
      simp: Rep_mem_rep_inverse Abs_mem_rep_inverse bytes_takefill_def
            write_bytes_def mem_rep_write_bytes_def mem_m_assn_def
            init_mem_m_v_def store_def mem_length_def mem_rep_length.rep_eq)

lemma init_tab_triple: 
  "<a \<mapsto>\<^sub>a tabrep * \<up>(tab_m=(a,t_max))>
  init_tab_m_v tab_m n icls
  <\<lambda>r_opt. expect_assn (\<lambda>t' r_m. a \<mapsto>\<^sub>a (fst t') * \<up>(tab_m=(a,(snd t')))) (a \<mapsto>\<^sub>a t * \<up>(tab_m=(a,t_max)))
    (store_tab (tabrep, t_max) n icls) r_opt>"
  sorry

(* run_step_b_e *)

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
    case (Get_global k)
    then show ?thesis unfolding unfold_vars_assns s_m_assn_def 
      by (sep_auto heap:get_global_triple split:prod.splits)
  next
    case (Set_global k)
    then show ?thesis unfolding unfold_vars_assns s_m_assn_def 
      by (sep_auto heap:set_global_triple split:prod.splits)
  next
    case (Load t tp_sx a off)
    then show ?thesis unfolding unfold_vars_assns s_m_assn_def 
      by (sep_auto heap:load_maybe_packed_triple split:prod.splits)
  next
    case (Store t tp a off)
    then show ?thesis unfolding unfold_vars_assns s_m_assn_def
      by (sep_auto heap:store_maybe_packed_triple split:prod.splits)
  next
    case Grow_memory
    then show ?thesis unfolding unfold_vars_assns s_m_assn_def 
      by (sep_auto heap:mem_grow_triple split:prod.splits)
  next
    case Current_memory
    then show ?thesis unfolding unfold_vars_assns s_m_assn_def 
      by (sep_auto heap:mem_size_triple split:prod.splits)
  next
    case (Get_local k)
    then show ?thesis 
      unfolding unfold_vars_assns by (sep_auto heap:get_local_triple)
  next
    case (Set_local k)
    then show ?thesis unfolding unfold_vars_assns
      by (sep_auto heap: set_local_triple split:prod.splits)
  next
    case (Tee_local k)
    then show ?thesis unfolding unfold_vars_assns by sep_auto
  next
    case (Call k)
    then show ?thesis unfolding unfold_vars_assns 
      by (sep_auto heap:call_triple split:prod.splits)
  next
    case (Call_indirect k)
    then show ?thesis unfolding unfold_vars_assns s_m_assn_def 
      by (sep_auto heap:call_indirect_triple split:prod.splits)
  next
    case Return 
    then show ?thesis unfolding unfold_vars_assns fcs_m_assn_def
      by (sep_auto split:frame_context_m.splits frame_context.splits list.split)
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


(* run_step_e_m *)

abbreviation "s_m_vs_pair_assn i_s \<equiv> \<lambda>(s, vs) (s_m, vs_m). s_m_assn i_s s s_m * \<up>(vs=vs_m)"

lemma host_apply_impl_m_triple:
 "< s_m_assn i_s s s_m>
 host_apply_impl_m s_m tf h vs
 <\<lambda>r_opt. expect_assn (\<lambda>r r_m. s_m_vs_pair_assn i_s r r_m) (s_m_assn i_s s s_m)
  (host_apply_impl s tf h vs) r_opt >"
  sorry

lemma funcs_nth_triple:
  "< fs_m\<mapsto>\<^sub>a fs_i * list_assn (cl_m_assn i_s) fs fs_i> 
  Array.nth fs_m i 
  <\<lambda>r. \<up>(i < length fs_i \<and> r = fs_i!i) 
  * cl_m_assn i_s (fs!i) r * fs_m \<mapsto>\<^sub>a fs_i * list_assn (cl_m_assn i_s) fs fs_i>"
  unfolding funcs_m_assn_def list_assn_conv_idx 
  apply(sep_auto)
  apply(extract_pre_pure)
  apply(extract_list_idx i)
  apply(subst pure_dup[OF cl_m_assn_pure])
  apply(reinsert_list_idx i)
  apply(sep_auto)
  done

lemma funcs_nth_triple_s:
  "< s_m_assn i_s s s_m> 
  Array.nth (s_m.funcs s_m) i 
  <\<lambda>r. \<up>(i < length (s.funcs s)) 
  * cl_m_assn i_s (s.funcs s!i) r * s_m_assn i_s s s_m>"
  unfolding s_m_assn_def funcs_m_assn_def
  by (sep_auto heap:funcs_nth_triple heap del:nth_rule, extract_pre_pure)

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
      apply(sep_auto heap: funcs_nth_triple_s split:cl_m.splits) 
      supply [simp] = Let_def and 
        [split] = v.splits option.splits 
        cl.splits cl_m.splits tf.splits nat.splits
       apply(sep_auto simp:cl_m_assn_def locs_m_assn_def s_m_assn_def funcs_m_assn_def fc_m_assn_def)
      apply(sep_auto heap:host_apply_impl_m_triple simp:cl_m_assn_def)
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
  next
    case (Init_mem x61 x62)
    then show ?thesis sorry
  next
    case (Init_tab x71 x72)
    then show ?thesis sorry
  qed
qed 


(* run_iter *)

lemma update_fc_return_preserve_assn:
  "cfg_m_assn i_s (Config d s fc (fc'#fcs)) (Config_m d_m s_m fc_m (fc'_m#fcs_m)) 
  \<Longrightarrow>\<^sub>A cfg_m_assn i_s (Config (Suc d) s (update_fc_return fc' v_s) fcs)
    (Config_m (Suc d_m) s_m (update_fc_return_m fc'_m v_s) fcs_m) * true"
  unfolding cfg_m_assn_def 
  apply (sep_auto)
  unfolding fc_m_assn_def
  by (sep_auto split:frame_context.splits frame_context_m.splits)

lemma update_redex_lc_preserve_assn:"cfg_m_assn i_s 
       (Config d s (Frame_context redex lcs nf f) fcs)
       (Config_m d_m s_m (Frame_context_m redex_m 
        lcs_m nf_m f_locs1 f_inst2) fcs_m)
  \<Longrightarrow>\<^sub>A cfg_m_assn i_s 
       (Config d s (Frame_context (g1 redex lcs) (g2 redex lcs) nf f) fcs)
       (Config_m d_m s_m (Frame_context_m (g1 redex_m lcs) 
        (g2 redex_m lcs_m) nf_m f_locs1 f_inst2) fcs_m) "
  unfolding cfg_m_assn_def fc_m_assn_def
  by (sep_auto)

lemma run_iter_m_triple:
    "<cfg_m_assn i_s cfg cfg_m> 
    run_iter_m n cfg_m 
    <\<lambda>r. cfg_m_pair_assn i_s (run_iter n cfg) r>\<^sub>t"
proof(induct n arbitrary: i_s cfg cfg_m)
  case 0
  show ?case unfolding 0 by sep_auto
next
  case (Suc n)

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

  show ?case unfolding unfold_vars
    supply [simp del] = run_step_b_e_m.simps run_step_b_e.simps 
      run_step_e_m.simps run_step_e.simps
    apply(extract_pre_pure, simp add:cfg_m_assn_pure_def fc_m_assn_pure_def)
    apply(sep_auto)
       apply(cases fcs, auto)
       apply(rule cons_pre_rule[OF update_fc_return_preserve_assn])
       apply(sep_auto heap:Suc)
      apply(sep_auto split:label_context.splits)
      apply(rule cons_pre_rule[OF update_redex_lc_preserve_assn])
      apply(sep_auto heap:Suc)
     apply(sep_auto split:prod.splits)
      apply(rule cons_pre_rule[OF update_redex_lc_preserve_assn])
      apply(sep_auto heap:Suc)
     apply(sep_auto)
      apply(rule cons_pre_rule[OF update_redex_lc_preserve_assn])
      apply(sep_auto heap:run_step_b_e_m_triple)
     apply(sep_auto split:prod.splits res_step.splits heap:Suc)
    apply(sep_auto)
     apply(rule cons_pre_rule[OF update_redex_lc_preserve_assn])
     apply(sep_auto heap:run_step_e_m_triple)
    apply(sep_auto split:res_step.splits prod.splits heap:Suc)
    done
qed


end