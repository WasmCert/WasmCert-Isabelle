theory Wasm_Monad_Aux
  imports Wasm_Interpreter_Monad "../libs/Misc_Generic_Lemmas" "../libs/List_Assn" begin
(* separation logic methods *)

method extract_list_idx for i :: nat =
  (subst listI_assn_extract[of i], (simp;fail), (simp;fail))
  
method reinsert_list_idx for i :: nat =
  rule listI_assn_reinsert[where i=i] listI_assn_reinsert'[where i=i],
  (frame_inference; fail),
  (simp;fail),
  (simp;fail)

method extract_reinsert_list_idx for i :: nat uses heap = 
 extract_pre_pure?, extract_list_idx i, sep_auto heap:heap, extract_pre_pure?, reinsert_list_idx i


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


(* some lemmas *)

lemma cl_m_agree_type: "cl_m_agree i_s cl cl_m \<Longrightarrow> cl_type cl = cl_m_type cl_m"
  unfolding cl_m_agree_def cl_m_agree_j_def cl_type_def cl_m_type_def
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
    <\<lambda>r. mem_m_assn m mi * \<up>(r=mem_length m)>"
  unfolding mem_m_assn_def mem_length_def mem_rep_length_def
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