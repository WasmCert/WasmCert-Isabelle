theory List_Assn
imports "Separation_Logic_Imperative_HOL_Partial/Sep_Main" "HOL-Library.Rewrite"
begin

subsection "Lists"

fun list_assn :: "('a \<Rightarrow> 'c \<Rightarrow> assn) \<Rightarrow> 'a list \<Rightarrow> 'c list \<Rightarrow> assn" where
  "list_assn P [] [] = emp"
| "list_assn P (a#as) (c#cs) = P a c * list_assn P as cs"
| "list_assn _ _ _ = false"

lemma list_assn_aux_simps[simp]:
  "list_assn P [] l' = (\<up>(l'=[]))"
  "list_assn P l [] = (\<up>(l=[]))"
   apply (cases l')
    apply simp
   apply simp
  apply (cases l)
   apply simp
  apply simp
  done

lemma list_assn_aux_append[simp]:
  "length l1=length l1' \<Longrightarrow> 
    list_assn P (l1@l2) (l1'@l2') 
    = list_assn P l1 l1' * list_assn P l2 l2'"
  apply (induct rule: list_induct2)
   apply simp
  apply (simp add: star_assoc)
  done

lemma list_assn_aux_ineq_len: "length l \<noteq> length li \<Longrightarrow> list_assn A l li = false"
proof (induction l arbitrary: li)
  case (Cons x l li) thus ?case by (cases li; auto)
qed simp

lemma list_assn_aux_append2[simp]:
  assumes "length l2=length l2'"  
  shows "list_assn P (l1@l2) (l1'@l2') 
    = list_assn P l1 l1' * list_assn P l2 l2'"
  apply (cases "length l1 = length l1'")
   apply (erule list_assn_aux_append)
  apply (simp add: list_assn_aux_ineq_len assms)
  done

lemma list_assn_simps[simp]:
  "(list_assn P) [] [] = emp"
  "(list_assn P) (a#as) (c#cs) = P a c * (list_assn P) as cs"
  "(list_assn P) (a#as) [] = false"
  "(list_assn P) [] (c#cs) = false"
     apply simp_all
  done


lemma list_assn_mono: 
  "\<lbrakk>\<And>x x'. P x x'\<Longrightarrow>\<^sub>AP' x x'\<rbrakk> \<Longrightarrow> list_assn P l l' \<Longrightarrow>\<^sub>A list_assn P' l l'"
  apply (induct P l l' rule: list_assn.induct)
  by (auto intro: ent_star_mono)

lemma list_assn_cong[fundef_cong]:
  assumes "xs=xs'" "xsi=xsi'"
  assumes "\<And>x xi. x\<in>set xs' \<Longrightarrow> xi\<in>set xsi' \<Longrightarrow> A x xi = A' x xi"
  shows "list_assn A xs xsi = list_assn A' xs' xsi'"  
  using assms
  apply (induct A\<equiv>A xs' xsi' arbitrary: xs xsi rule: list_assn.induct)
     apply simp_all
  done

term prod_list


definition "listI_assn I A xs xsi \<equiv> 
    \<up>(length xsi=length xs \<and> I\<subseteq>{0..<length xs}) 
  * Finite_Set.fold (\<lambda>i a. a * A (xs!i) (xsi!i)) 1 I"


lemma aux: "Finite_Set.fold (\<lambda>i aa. aa * P ((a # as) ! i) ((c # cs) ! i)) emp {0..<Suc (length as)}
  = P a c * Finite_Set.fold (\<lambda>i aa. aa * P (as ! i) (cs ! i)) emp {0..<length as}" 
proof -
  have 1: "{0..<Suc (length as)} = Set.insert 0 {1..<Suc (length as)}" by auto 

  have 2: "{Suc 0..<Suc (Suc n)} = Set.insert (Suc n) {Suc 0 ..< Suc n}" for n by auto
  have 3: "{0..<Suc n} = Set.insert n {0..<n}" for n by auto

  have A: "
    Finite_Set.fold P emp {Suc 0..<Suc n} 
    = Finite_Set.fold Q emp {0..<n}" 
    if "\<forall>i x. P (Suc i) x = Q i x"
      and "comp_fun_commute P"
      and "comp_fun_commute Q"
    for P Q n
    using that
    apply (induction n arbitrary: a)
    subgoal by simp
    apply (simp add: comp_fun_commute.fold_insert)
    apply (subst 2)
    apply (subst 3)
    apply (simp add: comp_fun_commute.fold_insert)
    done 
  show ?thesis
    apply (simp add: 1)
    apply (subst comp_fun_commute.fold_insert_remove)
    subgoal
      apply unfold_locales
      apply (auto simp: fun_eq_iff algebra_simps)
      done
    subgoal by simp
    apply simp
    apply (rewrite at "\<hole> = _*_" mult.commute)
    apply (rule arg_cong[where f="\<lambda>x. P _ _ * x"])
    apply (rule A)
    subgoal by auto
    subgoal
      apply unfold_locales
      apply (auto simp: fun_eq_iff algebra_simps)
      done
    subgoal
      apply unfold_locales
      apply (auto simp: fun_eq_iff algebra_simps)
      done
    done
qed    


lemma list_assn_conv_idx: "list_assn A xs xsi = listI_assn {0..<length xs} A xs xsi"  
  apply (induction A xs xsi rule: list_assn.induct)
     apply (auto simp: listI_assn_def aux)
  done

lemma listI_assn_conv: "n=length xs \<Longrightarrow> listI_assn {0..<n} A xs xsi = list_assn A xs xsi"
  by (simp add: list_assn_conv_idx)

lemma listI_assn_conv': "n=length xs \<Longrightarrow> listI_assn {0..<n} A xs xsi *F  = list_assn A xs xsi* F"
  by (simp add: list_assn_conv_idx)

lemma listI_assn_finite[simp]: "\<not>finite I \<Longrightarrow> listI_assn I A xs xsi = false"
  using subset_eq_atLeast0_lessThan_finite by (auto simp: listI_assn_def)


find_theorems Finite_Set.fold name: cong  

lemma mult_fun_commute: "comp_fun_commute (\<lambda>i (a::assn). a * f i)"
  apply unfold_locales
  apply (auto simp: fun_eq_iff mult_ac)
  done

lemma listI_assn_weak_cong: 
  assumes I: "I=I'" "A=A'" "length xs=length xs'" "length xsi=length xsi'"
  assumes A: "\<And>i. \<lbrakk>i\<in>I; i<length xs; length xs=length xsi \<rbrakk> 
    \<Longrightarrow> xs!i = xs'!i \<and> xsi!i = xsi'!i"
  shows "listI_assn I A xs xsi = listI_assn I' A' xs' xsi'"
  unfolding listI_assn_def
  apply (simp add: I)
  apply (cases "length xsi' = length xs' \<and> I' \<subseteq> {0..<length xs'}"; simp only:; simp)
  apply (rule Finite_Set.fold_cong)
       apply (simp_all add: mult_fun_commute)
  subgoal by (meson subset_eq_atLeast0_lessThan_finite)
  subgoal using A by (auto simp: fun_eq_iff I)
  done

lemma listI_assn_cong: 
  assumes I: "I=I'" "length xs=length xs'" "length xsi=length xsi'"
  assumes A: "\<And>i. \<lbrakk>i\<in>I; i<length xs; length xs=length xsi \<rbrakk> 
    \<Longrightarrow> xs!i = xs'!i \<and> xsi!i = xsi'!i 
      \<and> A (xs!i) (xsi!i) = A' (xs'!i) (xsi'!i)"
  shows "listI_assn I A xs xsi = listI_assn I' A' xs' xsi'"
  unfolding listI_assn_def
  apply (simp add: I)
  apply (cases "length xsi' = length xs' \<and> I' \<subseteq> {0..<length xs'}"; simp only:; simp)
  apply (rule Finite_Set.fold_cong)
       apply (simp_all add: mult_fun_commute)
  subgoal by (meson subset_eq_atLeast0_lessThan_finite)
  subgoal using A by (fastforce simp: fun_eq_iff I)
  done



lemma listI_assn_insert: "i\<notin>I \<Longrightarrow> i<length xs \<Longrightarrow> 
       listI_assn (Set.insert i I) A xs xsi = A (xs!i) (xsi!i) * listI_assn I A xs xsi"
  apply (cases "finite I"; simp?)
  unfolding listI_assn_def
  apply (subst comp_fun_commute.fold_insert)
  subgoal 
    apply unfold_locales
    apply (auto simp: fun_eq_iff algebra_simps)
    done
  subgoal by simp  
  subgoal by simp  
  subgoal by (auto simp: algebra_simps)
  done

lemma listI_assn_extract:
  assumes "i\<in>I" "i<length xs"  
  shows "listI_assn I A xs xsi = A (xs!i) (xsi!i) * listI_assn (I-{i}) A xs xsi"  
proof -
  have 1: "I = Set.insert i (I-{i})" using assms by auto 
  show ?thesis
    apply (subst 1)
    apply (subst listI_assn_insert)
    using assms by auto
qed    


lemma listI_assn_reinsert:
  assumes "P \<Longrightarrow>\<^sub>A A (xs!i) (xsi!i) * listI_assn (I-{i}) A xs xsi * F"
  assumes "i<length xs" "i\<in>I"
  assumes "listI_assn I A xs xsi * F \<Longrightarrow>\<^sub>A Q"
  shows "P \<Longrightarrow>\<^sub>A Q"
proof -
  show ?thesis
    apply (rule ent_trans[OF assms(1)])
    apply (subst listI_assn_extract[symmetric])
    subgoal by fact
    subgoal by fact
    subgoal by fact
    done
qed  

lemma listI_assn_reinsert_upd:
  fixes xs xsi :: "_ list"
  assumes "P \<Longrightarrow>\<^sub>A A x xi * listI_assn (I-{i}) A xs xsi * F"
  assumes "i<length xs" "i\<in>I"
  assumes "listI_assn I A (xs[i:=x]) (xsi[i:=xi]) * F \<Longrightarrow>\<^sub>A Q"
  shows "P \<Longrightarrow>\<^sub>A Q"
proof (cases "length xs = length xsi")
  case True
  have 1: "listI_assn (I-{i}) A xs xsi = listI_assn (I-{i}) A (xs[i:=x]) (xsi[i:=xi])"
    by (rule listI_assn_cong) auto

  have 2: "A x xi = A ((xs[i:=x])!i) ((xsi[i:=xi])!i)" using \<open>i<length xs\<close> True by auto

  from assms[unfolded 1 2] show ?thesis 
    apply (rule_tac listI_assn_reinsert)
       apply assumption
      apply simp_all
    done

next    
  case False
  with assms(1) have "P \<Longrightarrow>\<^sub>A false"
    by (simp add: listI_assn_def)
  thus ?thesis using ent_false_iff entailsI by blast  
qed  


lemma listI_assn_reinsert':
  assumes "P \<Longrightarrow>\<^sub>A A (xs!i) (xsi!i) * listI_assn (I-{i}) A xs xsi * F"
  assumes "i<length xs" "i\<in>I"
  assumes "<listI_assn I A xs xsi * F>c<Q>"
  shows "<P>c<Q>"
proof -
  show ?thesis
    apply (rule cons_pre_rule[OF assms(1)])
    apply (subst listI_assn_extract[symmetric])
    subgoal by fact
    subgoal by fact
    subgoal by fact
    done
qed  

lemma listI_assn_reinsert_upd':
  fixes xs xsi :: "_ list"
  assumes "P \<Longrightarrow>\<^sub>A A x xi * listI_assn (I-{i}) A xs xsi * F"
  assumes "i<length xs" "i\<in>I"
  assumes "<listI_assn I A (xs[i:=x]) (xsi[i:=xi]) * F> c <Q>"
  shows "<P> c <Q>"
  by (meson assms(1) assms(2) assms(3) assms(4) cons_pre_rule ent_refl listI_assn_reinsert_upd)



definition "unwrap_list_idxs (xsi::_::heap list) \<equiv> return ()" (* list_assn \<rightarrow> list_assnI *)
definition "wrap_list_idxs (xsi::_::heap list) \<equiv> return ()" (* list_assnI \<rightarrow> list_assn *)

definition "extract_list_idx (xsi::_::heap list) (i::nat) \<equiv> return ()" (* list_assnI _ A \<rightarrow> A (xs!i) (xsi!i) * \<dots> *)
definition "reinsert_list_idx (xsi::_::heap list) (i::nat) \<equiv> return ()" (* A (xs!i) (xsi!i) * \<dots> \<rightarrow> list_assnI _ A *)

lemma unwrap_list_idxs_rule[sep_heap_rules]: 
  "<list_assn A xs xsi> unwrap_list_idxs xsi <\<lambda>_. listI_assn {0..<length xs} A xs xsi>"
  unfolding unwrap_list_idxs_def
  by (sep_auto simp: list_assn_conv_idx)

lemma wrap_list_idxs_rule[sep_heap_rules]:
  "I={0..<length xs} \<Longrightarrow> <listI_assn I A xs xsi> wrap_list_idxs xsi <\<lambda>_. list_assn A xs xsi>"
  unfolding wrap_list_idxs_def
  by (sep_auto simp: list_assn_conv_idx)

lemma extract_list_idx_rule[sep_heap_rules]:
  "i\<in>I \<Longrightarrow> <listI_assn I A xs xsi> extract_list_idx xsi i <\<lambda>_. A (xs!i) (xsi!i) * listI_assn (I-{i}) A xs xsi>"
  unfolding extract_list_idx_def
  apply sep_auto 
    (* TODO: Cleaner proof. listI_assn implies that index set is <length! *)
  by (smt (verit, best) atLeastLessThan_iff ent_false ent_refl insert_absorb insert_subset 
      listI_assn_def listI_assn_extract pure_false star_false_left)

lemma reinsert_list_idx_rule[sep_heap_rules]:
  "i\<notin>I \<Longrightarrow> i<length xs \<Longrightarrow> <A (xs!i) (xsi!i) * listI_assn I A xs xsi> reinsert_list_idx xsi i <\<lambda>_. listI_assn (Set.insert i I) A xs xsi>"
  unfolding reinsert_list_idx_def
  apply sep_auto
  by (simp add: listI_assn_insert)





lemma subst_not_in: 
  assumes "i\<notin>I " " i<length xs "
  shows "listI_assn I A (xs[i:=x1]) (xsi[i := x2]) = listI_assn I A xs xsi"
  apply (rule listI_assn_cong)
  using assms
  by (auto simp add: nth_list_update')

lemma listI_assn_subst: 
  assumes "i\<notin>I "" i<length xs "
  shows "listI_assn (Set.insert i I) A (xs[i:=x1]) (xsi[i := x2]) = A x1 x2 * listI_assn I A xs xsi" 
  by (smt (z3) assms(1) assms(2) length_list_update listI_assn_def listI_assn_insert nth_list_update_eq pure_false star_false_left star_false_right subst_not_in)


(* TODO: Move *)  
lemma mod_starE: assumes "h \<Turnstile> a*b" obtains h\<^sub>1 h\<^sub>2 where "h\<^sub>1 \<Turnstile> a" "h\<^sub>2 \<Turnstile> b"
  using assms by (auto dest: mod_starD)

named_theorems extract_pure_rules  
  
lemma extract_pre_list_assn_lengthD[extract_pure_rules]: "h \<Turnstile> list_assn A xs xsi \<Longrightarrow> length xsi = length xs"
  by (metis list_assn_aux_ineq_len mod_false)
  
lemma extract_pre_listI_assn_lengthD[extract_pure_rules]: "h \<Turnstile> listI_assn I A xs xsi \<Longrightarrow> length xsi = length xs"
  by (simp add: listI_assn_def)
  

method extract_pre_pure uses dest =
  (rule hoare_triple_preI | drule asm_rl[of "_\<Turnstile>_"]),
  (determ \<open>elim mod_starE dest[elim_format] extract_pure_rules[elim_format]\<close>)?,
  ((determ \<open>thin_tac "_ \<Turnstile> _"\<close>)+)?,
  (simp (no_asm) only: triv_forall_equality)?



end
