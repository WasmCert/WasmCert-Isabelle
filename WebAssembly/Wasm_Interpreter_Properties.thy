section \<open>Soundness of Interpreter\<close>

theory Wasm_Interpreter_Properties imports Wasm_Interpreter Wasm_Properties begin

lemma is_const_list_vs_to_es_list: "const_list ($C* vs)"
  using is_const_list
  by auto

lemma not_const_vs_to_es_list:
  assumes "~(is_const e)"
  shows "vs1 @ [e] @ vs2 \<noteq> $C* vs"
proof -
  fix vs
  {
    assume "vs1 @ [e] @ vs2 = $C* vs"
    hence "(\<forall>y\<in>set (vs1 @ [e] @ vs2). \<exists>x. y = $C x)"
      by simp
    hence False
      using assms
      unfolding is_const_def
      by fastforce
  }
  thus "vs1 @ [e] @ vs2 \<noteq> $C* vs"
    by fastforce
qed


lemma split_vals_e_not_const_list:
  assumes "\<not>const_list xs"
  shows "\<exists>as b bs. split_vals_e xs = (as, b#bs)"
  using assms
proof (induction xs)
  case Nil
  thus ?case
    by (simp add: const_list_def)
next
  case (Cons a xs)
  show ?case
  proof (cases "is_const a")
    case True
    hence 1:"\<not> const_list xs"
      using Cons(2)
      by (simp add: const_list_def)
    obtain ac where "a = $C ac"
      using e_type_const_unwrap[OF True]
      by blast
    thus ?thesis
      using Cons(1)[OF 1]
      by auto
  next
    case False
    hence "split_vals_e (a#xs) = ([],a#xs)"
    proof (cases a)
      case (Basic x1)
      thus ?thesis
        using False
        by (cases x1) (auto simp add: is_const_def)
    qed (auto simp add: is_const_def)
    thus ?thesis
      by blast
  qed
qed

lemma neq_label_nested:"[Label n les es] \<noteq> es"
proof -
  have "size_list size [Label n les es] > size_list size es"
    by simp
  thus ?thesis
    by fastforce
qed

lemma neq_local_nested:"[Frame n f es] \<noteq> es"
proof -
  have "size_list size [Frame n f es] > size_list size es"
    by simp
  thus ?thesis
    by fastforce
qed

lemma trap_not_value:"[Trap] \<noteq> $C*es"
  by fastforce

thm Lfilled.simps[of _ _ _ "[e]", simplified]

lemma lfilled_single:
  assumes "Lfilled k lholed es [e]"
          "\<And> a b c. e \<noteq> Label a b c"
  shows "(es = [e] \<and> lholed = LBase [] [] \<and> k = 0) \<or> es = []"
  using assms
proof (cases rule: Lfilled.cases)
  case (L0 vs es')
  thus ?thesis
    by (metis (no_types, lifting) Cons_eq_append_conv append_is_Nil_conv list.map_disc_iff)
next
  case (LN vs n es' l es'' k lfilledk)
  assume "(\<And>a b c. e \<noteq> Label a b c)"
  thus ?thesis
    using LN(2)
    unfolding Cons_eq_append_conv
    by fastforce
qed

lemma lfilled_eq:
  assumes "Lfilled j lholed es LI"
          "Lfilled j lholed es' LI"
  shows "es = es'"
  using assms
proof (induction arbitrary: es' rule: Lfilled.induct)
  case (L0 vs lholed es' es)
  thus ?case
    using Lfilled.simps[of 0, simplified]
    by auto
next
  case (LN lholed vs n les' l les'' k les lfilledk)
  thus ?case
    using Lfilled.simps[of "(k+1)" "LRec vs n les' l les''" es' "(($C*vs) @ [Label n les' lfilledk] @ les'')", simplified]
    by auto
qed

lemma lfilled_size:
  assumes "Lfilled j lholed es LI"
  shows "size_list size LI \<ge> size_list size es"
  using assms
  by (induction rule: Lfilled.induct) auto

thm Lfilled.simps[of _ _ es es, simplified]

lemma reduce_simple_not_eq:
  assumes "\<lparr>es\<rparr> \<leadsto> \<lparr>es'\<rparr>"
  shows "es \<noteq> es'"
  using assms
proof (induction es' rule: reduce_simple.induct)
  case (label_const vs n es)
  thus ?case
    using neq_label_nested
    by auto
next
  case (br vs n i lholed LI es)
  have "size_list size [Label n es LI] > size_list size (($C*vs) @ es)"
    using lfilled_size[OF br(2)]
    by simp
  thus ?case
    by fastforce
next
  case (local_const es f vs)
  thus ?case
    using neq_local_nested
    by auto
next
  case (return vs n j lholed es f)
  hence "size_list size [Frame n f es] > size_list size ($C*vs)"
        using lfilled_size[OF return(2)]
    by simp
  thus ?case
    by auto
qed auto
    
lemma reduce_not_eq:
  assumes "\<lparr>s;f;es\<rparr> \<leadsto> \<lparr>s';f';es'\<rparr>"
  shows "es \<noteq> es'"
  using assms
proof (induction es' rule: reduce.induct)
  case (basic e e' s vs)
  thus ?case
    using reduce_simple_not_eq
    by simp
next
  case (invoke_host_Some cl t1s t2s f ves vcs n m s hs s' vcs' vs)
  thus ?case
    by (cases vcs' rule:rev_cases) auto
next
  case (label s vs es s' vs' es' k lholed les les')
  thus ?case
    using lfilled_eq
    by fastforce
qed auto

lemma reduce_simple_not_value:
  assumes "\<lparr>es\<rparr> \<leadsto> \<lparr>es'\<rparr>"
  shows "es \<noteq> $C* vs"
  using assms
proof (induction rule: reduce_simple.induct)
  case (block vs n t1s t2s m es)
  have "\<not>(is_const ($Block (t1s _> t2s) es))"
    unfolding is_const_def
    by simp
  thus ?case
    using not_const_vs_to_es_list
    by (metis append.right_neutral)
next
  case (loop vs n t1s t2s m es)
  have "\<not>(is_const ($Loop (t1s _> t2s) es))"
    unfolding is_const_def
    by simp
  thus ?case
    using not_const_vs_to_es_list
    by (metis append.right_neutral)
next
  case (trap lholed es)
  show ?case
    using trap(2)
  proof (cases rule: Lfilled.cases)
    case L0
    have "\<not>(is_const Trap)"
      unfolding is_const_def
      by simp
    thus ?thesis
      using L0 not_const_vs_to_es_list
      by fastforce
  qed auto
qed auto

lemma reduce_not_value:
  assumes "\<lparr>s;f;es\<rparr> \<leadsto> \<lparr>s';f';es'\<rparr>"
  shows "es \<noteq> $C* ves"
  using assms
proof (induction es' arbitrary: ves rule: reduce.induct)
  case (basic e e' s vs i)
  thus ?case
    using reduce_simple_not_value
    by fastforce
next
  case (invoke_native s i_cl j t1s t2s ts es ves vcs n k m zs f)
  have "\<not>(is_const (Invoke i_cl))"
    unfolding is_const_def
    by simp
  thus ?case
    using not_const_vs_to_es_list
    by (metis append.right_neutral)
next
  case (invoke_host_Some s i_cl t1s t2s h ves vcs n m hs s' vcs' f)
  have "\<not>(is_const (Invoke i_cl))"
    unfolding is_const_def
    by simp
  thus ?case
    using not_const_vs_to_es_list
    by (metis append.right_neutral)
next
  case (invoke_host_None s i_cl t1s t2s f ves vcs n m vs i)
  have "\<not>(is_const (Invoke i_cl))"
    unfolding is_const_def
    by simp
  thus ?case
    using not_const_vs_to_es_list
    by (metis append.right_neutral)
next
  case (label s vs es i s' vs' es' k lholed les les')
  show ?case
    using label(2,4)
  proof (induction rule: Lfilled.induct)
    case (L0 lholed lvs les' les)
    {
      assume "($C*lvs) @ les @ les' = $C* ves"
      hence "(\<forall>y\<in>set (($C*lvs) @ les @ les'). \<exists>x. y = $C x)"
        by simp
      hence "(\<forall>y\<in>set les. \<exists>x. y = $C x)"
        by simp
      hence "\<exists>vs1. les = $C* vs1"
        unfolding ex_map_conv.
    }
    thus ?case
      using L0(2)
      by (metis consts_app_ex(1) consts_app_ex(2))
  next
    case (LN lvs lholed ln les' l les'' k les lfilledk)
    have "\<not>(is_const (Label ln les' lfilledk))"
      unfolding is_const_def
      by simp
    thus ?case
      using not_const_vs_to_es_list
      by fastforce
  qed
qed auto

lemma reduce_simple_not_nil:
  assumes "\<lparr>es\<rparr> \<leadsto> \<lparr>es'\<rparr>"
  shows "es \<noteq> []"
  using assms
proof (induction rule: reduce_simple.induct)
  case (trap es lholed)
  thus ?case
    using Lfilled.simps[of 0 lholed "[Trap]"]
    by auto
qed auto

lemma reduce_not_nil:
  assumes "\<lparr>s;f;es\<rparr> \<leadsto> \<lparr>s';f';es'\<rparr>"
  shows "es \<noteq> []"
  using assms
proof (induction rule: reduce.induct)
  case (basic e e' s vs)
  thus ?case
    using reduce_simple_not_nil
    by simp
next
  case (label s vs es s' vs' es' k lholed les les')
  show ?case
    using lfilled_size[OF label(2)] label(4)
    by (metis One_nat_def add_is_0 le_0_eq list.exhaust list.size(2) list.size_gen(1) zero_neq_one)
qed auto

lemma reduce_simple_not_trap:
  assumes "\<lparr>es\<rparr> \<leadsto> \<lparr>es'\<rparr>"
  shows "es \<noteq> [Trap]"
  using assms
  by (induction rule: reduce_simple.induct) auto

lemma reduce_not_trap:
  assumes "\<lparr>s;f;es\<rparr> \<leadsto> \<lparr>s';f';es'\<rparr>"
  shows "es \<noteq> [Trap]"
  using assms
proof (induction rule: reduce.induct)
  case (basic e e' s vs)
  thus ?case
    using reduce_simple_not_trap
    by simp
next
  case (label s vs es s' vs' es' k lholed les les')
  {
    assume "les = [Trap]"
    hence "Lfilled k lholed es [Trap]"
      using label(2)
      by simp
    hence False
      using lfilled_single reduce_not_nil[OF label(1)] label(4)
      by fastforce
  }
  thus ?case
    by auto
qed auto

lemma reduce_simple_call: "\<not>\<lparr>[$Call j]\<rparr> \<leadsto> \<lparr>es'\<rparr>"
  using reduce_simple.simps[of "[$Call j]", simplified] lfilled_single
  by fastforce

lemma reduce_call:
  assumes "\<lparr>s;f;[$Call j]\<rparr> \<leadsto> \<lparr>s';f';es'\<rparr>"
  shows "s = s'"
        "f = f'"
        "es' = [Invoke (sfunc_ind (f_inst f) j)]"
  using assms
proof (induction "[$Call j]:: e list" s' f' es' rule: reduce.induct)
  case (label s f es s' f' es' k lholed les')
  have "es = [$Call j]"
       "lholed = LBase [] []"
    using reduce_not_nil[OF label(1)] lfilled_single[OF label(5)]
    by auto
  thus "s = s'"
       "f = f'"
       "les' = [Invoke (sfunc_ind (f_inst f) j)]"
    using label(2,3,4,6) Lfilled.simps[of k "LBase [] []" "[Invoke (sfunc_ind (f_inst f) j)]" les']
    by auto
qed (auto simp add: reduce_simple_call)

lemma run_step_basic_unreachable_result:
  assumes "run_step d (s,f,ves,($Unreachable) # es') = (s', f', res)"
  shows "\<exists>rv re. res = RSNormal rv re"
  using assms
  by auto

lemma run_step_basic_nop_result:
  assumes "run_step d (s,f,ves,($Nop) # es') = (s', f', res)"
  shows "\<exists>rv re. res = RSNormal rv re"
  using assms
  by auto

lemma run_step_basic_drop_result:
  assumes "run_step d (s,f,ves,($Drop) # es') = (s', f', res)"
  shows "(\<exists>rv re. res = RSNormal rv re) \<or> (\<exists>e. res = RSCrash e)"
  using assms
  by (cases ves) auto

lemma run_step_basic_select_result:
  assumes "run_step d (s,f,ves,($Select) # es') = (s', f', res)"
  shows "(\<exists>rv re. res = RSNormal rv re) \<or> (\<exists>e. res = RSCrash e)"
  using assms
proof (cases ves)
  case (Cons a list)
  thus ?thesis
    using assms
  proof (cases a; cases list)
    fix x1a aa listaa
    assume "a = ConstInt32 x1a" and "list = aa#listaa"
    thus ?thesis
      using assms Cons
      by (cases listaa; cases "int_eq x1a 0") auto
  qed auto
qed auto

lemma run_step_basic_block_result:
  assumes "run_step d (s,f,ves,($(Block x51 x52)) # es') = (s', f', res)"
  shows "(\<exists>rv re. res = RSNormal rv re) \<or> (\<exists>e. res = RSCrash e)"
  using assms
proof -
  obtain t1s t2s where "x51 = (t1s _> t2s)"
    using tf.exhaust
    by blast
  moreover obtain ves' ves'' where "split_n ves (length t1s) = (ves', ves'')"
    by (metis surj_pair)
  ultimately
    show ?thesis
    using assms 
    by (cases "length t1s \<le> length ves") auto
qed

lemma run_step_basic_loop_result:
  assumes "run_step d (s,f,ves,($(Loop x61 x62)) # es') = (s', f', res)"
  shows "(\<exists>rv re. res = RSNormal rv re) \<or> (\<exists>e. res = RSCrash e)"
  using assms
proof -
  obtain t1s t2s where "x61 = (t1s _> t2s)"
    using tf.exhaust
    by blast
  moreover obtain ves' ves'' where "split_n ves (length t1s) = (ves', ves'')"
    by (metis surj_pair)
  ultimately
    show ?thesis
    using assms 
    by (cases "length t1s \<le> length ves") auto
qed

lemma run_step_basic_if_result:
  assumes "run_step d (s,f,ves,($(If x71 x72 x73)) # es') = (s', f', res)"
  shows "(\<exists>rv re. res = RSNormal rv re) \<or> (\<exists>e. res = RSCrash e)"
  using assms
proof (cases ves)
  case (Cons a list)
  thus ?thesis
    using assms
  proof (cases a)
    fix x1a
    assume "a = ConstInt32 x1a"
    thus ?thesis
      using assms Cons
      by (cases "int_eq x1a 0") auto
  qed auto
qed auto

lemma run_step_basic_br_result:
  assumes "run_step d (s,f,ves,($Br x8)#es') = (s', f', res)"
  shows "\<exists>r vrs. res = RSBreak r vrs"
  using assms
  by (cases ves) auto

lemma run_step_basic_br_if_result:
  assumes "run_step d (s,f,ves,($Br_if x9)#es') = (s', f', res)"
  shows "(\<exists>rv re. res = RSNormal rv re) \<or> (\<exists>e. res = RSCrash e)"
  using assms
proof (cases ves)
  case (Cons a list)
  thus ?thesis
    using assms
  proof (cases a)
    case (ConstInt32 x1)
    thus ?thesis
      using assms Cons
      by (cases "int_eq x1 0") auto
  qed auto
qed auto

lemma run_step_basic_br_table_result:
  assumes "run_step d (s,f,ves,($Br_table js j)#es') = (s', f', res)"
  shows "(\<exists>rv re. res = RSNormal rv re) \<or> (\<exists>e. res = RSCrash e)"
  using assms
proof (cases ves)
  case (Cons a list)
  thus ?thesis
    using assms
  proof (cases a)
    case (ConstInt32 x1)
    thus ?thesis
      using assms Cons
      by (cases "nat_of_int x1 < length js") auto
  qed auto
qed auto

lemma run_step_basic_return_result:
  assumes "run_step d (s,f,ves,($Return)#es') = (s', f', res)"
  shows "\<exists>vrs. res = RSReturn vrs"
  using assms
  by (cases ves) auto

lemma run_step_basic_call_result:
  assumes "run_step d (s,f,ves,($Call x12)#es') = (s', f', res)"
  shows "\<exists>rv re. res = RSNormal rv re"
  using assms
  by (cases ves) auto

lemma run_step_basic_call_indirect_result:
  assumes "run_step d (s,f,ves,($Call_indirect x13)#es') = (s', f', res)"
  shows "(\<exists>rv re. res = RSNormal rv re) \<or> (\<exists>e. res = RSCrash e)"
  using assms
proof (cases ves)
  case (Cons a list)
  thus ?thesis
    using assms
  proof (cases a)
    case (ConstInt32 x1)
    thus ?thesis
      using Cons assms
    proof (cases "stab s (f_inst f) (nat_of_int x1)")
      case (Some cl)
      thus ?thesis
        using Cons assms ConstInt32
        by (cases cl; cases "stypes s (f_inst f) x13 = cl_type (funcs s!cl)") auto
    qed auto
  qed auto
qed auto

lemma run_step_basic_get_local_result:
  assumes "run_step d (s,f,ves,($Get_local x14) # es') = (s', f', res)"
  shows "(\<exists>rv re. res = RSNormal rv re) \<or> (\<exists>e. res = RSCrash e)"
  using assms
  by (cases "x14 < length (f_locs f)") auto

lemma run_step_basic_set_local_result:
  assumes "run_step d (s,f,ves,($Set_local x15) # es') = (s', f', res)"
  shows "(\<exists>rv re. res = RSNormal rv re) \<or> (\<exists>e. res = RSCrash e)"
  using assms
  by (cases ves; cases "x15 < length (f_locs f)") auto

lemma run_step_basic_tee_local_result:
  assumes "run_step d (s,f,ves,($Tee_local x16) # es') = (s', f', res)"
  shows "(\<exists>rv re. res = RSNormal rv re) \<or> (\<exists>e. res = RSCrash e)"
  using assms
  by (cases ves) auto

lemma run_step_basic_get_global_result:
  assumes "run_step d (s,f,ves,($Get_global x17) # es') = (s', f', res)"
  shows "(\<exists>rv re. res = RSNormal rv re) \<or> (\<exists>e. res = RSCrash e)"
  using assms
  by auto

lemma run_step_basic_set_global_result:
  assumes "run_step d (s,f,ves,($Set_global x18)#es') = (s', f', res)"
  shows "(\<exists>rv re. res = RSNormal rv re) \<or> (\<exists>e. res = RSCrash e)"
  using assms
  by (cases ves) auto

lemma run_step_basic_load_result:
  assumes "run_step d (s,f,ves,($Load x191 x192 x193 x194)#es') = (s', f', res)"
  shows "(\<exists>rv re. res = RSNormal rv re) \<or> (\<exists>e. res = RSCrash e)"
proof (cases x192)
  case None
  thus ?thesis
    using assms
  proof (cases ves)
    case (Cons a list)
    thus ?thesis
      using assms None
    proof (cases "smem_ind s (f_inst f)"; cases a)
      fix aa x1
      assume "smem_ind s (f_inst f) = Some aa" and "a = ConstInt32 x1" 
      thus ?thesis
        using assms None Cons
        by (cases "load (s.mems s ! aa) (nat_of_int x1) x194 (t_length x191)") auto
    qed auto
  qed auto
next
  case (Some a)
  thus ?thesis
    using assms
  proof (cases ves)
    case (Cons a' list)
    thus ?thesis
      using assms Some
    proof (cases "smem_ind s (f_inst f)"; cases a; cases a')
      fix aa x y x1
      assume "smem_ind s (f_inst f) = Some aa" and "a = (x, y)" and "a' = ConstInt32 x1"
      thus ?thesis
        using assms Some Cons
        by (cases "load_packed y (s.mems s ! aa) (nat_of_int x1) x194 (tp_length x) (t_length x191)") auto
    qed auto
  qed auto
qed

lemma run_step_basic_store_result:
  assumes "run_step d (s,f,ves,($Store x201 x202 x203 x204)#es') = (s', f', res)"
  shows "(\<exists>rv re. res = RSNormal rv re) \<or> (\<exists>e. res = RSCrash e)"
proof (cases x202)
  case None
  thus ?thesis
    using assms
  proof (cases ves)
    case (Cons a list)
    note outer_Cons = Cons
    thus ?thesis
      using assms None
    proof (cases list)
      case (Cons a' list')
      thus ?thesis
        using assms None outer_Cons
      proof (cases a'; cases "types_agree x201 a"; cases "smem_ind s (f_inst f)")
        fix k aa
        assume "a' = ConstInt32 k" and "types_agree x201 a" and "smem_ind s (f_inst f) = Some aa"
        thus ?thesis
          using assms None outer_Cons Cons
          by (cases "store (s.mems s ! aa) (nat_of_int k) x204 (bits a) (t_length x201)") auto
      qed auto
    qed auto
  qed auto
next
  case (Some a'')
  thus ?thesis
    using assms
  proof (cases ves)
    case (Cons a list)
    note outer_Cons = Cons
    thus ?thesis
      using assms Some
    proof (cases list)
      case (Cons a' list')
      thus ?thesis
        using assms Some outer_Cons
      proof (cases a'; cases "types_agree x201 a"; cases "smem_ind s (f_inst f)")
        fix k aa
        assume "a' = ConstInt32 k" and "types_agree x201 a" and "smem_ind s (f_inst f) = Some aa"
        thus ?thesis
          using assms Some outer_Cons Cons
          by (cases "store_packed (s.mems s ! aa) (nat_of_int k) x204 (bits a) (tp_length a'')") auto
      qed auto
    qed auto
  qed auto
qed

lemma run_step_basic_current_memory_result:
  assumes "run_step d (s,f,ves,($Current_memory)#es') = (s', f', res)"
  shows "(\<exists>rv re. res = RSNormal rv re) \<or> (\<exists>e. res = RSCrash e)"
  using assms
  by (cases "smem_ind s (f_inst f)") auto

lemma run_step_basic_grow_memory_result:
  assumes "run_step d (s,f,ves,($Grow_memory)#es') = (s', f', res)"
  shows "(\<exists>rv re. res = RSNormal rv re) \<or> (\<exists>e. res = RSCrash e)"
  using assms
proof (cases ves)
  case (Cons a list)
  thus ?thesis
    using assms
  proof (cases a; cases "smem_ind s (f_inst f)")
    fix c a'
    assume "a = ConstInt32 c" and "smem_ind s (f_inst f) = Some a'"
    thus ?thesis
      using assms Cons
      by (cases "mem_grow (s.mems s ! a') (nat_of_int c)") auto
  qed auto
qed auto

lemma run_step_basic_const_result:
  assumes "run_step d (s,f,ves,($EConst x23)#es') = (s', f', res)"
  shows "\<exists>e. res = RSCrash e"
  using assms
  by auto

lemma run_step_basic_unop_result:
  assumes "run_step d (s,f,ves,($Unop x241 x242)#es') = (s', f', res)"
  shows "(\<exists>rv re. res = RSNormal rv re) \<or> (\<exists>e. res = RSCrash e)"
  using assms
proof (cases ves)
  case (Cons a list)
  thus ?thesis
    using assms
    by (cases x241; cases a) auto
qed (cases x241; auto)

lemma run_step_basic_binop_result:
  assumes "run_step d (s,f,ves,($Binop x261 x262)#es') = (s', f', res)"
  shows "(\<exists>rv re. res = RSNormal rv re) \<or> (\<exists>e. res = RSCrash e)"
  using assms
proof (cases ves)
  case (Cons a list)
  note outer_Cons = Cons
  thus ?thesis
    using assms
  proof (cases list)
    case (Cons a' list')
    thus ?thesis
      using assms outer_Cons
      by (auto split: option.splits)
  qed (cases x261; cases a; auto)
qed (cases x261; auto)

lemma run_step_basic_testop_result:
  assumes "run_step d (s,f,ves,($Testop x281 x282)#es') = (s', f', res)"
  shows "(\<exists>rv re. res = RSNormal rv re) \<or> (\<exists>e. res = RSCrash e)"
  using assms
proof (cases ves)
  case (Cons a list)
  thus ?thesis
    using assms
    by (cases x281; cases a) auto
qed (cases x281; auto)

lemma run_step_basic_relop_result:
  assumes "run_step d (s,f,ves,($Relop x291 x292)#es') = (s', f', res)"
  shows "(\<exists>rv re. res = RSNormal rv re) \<or> (\<exists>e. res = RSCrash e)"
  using assms
  by (auto split: list.splits)

lemma run_step_basic_cvtop_result:
  assumes "run_step d (s,f,ves,($Cvtop t2 x312 t1 sx)#es') = (s', f', res)"
  shows "(\<exists>rv re. res = RSNormal rv re) \<or> (\<exists>e. res = RSCrash e)"
  using assms
proof (cases ves; cases x312)
  fix a ves'
  assume "ves = a#ves'" and "x312 = Convert" 
  thus ?thesis
    using assms
    by (cases "cvt t2 sx a"; cases "types_agree t1 a") auto
next
  fix a ves'
  assume "ves = a#ves'" and "x312 = Reinterpret" 
  thus ?thesis
    using assms
    by (cases sx; cases "types_agree t1 a") auto
qed auto

lemma run_step_trap_result:
  assumes "run_step d (s,f,ves,Trap#es') = (s', f', res)"
  shows "(res = res_trap [] []) \<or> (\<exists>e. res = RSCrash e)"
  using assms
  by (auto split: if_splits)

lemma run_step_invoke_result:
  assumes "run_step d (s,f,ves,(Invoke i_cl)#es') = (s', f', res)"
  shows "(\<exists>rv re. res = RSNormal rv re) \<or> (\<exists>e. res = RSCrash e)"
proof -
  obtain t1s t2s where cl_type_is:"cl_type (funcs s!i_cl) = (t1s _> t2s)"
    using tf.exhaust
    by blast
  obtain ves' ves'' where split_n_is:"split_n ves (length t1s) = (ves', ves'')"
    by fastforce
  show ?thesis
  proof (cases "(funcs s!i_cl)")
    case (Func_native x11 x12 x13 x14)
    thus ?thesis
      using assms cl_type_is split_n_is
      unfolding cl_type_def
      by (cases "length t1s \<le> length ves") auto
  next
    case (Func_host x21 x22)
    show ?thesis
    proof (cases "host_apply_impl s (t1s _> t2s) x22 (rev ves')")
      case None
      thus ?thesis
        using assms cl_type_is split_n_is Func_host
        unfolding cl_type_def
        by (cases "length t1s \<le> length ves")  auto
    next
      case (Some a)
      thus ?thesis
      proof (cases a)
        case (Pair s' vcs')
        thus ?thesis
          using assms cl_type_is split_n_is Func_host Some
          unfolding cl_type_def
          by (cases "length t1s \<le> length ves"; cases "list_all2 types_agree t2s vcs'")  auto
      qed
    qed
  qed
qed

lemma run_step_label_result:
  assumes "run_step d (s,f,ves,(Label x41 x42 x43)#es') = (s', f', res)"
  shows "(\<exists>rv re. res = RSNormal rv re) \<or> (\<exists>r rvs. res = RSBreak r rvs) \<or> (\<exists>rvs. res = RSReturn rvs) \<or> (\<exists>e. res = RSCrash e)"
  using assms
  by (cases res) auto

lemma run_step_local_result:
  assumes "run_step d (s,f,ves,(Frame x51 fl x54)#es') = (s', f', res)"
  shows "(\<exists>rv re. res = RSNormal rv re) \<or> (\<exists>e. res = RSCrash e)"
  using assms
  by (auto split: if_splits prod.splits list.splits nat.splits res_step.splits)

lemma run_step_break:
  assumes "run_step d (s,f,ves,e#es') = (s', f', RSBreak n res)"
  shows "(e = $Br n) \<or> (\<exists>n les es. e = Label n les es)"
proof (cases e)
  case (Basic x1)
  thus ?thesis
  proof (cases x1)
    case Unreachable
    thus ?thesis
      using run_step_basic_unreachable_result assms Basic
      by fastforce
  next
    case Nop
    thus ?thesis
      using assms Basic
      by fastforce
  next
    case Drop
    thus ?thesis
      using run_step_basic_drop_result assms Basic
      by fastforce
  next
    case Select
    thus ?thesis
      using run_step_basic_select_result assms Basic
      by fastforce
  next
    case (Block x51 x52)
    thus ?thesis
      using run_step_basic_block_result assms Basic
      by fastforce
  next
    case (Loop x61 x62)
    thus ?thesis
      using run_step_basic_loop_result assms Basic
      by fastforce
  next
    case (If x71 x72 x73)
    thus ?thesis
      using run_step_basic_if_result assms Basic
      by fastforce
  next
    case (Br x8)
    thus ?thesis
      using run_step_basic_br_result assms Basic
      by fastforce
  next
    case (Br_if x9)
    thus ?thesis
      using run_step_basic_br_if_result assms Basic
      by fastforce
  next
    case (Br_table x10)
    thus ?thesis
      using run_step_basic_br_table_result assms Basic
      by fastforce
  next
    case Return
    thus ?thesis
      using run_step_basic_return_result assms Basic
      by fastforce
  next
    case (Call x12)
    thus ?thesis
      using run_step_basic_call_result assms Basic
      by fastforce
  next
    case (Call_indirect x13)
    thus ?thesis
      using run_step_basic_call_indirect_result assms Basic
      by fastforce
  next
    case (Get_local x14)
    thus ?thesis
      using run_step_basic_get_local_result assms Basic
      by fastforce
  next
    case (Set_local x15)
    thus ?thesis
      using run_step_basic_set_local_result assms Basic
      by fastforce
  next
    case (Tee_local x16)
    thus ?thesis
      using run_step_basic_tee_local_result assms Basic
      by fastforce
  next
    case (Get_global x17)
    thus ?thesis
      using assms Basic
      by fastforce
  next
    case (Set_global x18)
    thus ?thesis
      using run_step_basic_set_global_result assms Basic
      by fastforce
  next
    case (Load x191 x192 x193 x194)
    thus ?thesis
      using run_step_basic_load_result assms Basic
      by fastforce
  next
    case (Store x201 x202 x203 x204)
    thus ?thesis
      using run_step_basic_store_result assms Basic
      by fastforce
  next
    case Current_memory
    thus ?thesis
      using run_step_basic_current_memory_result assms Basic
      by fastforce
  next
    case Grow_memory
    thus ?thesis
      using run_step_basic_grow_memory_result assms Basic
      by fastforce
  next
    case (EConst x23)
    thus ?thesis
      using assms Basic
      by fastforce
  next
    case (Unop x241 x242)
    thus ?thesis
      using run_step_basic_unop_result assms Basic
      by fastforce
  next
    case (Binop x261 x262)
    thus ?thesis
      using run_step_basic_binop_result assms Basic
      by fastforce
  next
    case (Testop x281 x282)
    thus ?thesis
      using run_step_basic_testop_result assms Basic
      by fastforce
  next
    case (Relop x291 x292)
    thus ?thesis
      using run_step_basic_relop_result assms Basic
      by fastforce
  next
    case (Cvtop x311 x312 x313 x314)
    thus ?thesis
      using run_step_basic_cvtop_result assms Basic
      by fastforce
  qed
next
  case Trap
  thus ?thesis
    using assms
    by (auto split: if_splits)
next
  case (Invoke x3)
  thus ?thesis
    using assms run_step_invoke_result
    by fastforce
next
  case (Label x41 x42 x43)
  thus ?thesis
    by auto
next
  case (Frame x51 fl x54)
  thus ?thesis
    using assms run_step_local_result
    by fastforce
qed

lemma run_step_return:
  assumes "run_step d (s,f,ves,e#es') = (s', f', RSReturn res)"
  shows "(e = $Return) \<or> (\<exists>n les es. e = Label n les es)"
proof (cases e)
  case (Basic x1)
  thus ?thesis
  proof (cases x1)
    case Unreachable
    thus ?thesis
      using run_step_basic_unreachable_result assms Basic
      by fastforce
  next
    case Nop
    thus ?thesis
      using assms Basic
      by fastforce
  next
    case Drop
    thus ?thesis
      using run_step_basic_drop_result assms Basic
      by fastforce
  next
    case Select
    thus ?thesis
      using run_step_basic_select_result assms Basic
      by fastforce
  next
    case (Block x51 x52)
    thus ?thesis
      using run_step_basic_block_result assms Basic
      by fastforce
  next
    case (Loop x61 x62)
    thus ?thesis
      using run_step_basic_loop_result assms Basic
      by fastforce
  next
    case (If x71 x72 x73)
    thus ?thesis
      using run_step_basic_if_result assms Basic
      by fastforce
  next
    case (Br x8)
    thus ?thesis
      using run_step_basic_br_result assms Basic
      by fastforce
  next
    case (Br_if x9)
    thus ?thesis
      using run_step_basic_br_if_result assms Basic
      by fastforce
  next
    case (Br_table x10)
    thus ?thesis
      using run_step_basic_br_table_result assms Basic
      by fastforce
  next
    case Return
    thus ?thesis
      using run_step_basic_return_result assms Basic
      by fastforce
  next
    case (Call x12)
    thus ?thesis
      using run_step_basic_call_result assms Basic
      by fastforce
  next
    case (Call_indirect x13)
    thus ?thesis
      using run_step_basic_call_indirect_result assms Basic
      by fastforce
  next
    case (Get_local x14)
    thus ?thesis
      using run_step_basic_get_local_result assms Basic
      by fastforce
  next
    case (Set_local x15)
    thus ?thesis
      using run_step_basic_set_local_result assms Basic
      by fastforce
  next
    case (Tee_local x16)
    thus ?thesis
      using run_step_basic_tee_local_result assms Basic
      by fastforce
  next
    case (Get_global x17)
    thus ?thesis
      using assms Basic
      by fastforce
  next
    case (Set_global x18)
    thus ?thesis
      using run_step_basic_set_global_result assms Basic
      by fastforce
  next
    case (Load x191 x192 x193 x194)
    thus ?thesis
      using run_step_basic_load_result assms Basic
      by fastforce
  next
    case (Store x201 x202 x203 x204)
    thus ?thesis
      using run_step_basic_store_result assms Basic
      by fastforce
  next
    case Current_memory
    thus ?thesis
      using run_step_basic_current_memory_result assms Basic
      by fastforce
  next
    case Grow_memory
    thus ?thesis
      using run_step_basic_grow_memory_result assms Basic
      by fastforce
  next
    case (EConst x23)
    thus ?thesis
      using assms Basic
      by fastforce
  next
    case (Unop x241 x242)
    thus ?thesis
      using run_step_basic_unop_result assms Basic
      by fastforce
  next
    case (Binop x261 x262)
    thus ?thesis
      using run_step_basic_binop_result assms Basic
      by fastforce
  next
    case (Testop x281 x282)
    thus ?thesis
      using run_step_basic_testop_result assms Basic
      by fastforce
  next
    case (Relop x291 x292)
    thus ?thesis
      using run_step_basic_relop_result assms Basic
      by fastforce
  next
    case (Cvtop x311 x312 x313 x314)
    thus ?thesis
      using run_step_basic_cvtop_result assms Basic
      by fastforce
  qed
next
  case Trap
  thus ?thesis
    using assms
    by (auto split: if_splits)
next
  case (Invoke x3)
  thus ?thesis
    using assms run_step_invoke_result
    by fastforce
next
  case (Label x41 x42 x43)
  thus ?thesis
    by auto
next
  case (Frame x51 f x54)
  thus ?thesis
    using assms run_step_local_result
    by fastforce
qed

lemma run_step_label_break_imp_break:
  assumes "run_step d (s, f, ves, (Label ln les es)#es') = (s', f', RSBreak n res)"
          "split_vals_e es = (lves, les)"
  shows "run_step d (s, f, (rev lves, les)) = (s', f', RSBreak (Suc n) res)"
  using assms
  by (auto split: if_splits prod.splits list.splits nat.splits res_step.splits)

lemma run_step_label_return_imp_return:
  assumes "run_step d (s, f, ves, (Label n les es)#es') = (s', f', RSReturn res)"
          "split_vals_e es = (lves, les)"
  shows "run_step d (s, f, (rev lves, les)) = (s', f', RSReturn res)"
  using assms
  by (auto split: if_splits prod.splits list.splits nat.splits res_step.splits)

(* These definitions are needed because the automatic induction process hangs if they are unrolled *)
definition run_step_break_imp_lfilled_prop where
  "run_step_break_imp_lfilled_prop s' f' n res =
     (\<lambda>d (s,f,ves,es). (run_step d (s,f,ves,es) = (s', f', RSBreak n res)) \<longrightarrow>
       s = s' \<and> f = f' \<and>
       (\<exists>n' lfilled es_c. n' \<ge> n \<and> Lfilled_exact (n'-n) lfilled ((vs_to_es res) @ [$Br n'] @ es_c) es))"

lemma run_step_break_imp_lfilled:
  assumes "run_step d (s,f,ves,es) = (s', f', RSBreak n res)"
  shows "s = s' \<and>
         f = f' \<and>
         (\<exists>n' lfilled es_c. n' \<ge> n \<and>
                            Lfilled_exact (n'-n) lfilled ((vs_to_es res) @ [$Br n'] @ es_c) ((vs_to_es ves)@es))"
  using assms
proof (induction d "(s,f,ves,es)" arbitrary: n ves es rule: run_step.induct)
  case (1 d ves es)
  show ?case
  proof (cases es)
    case Nil
    thus ?thesis
      using 1(3)
      by simp
  next
    case (Cons e es')
    consider (a) "e = $Br n" | (b) n' lles les where "e = Label n' lles les"
      using run_step_break 1(3) Cons
      by blast
    thus ?thesis
    proof cases
      case a
      thus ?thesis
        using 1(3) Cons Lfilled_exact.intros(1)
        by fastforce
    next
      case b
      then obtain x1 x21 x22 where les_is:
       "es = Label n' lles les # es'"
       "\<not> es_is_trap les"
       "(x1, x21 # x22) = split_vals_e les"
       "run_step d (s, f, rev x1, x21 # x22) = (s', f', RSBreak (Suc n) res)"
        using 1(3) Cons
        unfolding run_step.simps[of d s f ves es]
        by (simp split: if_splits prod.splits res_step.splits nat.splits list.splits del: run_step.simps)
      obtain n'' where "s = s' \<and>
            f = f' \<and>
            (\<exists>lfilled es_c.
                Suc n \<le> n'' \<and>
                Lfilled_exact (n'' - n - 1) lfilled
                 (vs_to_es res @ [$Br n''] @ es_c)
                 (vs_to_es (rev x1) @ x21 # x22))"
        using 1(1)[OF les_is(1) _ _ les_is(2,3) _ les_is(4)]
        by fastforce
      thus ?thesis
        using Lfilled_exact.intros(2)[of _ "rev ves" n' lles _ es' "n'' - Suc n"] les_is(1,3)
        using split_vals_e_conv_app[OF les_is(3)[symmetric]]
        apply simp
        apply (metis Suc_diff_le Suc_leD diff_Suc_Suc)
        done
    qed
  qed
qed

lemma run_step_return_imp_lfilled:
  assumes "run_step d (s,f,ves,es) = (s', f', RSReturn res)"
  shows "s = s' \<and> f = f' \<and> (\<exists>n lfilled es_c. Lfilled_exact n lfilled ((vs_to_es res) @ [$Return] @ es_c) ((vs_to_es ves)@es))"
  using assms
proof (induction d "(s,f,ves,es)" arbitrary: ves es rule: run_step.induct)
  case (1 d ves es)
  show ?case
  proof (cases es)
    case Nil
    thus ?thesis
      using 1(3)
      by simp
  next
    case (Cons e es')
    consider (a) "e = $Return" | (b) n' lles les where "e = Label n' lles les"
      using run_step_return 1(3) Cons
      by blast
    thus ?thesis
    proof cases
      case a
      thus ?thesis
        using 1(3) Cons Lfilled_exact.intros(1)
        by fastforce
    next
      case b
      then obtain x1 x21 x22 where les_is:
       "es = Label n' lles les # es'"
       "\<not> es_is_trap les"
       "(x1, x21 # x22) = split_vals_e les"
       "run_step d (s, f, rev x1, x21 # x22) = (s', f', RSReturn res)"
        using 1(3) Cons
        unfolding run_step.simps[of d s f ves es]
        by (simp split: if_splits prod.splits res_step.splits nat.splits list.splits del: run_step.simps)
      obtain n'' where "s = s' \<and>
            f = f' \<and>
            (\<exists>lfilled es_c.
                Lfilled_exact n'' lfilled
                 (vs_to_es res @ [$Return] @ es_c)
                 (vs_to_es (rev x1) @ x21 # x22))"
        using 1(1)[OF les_is(1) _ _ les_is(2,3) _ les_is(4)]
        by fastforce
      thus ?thesis
        using Lfilled_exact.intros(2)[of _ "rev ves" n' lles _ es'] les_is(1,3)
        using split_vals_e_conv_app[OF les_is(3)[symmetric]]
        apply simp
        apply metis
        done
    qed
  qed
qed

lemma run_step_basic_unop_testop_sound:
  assumes "(run_step d (s,f,ves,($b_e)#es') = (s', f', RSNormal rvs res))"
          "b_e = Unop t op \<or> b_e = Testop t testop"
  shows "\<lparr>s;f;(vs_to_es ves)@($b_e)#es'\<rparr> \<leadsto> \<lparr>s';f';(vs_to_es rvs)@res\<rparr>"
proof -
  consider (1) "b_e = Unop t op" | (3) "b_e = Testop t testop"
    using assms(2)
    by blast
  note b_e_cases = this
  show ?thesis
    using assms(1)
  proof (cases ves)
    case (Cons a list)
    thus ?thesis
    using assms Cons
       is_const_list_vs_to_es_list[of "rev list"]
       progress_L0[OF reduce.intros(1)[OF reduce_simple.intros(1)]]
       progress_L0[OF reduce.intros(1)[OF reduce_simple.intros(4)]]
    by fastforce
  qed (cases rule: b_e_cases; cases t; auto)
qed

lemma run_step_basic_binop_relop_sound:
  assumes "(run_step d (s,f,ves,($b_e)#es') = (s', f', RSNormal rvs res))"
          "b_e = Binop t op \<or> b_e = Relop t rop"
  shows "\<lparr>s;f;(vs_to_es ves)@($b_e)#es'\<rparr> \<leadsto> \<lparr>s';f';(vs_to_es rvs)@res\<rparr>"
proof -
  consider
    (1) "b_e = Binop t op"
  | (3) "b_e = Relop t rop"
    using assms(2)
    by blast
  note b_e_cases = this
  show ?thesis
    using assms(1)
  proof (cases ves)
    case outer_Cons:(Cons v1 list)
    thus ?thesis
      using assms(1)
    proof (cases list)
      case (Cons v2 list')
      thus ?thesis
        using assms outer_Cons
             is_const_list_vs_to_es_list[of "rev list'"]
             progress_L0[OF reduce.intros(1)[OF reduce_simple.intros(2)]]
             progress_L0[OF reduce.intros(1)[OF reduce_simple.intros(3)]]
             progress_L0[OF reduce.intros(1)[OF reduce_simple.intros(5)]]
        by (cases "app_binop op v2 v1"; fastforce)
    qed (cases rule: b_e_cases; cases t; cases v1; auto)
  qed (cases rule: b_e_cases; cases t; auto)
qed

lemma run_step_basic_sound:
  assumes "(run_step d (s,f,ves,($b_e)#es') = (s', f', RSNormal rvs res))"
  shows "\<lparr>s;f;(vs_to_es ves)@($b_e)#es'\<rparr> \<leadsto> \<lparr>s';f';(vs_to_es rvs)@res\<rparr>"
proof -
  show ?thesis
  proof (cases b_e)
    case Unreachable
    thus ?thesis
      using is_const_list_vs_to_es_list[of "rev ves"]
            progress_L0[OF reduce.intros(1)[OF reduce_simple.intros(9)]]
            assms
      by fastforce
  next
    case Nop
    thus ?thesis
      using is_const_list_vs_to_es_list[of "rev ves"]
            progress_L0[OF reduce.intros(1)[OF reduce_simple.intros(10)]]
            assms
      by fastforce
  next
    case Drop
    thus ?thesis
      using assms
    proof (cases ves)
      case (Cons a list)
      hence "vs_to_es ves = vs_to_es list @ [$C a]"
        by fastforce
      thus ?thesis
        using is_const_list_vs_to_es_list[of "rev list"]
              progress_L0[OF reduce.intros(1)[OF reduce_simple.intros(11)]]
              Drop assms Cons
        by auto
    qed auto
  next
    case Select
    thus ?thesis
      using assms
    proof (cases ves)
      case outer_outer_cons:(Cons a list)
      thus ?thesis
        using Select assms
      proof (cases a; cases list)
        case (ConstInt32 x1a)
        case outer_cons:(Cons a' list')
        thus ?thesis
          using assms outer_outer_cons ConstInt32 Select
        proof (cases list')
          case (Cons a'' list'')
          hence "vs_to_es ves = vs_to_es list'' @ [$C a'', $C a', $C ConstInt32 x1a]"
            using outer_outer_cons outer_cons ConstInt32
            by fastforce
          thus ?thesis
            using is_const_list_vs_to_es_list[of "rev list''"]
                  progress_L0[OF reduce.intros(1)[OF reduce_simple.intros(12)], of x1a s f "rev list''" a'' a' es']
                  progress_L0[OF reduce.intros(1)[OF reduce_simple.intros(13)], of x1a s f "rev list''" a'' a' es']
                  assms outer_outer_cons outer_cons Cons ConstInt32 Select
            by (fastforce split: if_splits)
        qed auto
      qed auto
    qed auto
  next
    case (Block x51 x52)
    thus ?thesis
    proof (cases x51)
      case (Tf t1s t2s)
      thus ?thesis
        using Block assms
      proof (cases "length t1s \<le> length ves"; cases "split_n ves (length t1s)")
        case True
        case (Pair ves' ves'')
        hence "vs_to_es ves = vs_to_es ves'' @ vs_to_es ves'"
          using split_n_conv_app
          by fastforce
        moreover
        have "s = s'" "f = f'" "res = [Label (length t2s) [] (vs_to_es ves' @ ($* x52))] @ es'"
             "rvs = ves''"
          using Block assms Tf True Pair
          by simp_all
        moreover
        have "\<lparr>s;f;(vs_to_es ves'')@(vs_to_es ves')@[$Block x51 x52]@es'\<rparr> \<leadsto> \<lparr>s;f;(vs_to_es ves'')@[Label (length t2s) [] (vs_to_es ves' @ ($* x52))]@es'\<rparr>"
          using Tf split_n_length[OF Pair True] progress_L0[OF reduce.intros(1)[OF reduce_simple.intros(14)]]
                is_const_list_vs_to_es_list[of "rev ves'"] is_const_list_vs_to_es_list[of "rev ves''"]
          by simp
        ultimately
        show ?thesis
          using Block
          by auto
      qed auto
    qed
  next
    case (Loop x61 x62)
    thus ?thesis
    proof (cases x61)
      case (Tf t1s t2s)
      thus ?thesis
        using Loop assms
      proof (cases "length t1s \<le> length ves"; cases "split_n ves (length t1s)")
        case True
        case (Pair ves' ves'')
        hence "vs_to_es ves = vs_to_es ves'' @ vs_to_es ves'"
          using split_n_conv_app
          by fastforce
        moreover
        have "s = s'" "f = f'" "res = [Label (length t1s) [$Loop x61 x62] (vs_to_es ves' @ ($* x62))] @ es'"
             "rvs = ves''"
          using Loop assms Tf True Pair
          by auto
        moreover
        have "\<lparr>s;f;(vs_to_es ves'')@(vs_to_es ves')@[$Loop x61 x62]@es'\<rparr> \<leadsto> \<lparr>s;f;(vs_to_es ves'')@[Label (length t1s) [$Loop x61 x62] (vs_to_es ves' @ ($* x62))]@es'\<rparr>"
          using Tf split_n_length[OF Pair True] progress_L0[OF reduce.intros(1)[OF reduce_simple.intros(15)]]
                is_const_list_vs_to_es_list[of "rev ves'"] is_const_list_vs_to_es_list[of "rev ves''"]
          by simp
        ultimately
        show ?thesis
          using Loop
          by auto
      qed auto
    qed
  next
    case (If x71 x72 x73)
    thus ?thesis
      using assms
    proof (cases ves)
      case (Cons a list)
      thus ?thesis
        using assms If
      proof (cases a)
        case (ConstInt32 x1)
      hence "vs_to_es ves = vs_to_es list @ [$C ConstInt32 x1]"
        unfolding Cons
        by simp
      thus ?thesis
        using progress_L0[OF reduce.intros(1)[OF reduce_simple.intros(16)]]
              progress_L0[OF reduce.intros(1)[OF reduce_simple.intros(17)]]
              is_const_list_vs_to_es_list[of "rev list"]
              assms Cons If ConstInt32
        by (cases "int_eq x1 0") auto
      qed auto
    qed auto
  next
    case (Br x8)
    thus ?thesis
      using assms
      by auto
  next
    case (Br_if x9)
    thus ?thesis
      using assms
    proof (cases ves)
      case (Cons a list)
      thus ?thesis
        using assms Br_if
      proof (cases a)
        case (ConstInt32 x1)
      hence "vs_to_es ves = vs_to_es list @ [$C ConstInt32 x1]"
        unfolding Cons
        by simp
      thus ?thesis
        using progress_L0[OF reduce.intros(1)[OF reduce_simple.intros(21)]]
              progress_L0[OF reduce.intros(1)[OF reduce_simple.intros(22)]]
              is_const_list_vs_to_es_list[of "rev list"]
              assms Cons Br_if ConstInt32
        by (cases "int_eq x1 0") auto
      qed auto
    qed auto
  next
    case (Br_table x10)
    thus ?thesis
      using assms
    proof (cases ves)
      case (Cons a list)
      thus ?thesis
        using assms Br_table
      proof (cases a)
        case (ConstInt32 x1)
        thus ?thesis
          using progress_L0[OF reduce.intros(1)[OF reduce_simple.intros(23)]]
                progress_L0[OF reduce.intros(1)[OF reduce_simple.intros(24)]]
                is_const_list_vs_to_es_list[of "rev list"]
                assms Br_table Cons
          by (cases "(nat_of_int x1) < length x10") auto
      qed auto
    qed auto
  next
    case Return
    thus ?thesis
      using assms
      by simp
  next
    case (Call x12)
    thus ?thesis
      using assms progress_L0[OF reduce.intros(2)]
            is_const_list_vs_to_es_list[of "rev ves"]
      by auto
  next
    case (Call_indirect x13)
    thus ?thesis
      using assms
    proof (cases ves)
      case (Cons a list)
      thus ?thesis
        using assms Call_indirect
      proof (cases a)
        case (ConstInt32 c)
        thus ?thesis
        proof (cases "stab s (f_inst f) (nat_of_int c)")
          case None
          thus ?thesis
            using assms Call_indirect Cons ConstInt32
                  progress_L0[OF reduce.intros(4)]
                  is_const_list_vs_to_es_list[of "rev list"]
            by auto
        next
          case (Some cl)
          thus ?thesis
          proof (cases "stypes s (f_inst f) x13 = cl_type (funcs s!cl)")
            case True
            hence "\<lparr>s;f;(vs_to_es list) @ [$C ConstInt32 c, $Call_indirect x13]@es'\<rparr> \<leadsto> \<lparr>s;f;(vs_to_es list) @ [Invoke cl]@es'\<rparr>"
              using progress_L0[OF reduce.intros(3)] True Some is_const_list_vs_to_es_list[of "rev list"]
              by fastforce
            thus ?thesis
              using assms Call_indirect Cons ConstInt32 Some True
              by auto
          next
            case False
            hence "\<lparr>s;f;(vs_to_es list)@[$C ConstInt32 c, $Call_indirect x13]@es'\<rparr> \<leadsto> \<lparr>s;f;(vs_to_es list)@[Trap]@es'\<rparr>"
              using progress_L0[OF reduce.intros(4)] False Some is_const_list_vs_to_es_list[of "rev list"]
              by fastforce
            thus ?thesis
              using assms Call_indirect Cons ConstInt32 Some False
              by auto
          qed
        qed
      qed auto
    qed auto
  next
    case (Get_local j)
    thus ?thesis
      using assms
    proof (cases "j < length (f_locs f)")
      case True
      then obtain vs1 v vs2 where "(f_locs f) = vs1@[v]@vs2" "length vs1 = j"
        using id_take_nth_drop
        by fastforce
      thus ?thesis
        using assms Get_local True
              progress_L0[OF reduce.intros(8)]
              is_const_list_vs_to_es_list[of "rev ves"]
        by auto
    qed auto
  next
    case (Set_local j)
    thus ?thesis
      using assms      
    proof (cases ves)
      case (Cons a list)
      thus ?thesis
        using assms Set_local
      proof (cases "j < length (f_locs f)")
        case True
        obtain vs1 v vs2 where vs_def:"f_locs f = vs1@[v]@vs2" "length vs1 = j"
          using id_take_nth_drop True
          by fastforce
        have f_is:"f = \<lparr>f_locs = vs1 @ [v] @ vs2, f_inst = f_inst f\<rparr>"
                  "f' = \<lparr>f_locs = vs1 @ [a] @ vs2, f_inst = f_inst f\<rparr>"
                  "rvs = list"
                  "s = s'"
                  "res = es'"
          using assms Set_local True Cons vs_def
          by auto
        thus ?thesis
          using Set_local True Cons vs_def(1)
                progress_L0[OF reduce.intros(9)[OF vs_def(2)], of s v vs2 "f_inst f" "rev list" a es']
          apply simp
          apply (metis f_is(1) vs_def(1))
          done
      qed auto
    qed auto
  next
    case (Tee_local x16)
    thus ?thesis
      using assms
    proof (cases ves)
      case (Cons a list)
      thus ?thesis
        using assms Tee_local
              progress_L0[OF reduce.intros(1)[OF reduce_simple.intros(28)]]
                              is_const_list_vs_to_es_list[of "rev list"]
        by (auto simp add: is_const_def)
    qed auto
  next
    case (Get_global x17)
    thus ?thesis
      using assms
            progress_L0[OF reduce.intros(10)]
            is_const_list_vs_to_es_list[of "rev ves"]
      by (auto simp add: is_const_def)
  next
    case (Set_global x18)
    thus ?thesis
      using assms
    proof (cases ves)
      case (Cons a list)
      thus ?thesis
        using assms Set_global
              progress_L0[OF reduce.intros(11)]
              is_const_list_vs_to_es_list[of "rev list"]
        by (auto simp add: is_const_def)
    qed auto
  next
    case (Load x191 x192 x193 x194)
    thus ?thesis
      using assms
    proof (cases x192; cases ves)
      case None
      case (Cons a list)
      thus ?thesis
        using Load assms None
      proof (cases a; cases "smem_ind s (f_inst f)")
        case (ConstInt32 x1)
        case (Some a)
        thus ?thesis
          using Load assms None Cons ConstInt32
              progress_L0[OF reduce.intros(12)]
              progress_L0[OF reduce.intros(13)]
              is_const_list_vs_to_es_list[of "rev list"]
          apply (cases "load (s.mems s ! a) (nat_of_int x1) x194 (t_length x191)" )
          apply (fastforce simp add: is_const_def)+
          done
      qed auto
    next
      case outer_some:(Some tp_sx)
      case (Cons a list)
      thus ?thesis
        using Load assms outer_some
        proof (cases a; cases "smem_ind s (f_inst f)"; cases tp_sx)
          case (ConstInt32 x1)
          case (Pair tp sx)
          case (Some a)
          thus ?thesis
            using Load assms outer_some Cons ConstInt32 Pair
                  progress_L0[OF reduce.intros(14)]
                  progress_L0[OF reduce.intros(15)]
                  is_const_list_vs_to_es_list[of "rev list"]
            by (cases "load_packed sx (s.mems s ! a) (nat_of_int x1) x194 (tp_length tp) (t_length x191)")
               (fastforce simp add: is_const_def)+
        qed auto
    qed auto
  next
    case (Store t tp a off)
    thus ?thesis
      using assms
    proof (cases ves)
      case outer_Cons:(Cons a list)
      thus ?thesis
        using Store assms
      proof (cases list)
        case (Cons a' list')
        thus ?thesis
          using Store outer_Cons assms
        proof (cases a')
          case (ConstInt32 x1)
          thus ?thesis
            using Store outer_Cons Cons assms
          proof (cases "(types_agree t a)"; cases "smem_ind s (f_inst f)")
            case True
            case outer_Some:(Some j)
            show ?thesis
            proof (cases tp)
              case None
              thus ?thesis
                using Store outer_Cons Cons assms True outer_Some ConstInt32
                      progress_L0[OF reduce.intros(16)]
                      progress_L0[OF reduce.intros(17)]
                      is_const_list_vs_to_es_list[of "rev list'"]
                by (cases "store (s.mems s ! j) (nat_of_int x1) off (bits a) (t_length t)")
                   fastforce+
            next
              case (Some the_tp)
              thus ?thesis
                using Store outer_Cons Cons assms True outer_Some ConstInt32
                      progress_L0[OF reduce.intros(18)]
                      progress_L0[OF reduce.intros(19)]
                      is_const_list_vs_to_es_list[of "rev list'"]
                by (cases "store_packed (s.mems s ! j) (nat_of_int x1) off (bits a) (tp_length the_tp)")
                   fastforce+
            qed
          qed (cases tp; auto)+
        qed (cases tp; auto)+
      qed (cases tp; auto)
    qed (cases tp; auto)
  next
    case Current_memory
    thus ?thesis
      using assms
    proof (cases "smem_ind s (f_inst f)")
      case (Some a)
      thus ?thesis
        using assms Current_memory 
              progress_L0[OF reduce.intros(20)]
              is_const_list_vs_to_es_list[of "rev ves"]
        by (fastforce simp add: is_const_def)
    qed auto
  next
    case Grow_memory
    thus ?thesis
      using assms
    proof (cases ves)
      case (Cons a list)
      thus ?thesis
        using assms Grow_memory
      proof (cases a; cases "smem_ind s (f_inst f)")
        case (ConstInt32 x1)
        case (Some j)
        thus ?thesis
          using assms Grow_memory Cons ConstInt32
                             progress_L0[OF reduce.intros(21)]
                             progress_L0[OF reduce.intros(22)]
              is_const_list_vs_to_es_list[of "rev list"] 
          by (cases "mem_grow (s.mems s ! j) (nat_of_int x1)") (fastforce simp add: is_const_def)+
      qed auto
    qed auto
  next
    case (EConst x23)
    thus ?thesis
      using assms
      by auto
  next
    case (Unop x241 x242)
    thus ?thesis
      using run_step_basic_unop_testop_sound[OF assms]
      by fastforce
  next
    case (Binop x261 x262)
    thus ?thesis
      using run_step_basic_binop_relop_sound[OF assms]
      by fastforce
  next
    case (Testop x281 x282)
    thus ?thesis
      using run_step_basic_unop_testop_sound[OF assms]
      by fastforce
  next
    case (Relop x291 x292)
    thus ?thesis
      using run_step_basic_binop_relop_sound[OF assms]
      by fastforce
  next
    case (Cvtop t2 cvtop t1 sx)
    thus ?thesis
      using assms
    proof (cases ves)
      case (Cons a list)
      thus ?thesis
        using assms Cvtop
      proof (cases cvtop; cases "types_agree t1 a")
        case Convert
        case True
        thus ?thesis
          using Convert assms Cvtop Cons
                progress_L0[OF reduce.intros(1)[OF reduce_simple.intros(7)[OF True]], of t2 sx s f "rev list" es']
                progress_L0[OF reduce.intros(1)[OF reduce_simple.intros(6)[OF True]], of t2 sx _ s f "rev list" es']
                is_const_list_vs_to_es_list[of "rev list"]
          apply (cases "(cvt t2 sx a)")
          apply fastforce+
          done
      next
        case Reinterpret
        case True
        thus ?thesis
          using Reinterpret assms Cvtop Cons
                progress_L0[OF reduce.intros(1)[OF reduce_simple.intros(8)]]
                is_const_list_vs_to_es_list[of "rev list"]
          by (cases sx) auto
      qed auto
    qed (cases cvtop; auto)
  qed
qed

theorem run_step_sound:
  assumes "run_step d (s,f,ves,es) = (s', f', RSNormal rvs res)"
  shows "\<lparr>s;f;(vs_to_es ves)@es\<rparr> \<leadsto> \<lparr>s';f';(vs_to_es rvs)@res\<rparr>"
  using assms
proof (induction d "(s, f, ves, es)" arbitrary: s' f es f' rvs res ves rule: run_step.induct)
    case (1 d f ves es)
    show ?case
    proof (cases es)
      case Nil
      thus ?thesis
        using 1(3)
        by simp
    next
      case (Cons e es')
      thus ?thesis
      proof (cases e)
        case (Basic x1)
        thus ?thesis
          using run_step_basic_sound 1(3) Cons
          by simp
      next
        case Trap
        thus ?thesis
          using 1(3) Cons reduce_simple.trap[of es "LBase (rev ves) es'"]
                Lfilled.L0[of _ "rev ves" es' "[Trap]"]
          apply (simp split: if_splits)
          apply (metis Lholed.inject(1) Nil_is_rev_conv basic e.distinct(11) lfilled_single list.discI trap)
          done
      next
        case (Invoke cl)
        obtain t1s t2s where "cl_type (funcs s!cl) = (t1s _> t2s)"
          using tf.exhaust[of _ thesis]
          by fastforce
        moreover
        obtain n where "length t1s = n"
          by blast
        moreover
        obtain m where "length t2s = m"
          by blast
        moreover
        note local_defs = calculation
        show ?thesis
        proof (cases "length ves \<ge> n")
          case outer_True:True
          obtain ves' ves'' where true_defs:"split_n ves n = (ves', ves'')"
            by (metis surj_pair)
          have ves'_length:"length (rev ves') = n"
            using split_n_length[OF true_defs outer_True] inj_basic_econst length_rev map_injective
            by blast
          show ?thesis
          proof (cases "(funcs s!cl)")
            case (Func_native i' tf fts fes)
            hence "s' = s" "f' = f" "res = ([Frame (length t2s) \<lparr> f_locs = (rev ves' @ (n_zeros fts)), f_inst = i'\<rparr> [$Block ([] _> t2s) fes]] @ es')"
                  "rvs = ves''"
              using 1(3) Invoke local_defs outer_True true_defs Cons
              unfolding cl_type_def
              by auto
            moreover
            have "\<lparr>s;f;(vs_to_es ves')@[Invoke cl]\<rparr> \<leadsto> \<lparr>s;f;([Frame (length t2s) \<lparr> f_locs = (rev ves' @ (n_zeros fts)), f_inst = i'\<rparr> [$Block ([] _> t2s) fes]])\<rparr>"
              using reduce.intros(5) local_defs(1,2) Func_native ves'_length
              unfolding cl_type_def
              by fastforce
            ultimately
            show ?thesis
              using Invoke progress_L0 is_const_list[of _ "(rev ves'')"] Cons
              unfolding split_n_conv_app[OF true_defs(1)]
              by fastforce
          next
            case (Func_host x21 x22)
            thus ?thesis
            proof (cases "host_apply_impl s (t1s _> t2s) x22 (rev ves')")
              case None
              hence "s = s'"
                    "f = f'"
                    "res = [Trap] @ es'"
                    "rvs = ves''"
                using Cons 1(3) Invoke local_defs outer_True true_defs Func_host
                unfolding cl_type_def
                by auto
              thus ?thesis
                using is_const_list[of _ "(rev ves'')"]
                      reduce.intros(7)[OF _ _ ves'_length local_defs(2)]
                      split_n_conv_app[OF true_defs] Cons
                      progress_L0 Invoke Func_host local_defs(1)
                unfolding cl_type_def
                by fastforce
            next
              case (Some a)
              show ?thesis
              proof (cases a)
              case (Pair rs rves)
                thus ?thesis
                  using Cons 1(3) Invoke local_defs outer_True true_defs Func_host Some
                  unfolding cl_type_def
                proof (cases "list_all2 types_agree t2s rves")
                  case True
                  hence "rs = s'"
                        "f = f'"
                        "rvs = rev rves @ ves''"
                        "res = es'"
                    using 1(3) Cons Invoke local_defs outer_True true_defs Func_host Pair Some      
                    unfolding cl_type_def
                    by simp_all
                  thus ?thesis
                    using progress_L0 Cons reduce.intros(6)[OF _ _ ves'_length local_defs(2)] Pair
                          Invoke Func_host local_defs(1) True is_const_list[of _ "(rev ves'')"]
                          split_n_conv_app[OF true_defs] host_apply_impl_correct[OF Some]
                    unfolding cl_type_def
                    by fastforce
                qed auto
              qed
            qed
          qed
        next
          case False
          thus ?thesis
            using 1(3) Cons Invoke local_defs
            unfolding cl_type_def
            by (cases "(funcs s!cl)") auto
        qed
      next
        case (Label ln lles les)
        thus ?thesis
        proof (cases "es_is_trap les")
          case True
          thus ?thesis
            using 1(3) Cons is_const_list_vs_to_es_list
                  Label progress_L0[OF reduce.intros(1)[OF reduce_simple.intros(19)]]
              by fastforce
        next
          case False
          note outer_outer_false = False
          show ?thesis
          proof (cases "(const_list les)")
            case True
            thus ?thesis
              using 1(3) Cons split_vals_e_const_list outer_outer_false Label reduce.intros(1)[OF reduce_simple.intros(18)]
                    progress_L0[OF _, where ?es_c="es'"] e_type_const_conv_vs[of les]
              by fastforce
          next
            case False
            then obtain levs lee lees where les_is:"split_vals_e les = (levs, lee#lees)"
              using split_vals_e_not_const_list[OF False]
              by blast
            obtain s'' f'' es'' where run_step_is:"run_step d (s, f, (rev levs, lee#lees)) = (s'', f'', es'')"
              by (metis surj_pair)
            show ?thesis
            proof (cases es'')
              case (RSCrash rsc)
              thus ?thesis
                using outer_outer_false False Cons Label 1(3) les_is
                apply (simp only: run_step.simps[of d s f ves])
                apply (simp add: run_step_is del: run_step.simps)
                done
            next
              case (RSBreak bn bvs)
              thus ?thesis
              proof (cases bn)
                case 0
                have run_step_is_break0:"run_step d (s, f, (rev levs, lee#lees)) = (s'', f'', RSBreak 0 bvs)"
                  using run_step_is RSBreak 0
                  by simp
                hence es'_def:"take ln bvs @ ves = rvs \<and> lles @ es' = res \<and> s' = s'' \<and> f' = f'' \<and> ln \<le> length bvs"
                  using les_is Cons outer_outer_false False run_step_is Label 1(3) RSBreak
                  apply (cases "ln \<le> length bvs")
                  apply (simp_all del: run_step.simps add: run_step.simps[of d s f ves])
                  done
                then obtain n lfilled es_c where local_eqs:"s=s'" "f=f'" "ln \<le> length bvs" "Lfilled_exact n lfilled ((vs_to_es bvs) @ [$Br n] @ es_c) les"
                  using les_is run_step_break_imp_lfilled[OF run_step_is_break0] RSBreak es'_def
                        split_vals_e_conv_app
                  by auto
                then obtain lfilled' where lfilled_int:"Lfilled n lfilled' ((vs_to_es bvs) @ [$Br n]) les"
                  using lfilled_collapse2[OF Lfilled_exact_imp_Lfilled]
                  by fastforce
                obtain lfilled'' where "Lfilled n lfilled'' ((drop (length bvs - ln) (vs_to_es bvs)) @ [$Br n]) les"
                  using lfilled_collapse1[OF lfilled_int] is_const_list_vs_to_es_list[of "rev bvs"] local_eqs(3)
                  by (metis drop_map length_rev)
                hence "\<lparr>[Label ln lles les]\<rparr> \<leadsto> \<lparr>(drop (length bvs - ln) (vs_to_es bvs))@lles\<rparr>"
                  using reduce_simple.intros(20) local_eqs(3) is_const_list_vs_to_es_list
                  unfolding drop_map
                  by fastforce
                hence 1:"\<lparr>s;f;[Label ln lles les]\<rparr> \<leadsto> \<lparr>s';f';(drop (length bvs - ln) (vs_to_es bvs))@lles\<rparr>"
                  using reduce.intros(1) local_eqs(1,2)
                  by fastforce
                have "\<lparr>s;f;(vs_to_es ves)@es\<rparr> \<leadsto> \<lparr>s';f';(vs_to_es ves)@(drop (length bvs - ln) (vs_to_es bvs))@lles@es'\<rparr>"
                  using Label "1" progress_L0 Cons
                  by fastforce
                thus ?thesis
                  using es'_def
                  unfolding drop_map rev_take[symmetric]
                  by auto
              next
                case (Suc nat)
                thus ?thesis
                  using les_is Cons outer_outer_false False run_step_is Label 1(3) RSBreak
                  by (simp del: run_step.simps add: run_step.simps[of d s f ves])
              qed
            next
              case (RSReturn x3)
              thus ?thesis
                using les_is Cons outer_outer_false False run_step_is Label 1(3)
                by (simp del: run_step.simps add: run_step.simps[of d s f ves])
            next
              case (RSNormal rrvs rres)
              hence n3:"ves = rvs" "Label ln lles (vs_to_es rrvs @ rres) # es' = res" "s' = s''" "f' = f''"
                using les_is Cons outer_outer_false False run_step_is Label 1(3) run_step_is
                by (simp_all del: run_step.simps add: run_step.simps[of d s f ves])
              have n1:"Lfilled 1 (LRec (rev ves) ln lles (LBase [] []) []) les ((vs_to_es ves)@[Label ln lles les])"
                using Lfilled.intros(1)[of _ "[]" "[]" les]
                      Lfilled.intros(2)
                      is_const_list_vs_to_es_list[of "rev ves"]
                unfolding const_list_def
                by fastforce
              have n2:"Lfilled 1 (LRec (rev ves) ln lles (LBase [] []) []) (vs_to_es rrvs @ rres) ((vs_to_es ves)@[Label ln lles (vs_to_es rrvs @ rres)])"
                using Lfilled.intros(1)[of _ "[]" "[]" "(vs_to_es rrvs @ rres)"]
                      Lfilled.intros(2)
                      is_const_list_vs_to_es_list[of "rev ves"]
                unfolding const_list_def
                by fastforce
              hence "($C* levs) @ lee # lees \<noteq> [Trap]"
                using outer_outer_false split_vals_e_conv_app[OF les_is]
                by (simp add: append_eq_Cons_conv)
              hence inner_reduce:"\<lparr>s;f;les\<rparr> \<leadsto> \<lparr>s'';f'';(vs_to_es rrvs @ rres)\<rparr>"
                using 1(1)[OF Cons _ Label(1) _ les_is[symmetric], of lee lees s'' f'' rrvs rres] n3 RSNormal
                using  split_vals_e_conv_app[OF les_is] Label(1) run_step_is
                by (simp del: run_step.simps)
              show ?thesis
                using Label 1(3) outer_outer_false False
                      progress_L0[OF reduce.intros(23)[OF inner_reduce n1 n2], of "[]" es'] Cons n3
                by simp
            qed
          qed
        qed
      next
        case (Frame ln fl fes)
        thus ?thesis
        proof (cases "es_is_trap fes")
          case True
          thus ?thesis
            using 1(3) is_const_list_vs_to_es_list Cons
                  Frame progress_L0[OF reduce.intros(1)[OF reduce_simple.intros(26)]]
            apply (simp_all del: run_step.simps add: run_step.simps[of d s f ves])
            apply blast
            done
        next
          case False
          note outer_outer_false = False
          show ?thesis
          proof (cases "(const_list fes)")
            case True
            note outer_true = True
            thus ?thesis
              using 1(3) Frame split_vals_e_const_list  e_type_const_conv_vs[OF outer_true]
                    Cons outer_outer_false outer_true is_const_list_vs_to_es_list[of "rev ves"]
                    progress_L0[OF reduce.intros(1)[OF reduce_simple.local_const[of ln fl]]]
              by (auto simp del: run_step.simps simp add: run_step.simps[of d s f ves])
          next
            case False
            then obtain fevs fee fees where fes_is:"split_vals_e fes = (fevs, fee#fees)"
              using split_vals_e_not_const_list[OF False]
              by blast
            show ?thesis
            proof (cases d)
              case 0
              thus ?thesis
                using 1(3) Cons fes_is Frame outer_outer_false False is_const_list_vs_to_es_list[of "rev ves"]
                by (auto simp del: run_step.simps simp add: run_step.simps[of _ s f ves])
            next
              case (Suc d')
              obtain s'' fl'' es'' where run_step_is:"run_step d' (s, fl, (rev fevs, fee#fees)) = (s'', fl'', es'')"
                by (metis surj_pair)
              show ?thesis
              proof (cases es'')
                case RSCrash
                thus ?thesis
                  using fes_is outer_outer_false False run_step_is Frame Cons 1(3) Suc
                  by (auto simp del: run_step.simps simp add: run_step.simps[of _ s f ves])
              next
                case (RSBreak x21 x22)
                thus ?thesis
                  using fes_is Cons outer_outer_false False run_step_is Frame 1(3) Suc
                  by (auto simp del: run_step.simps simp add: run_step.simps[of _ s f ves])
              next
                case (RSReturn x3)
                hence es'_def:"es' = res \<and> rvs = take ln x3 @ ves \<and> s' = s'' \<and> f = f' \<and> ln \<le> length x3"
                  using Cons fes_is outer_outer_false False run_step_is Frame 1(3) Suc
                  apply (cases "ln \<le> length x3")
                  apply (auto simp del: run_step.simps simp add: run_step.simps[of _ s f ves])
                  done
               then obtain n lfilled es_c where local_eqs:"s=s'" "f=f'" "ln \<le> length x3" "Lfilled_exact n lfilled ((vs_to_es x3) @ [$Return] @ es_c) (fes)"
                 using run_step_is split_vals_e_conv_app[OF fes_is]
                       run_step_return_imp_lfilled[of d' s fl "rev fevs" "fee#fees"] RSReturn
                 by (fastforce simp del: run_step.simps)
                then obtain lfilled' where lfilled_int:"Lfilled n lfilled' ((vs_to_es x3) @ [$Return]) fes"
                  using lfilled_collapse2[OF Lfilled_exact_imp_Lfilled]
                  by fastforce
                obtain lfilled'' where "Lfilled n lfilled'' ((drop (length x3 - ln) (vs_to_es x3)) @ [$Return]) fes"
                  using lfilled_collapse1[OF lfilled_int] is_const_list_vs_to_es_list[of "rev x3"] local_eqs(3)
                  by (metis drop_map length_rev)
                hence "\<lparr>[Frame ln fl fes]\<rparr> \<leadsto> \<lparr>(drop (length x3 - ln) (vs_to_es x3))\<rparr>"
                  using reduce_simple.intros(27) local_eqs(3) is_const_list_vs_to_es_list
                  unfolding drop_map
                  by fastforce
                hence 1:"\<lparr>s;f;[Frame ln fl fes]\<rparr> \<leadsto> \<lparr>s';f';(drop (length x3 - ln) (vs_to_es x3))\<rparr>"
                  using reduce.intros(1) local_eqs(1,2)
                  by fastforce
                have "\<lparr>s;f;(vs_to_es ves)@es\<rparr> \<leadsto> \<lparr>s';f';(vs_to_es ves)@(drop (length x3 - ln) (vs_to_es x3))@es'\<rparr>"
                  using Frame "1" progress_L0 Cons
                  by fastforce
                thus ?thesis
                  using es'_def
                  unfolding drop_map rev_take[symmetric]
                  by auto
              next
                case (RSNormal ffves ffes)
                hence inner_reduce:"\<lparr>s;fl;fes\<rparr> \<leadsto> \<lparr>s'';fl'';(vs_to_es ffves)@ffes\<rparr>"
                  using 1(2)[OF Cons _ Frame outer_outer_false fes_is[symmetric] _ Suc] Frame outer_outer_false False run_step_is Suc
                        split_vals_e_conv_app[OF fes_is]
                  by auto
                thus ?thesis
                  using Frame 1(3) Frame outer_outer_false False run_step_is Suc Cons
                        progress_L0[OF reduce.intros(24)[OF inner_reduce], of f "rev ves" ln es'] RSNormal
                        is_const_list_vs_to_es_list[of "rev ves"] fes_is
                  by (auto simp del: run_step.simps simp add: run_step.simps[of _ s f ves])
            qed
          qed
        qed
      qed
    qed
  qed
qed

theorem run_vs_es_sound:
  assumes "run_vs_es c d (s,f,ves,es) = (s', RValue rvs)"
  shows "\<exists>f'. reduce_trans (s,f,(vs_to_es ves)@es) (s',f',$C* rvs)"
  using assms
proof (induction c d "(s,f,ves,es)" arbitrary: s f ves es rule: run_vs_es.induct)
  case (1 n d s f ves es)
  note outer_1 = 1
  consider (1) "es_is_trap es" | (2) "const_list es" | (3) "\<not>es_is_trap es" "\<not>const_list es"
    by blast
  thus ?case
  proof cases
    case 1
    thus ?thesis
      using outer_1
      by simp
  next
    case 2
    show ?thesis
    proof (cases es)
      case Nil
      thus ?thesis
        using 1(2)
        by (auto simp add: reduce_trans_def)
    next
      case (Cons a list)
      obtain c where "a = $C c"
        using Cons 2 e_type_const_conv_vs
        by blast
      thus ?thesis
        using 1(2) Cons
        by simp
    qed
  next
    case 3
    then obtain s'' f' rrvs rres where s''_is:
      "(run_step d (s,f,ves,es)) = (s'',f',RSNormal rrvs rres)"
      "run_vs_es n d (s'',f',rrvs, rres) = (s', RValue rvs)"
      using outer_1(2)
      by (simp add: is_const_list del: run_step.simps split: if_splits res_step.splits prod.splits)
    show ?thesis
      using outer_1(1)[OF 3(1) _ s''_is(1)[symmetric]] s''_is(2)
            reduce_trans_app[OF run_step_sound[OF s''_is(1)]]
      apply simp
      apply (metis "3"(2) is_const_list list.simps(8))
      done
  qed
next
  case (2 d s f es)
  thus ?case
    by simp
qed

theorem run_v_sound:
  assumes "run_v c d (s,f,es) = (s', RValue rvs)"
  shows "\<exists>f'. reduce_trans (s,f,es) (s',f',$C* rvs)"
  using assms run_vs_es_sound split_vals_e_conv_app
  by (fastforce split: prod.splits)


end