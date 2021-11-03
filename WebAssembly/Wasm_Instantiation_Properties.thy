theory Wasm_Instantiation_Properties imports Wasm_Instantiation begin

lemma list_all_ex_list_all2:
  assumes "\<And>i. i < length xs \<Longrightarrow> \<exists>y. P (xs!i) y"
  shows "\<exists>ys. list_all2 P xs ys"
  using assms
proof (induction xs)
  case (Cons x xs)
  have "\<exists>y. P x y"
       "\<And>i. i < length xs \<Longrightarrow> (\<exists>a. P (xs ! i) a)"
    using Cons(2)
    by fastforce+
  thus ?case
    using Cons(1)
    by blast
qed auto

theorem instantiation_sound:
  assumes "store_typing s"
          "(instantiate s m v_imps ((s', inst, v_exps), start))"
  shows "store_typing s'"
        "\<exists>\<C>. inst_typing s' inst \<C>"
        "\<exists>tes. list_all2 (\<lambda>v_exp te. external_typing s' (E_desc v_exp) te) v_exps tes"
        "pred_option (\<lambda>i. i < length (s.funcs s')) start"
proof -

  show "store_typing s'"
  proof -
    have 1:"list_all (\<lambda>cl. \<exists>tf. cl_typing s' cl tf) (funcs s')"
      sorry
    have 2:"list_all (tab_agree s') (tabs s')"
      sorry
    have 3:"list_all mem_agree (mems s')"
      sorry
    show ?thesis
      using 1 2 3 store_typing.intros
      by blast
  qed

  show "\<exists>\<C>. inst_typing s' inst \<C>"
  proof -
    have 1:"\<exists>tfs. list_all2 (funci_agree (funcs s')) (inst.funcs inst) tfs"
      sorry
    have 2:"\<exists>tgs. list_all2 (globi_agree (globs s')) (inst.globs inst) tgs"
      sorry
    have 3:"\<exists>tabs_t. list_all2 (tabi_agree (tabs s')) (inst.tabs inst) tabs_t"
      sorry
    have 4:"\<exists>mems_t. list_all2 (memi_agree (mems s')) (inst.mems inst) mems_t"
      sorry
    show ?thesis
      using 1 2 3 4 inst_typing.intros
      by (metis (full_types) inst.surjective unit.exhaust)
  qed

  show "\<exists>tes. list_all2 (\<lambda>v_exp te. external_typing s' (E_desc v_exp) te) v_exps tes"
  proof -
  have "\<And>i. i < length v_exps \<Longrightarrow> (\<exists>te. external_typing s' (E_desc (v_exps!i)) te)"
    sorry
  thus ?thesis
    by (simp add: list_all_ex_list_all2)
  qed

  show "pred_option (\<lambda>i. i < length (s.funcs s')) start"
    sorry
qed

end