theory Sshiftr
  imports "Word_Lib.Reversed_Bit_Lists"
begin

text\<open>
Added to the afp: https://foss.heptapod.net/isa-afp/afp-devel/-/commit/6b53a6d8121ef1088de9668d98061fb500e915e5
So this theory can be removed once it's in a release.
\<close>

text\<open>Some auxiliaries for shifting by the entire word length or more\<close>


text\<open>
Like @{thm shiftr1_bl_of}, but the precondition is stronger because we need to pick the msb out of
the list.
\<close>
lemma sshiftr1_bl_of:
  "length bl = LENGTH('a) \<Longrightarrow>
    sshiftr1 (of_bl bl::'a::len word) = of_bl (hd bl # butlast bl)"
  apply (rule word_bl.Rep_eqD)
  apply (subst bl_sshiftr1[of "of_bl bl :: 'a word"])
  by (simp add: word_bl.Abs_inverse)

text\<open>
Like @{thm sshiftr1_bl_of}, with a weaker precondition.
We still get a direct equation for @{term \<open>sshiftr1 (of_bl bl)\<close>}, it's just uglier.
\<close>
lemma sshiftr1_bl_of':
  "LENGTH('a) \<le> length bl \<Longrightarrow>
    sshiftr1 (of_bl bl::'a::len word) =
    of_bl (hd (drop (length bl - LENGTH('a)) bl) # butlast (drop (length bl - LENGTH('a)) bl))"
  apply (subst of_bl_drop'[symmetric, of "length bl - LENGTH('a)"])
  using sshiftr1_bl_of[of "drop (length bl - LENGTH('a)) bl"]
  by auto

text\<open>
Like @{thm shiftr_bl_of}.
\<close>
lemma sshiftr_bl_of:
  assumes "length bl = LENGTH('a)"
  shows "(of_bl bl::'a::len word) >>> n = of_bl (replicate n (hd bl) @ take (length bl - n) bl)"
proof -
  {
    fix n
    assume "n \<le> LENGTH('a)"
    hence "(of_bl bl::'a::len word) >>> n = of_bl (replicate n (hd bl) @ take (length bl - n) bl)"
    proof (induction n)
      case (Suc n)
      hence "n < length bl" by (simp add: assms)
      hence ne: "\<not>take (length bl - n) bl = []" by auto
      have left: "hd (replicate n (hd bl) @ take (length bl - n) bl) = (hd bl)"
        by (cases "0 < n") auto
      have right: "butlast (take (length bl - n) bl) = take (length bl - Suc n) bl"
        by (subst butlast_take) auto
      have "(of_bl bl::'a::len word) >>> Suc n = sshiftr1 ((of_bl bl::'a::len word) >>> n)"
        unfolding sshiftr_eq_funpow_sshiftr1 by simp
      also have "\<dots> = of_bl (replicate (Suc n) (hd bl) @ take (length bl - Suc n) bl)"
        apply (subst Suc.IH[OF Suc_leD[OF Suc.prems]])
        apply (subst sshiftr1_bl_of)
        subgoal using assms Suc.prems by simp
        apply (rule arg_cong[where f=of_bl])
        apply (subst butlast_append)
        unfolding left right using ne by simp
      finally show ?case .
    qed (transfer, simp)
  }
  note pos = this
  {
    assume n: "LENGTH('a) \<le> n"
    have "(of_bl bl::'a::len word) >>> n = (of_bl bl::'a::len word) >>> LENGTH('a)"
      by (rule sshiftr_clamp[OF n])
    also have "\<dots> = of_bl (replicate LENGTH('a) (hd bl) @ take (length bl - LENGTH('a)) bl)"
      apply (rule pos) ..
    also have "\<dots> = of_bl (replicate n (hd bl) @ take (length bl - n) bl)"
    proof -
      have "(of_bl (replicate LENGTH('a) (hd bl)) :: 'a word) = of_bl (replicate n (hd bl))"
        apply (subst of_bl_drop'[symmetric, of "n - LENGTH('a)" "replicate n (hd bl)"])
        unfolding length_replicate by (auto simp: n)
      thus ?thesis by (simp add: assms n)
    qed
    finally have "(of_bl bl::'a::len word) >>> n
      = of_bl (replicate n (hd bl) @ take (length bl - n) bl)" .
  }
  thus ?thesis using pos by fastforce
qed

text\<open>Like @{thm shiftr_bl}\<close>
lemma sshiftr_bl: "x >>> n \<equiv> of_bl (replicate n (msb x) @ take (LENGTH('a) - n) (to_bl x))"
  for x :: "'a::len word"
  unfolding word_msb_alt
  by (smt (z3) length_to_bl_eq sshiftr_bl_of word_bl.Rep_inverse)

end
