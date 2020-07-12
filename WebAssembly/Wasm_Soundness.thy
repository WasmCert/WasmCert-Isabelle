section {* Soundness Theorems *}

theory Wasm_Soundness imports Main Wasm_Properties begin

theorem preservation:
  assumes "\<turnstile> s;f;es : ts"
          "\<lparr>s;f;es\<rparr> \<leadsto> \<lparr>s';f';es'\<rparr>"
  shows "\<turnstile> s';f';es' : ts"
proof -
  have "store_typing s" "s\<bullet>None \<tturnstile> f;es : ts"
    using assms(1) config_typing.simps
    by blast+
  hence "store_typing s'" "s'\<bullet>None \<tturnstile> f';es' : ts"
    using assms(2)
          store_preserved
          types_preserved_e
    by blast+
  thus ?thesis
    using config_typing.intros
    by blast
qed

theorem progress:
  assumes "\<turnstile> s;f;es : ts"
  shows "const_list es \<or> es = [Trap] \<or> (\<exists>a s' f' es'. \<lparr>s;f;es\<rparr> \<leadsto> \<lparr>s';f';es'\<rparr>)"
proof -
  have "store_typing s" "s\<bullet>None \<tturnstile> f;es : ts"
    using assms config_typing.simps
    by blast+
  thus ?thesis
    using progress_e3
    by blast
qed

end