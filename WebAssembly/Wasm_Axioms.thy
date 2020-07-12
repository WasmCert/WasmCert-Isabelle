section {* Host Properties *}

theory Wasm_Axioms imports Wasm begin

lemma old_mem_size_def:
  shows "mem_size m = length (fst (Rep_mem m)) div Ki64"
  unfolding mem_size_def mem_length_def
  by (simp split: prod.splits)

(* these were originally axioms, but memory now has a concrete representation in the model *)
lemma mem_grow_size:
  assumes "mem_grow m n = Some m'"
  shows "(mem_size m + n) = mem_size m'"
  using assms Abs_mem_inverse
  unfolding mem_grow_def old_mem_size_def mem_append_def bytes_replicate_def
  by (auto simp add: Ki64_def Let_def split: prod.splits if_splits)

lemma mem_grow_max1:
  assumes "mem_grow m n = Some m'"
  shows "mem_max m = mem_max m'"
  using assms Abs_mem_inverse
  unfolding mem_grow_def mem_max_def mem_append_def 
  by (auto simp add: Ki64_def Let_def split: prod.splits if_splits)

lemma mem_grow_max2:
  assumes "mem_grow m n = Some m'"
  shows "pred_option ((\<le>) (mem_size m')) (mem_max m')"
  using assms Abs_mem_inverse
  unfolding mem_grow_def mem_max_def mem_append_def
  by (auto simp add: assms mem_grow_size Let_def split: prod.splits if_splits)

lemma mem_grow_length:
  assumes "mem_grow m n = Some m'"
  shows "(mem_length m + (n * Ki64)) = mem_length m'"
  using assms Abs_mem_inverse
        bytes_replicate_def mem_append.rep_eq mem_length.rep_eq
  unfolding mem_grow_def old_mem_size_def mem_append_def bytes_replicate_def
  by (auto simp add: Let_def split: prod.splits if_splits)

lemma mem_grow_byte_at_m:
  assumes "k < mem_length m"
          "(mem_grow m n) = Some m'"
  shows "byte_at m' k = byte_at m k"
  using assms
  unfolding byte_at.rep_eq mem_length.rep_eq mem_grow_def mem_append.rep_eq mem_append_def
  by (auto simp add: Abs_mem_inverse nth_append Let_def split: prod.splits if_splits)

lemma mem_grow_byte_at_m_n:
  assumes "k \<ge> mem_length m"
          "(mem_grow m n) = Some m'"
          "k < mem_length m'"
  shows "byte_at m' k = (0::byte)"
  using assms
  unfolding byte_at.rep_eq mem_length.rep_eq mem_grow_def mem_append.rep_eq bytes_replicate_def mem_append_def
  by (auto simp add: Abs_mem_inverse nth_append Let_def split: prod.splits if_splits)

lemma load_size:
  "(load m n off l = None) = (mem_length m < (off + n + l))"
  unfolding load_def
  by (cases "n + off + l \<le> mem_length m") auto

lemma load_packed_size:
  "(load_packed sx m n off lp l = None) = (mem_length m < (off + n + lp))"
  using load_size
  unfolding load_packed_def
  by (cases "n + off + l \<le> mem_length m") auto  

lemma store_size1:
  "(store m n off v l = None) = (mem_length m < (off + n + l))"
  unfolding store_def
  by (cases "n + off + l \<le> mem_length m") auto

lemma store_size:
  assumes "(store m n off v l = Some m')"
  shows "mem_size m = mem_size m'"
  using assms Abs_mem_inverse mem_length.rep_eq
  unfolding store_def write_bytes_def bytes_takefill_def
  by (cases "n + off + l \<le> mem_length m") (auto simp add: old_mem_size_def split: prod.splits)

lemma store_max:
  assumes "(store m n off v l = Some m')"
  shows "mem_max m = mem_max m'"
  using assms Abs_mem_inverse
  unfolding store_def mem_max.rep_eq write_bytes_def
  by (auto split: if_splits prod.splits)

lemma store_length:
  assumes "(store m n off v l = Some m')"
  shows "mem_length m = mem_length m'"
  using assms Abs_mem_inverse mem_length.rep_eq
  unfolding store_def write_bytes_def bytes_takefill_def
  by (cases "n + off + l \<le> mem_length m") (auto split: prod.splits)

lemma store_packed_size1:
  "(store_packed m n off v l = None) = (mem_length m < (off + n + l))"
  using store_size1
  unfolding store_packed_def
  by simp

lemma store_packed_size:
  assumes "(store_packed m n off v l = Some m')"
  shows "mem_size m = mem_size m'"
  using assms store_size
  unfolding store_packed_def
  by simp

lemma store_packed_max:
  assumes "(store_packed m n off v l = Some m')"
  shows "mem_max m = mem_max m'"
  using assms store_max
  unfolding store_packed_def
  by simp

axiomatization where
  wasm_deserialise_type:"typeof (wasm_deserialise bs t) = t"

axiomatization where
    host_apply_preserve_store1:"host_apply s (t1s _> t2s) f vs hs = Some (s', vs') \<Longrightarrow> store_extension s s'"
and host_apply_preserve_store2:"host_apply s (t1s _> t2s) f vs hs = Some (s', vs') \<Longrightarrow> store_typing s \<Longrightarrow> store_typing s'"
and host_apply_respect_type:"list_all2 types_agree t1s vs \<Longrightarrow> host_apply s (t1s _> t2s) f vs hs = Some (s', vs') \<Longrightarrow> list_all2 types_agree t2s vs'"

lemma host_apply_preserve_store:
  assumes "host_apply s (t1s _> t2s) f vs hs = Some (s', vs')"
          "store_typing s"
  shows "store_extension s s' \<and> store_typing s'"
  using assms host_apply_preserve_store1 host_apply_preserve_store2
  by blast

end