theory Misc_Generic_Lemmas imports Main Word_Lib.Reversed_Bit_Lists begin

(* These lemmas are fairly generic and could be contributed back to their libs? *)

lemma map_takefill:"(map f (takefill k n bs)) = (takefill (f k) n (map f bs))"
  apply (induction n arbitrary: bs)
  apply (simp_all split: list.splits)
  done

lemma length_filter_fold:"length (filter P l) + n =
                            fold (\<lambda>n acc. if P n then acc + 1 else acc) l n"
proof (induction l arbitrary: n)
  case Nil
  thus ?case
    by simp
next
  case (Cons a l)
  thus ?case
    apply simp
    apply (metis add_Suc_right)
    done
qed


text \<open>Just an alternative characterization of find, 
  to increase trust in that it actually finds first occurrence.
\<close>

definition "is_first_elem_with_prop P xs x \<equiv> 
  \<exists>xs\<^sub>1 xs\<^sub>2. xs = xs\<^sub>1@x#xs\<^sub>2 \<and> P x \<and> (\<forall>x'\<in>set xs\<^sub>1. \<not>P x')"

lemma is_first_elem_with_prop_propI: "is_first_elem_with_prop P xs x \<Longrightarrow> P x"  
  unfolding is_first_elem_with_prop_def
  by auto
  
lemma find_finds_first: "List.find P xs = Some x 
  \<longleftrightarrow> is_first_elem_with_prop P xs x"
  unfolding is_first_elem_with_prop_def
  apply (rule iffI)
  subgoal
    apply (clarsimp simp: List.find_Some_iff)
    subgoal for i
      by (auto 0 3
        simp: in_set_conv_nth Cons_nth_drop_Suc
        intro: exI[where x="drop (Suc i) xs"] exI[where x="take i xs"])
    done    
  subgoal
    apply (clarsimp simp: List.find_Some_iff)
    by (metis add_Suc_right length_Cons length_greater_0_conv less_add_same_cancel1 list.simps(3) nth_append nth_append_length nth_mem)
  done  



end
