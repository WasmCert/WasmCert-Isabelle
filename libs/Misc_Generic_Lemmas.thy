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

end
