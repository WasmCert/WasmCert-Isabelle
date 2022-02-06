theory Misc_Generic_Lemmas imports Main Word_Lib.Reversed_Bit_Lists begin

(* These lemmas are fairly generic and could be contributed back to their libs? *)

lemma map_takefill:"(map f (takefill k n bs)) = (takefill (f k) n (map f bs))"
  apply (induction n arbitrary: bs)
  apply (simp_all split: list.splits)
  done

end
