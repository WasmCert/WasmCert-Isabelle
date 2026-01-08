theory OCaml_Printing imports Main begin

(* OCaml-specific hacks follow... *)

lemma [code]: "pred_option P None = True"
  using Option.option.pred_inject(1)
  by auto

lemmas[code] = Option.option.pred_inject(2)

(* The following code was used to provide a *)
(* more helpful error message in case of an out of bounds *)
(* access of list. Since Isabelle 2025-1 the code generation *)
(* utilities were modifies so that newly added code lemmas *)
(* remove the code generation lemmas from the previous theories *)
(* and this makes the code generation for nth miss some pattern cases. *)
(*
definition "failwith_nth n \<equiv> []!n"

declare [[code abort: failwith_nth]]

lemma nth_emp[code]: "nth [] n = failwith_nth n"
  unfolding failwith_nth_def ..
*)
  
(* The model uses a naive list-based memory *)
(* The list can get very large, so relevant functions must be tail-recursive *)

primrec replicate_tr :: "nat \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "replicate_tr 0 x acc = acc"
| "replicate_tr (Suc n) x acc = replicate_tr n x (x # acc)"

lemma[code]: "replicate n x = replicate_tr n x []"
proof -
  have "\<And>acc. (replicate n x)@acc = replicate_tr n x acc"
    apply (induction n)
    apply simp_all
    apply (metis replicate_app_Cons_same)
    done
  thus ?thesis
    by (metis self_append_conv)
qed

(* n.b. `rev` is tail-recursive when extracted to OCaml *)

fun take_tr:: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "take_tr n [] acc_r = rev acc_r"
| "take_tr n (x # xs) acc_r =
    (case n of
      0 \<Rightarrow> (rev acc_r)
    | Suc n' \<Rightarrow> take_tr n' xs (x # acc_r))"

lemma[code]: "take n xs = take_tr n xs []"
proof -
  { fix acc_r :: "'a list"

    have "take_tr n xs acc_r = (rev acc_r)@(take n xs)"
    proof (induction n xs acc_r arbitrary: acc_r rule: take_tr.induct)
      case (2 n x xs acc_r)
      thus ?case
        apply (cases n)
        apply auto
        done
    qed simp_all
  }
  thus ?thesis
    by simp
qed

fun app_rev_tr:: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "app_rev_tr [] ys = ys"
| "app_rev_tr (x#xs) ys = app_rev_tr xs (x#ys)"

lemma append_app_rev_tr:
  "app_rev_tr xs ys = append (rev xs) ys"
  by (induction xs ys arbitrary: ys rule: app_rev_tr.induct) simp_all

end