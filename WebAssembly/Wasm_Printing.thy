theory Wasm_Printing imports Wasm_Instantiation_Printing Wasm_Checker_Printing Wasm_Interpreter_Printing Wasm_Type_Printing "HOL-Library.Code_Target_Nat" begin

(* OCaml-specific hacks follow... *)

lemma [code]: "pred_option P None = True"
  using Option.option.pred_inject(1)
  by auto

lemmas[code] = Option.option.pred_inject(2)

axiomatization
  failwith_nth :: 'a where
  nth_emp[code]: "nth [] n = failwith_nth"

code_printing
  constant failwith_nth \<rightharpoonup> (OCaml) "failwith \"nth\""

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

lemma[code]: "mem_rep_append (Abs_mem_rep m) n b = Abs_mem_rep (app_rev_tr (rev m) (replicate n b))"
  using mem_rep_append.abs_eq
  by (simp add: append_app_rev_tr)

export_code open m_imports module_type_checker interp_instantiate typing run in OCaml module_name WasmRef_Isa file "code/WasmRef_Isa.ml"

end