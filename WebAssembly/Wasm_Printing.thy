theory Wasm_Printing imports OCaml_Printing Wasm_Instantiation_Printing Wasm_Checker_Printing Wasm_Interpreter_Printing Wasm_Type_Printing "HOL-Library.Code_Target_Nat" begin

lemma[code]: "mem_rep_append (Abs_mem_rep m) n b = Abs_mem_rep (app_rev_tr (rev m) (replicate n b))"
  using mem_rep_append.abs_eq
  by (simp add: append_app_rev_tr)

(* avoid name-mangling *)
code_identifier constant Neg \<rightharpoonup> (OCaml) "WasmRef_Isa.Neg"

(* TODO: work out where this is being used - Code_Target_Nat and Code_Numeral are not playing nice *)
lemmas[code del] = drop_bit_int_code

lemma drop_bit_int_code_ [code]: fixes i :: int shows
  "drop_bit n 0 = (0 :: int)"
  "drop_bit n (Int.Pos num.One) = (case n of 0 \<Rightarrow> (Int.Pos num.One) | Suc n \<Rightarrow> 0)"
  "drop_bit n (Int.Pos (num.Bit0 m)) = (case n of 0 \<Rightarrow> (Int.Pos (num.Bit0 m)) | Suc n \<Rightarrow> drop_bit n (Int.Pos m))"
  "drop_bit n (Int.Pos (num.Bit1 m)) = (case n of 0 \<Rightarrow> (Int.Pos (num.Bit1 m)) | Suc n \<Rightarrow> drop_bit n (Int.Pos m))"
  "drop_bit n (Int.Neg num.One) = (case n of 0 \<Rightarrow> (Int.Neg num.One) | Suc n \<Rightarrow> - 1)"
  "drop_bit n (Int.Neg (num.Bit0 m)) = (case n of 0 \<Rightarrow> (Int.Neg (num.Bit0 m)) | Suc n \<Rightarrow> drop_bit n (Int.Neg m))"
  "drop_bit n (Int.Neg (num.Bit1 m)) = (case n of 0 \<Rightarrow> (Int.Neg (num.Bit1 m)) | Suc n \<Rightarrow> drop_bit n (Int.Neg (Num.inc m)))"
  by (simp_all add: shiftr_eq_drop_bit drop_bit_Suc add_One split: nat.splits)

export_code open nat_of_byte byte_of_nat
                 ocaml_int32_to_isabelle_int32
                 isabelle_int32_to_ocaml_int32
                 ocaml_int64_to_isabelle_int64
                 isabelle_int64_to_ocaml_int64
                 ocaml_char_to_isabelle_byte
                 isabelle_byte_to_ocaml_char
                 m_imports module_type_checker interp_instantiate typing run run_invoke
  in OCaml module_name WasmRef_Isa file_prefix WasmRef_Isa

end
