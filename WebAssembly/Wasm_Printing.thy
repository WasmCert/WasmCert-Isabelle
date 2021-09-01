theory Wasm_Printing imports OCaml_Printing Wasm_Instantiation_Printing Wasm_Checker_Printing Wasm_Interpreter_Printing Wasm_Type_Printing "HOL-Library.Code_Target_Nat" begin

lemma[code]: "mem_rep_append (Abs_mem_rep m) n b = Abs_mem_rep (app_rev_tr (rev m) (replicate n b))"
  using mem_rep_append.abs_eq
  by (simp add: append_app_rev_tr)

(* avoid name-mangling *)
code_identifier constant Neg \<rightharpoonup> (OCaml) "WasmRef_Isa.Neg"

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
