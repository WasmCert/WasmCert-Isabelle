theory Wasm_Monad_Printing imports OCaml_Printing Wasm_Instantiation_Monad Wasm_Checker_Printing Wasm_Interpreter_Monad_Printing Wasm_Type_Printing "HOL-Library.Code_Target_Nat" begin

(* avoid name-mangling *)
code_identifier constant Neg \<rightharpoonup> (OCaml) "WasmRef_Isa.Neg"

export_code open nat_of_byte byte_of_nat
                 ocaml_int32_to_isabelle_int32
                 isabelle_int32_to_ocaml_int32
                 ocaml_int64_to_isabelle_int64
                 isabelle_int64_to_ocaml_int64
                 ocaml_char_to_isabelle_byte
                 isabelle_byte_to_ocaml_char
                 m_imports module_type_checker interp_instantiate_m typing run_m run_invoke_m
  in OCaml_imp module_name WasmRef_Isa_m file_prefix WasmRef_Isa_m

end