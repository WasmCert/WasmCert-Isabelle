theory Wasm_Monad_Printing imports OCaml_Printing Wasm_Instantiation_Monad Wasm_Checker_Printing Wasm_Interpreter_Monad_Printing Wasm_Type_Printing "../libs/Code_Target_Byte_Array" "HOL-Library.Code_Target_Nat" "Native_Word.Code_Target_Bits_Int" begin

(* avoid name-mangling *)
code_identifier constant Neg \<rightharpoonup> (OCaml) "WasmRef_Isa.Neg"
code_identifier constant  Array.nth \<rightharpoonup> (OCaml) "WasmRef_Isa.array_nth"

(* TODO: why is this not a thing already? *)
declare [[code drop: map_Heap]]
lemma[code]:
  "map_Heap f M = do { a \<leftarrow> M; return (f a) }"
  apply (cases M)
  apply (simp add: bind_def map_conv_bind_option fun_eq_iff execute_return split: option.splits)
  done

(* restore naive blit implementation *)
declare [[code drop: blit]]
lemmas[code] = blit.simps

export_code open nat_of_byte byte_of_nat
                 ocaml_int32_to_isabelle_int32
                 isabelle_int32_to_ocaml_int32
                 ocaml_int64_to_isabelle_int64
                 isabelle_int64_to_ocaml_int64
                 ocaml_char_to_isabelle_byte
                 isabelle_byte_to_ocaml_char
                 zero_byte negone_byte m_imports
                 make_empty_store_m module_type_checker interp_instantiate_m typing run_m run_invoke_m
  in OCaml_imp module_name WasmRef_Isa file_prefix WasmRef_Isa_m

end
