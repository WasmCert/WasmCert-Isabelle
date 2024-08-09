theory Wasm_Monad_Printing imports OCaml_Printing Wasm_Instantiation_Monad Wasm_Checker_Printing Wasm_Interpreter_Monad_Printing Wasm_Type_Printing "../libs/Code_Target_Byte_Array" "HOL-Library.Code_Target_Nat" "Native_Word.Code_Target_Integer_Bit" begin

(* avoid name-mangling *)
code_identifier constant Neg \<rightharpoonup> (OCaml) "WasmRef_Isa.Neg"
code_identifier constant  Array.nth \<rightharpoonup> (OCaml) "WasmRef_Isa.array_nth"

(* restore naive blit implementation *)
declare [[code drop: blit]]
lemmas[code] = blit.simps

(* more efficient bitmask generation *)
declare [[code drop: "mask::nat\<Rightarrow>uint32"]]
declare [[code drop: "mask::nat\<Rightarrow>uint64"]]

lemma[code]: "((mask n) :: uint32) = shiftr (-1) (32 - n)"
proof -
  show ?thesis
    unfolding shiftr_def
    apply transfer'
    apply transfer'
    apply (simp add: drop_bit_take_bit)
    by (metis add_diff_cancel_left' drop_bit_mask_eq min_minus min_pm1 take_bit_of_mask)
qed

lemma[code]: "((mask n) :: uint64) = shiftr (-1) (64 - n)"
proof -
  show ?thesis
    unfolding shiftr_def
    apply transfer'
    apply transfer'
    apply (simp add: drop_bit_take_bit)
    by (metis add_diff_cancel_left' drop_bit_mask_eq min_minus min_pm1 take_bit_of_mask)
qed
   

export_code open nat_of_byte byte_of_nat
                 ocaml_int32_to_isabelle_int32
                 isabelle_int32_to_ocaml_int32
                 ocaml_int64_to_isabelle_int64
                 isabelle_int64_to_ocaml_int64
                 ocaml_char_to_isabelle_byte
                 isabelle_byte_to_ocaml_char
                 zero_byte negone_byte m_imports
                 make_empty_store_m module_type_checker interp_instantiate_init_m typing run_m run_invoke_m
                 run_fuzz run_fuzz_entry
  in OCaml_imp module_name WasmRef_Isa file_prefix WasmRef_Isa_m

end
