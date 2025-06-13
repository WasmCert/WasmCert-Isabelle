theory Wasm_Printing
  imports
    "HOL-Library.Code_Target_Nat" 
    "Native_Word.Code_Int_Integer_Conversion"
    "Native_Word.Code_Target_Int_Bit"
    OCaml_Printing
    Wasm_Type_Printing
    Wasm_Instantiation_Printing
    Wasm_Checker_Printing
    Wasm_Interpreter_Printing
  begin

(*
lemma[code]: "mem_rep_append (Abs_mem_rep m) n b = Abs_mem_rep (app_rev_tr (rev m) (replicate n b))"
  using mem_rep_append.abs_eq
  by (simp add: append_app_rev_tr) *)

code_printing
  type_constructor mem_rep \<rightharpoonup> (OCaml) "uint8 Parray.t"
  | constant mem_rep_length \<rightharpoonup> (OCaml) "nat'_of'_integer (LibAux.z'_of'_uint32 (Int32.of'_int (Parray.length _)))"
  | constant mem_rep_mk_with_default_value \<rightharpoonup> (OCaml) "Parray.make (65536*(Int32.to'_int (LibAux.uint32'_of'_z (integer'_of'_nat _)))) _"
  | constant mem_rep_byte_at \<rightharpoonup> (OCaml) "MemRepWrapper.memRepByteAt _ (Int32.to'_int (LibAux.uint32'_of'_z (integer'_of'_nat _)))"
  | constant mem_rep_read_bytes \<rightharpoonup> (OCaml) "MemRepWrapper.memRepReadBytes _ (Int32.to'_int (LibAux.uint32'_of'_z (integer'_of'_nat _))) (Int32.to'_int (LibAux.uint32'_of'_z (integer'_of'_nat _)))"
  | constant mem_rep_write_bytes \<rightharpoonup> (OCaml) "MemRepWrapper.memRepWriteBytes _ (Int32.to'_int (LibAux.uint32'_of'_z (integer'_of'_nat _))) _"
  | constant mem_rep_append \<rightharpoonup> (OCaml) "MemRepWrapper.memRepAppend _ (Int32.to'_int (LibAux.uint32'_of'_z (integer'_of'_nat _))) _"

(*
(nat_of_integer (LibAux.z_of_uint32 ( (Int32.of_int (mem_length m)))))*)

(* avoid name-mangling *)
code_identifier constant Neg \<rightharpoonup> (OCaml) "WasmRef_Isa.Neg"

export_code open 
                 ocaml_int32_to_isabelle_int32
                 isabelle_int32_to_ocaml_int32
                 ocaml_int64_to_isabelle_int64
                 isabelle_int64_to_ocaml_int64
                 ocaml_char_to_isabelle_byte
                 isabelle_byte_to_ocaml_char
                 nat_of_byte byte_of_nat
                 m_imports module_type_checker interp_instantiate_init typing run run_invoke
  in OCaml module_name WasmRef_Isa file_prefix WasmRef_Isa

end
