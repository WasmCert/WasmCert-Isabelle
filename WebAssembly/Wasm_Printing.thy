theory Wasm_Printing
  imports
    "HOL-Library.Code_Target_Numeral"
    (* The following does not appear to change the extracted code *)
    (* but might be useful in the future. *)
    "HOL-Library.Code_Bit_Shifts_for_Arithmetic"
    OCaml_Printing
    Wasm_Type_Printing
    Wasm_Instantiation_Printing
    Wasm_Checker_Printing
    Wasm_Interpreter_Printing
    Wasm_Memory_Printing
begin

(* avoid name-mangling *)
code_identifier constant Neg \<rightharpoonup> (OCaml) "WasmRef_Isa.Neg"

export_code open ocaml_char_to_isabelle_byte
                 isabelle_byte_to_ocaml_char
                 nat_of_byte byte_of_nat
                 m_imports
                 module_type_checker
                 interp_instantiate_init
                 typing
                 run run_invoke
  in OCaml module_name WasmRef_Isa file_prefix WasmRef_Isa

end
