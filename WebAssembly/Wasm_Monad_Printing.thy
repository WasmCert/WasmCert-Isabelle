theory Wasm_Monad_Printing imports OCaml_Printing Wasm_Instantiation_Monad Wasm_Checker_Printing Wasm_Interpreter_Monad_Printing Wasm_Type_Printing "../libs/Code_Target_Byte_Array" "HOL-Library.Code_Target_Nat" "Native_Word.Code_Target_Bits_Int" begin

(* avoid name-mangling *)
code_identifier constant Neg \<rightharpoonup> (OCaml) "WasmRef_Isa.Neg"
code_identifier constant  Array.nth \<rightharpoonup> (OCaml) "WasmRef_Isa.array_nth"

(* restore naive blit implementation *)
declare [[code drop: blit]]
lemmas[code] = blit.simps

fun run_fuzz :: "fuel \<Rightarrow> depth \<Rightarrow> s_m \<Rightarrow> m \<Rightarrow> v_ext list \<Rightarrow> (s_m \<times> res) Heap" where
  "run_fuzz n d s m v_imps = do {
   i_res \<leftarrow> interp_instantiate_init_m s m v_imps;
   case i_res of
     (s', RI_res_m inst v_exps init_es) \<Rightarrow>
       do {
         res \<leftarrow> run_instantiate_m n d (s', inst, init_es);
         (case res of
            (s'', RValue []) \<Rightarrow>
              (case (List.find (\<lambda>exp. case (E_desc exp) of Ext_func i \<Rightarrow> True | _ \<Rightarrow> False) v_exps) of
                Some exp \<Rightarrow> (case (E_desc exp) of Ext_func i \<Rightarrow> do {
                               cl \<leftarrow> Array.nth (s_m.funcs s'') i;
                               case (cl_m_type cl) of
                                 (t1 _> t2) \<Rightarrow> run_invoke_v_m n d (s'', (map bitzero t1), i) })
              | None \<Rightarrow> return (s'', RCrash (Error_invariant (STR ''no import to invoke''))))
          | (s'', RValue (x#xs)) \<Rightarrow> return (s'', RCrash (Error_invalid (STR ''start function'')))
          | x \<Rightarrow> return x)}
  | (s', RI_crash_m res) \<Rightarrow> return (s', RCrash res)
  | (s', RI_trap_m msg) \<Rightarrow> return (s', RTrap msg) }"

export_code open nat_of_byte byte_of_nat
                 ocaml_int32_to_isabelle_int32
                 isabelle_int32_to_ocaml_int32
                 ocaml_int64_to_isabelle_int64
                 isabelle_int64_to_ocaml_int64
                 ocaml_char_to_isabelle_byte
                 isabelle_byte_to_ocaml_char
                 zero_byte negone_byte m_imports
                 make_empty_store_m module_type_checker interp_instantiate_init_m typing run_m run_invoke_m
                 run_fuzz
  in OCaml_imp module_name WasmRef_Isa file_prefix WasmRef_Isa_m

end
