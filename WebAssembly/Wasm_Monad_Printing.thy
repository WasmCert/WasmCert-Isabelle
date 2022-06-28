theory Wasm_Monad_Printing imports OCaml_Printing Wasm_Instantiation_Monad Wasm_Checker_Printing Wasm_Interpreter_Monad_Printing Wasm_Type_Printing "../libs/Code_Target_Byte_Array" "HOL-Library.Code_Target_Nat" "Native_Word.Code_Target_Bits_Int" begin

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

fun run_fuzz :: "fuel \<Rightarrow> depth \<Rightarrow> s_m \<Rightarrow> m \<Rightarrow> v_ext list \<Rightarrow> (v list) option \<Rightarrow> (s_m \<times> res) Heap" where
  "run_fuzz n d s m v_imps opt_vs = do {
   i_res \<leftarrow> interp_instantiate_init_m s m v_imps;
   case i_res of
     (s', RI_res_m inst v_exps init_es) \<Rightarrow>
     (case (List.find (\<lambda>exp. case (E_desc exp) of Ext_func i \<Rightarrow> True | _ \<Rightarrow> False) v_exps) of
        Some exp \<Rightarrow> (case (E_desc exp) of Ext_func i \<Rightarrow> do {
                       cl \<leftarrow> Array.nth (s_m.funcs s') i;
                       case (cl_m_type cl) of
                         (t1 _> t2) \<Rightarrow>
                           let params = case opt_vs of Some vs \<Rightarrow> (rev vs) | None \<Rightarrow> (map bitzero t1) in
                           run_invoke_v_m n d (s', params, i) })
      | None \<Rightarrow> return (s', RCrash (Error_invariant (STR ''no import to invoke''))))
  | (s', RI_crash_m res) \<Rightarrow> return (s', RCrash res)
  | (s', RI_trap_m msg) \<Rightarrow> return (s', RTrap msg) }"

fun run_fuzz_entry :: "fuel \<Rightarrow> m \<Rightarrow> (v list) option \<Rightarrow> (s_m \<times> res) Heap" where
  "run_fuzz_entry n m vs_opt = do {
     s_m \<leftarrow> make_empty_store_m;
     run_fuzz n 300 s_m m [] vs_opt }"

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
