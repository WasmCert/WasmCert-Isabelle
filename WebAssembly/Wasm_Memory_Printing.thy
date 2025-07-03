theory Wasm_Memory_Printing imports Wasm_Base_Defs Wasm_Type_Printing begin

(* Perhaps a more appropriate place for ocaml_int and related conversions is in Wasm_Type_Printing *)
(* But right now it is only used for Parray memory representation *)
typedecl ocaml_int

consts
  ocaml_i32_to_ocaml_int :: "ocaml_i32 \<Rightarrow> ocaml_int"
  ocaml_int_to_ocaml_i32 :: "ocaml_int \<Rightarrow> ocaml_i32"

code_printing
  type_constructor ocaml_int \<rightharpoonup> (OCaml) "Int.t"
| constant ocaml_i32_to_ocaml_int \<rightharpoonup> (OCaml) "Int32.to'_int"
| constant ocaml_int_to_ocaml_i32 \<rightharpoonup> (OCaml) "Int32.of'_int"

consts
  ocaml_mem_rep_length :: "mem_rep \<Rightarrow> ocaml_int"
  ocaml_mem_rep_mk :: "ocaml_int \<Rightarrow> byte \<Rightarrow> mem_rep"
  ocaml_mem_rep_byte_at :: "mem_rep \<Rightarrow> ocaml_int \<Rightarrow> byte"
  ocaml_mem_rep_read_bytes :: "mem_rep \<Rightarrow> ocaml_int \<Rightarrow> ocaml_int \<Rightarrow> bytes"
  ocaml_mem_rep_write_bytes :: "mem_rep \<Rightarrow> ocaml_int \<Rightarrow> bytes \<Rightarrow> mem_rep"
  ocaml_mem_rep_append :: "mem_rep \<Rightarrow> ocaml_int \<Rightarrow> byte \<Rightarrow> mem_rep"

code_printing
  type_constructor mem_rep \<rightharpoonup> (OCaml) "uint8 Parray.t"
| constant ocaml_mem_rep_mk \<rightharpoonup> (OCaml) "MemWrapper.Pa"
| constant ocaml_mem_rep_length  \<rightharpoonup> (OCaml) "Parray.length"
| constant ocaml_mem_rep_byte_at \<rightharpoonup> (OCaml) "MemRepWrapper.memRepByteAt"
| constant ocaml_mem_rep_read_bytes \<rightharpoonup> (OCaml) "MemRepWrapper.memRepReadBytes"
| constant ocaml_mem_rep_write_bytes \<rightharpoonup> (OCaml) "MemRepWrapper.memRepWriteBytes"
| constant ocaml_mem_rep_append \<rightharpoonup> (OCaml) "MemRepWrapper.memRepAppend"
| constant ocaml_mem_rep_mk \<rightharpoonup> (OCaml) "Parray.make"

axiomatization where
  mem_rep_length_is[code]: "mem_rep_length \<equiv> nat_of_integer \<circ> ocaml_i32_to_integer \<circ> ocaml_int_to_ocaml_i32 \<circ> ocaml_mem_rep_length" and
  mem_rep_byte_at_is[code]: "mem_rep_byte_at m x \<equiv> (ocaml_mem_rep_byte_at m (ocaml_i32_to_ocaml_int (integer_to_ocaml_i32 (integer_of_nat x))))" and
  mem_rep_read_bytes_is[code]: "mem_rep_read_bytes m x y \<equiv> ocaml_mem_rep_read_bytes m (ocaml_i32_to_ocaml_int (integer_to_ocaml_i32 (integer_of_nat x))) (ocaml_i32_to_ocaml_int (integer_to_ocaml_i32 (integer_of_nat y)))" and
  mem_rep_write_bytes_is[code]: "mem_rep_write_bytes m x bs \<equiv> ocaml_mem_rep_write_bytes m (ocaml_i32_to_ocaml_int (integer_to_ocaml_i32 (integer_of_nat x))) bs" and
  mem_rep_append_is[code]: "mem_rep_append m x b\<equiv> ocaml_mem_rep_append m (ocaml_i32_to_ocaml_int (integer_to_ocaml_i32 (integer_of_nat x))) b" and
  mem_rep_mk_is[code]: "mem_rep_mk x = ocaml_mem_rep_mk (ocaml_i32_to_ocaml_int (integer_to_ocaml_i32 (integer_of_nat (x * Ki64)))) zero_byte"

end