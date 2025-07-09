theory Wasm_Memory_Bytes_Printing imports Wasm_Base_Defs Wasm_Type_Printing begin

(* Perhaps a more appropriate place for ocaml_int and related conversions is in Wasm_Type_Printing *)
(* But right now it is only used for Parray memory representation *)
typedecl ocaml_int

consts
  ocaml_int_to_integer :: "ocaml_int \<Rightarrow> integer"
  integer_to_ocaml_int :: "integer \<Rightarrow> ocaml_int"

code_printing
  type_constructor ocaml_int \<rightharpoonup> (OCaml) "Int.t"
| constant ocaml_int_to_integer \<rightharpoonup> (OCaml) "Z.of'_int"
| constant integer_to_ocaml_int \<rightharpoonup> (OCaml) "Z.to'_int"

definition ocaml_int_to_nat :: "ocaml_int \<Rightarrow> nat" where
  "ocaml_int_to_nat x = nat_of_integer (ocaml_int_to_integer x)"

definition nat_to_ocaml_int :: "nat \<Rightarrow> ocaml_int" where
  "nat_to_ocaml_int x = integer_to_ocaml_int (integer_of_nat x)"

consts
  ocaml_mem_rep_length :: "mem_rep \<Rightarrow> ocaml_int"
  ocaml_mem_rep_mk :: "ocaml_int \<Rightarrow> ocaml_char \<Rightarrow> mem_rep"
  ocaml_mem_rep_byte_at :: "mem_rep \<Rightarrow> ocaml_int \<Rightarrow> ocaml_char"
  ocaml_mem_rep_read_bytes :: "mem_rep \<Rightarrow> ocaml_int \<Rightarrow> ocaml_int \<Rightarrow> ocaml_char list"
  ocaml_mem_rep_write_bytes :: "mem_rep \<Rightarrow> ocaml_int \<Rightarrow> ocaml_char list \<Rightarrow> mem_rep"
  ocaml_mem_rep_append :: "mem_rep \<Rightarrow> ocaml_int \<Rightarrow> ocaml_char \<Rightarrow> mem_rep"

code_printing
  type_constructor mem_rep \<rightharpoonup> (OCaml) "Bytes.t"
| constant ocaml_mem_rep_mk \<rightharpoonup> (OCaml) "Bytes.make"
| constant ocaml_mem_rep_length  \<rightharpoonup> (OCaml) "Bytes.length"
| constant ocaml_mem_rep_byte_at \<rightharpoonup> (OCaml) "MemRepWrapper.memRepByteAt"
| constant ocaml_mem_rep_read_bytes \<rightharpoonup> (OCaml) "MemRepWrapper.memRepReadBytes"
| constant ocaml_mem_rep_write_bytes \<rightharpoonup> (OCaml) "MemRepWrapper.memRepWriteBytes"
| constant ocaml_mem_rep_append \<rightharpoonup> (OCaml) "MemRepWrapper.memRepAppend"

axiomatization where
  mem_rep_length_is[code]: "mem_rep_length m \<equiv> ocaml_int_to_nat (ocaml_mem_rep_length m)" and
  mem_rep_byte_at_is[code]: "mem_rep_byte_at m x \<equiv> ocaml_char_to_isabelle_byte (ocaml_mem_rep_byte_at m (nat_to_ocaml_int x))" and
  mem_rep_read_bytes_is[code]: "mem_rep_read_bytes m x y \<equiv> List.map ocaml_char_to_isabelle_byte (ocaml_mem_rep_read_bytes m (nat_to_ocaml_int x) (nat_to_ocaml_int y))" and
  mem_rep_write_bytes_is[code]: "mem_rep_write_bytes m x bs \<equiv> ocaml_mem_rep_write_bytes m (nat_to_ocaml_int x) (List.map isabelle_byte_to_ocaml_char bs)" and
  mem_rep_append_is[code]: "mem_rep_append m x b \<equiv> ocaml_mem_rep_append m (nat_to_ocaml_int x) (isabelle_byte_to_ocaml_char b)" and
  mem_rep_mk_is[code]: "mem_rep_mk x = ocaml_mem_rep_mk (nat_to_ocaml_int (x * Ki64)) (isabelle_byte_to_ocaml_char zero_byte)"

end