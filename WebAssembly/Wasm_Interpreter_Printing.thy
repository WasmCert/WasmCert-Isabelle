theory Wasm_Interpreter_Printing imports "Wasm_Interpreter_Properties" begin

definition "run = run_v (2^63) 300"

(* host *)

axiomatization
  Abs_host :: "((s \<times> v list) \<Rightarrow> (s \<times> v list) option) \<Rightarrow> host" and
  Rep_host :: "host \<Rightarrow> ((s \<times> v list) \<Rightarrow> (s \<times> v list) option)"
where
  host_is[code abstype]:
    "Abs_host (Rep_host h) = h"
and
  host_apply_impl_def[code] :
    "host_apply_impl s tf h vs = ((Rep_host h) (s,vs))"

(* memory *)

code_printing
  type_constructor byte \<rightharpoonup> (OCaml) "ImplWrapper.byte"

code_printing
  constant msb_byte \<rightharpoonup> (OCaml) "ImplWrapper.msb'_byte"
| constant zero_byte \<rightharpoonup> (OCaml) "ImplWrapper.zero'_byte"
| constant negone_byte \<rightharpoonup> (OCaml) "ImplWrapper.negone'_byte"

end