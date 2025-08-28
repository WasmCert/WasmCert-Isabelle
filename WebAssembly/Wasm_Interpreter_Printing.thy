theory Wasm_Interpreter_Printing imports "Wasm_Interpreter_Properties" begin

definition "run = run_v (2^63) 300"

definition "run_invoke = run_invoke_v (2^63) 300"

(* host *)

axiomatization
  Abs_host_func :: "((s \<times> v list) \<Rightarrow> (s \<times> v list) option) \<Rightarrow> host_func" and
  Rep_host_func :: "host_func \<Rightarrow> ((s \<times> v list) \<Rightarrow> (s \<times> v list) option)"
where
  host_func_is[code abstype]:
    "Abs_host_func (Rep_host_func h) = h"
and
  host_apply_impl_def[code] :
    "host_func_apply_impl s tf h vs = ((Rep_host_func h) (s,vs))"

code_printing
  type_constructor host_ref \<rightharpoonup> (OCaml) "int32"

(* memory *)

(*
code_printing
  type_constructor byte \<rightharpoonup> (OCaml) "ImplWrapper.byte"

code_printing
  constant msb_byte \<rightharpoonup> (OCaml) "ImplWrapper.msb'_byte"
| constant zero_byte \<rightharpoonup> (OCaml) "ImplWrapper.zero'_byte"
| constant negone_byte \<rightharpoonup> (OCaml) "ImplWrapper.negone'_byte"
*)

end