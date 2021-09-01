theory Wasm_Interpreter_Monad_Printing imports "Wasm_Interpreter_Monad_Properties" begin

definition "run_m = run_v_m (2^63) 300"

definition "run_invoke_m = run_invoke_v_m (2^63) 300"

(* host *)

axiomatization
  Abs_host_m :: "((s_m \<times> v list) \<Rightarrow> ((s_m \<times> v list) option) Heap) \<Rightarrow> host" and
  Rep_host_m :: "host \<Rightarrow> ((s_m \<times> v list) \<Rightarrow> ((s_m \<times> v list) option) Heap)"
where
  host_is[code abstype]:
    "Abs_host_m (Rep_host_m h) = h"
and
  host_apply_impl_def[code] :
    "host_apply_impl_m s tf h vs = ((Rep_host_m h) (s,vs))"

end