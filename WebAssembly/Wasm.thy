theory Wasm imports Wasm_Base_Defs begin

(* TYPING RELATION *)
inductive b_e_typing :: "[t_context, b_e list, tf] \<Rightarrow> bool" ("_ \<turnstile> _ : _" 60) where
  \<comment> \<open>\<open>num ops\<close>\<close>
  const_num:"\<C> \<turnstile> [EConstNum v] :([] _> [T_num (typeof_num v)])"
| const_vec:"\<C> \<turnstile> [EConstVec v] :([] _> [T_vec (typeof_vec v)])"
| unop:"unop_t_num_agree op t   \<Longrightarrow> \<C> \<turnstile> [Unop t op]  : ([T_num t]   _> [T_num t])"
| binop:"binop_t_num_agree op t \<Longrightarrow> \<C> \<turnstile> [Binop t op] : ([T_num t,T_num t] _> [T_num t])"
| testop:"is_int_t_num t   \<Longrightarrow> \<C> \<turnstile> [Testop t _]      : ([T_num t]   _> [T_num T_i32])"
| relop:"relop_t_num_agree op t   \<Longrightarrow> \<C> \<turnstile> [Relop t op] : ([T_num t,T_num t] _> [T_num T_i32])"
  \<comment> \<open>\<open>vector ops\<close>\<close>
| unop_vec:"\<C> \<turnstile> [Unop_vec op]  : ([T_vec T_v128]   _> [T_vec T_v128])"
| binop_vec:"\<lbrakk>binop_vec_wf op\<rbrakk> \<Longrightarrow> \<C> \<turnstile> [Binop_vec op]  : ([T_vec T_v128, T_vec T_v128]   _> [T_vec T_v128])"
| ternop_vec:"\<C> \<turnstile> [Ternop_vec op]  : ([T_vec T_v128, T_vec T_v128, T_vec T_v128]   _> [T_vec T_v128])"
| test_vec:"\<C> \<turnstile> [Test_vec op]  : ([T_vec T_v128]   _> [T_num T_i32])"
| shift_vec:"\<C> \<turnstile> [Shift_vec op]  : ([T_vec T_v128, T_num T_i32]   _> [T_vec T_v128])"
| splat_vec:"\<C> \<turnstile> [Splat_vec sv]  : ([T_num (vec_lane_t sv)]   _> [T_vec T_v128])"
| extract_vec:"\<lbrakk>i < vec_num sv; sx = U \<or> vec_length sv \<le> 2\<rbrakk> \<Longrightarrow> \<C> \<turnstile> [Extract_vec sv sx i]  : ([T_vec T_v128]   _> [T_num (vec_lane_t sv)])"
| replace_vec:"i < vec_num sv \<Longrightarrow> \<C> \<turnstile> [Replace_vec sv i]  : ([T_vec T_v128, T_num (vec_lane_t sv)]   _> [T_vec T_v128])"
  \<comment> \<open>\<open>convert\<close>\<close>
| convert:"\<lbrakk>(t1 \<noteq> t2); (sat_sx = None) = ((is_float_t_num t1 \<and> is_float_t_num t2) \<or> (is_int_t_num t1 \<and> is_int_t_num t2 \<and> (t_num_length t1 < t_num_length t2)))\<rbrakk> \<Longrightarrow> \<C> \<turnstile> [Cvtop t1 Convert t2 sat_sx] : ([T_num t2] _> [T_num t1])"
  \<comment> \<open>\<open>reinterpret\<close>\<close>
| reinterpret:"\<lbrakk>(t1 \<noteq> t2); t_num_length t1 = t_num_length t2\<rbrakk> \<Longrightarrow> \<C> \<turnstile> [Cvtop t1 Reinterpret t2 None] : ([T_num t2] _> [T_num t1])"
  \<comment> \<open>\<open>unreachable, nop, drop, select\<close>\<close>
| unreachable:"\<C> \<turnstile> [Unreachable] : (ts _> ts')"
| nop:"\<C> \<turnstile> [Nop] : ([] _> [])"
| drop:"\<C> \<turnstile> [Drop] : ([t] _> [])"
| select:"\<C> \<turnstile> [Select] : ([t,t,T_num T_i32] _> [t])"
  \<comment> \<open>\<open>block\<close>\<close>
| block:"\<lbrakk>tb_tf_t \<C> tb = Some (tn _> tm); \<C>\<lparr>label := ([tm] @ (label \<C>))\<rparr> \<turnstile> es : (tn _> tm)\<rbrakk> \<Longrightarrow> \<C> \<turnstile> [Block tb es] : (tn _> tm)"
  \<comment> \<open>\<open>loop\<close>\<close>
| loop:"\<lbrakk>tb_tf_t \<C> tb = Some (tn _> tm); \<C>\<lparr>label := ([tn] @ (label \<C>))\<rparr> \<turnstile> es : (tn _> tm)\<rbrakk> \<Longrightarrow> \<C> \<turnstile> [Loop tb es] : (tn _> tm)"
  \<comment> \<open>\<open>if then else\<close>\<close>
| if_wasm:"\<lbrakk>tb_tf_t \<C> tb = Some (tn _> tm); \<C>\<lparr>label := ([tm] @ (label \<C>))\<rparr> \<turnstile> es1 : (tn _> tm); \<C>\<lparr>label := ([tm] @ (label \<C>))\<rparr> \<turnstile> es2 : (tn _> tm)\<rbrakk> \<Longrightarrow> \<C> \<turnstile> [If tb es1 es2] : (tn @ [T_num T_i32] _> tm)"
  \<comment> \<open>\<open>br\<close>\<close>
| br:"\<lbrakk>i < length(label \<C>); (label \<C>)!i = ts\<rbrakk> \<Longrightarrow> \<C> \<turnstile> [Br i] : (t1s @ ts _> t2s)"
  \<comment> \<open>\<open>br_if\<close>\<close>
| br_if:"\<lbrakk>i < length(label \<C>); (label \<C>)!i = ts\<rbrakk> \<Longrightarrow> \<C> \<turnstile> [Br_if i] : (ts @ [T_num T_i32] _> ts)"
  \<comment> \<open>\<open>br_table\<close>\<close>
| br_table:"\<lbrakk>list_all (\<lambda>i. i < length(label \<C>) \<and> (label \<C>)!i = ts) (is@[i])\<rbrakk> \<Longrightarrow> \<C> \<turnstile> [Br_table is i] : (t1s @ ts @ [T_num T_i32] _> t2s)"
  \<comment> \<open>\<open>return\<close>\<close>
| return:"\<lbrakk>(return \<C>) = Some ts\<rbrakk> \<Longrightarrow> \<C> \<turnstile> [Return] : (t1s @ ts _> t2s)"
  \<comment> \<open>\<open>call\<close>\<close>
| call:"\<lbrakk>i < length(func_t \<C>); (func_t \<C>)!i = tf\<rbrakk> \<Longrightarrow> \<C> \<turnstile> [Call i] : tf"
  \<comment> \<open>\<open>call_indirect\<close>\<close>
| call_indirect:"\<lbrakk>i < length(types_t \<C>); (types_t \<C>)!i = (t1s _> t2s); length (table \<C>) \<ge> 1\<rbrakk> \<Longrightarrow> \<C> \<turnstile> [Call_indirect i] : (t1s @ [T_num T_i32] _> t2s)"
  \<comment> \<open>\<open>get_local\<close>\<close>
| get_local:"\<lbrakk>i < length(local \<C>); (local \<C>)!i = t\<rbrakk> \<Longrightarrow> \<C> \<turnstile> [Get_local i] : ([] _> [t])"
  \<comment> \<open>\<open>set_local\<close>\<close>
| set_local:"\<lbrakk>i < length(local \<C>); (local \<C>)!i = t\<rbrakk> \<Longrightarrow> \<C> \<turnstile> [Set_local i] : ([t] _> [])"
  \<comment> \<open>\<open>tee_local\<close>\<close>
| tee_local:"\<lbrakk>i < length(local \<C>); (local \<C>)!i = t\<rbrakk> \<Longrightarrow> \<C> \<turnstile> [Tee_local i] : ([t] _> [t])"
  \<comment> \<open>\<open>get_global\<close>\<close>
| get_global:"\<lbrakk>i < length(global \<C>); tg_t ((global \<C>)!i) = t\<rbrakk> \<Longrightarrow> \<C> \<turnstile> [Get_global i] : ([] _> [t])"
  \<comment> \<open>\<open>set_global\<close>\<close>
| set_global:"\<lbrakk>i < length(global \<C>); tg_t ((global \<C>)!i) = t; is_mut ((global \<C>)!i)\<rbrakk> \<Longrightarrow> \<C> \<turnstile> [Set_global i] : ([t] _> [])"
  \<comment> \<open>\<open>load\<close>\<close>
| load:"\<lbrakk>length (memory \<C>) \<ge> 1; load_store_t_bounds a (option_projl tp_sx) t\<rbrakk> \<Longrightarrow> \<C> \<turnstile> [Load t tp_sx a off] : ([T_num T_i32] _> [T_num t])"
  \<comment> \<open>\<open>store\<close>\<close>
| store:"\<lbrakk>length (memory \<C>) \<ge> 1; load_store_t_bounds a tp t\<rbrakk> \<Longrightarrow> \<C> \<turnstile> [Store t tp a off] : ([T_num T_i32,T_num t] _> [])"
  \<comment> \<open>\<open>load_vec\<close>\<close>
| load_vec:"\<lbrakk>length (memory \<C>) \<ge> 1; load_vec_t_bounds lvop a\<rbrakk> \<Longrightarrow> \<C> \<turnstile> [Load_vec lvop a off] : ([T_num T_i32] _> [T_vec T_v128])"
  \<comment> \<open>\<open>load_lane_vec\<close>\<close>
| load_lane_vec:"\<lbrakk>length (memory \<C>) \<ge> 1; i < vec_i_num svi \<and> 2^a \<le> (vec_i_length svi)\<rbrakk> \<Longrightarrow> \<C> \<turnstile> [Load_lane_vec svi i a off] : ([T_num T_i32, T_vec T_v128] _> [T_vec T_v128])"
  \<comment> \<open>\<open>store_vec\<close>\<close>
| store_vec:"\<lbrakk>length (memory \<C>) \<ge> 1; store_vec_t_bounds svop a\<rbrakk> \<Longrightarrow> \<C> \<turnstile> [Store_vec svop a off] : ([T_num T_i32,T_vec T_v128] _> [])"
  \<comment> \<open>\<open>current_memory\<close>\<close>
| current_memory:"length (memory \<C>) \<ge> 1 \<Longrightarrow> \<C> \<turnstile> [Current_memory] : ([] _> [T_num T_i32])"
  \<comment> \<open>\<open>Grow_memory\<close>\<close>
| grow_memory:"length (memory \<C>) \<ge> 1 \<Longrightarrow> \<C> \<turnstile> [Grow_memory] : ([T_num T_i32] _> [T_num T_i32])"
  \<comment> \<open>\<open>empty program\<close>\<close>
| empty:"\<C> \<turnstile> [] : ([] _> [])"
  \<comment> \<open>\<open>composition\<close>\<close>
| composition:"\<lbrakk>\<C> \<turnstile> es : (t1s _> t2s); \<C> \<turnstile> [e] : (t2s _> t3s)\<rbrakk> \<Longrightarrow> \<C> \<turnstile> es @ [e] : (t1s _> t3s)"
  \<comment> \<open>\<open>weakening\<close>\<close>
| weakening:"\<C> \<turnstile> es : (t1s _> t2s) \<Longrightarrow> \<C> \<turnstile> es : (ts @ t1s _> ts @ t2s)"

definition "glob_typing g tg = (tg_mut tg = g_mut g \<and> tg_t tg = typeof (g_val g))"

definition "globi_agree gs n g = (n < length gs \<and> glob_typing (gs!n) g)"

definition "limits_compat lt1 lt2 =
  ((l_min lt1) \<ge> (l_min lt2) \<and>
  pred_option (\<lambda>lt2_the. (case (l_max lt1) of
                            Some lt1_the \<Rightarrow> (lt1_the \<le> lt2_the)
                          | None \<Rightarrow> False)) (l_max lt2))"

definition "tab_typing t tt = (limits_compat \<lparr>l_min=(tab_size t),l_max=(tab_max t)\<rparr> tt)"

definition "tabi_agree ts n tab_t =
  ((n < length ts) \<and> (tab_typing (ts!n) tab_t))"

definition "mem_typing m mt = (limits_compat \<lparr>l_min=(mem_size m),l_max=(mem_max m)\<rparr> mt)"

definition "memi_agree ms n mem_t =
  ((n < length ms) \<and> mem_typing (ms!n) mem_t)"

definition "funci_agree fs n f = (n < length fs \<and> (cl_type (fs!n)) = f)"

inductive inst_typing :: "[s, inst, t_context] \<Rightarrow> bool" where
  "\<lbrakk>list_all2 (funci_agree (funcs s)) fs tfs;
    list_all2 (globi_agree (globs s)) gs tgs;
    list_all2 (tabi_agree (tabs s)) tbs tabs_t;
    list_all2 (memi_agree (mems s)) ms mems_t\<rbrakk>
      \<Longrightarrow> inst_typing s \<lparr>types = ts, funcs = fs, tabs = tbs, mems = ms, globs = gs\<rparr>
                        \<lparr>types_t = ts, func_t = tfs, global = tgs, table = tabs_t, memory = mems_t, local = [], label = [], return = None\<rparr>"

inductive frame_typing :: "[s, f, t_context] \<Rightarrow> bool" where
"\<lbrakk>tvs = map typeof (f_locs f); inst_typing s (f_inst f) \<C>\<rbrakk> \<Longrightarrow> frame_typing s f (\<C>\<lparr>local := tvs\<rparr>)"

inductive cl_typing :: "[s, cl, tf] \<Rightarrow> bool" where
   "\<lbrakk>inst_typing s i \<C>; tf = (t1s _> t2s); \<C>\<lparr>local := t1s @ ts, label := ([t2s] @ (label \<C>)), return := Some t2s\<rparr> \<turnstile> es : ([] _> t2s)\<rbrakk> \<Longrightarrow> cl_typing s (Func_native i tf ts es) (t1s _> t2s)"
 |  "cl_typing s (Func_host tf h) tf"


(* lifting the b_e_typing relation to the administrative operators *)
inductive e_typing :: "[s, t_context, e list, tf] \<Rightarrow> bool" ("_\<bullet>_ \<turnstile> _ : _" 60)
and       l_typing :: "[s, (t list) option, f, e list, t list] \<Rightarrow> bool" ("_\<bullet>_ \<tturnstile>' _;_ : _" 60) where
(* section: e_typing *)
  (* lifting *)
  "\<C> \<turnstile> b_es : tf \<Longrightarrow> \<S>\<bullet>\<C> \<turnstile> $*b_es : tf"
  (* composition *)
| "\<lbrakk>\<S>\<bullet>\<C> \<turnstile> es : (t1s _> t2s); \<S>\<bullet>\<C> \<turnstile> [e] : (t2s _> t3s)\<rbrakk> \<Longrightarrow> \<S>\<bullet>\<C> \<turnstile> es @ [e] : (t1s _> t3s)"
  (* weakening *)
| "\<S>\<bullet>\<C> \<turnstile> es : (t1s _> t2s) \<Longrightarrow>\<S>\<bullet>\<C> \<turnstile> es : (ts @ t1s _> ts @ t2s)"
| "\<S>\<bullet>\<C> \<turnstile> [Ref v_r] :([] _> [T_ref (typeof_ref v_r)])"
  (* trap *)
| "\<S>\<bullet>\<C> \<turnstile> [Trap] : tf"
  (* frame *)
| "\<lbrakk>\<S>\<bullet>Some ts \<tturnstile> f;es : ts; length ts = n\<rbrakk> \<Longrightarrow> \<S>\<bullet>\<C> \<turnstile> [Frame n f es] : ([] _> ts)"
  (* invoke *)
| "\<lbrakk>i < length (funcs \<S>); cl_type ((funcs \<S>)!i) = tf\<rbrakk> \<Longrightarrow> \<S>\<bullet>\<C>  \<turnstile> [Invoke i] : tf"
  (* label *)
| "\<lbrakk>\<S>\<bullet>\<C> \<turnstile> e0s : (ts _> t2s); \<S>\<bullet>\<C>\<lparr>label := ([ts] @ (label \<C>))\<rparr> \<turnstile> es : ([] _> t2s); length ts = n\<rbrakk> \<Longrightarrow> \<S>\<bullet>\<C> \<turnstile> [Label n e0s es] : ([] _> t2s)"
  (* Init_mem (instantiation) *)
| "\<lbrakk>length (memory \<C>) \<ge> 1\<rbrakk> \<Longrightarrow> \<S>\<bullet>\<C>  \<turnstile> [Init_mem n bs] : ([] _> [])"
  (* Init_tab (instantiation) *)
| "\<lbrakk>length (table \<C>) \<ge> 1; list_all (\<lambda>ti. ti < length (funcs \<S>)) tis\<rbrakk> \<Longrightarrow> \<S>\<bullet>\<C>  \<turnstile> [Init_tab n tis] : ([] _> [])"
(* section: l_typing *)
| "\<lbrakk>frame_typing \<S> f \<C>; \<S>\<bullet>\<C>\<lparr>return := rs\<rparr> \<turnstile> es : ([] _> ts)\<rbrakk> \<Longrightarrow> \<S>\<bullet>rs \<tturnstile> f;es : ts"

definition "tab_agree s tab =
  ((list_all (\<lambda>i_opt. (case i_opt of None \<Rightarrow> True | Some i \<Rightarrow> i < length (funcs s))) (fst tab)) \<and>
   pred_option (\<lambda>max. (tab_size tab) \<le> max) (tab_max tab))"

inductive store_typing :: "s \<Rightarrow> bool" where
  "\<lbrakk>list_all (\<lambda>cl. \<exists>tf. cl_typing s cl tf) (funcs s);
    list_all (tab_agree s) (tabs s);
    list_all mem_agree (mems s)
    \<rbrakk> \<Longrightarrow> store_typing s"

inductive config_typing :: "[s, f, e list, t list] \<Rightarrow> bool" ("\<turnstile> _;_;_ : _" 60) where
  "\<lbrakk>store_typing s; s\<bullet>None \<tturnstile> f;es : ts\<rbrakk> \<Longrightarrow> \<turnstile> s;f;es : ts"

(* REDUCTION RELATION *)

inductive reduce_simple :: "[e list, e list] \<Rightarrow> bool" ("\<lparr>_\<rparr> \<leadsto> \<lparr>_\<rparr>" 60) where
  \<comment> \<open>\<open>unary ops\<close>\<close>
  unop:"\<lparr>[$EConstNum v, $(Unop t op)]\<rparr> \<leadsto> \<lparr>[$EConstNum (app_unop op v)]\<rparr>"
  \<comment> \<open>\<open>binary ops\<close>\<close>
| binop_Some:"\<lbrakk>app_binop op v1 v2 = (Some v)\<rbrakk> \<Longrightarrow> \<lparr>[$EConstNum v1, $EConstNum v2, $(Binop t op)]\<rparr> \<leadsto> \<lparr>[$EConstNum v]\<rparr>"
| binop_None:"\<lbrakk>app_binop op v1 v2 = None\<rbrakk> \<Longrightarrow> \<lparr>[$EConstNum v1, $EConstNum v2, $(Binop t op)]\<rparr> \<leadsto> \<lparr>[Trap]\<rparr>"
  \<comment> \<open>\<open>testops\<close>\<close>
| testop:"\<lparr>[$EConstNum v, $(Testop t op)]\<rparr> \<leadsto> \<lparr>[$EConstNum (app_testop op v)]\<rparr>"
  \<comment> \<open>\<open>relops\<close>\<close>
| relop:"\<lparr>[$EConstNum v1, $EConstNum v2, $(Relop t op)]\<rparr> \<leadsto> \<lparr>[$EConstNum (app_relop op v1 v2)]\<rparr>"
  \<comment> \<open>\<open>convert\<close>\<close>
| convert_Some:"\<lbrakk>(typeof_num v) = t1; cvt t2 sat_sx v = (Some v')\<rbrakk> \<Longrightarrow> \<lparr>[$(EConstNum v), $(Cvtop t2 Convert t1 sat_sx)]\<rparr> \<leadsto> \<lparr>[$(EConstNum v')]\<rparr>"
| convert_None:"\<lbrakk>(typeof_num v) = t1; cvt t2 sat_sx v = None\<rbrakk> \<Longrightarrow> \<lparr>[$(EConstNum v), $(Cvtop t2 Convert t1 sat_sx)]\<rparr> \<leadsto> \<lparr>[Trap]\<rparr>"
  \<comment> \<open>\<open>reinterpret\<close>\<close>
| reinterpret:"(typeof_num v) = t1 \<Longrightarrow> \<lparr>[$(EConstNum v), $(Cvtop t2 Reinterpret t1 None)]\<rparr> \<leadsto> \<lparr>[$(EConstNum (wasm_reinterpret t2 v))]\<rparr>"
  \<comment> \<open>\<open>unary vector ops\<close>\<close>
| unop_vec:"\<lparr>[$EConstVec v, $(Unop_vec op)]\<rparr> \<leadsto> \<lparr>[$EConstVec (app_unop_vec op v)]\<rparr>"
  \<comment> \<open>\<open>binary vector ops\<close>\<close>
| binop_vec_Some:"\<lbrakk>app_binop_vec op v1 v2 = Some v\<rbrakk> \<Longrightarrow> \<lparr>[$EConstVec v1, $EConstVec v2, $(Binop_vec op)]\<rparr> \<leadsto> \<lparr>[$EConstVec v]\<rparr>"
| binop_vec_None:"\<lbrakk>app_binop_vec op v1 v2 = None\<rbrakk> \<Longrightarrow> \<lparr>[$EConstVec v1, $EConstVec v2, $(Binop_vec op)]\<rparr> \<leadsto> \<lparr>[Trap]\<rparr>"
  \<comment> \<open>\<open>ternary vector ops\<close>\<close>
| ternop_vec:"\<lparr>[$EConstVec v1, $EConstVec v2, $EConstVec v3, $(Ternop_vec op)]\<rparr> \<leadsto> \<lparr>[$EConstVec (app_ternop_vec op v1 v2 v3)]\<rparr>"
  \<comment> \<open>\<open>test vector ops\<close>\<close>
| test_vec:"\<lparr>[$EConstVec v, $(Test_vec op)]\<rparr> \<leadsto> \<lparr>[$EConstNum (ConstInt32 (app_test_vec op v))]\<rparr>"
  \<comment> \<open>\<open>shift vector ops\<close>\<close>
| shift_vec:"\<lparr>[$EConstVec v, $EConstNum (ConstInt32 n), $(Shift_vec op)]\<rparr> \<leadsto> \<lparr>[$EConstVec (app_shift_vec op v n)]\<rparr>"
  \<comment> \<open>\<open>splat vector ops\<close>\<close>
| splat_vec:"\<lparr>[$EConstNum v, $(Splat_vec sv)]\<rparr> \<leadsto> \<lparr>[$EConstVec (app_splat_vec sv v)]\<rparr>"
  \<comment> \<open>\<open>extract vector ops\<close>\<close>
| extract_vec:"\<lparr>[$EConstVec v, $(Extract_vec sv sx i)]\<rparr> \<leadsto> \<lparr>[$EConstNum (app_extract_vec sv sx i v)]\<rparr>"
  \<comment> \<open>\<open>replace vector ops\<close>\<close>
| replace_vec:"\<lparr>[$EConstVec v, $EConstNum vn, $(Replace_vec sv i)]\<rparr> \<leadsto> \<lparr>[$EConstVec (app_replace_vec sv i v vn)]\<rparr>"
  \<comment> \<open>\<open>unreachable\<close>\<close>
| unreachable:"\<lparr>[$ Unreachable]\<rparr> \<leadsto> \<lparr>[Trap]\<rparr>"
  \<comment> \<open>\<open>nop\<close>\<close>
| nop:"\<lparr>[$ Nop]\<rparr> \<leadsto> \<lparr>[]\<rparr>"

(*REVIEW THINGS BELLOW*)
  \<comment> \<open>\<open>drop\<close>\<close>
| drop:"\<lparr>[$C v, ($ Drop)]\<rparr> \<leadsto> \<lparr>[]\<rparr>"
  \<comment> \<open>\<open>select\<close>\<close>
| select_false:"int_eq n 0 \<Longrightarrow> \<lparr>[$C v1, $C v2, $EConstNum (ConstInt32 n), ($ Select)]\<rparr> \<leadsto> \<lparr>[$C v2]\<rparr>"
| select_true:"int_ne n 0 \<Longrightarrow> \<lparr>[$C v1, $C v2, $EConstNum (ConstInt32 n), ($ Select)]\<rparr> \<leadsto> \<lparr>[$C v1]\<rparr>"
  \<comment> \<open>\<open>if\<close>\<close>
| if_false:"int_eq n 0 \<Longrightarrow> \<lparr>[$EConstNum (ConstInt32 n), $(If tb e1s e2s)]\<rparr> \<leadsto> \<lparr>[$(Block tb e2s)]\<rparr>"
| if_true:"int_ne n 0 \<Longrightarrow> \<lparr>[$EConstNum (ConstInt32 n), $(If tb e1s e2s)]\<rparr> \<leadsto> \<lparr>[$(Block tb e1s)]\<rparr>"
  \<comment> \<open>\<open>label\<close>\<close>
| label_const:"\<lparr>[Label n es ($C* vs)]\<rparr> \<leadsto> \<lparr>($C* vs)\<rparr>"
| label_trap:"\<lparr>[Label n es [Trap]]\<rparr> \<leadsto> \<lparr>[Trap]\<rparr>"
  \<comment> \<open>\<open>br\<close>\<close>
| br:"\<lbrakk>length vs = n; Lfilled i lholed (($C* vs) @ [$(Br i)]) LI\<rbrakk> \<Longrightarrow> \<lparr>[Label n es LI]\<rparr> \<leadsto> \<lparr>($C* vs) @ es\<rparr>"
  \<comment> \<open>\<open>br_if\<close>\<close>
| br_if_false:"int_eq n 0 \<Longrightarrow> \<lparr>[$EConstNum (ConstInt32 n), $(Br_if i)]\<rparr> \<leadsto> \<lparr>[]\<rparr>"
| br_if_true:"int_ne n 0 \<Longrightarrow> \<lparr>[$EConstNum (ConstInt32 n), $(Br_if i)]\<rparr> \<leadsto> \<lparr>[$(Br i)]\<rparr>"
  \<comment> \<open>\<open>br_table\<close>\<close>
| br_table:"\<lbrakk>length is > (nat_of_int c)\<rbrakk> \<Longrightarrow> \<lparr>[$EConstNum (ConstInt32 c), $(Br_table is i)]\<rparr> \<leadsto> \<lparr>[$(Br (is!(nat_of_int c)))]\<rparr>"
| br_table_length:"\<lbrakk>length is \<le> (nat_of_int c)\<rbrakk> \<Longrightarrow> \<lparr>[$EConstNum (ConstInt32 c), $(Br_table is i)]\<rparr> \<leadsto> \<lparr>[$(Br i)]\<rparr>"
  \<comment> \<open>\<open>local\<close>\<close>
| local_const:"\<lparr>[Frame n f ($C* vs)]\<rparr> \<leadsto> \<lparr>($C* vs)\<rparr>"
| local_trap:"\<lparr>[Frame n f [Trap]]\<rparr> \<leadsto> \<lparr>[Trap]\<rparr>"
  \<comment> \<open>\<open>return\<close>\<close>
| return:"\<lbrakk>length vs = n; Lfilled j lholed (($C* vs) @ [$Return]) es\<rbrakk>  \<Longrightarrow> \<lparr>[Frame n f es]\<rparr> \<leadsto> \<lparr>($C* vs)\<rparr>"
  \<comment> \<open>\<open>tee_local\<close>\<close>
| tee_local:"\<lparr>[$C v, $(Tee_local i)]\<rparr> \<leadsto> \<lparr>[$C v, $C v, $(Set_local i)]\<rparr>"
| trap:"\<lbrakk>es \<noteq> [Trap]; Lfilled 0 lholed [Trap] es\<rbrakk> \<Longrightarrow> \<lparr>es\<rparr> \<leadsto> \<lparr>[Trap]\<rparr>"

(* full reduction rule *)
inductive reduce :: "[s, f, e list, s, f, e list] \<Rightarrow> bool" ("\<lparr>_;_;_\<rparr> \<leadsto> \<lparr>_;_;_\<rparr>" 60) where
  \<comment> \<open>\<open>lifting basic reduction\<close>\<close>

  basic:"\<lparr>e\<rparr> \<leadsto> \<lparr>e'\<rparr> \<Longrightarrow> \<lparr>s;f;e\<rparr> \<leadsto> \<lparr>s;f;e'\<rparr>"
  \<comment> \<open>\<open>call\<close>\<close>
| call:"\<lparr>s;f;[$(Call j)]\<rparr> \<leadsto> \<lparr>s;f;[Invoke (sfunc_ind (f_inst f) j)]\<rparr>"
  \<comment> \<open>\<open>call_indirect\<close>\<close>
| call_indirect_Some:"\<lbrakk>(f_inst f) = i; stab s i (nat_of_int c) = Some i_cl; stypes i j = tf; cl_type (funcs s!i_cl) = tf\<rbrakk> \<Longrightarrow> \<lparr>s;f;[$EConstNum (ConstInt32 c), $(Call_indirect j)]\<rparr> \<leadsto> \<lparr>s;f;[Invoke i_cl]\<rparr>"
| call_indirect_None:"\<lbrakk>(f_inst f) = i; (stab s i (nat_of_int c) = Some i_cl \<and> stypes i j \<noteq> cl_type (funcs s!i_cl)) \<or> stab s i (nat_of_int c) = None\<rbrakk> \<Longrightarrow> \<lparr>s;f;[$EConstNum (ConstInt32 c), $(Call_indirect j)]\<rparr> \<leadsto> \<lparr>s;f;[Trap]\<rparr>"
  \<comment> \<open>\<open>invoke\<close>\<close>
| invoke_native:"\<lbrakk>(funcs s!i_cl) = Func_native j (t1s _> t2s) ts es; ves = ($C* vcs); length vcs = n; length ts = k; length t1s = n; length t2s = m; (n_zeros ts = zs) \<rbrakk> \<Longrightarrow> \<lparr>s;f;ves @ [Invoke i_cl]\<rparr> \<leadsto> \<lparr>s;f;[Frame m \<lparr> f_locs = vcs@zs, f_inst = j \<rparr> [(Label m [] ($*es))]]\<rparr>"
| invoke_host_Some:"\<lbrakk>(funcs s!i_cl) = Func_host (t1s _> t2s) h; ves = ($C* vcs); length vcs = n; length t1s = n; length t2s = m; host_apply s (t1s _> t2s) h vcs hs (Some (s', vcs'))\<rbrakk> \<Longrightarrow> \<lparr>s;f;ves @ [Invoke i_cl]\<rparr> \<leadsto> \<lparr>s';f;($C* vcs')\<rparr>"
| invoke_host_None:"\<lbrakk>(funcs s!i_cl) = Func_host (t1s _> t2s) h; ves = ($C* vcs); length vcs = n; length t1s = n; length t2s = m\<rbrakk> \<Longrightarrow> \<lparr>s;f;ves @ [Invoke i_cl]\<rparr> \<leadsto> \<lparr>s;f;[Trap]\<rparr>"
  \<comment> \<open>\<open>get_local\<close>\<close>
| get_local:"\<lbrakk>length vi = j; f_locs f = (vi @ [v] @ vs)\<rbrakk> \<Longrightarrow> \<lparr>s;f;[$(Get_local j)]\<rparr> \<leadsto> \<lparr>s;f;[$C v]\<rparr>"
  \<comment> \<open>\<open>set_local\<close>\<close>
| set_local:"\<lbrakk>length vi = j\<rbrakk> \<Longrightarrow> \<lparr>s;\<lparr> f_locs = (vi @ [v] @ vs), f_inst = i \<rparr>;[$C v', $(Set_local j)]\<rparr> \<leadsto> \<lparr>s;\<lparr> f_locs = (vi @ [v'] @ vs), f_inst = i \<rparr>;[]\<rparr>"
  \<comment> \<open>\<open>get_global\<close>\<close>
| get_global:"\<lparr>s;f;[$(Get_global j)]\<rparr> \<leadsto> \<lparr>s;f;[$C(sglob_val s (f_inst f) j)]\<rparr>"
  \<comment> \<open>\<open>set_global\<close>\<close>
| set_global:"supdate_glob s (f_inst f) j v = s' \<Longrightarrow> \<lparr>s;f;[$C v, $(Set_global j)]\<rparr> \<leadsto> \<lparr>s';f;[]\<rparr>"
  \<comment> \<open>\<open>load\<close>\<close>
| load_Some:"\<lbrakk>smem_ind (f_inst f) = Some j; ((mems s)!j) = m; load m (nat_of_int k) off (t_num_length t) = Some bs\<rbrakk> \<Longrightarrow> \<lparr>s;f;[$EConstNum (ConstInt32 k), $(Load t None a off)]\<rparr> \<leadsto> \<lparr>s;f;[$EConstNum (wasm_deserialise_num bs t)]\<rparr>"
| load_None:"\<lbrakk>smem_ind (f_inst f) = Some j; ((mems s)!j) = m; load m (nat_of_int k) off (t_num_length t) = None\<rbrakk> \<Longrightarrow> \<lparr>s;f;[$EConstNum (ConstInt32 k), $(Load t None a off)]\<rparr> \<leadsto> \<lparr>s;f;[Trap]\<rparr>"
  \<comment> \<open>\<open>load packed\<close>\<close>
| load_packed_Some:"\<lbrakk>smem_ind (f_inst f) = Some j; ((mems s)!j) = m; load_packed sx m (nat_of_int k) off (tp_num_length tp) (t_num_length t) = Some bs\<rbrakk> \<Longrightarrow> \<lparr>s;f;[$EConstNum (ConstInt32 k), $(Load t (Some (tp, sx)) a off)]\<rparr> \<leadsto> \<lparr>s;f;[$EConstNum (wasm_deserialise_num bs t)]\<rparr>"
| load_packed_None:"\<lbrakk>smem_ind (f_inst f) = Some j; ((mems s)!j) = m; load_packed sx m (nat_of_int k) off (tp_num_length tp) (t_num_length t) = None\<rbrakk> \<Longrightarrow> \<lparr>s;f;[$EConstNum (ConstInt32 k), $(Load t (Some (tp, sx)) a off)]\<rparr> \<leadsto> \<lparr>s;f;[Trap]\<rparr>"
  \<comment> \<open>\<open>store\<close>\<close>
| store_Some:"\<lbrakk>(typeof_num v) = t; smem_ind (f_inst f) = Some j; ((mems s)!j) = m; store m (nat_of_int k) off (bits_num v) (t_num_length t) = Some mem'\<rbrakk> \<Longrightarrow> \<lparr>s;f;[$EConstNum (ConstInt32 k), $EConstNum v, $(Store t None a off)]\<rparr> \<leadsto> \<lparr>s\<lparr>mems:= ((mems s)[j := mem'])\<rparr>;f;[]\<rparr>"
| store_None:"\<lbrakk>(typeof_num v) = t; smem_ind (f_inst f) = Some j; ((mems s)!j) = m; store m (nat_of_int k) off (bits_num v) (t_num_length t) = None\<rbrakk> \<Longrightarrow> \<lparr>s;f;[$EConstNum (ConstInt32 k), $EConstNum v, $(Store t None a off)]\<rparr> \<leadsto> \<lparr>s;f;[Trap]\<rparr>"
  \<comment> \<open>\<open>store packed\<close>\<close> (* take only (tp_length tp) lower order bytes *)
| store_packed_Some:"\<lbrakk>(typeof_num v) = t; smem_ind (f_inst f) = Some j; ((mems s)!j) = m; store_packed m (nat_of_int k) off (bits_num v) (tp_num_length tp) = Some mem'\<rbrakk> \<Longrightarrow> \<lparr>s;f;[$EConstNum (ConstInt32 k), $EConstNum v, $(Store t (Some tp) a off)]\<rparr> \<leadsto> \<lparr>s\<lparr>mems:= ((mems s)[j := mem'])\<rparr>;f;[]\<rparr>"
| store_packed_None:"\<lbrakk>(typeof_num v) = t; smem_ind (f_inst f) = Some j; ((mems s)!j) = m; store_packed m (nat_of_int k) off (bits_num v) (tp_num_length tp) = None\<rbrakk> \<Longrightarrow> \<lparr>s;f;[$EConstNum (ConstInt32 k), $EConstNum v, $(Store t (Some tp) a off)]\<rparr> \<leadsto> \<lparr>s;f;[Trap]\<rparr>"
  \<comment> \<open>\<open>load vector\<close>\<close>
| load_vec_Some:"\<lbrakk>smem_ind (f_inst f) = Some j; ((mems s)!j) = m; load_vec lv m (nat_of_int k) off = Some bs\<rbrakk> \<Longrightarrow> \<lparr>s;f;[$EConstNum (ConstInt32 k), $(Load_vec lv a off)]\<rparr> \<leadsto> \<lparr>s;f;[$EConstVec (ConstVec128 (deserialise_v128 bs))]\<rparr>"
| load_vec_None:"\<lbrakk>smem_ind (f_inst f) = Some j; ((mems s)!j) = m; load_vec lv m (nat_of_int k) off = None\<rbrakk> \<Longrightarrow> \<lparr>s;f;[$EConstNum (ConstInt32 k), $(Load_vec lv a off)]\<rparr> \<leadsto> \<lparr>s;f;[Trap]\<rparr>"
  \<comment> \<open>\<open>load lane vector\<close>\<close>
| load_lane_vec_Some:"\<lbrakk>smem_ind (f_inst f) = Some j; ((mems s)!j) = m; load m (nat_of_int k) off (vec_i_length svi) = Some bs\<rbrakk> \<Longrightarrow> \<lparr>s;f;[$EConstNum (ConstInt32 k), $EConstVec (ConstVec128 v), $(Load_lane_vec svi i a off)]\<rparr> \<leadsto> \<lparr>s;f;[$EConstVec (ConstVec128 (insert_lane_vec svi i bs v))]\<rparr>"
| load_lane_vec_None:"\<lbrakk>smem_ind (f_inst f) = Some j; ((mems s)!j) = m; load m (nat_of_int k) off (vec_i_length svi) = None\<rbrakk> \<Longrightarrow> \<lparr>s;f;[$EConstNum (ConstInt32 k), $EConstVec (ConstVec128 v), $(Load_lane_vec svi i a off)]\<rparr> \<leadsto> \<lparr>s;f;[Trap]\<rparr>"
  \<comment> \<open>\<open>store vector\<close>\<close>
| store_vec_Some:"\<lbrakk>smem_ind (f_inst f) = Some j; ((mems s)!j) = m; (store_serialise_vec sv v) = bs; store m (nat_of_int k) off bs (length bs) = Some mem'\<rbrakk> \<Longrightarrow> \<lparr>s;f;[$EConstNum (ConstInt32 k), $EConstVec (ConstVec128 v), $(Store_vec sv a off)]\<rparr> \<leadsto> \<lparr>s\<lparr>mems:= ((mems s)[j := mem'])\<rparr>;f;[]\<rparr>"
| store_vec_None:"\<lbrakk>smem_ind (f_inst f) = Some j; ((mems s)!j) = m; (store_serialise_vec sv v) = bs; store m (nat_of_int k) off bs (length bs) = None\<rbrakk> \<Longrightarrow> \<lparr>s;f;[$EConstNum (ConstInt32 k), $EConstVec (ConstVec128 v), $(Store_vec sv a off)]\<rparr> \<leadsto> \<lparr>s;f;[Trap]\<rparr>"
  \<comment> \<open>\<open>current_memory\<close>\<close>
| current_memory:"\<lbrakk>smem_ind (f_inst f) = Some j; ((mems s)!j) = m; mem_size m = n\<rbrakk> \<Longrightarrow> \<lparr>s;f;[ $(Current_memory)]\<rparr> \<leadsto> \<lparr>s;f;[$EConstNum (ConstInt32 (int_of_nat n))]\<rparr>"
  \<comment> \<open>\<open>grow_memory\<close>\<close>
| grow_memory:"\<lbrakk>smem_ind (f_inst f) = Some j; ((mems s)!j) = m; mem_size m = n; mem_grow m (nat_of_int c) = Some mem'\<rbrakk> \<Longrightarrow> \<lparr>s;f;[$EConstNum (ConstInt32 c), $(Grow_memory)]\<rparr> \<leadsto> \<lparr>s\<lparr>mems:= ((mems s)[j := mem'])\<rparr>;f;[$EConstNum (ConstInt32 (int_of_nat n))]\<rparr>"
  \<comment> \<open>\<open>grow_memory fail\<close>\<close>
| grow_memory_fail:"\<lbrakk>smem_ind (f_inst f) = Some j; ((mems s)!j) = m; mem_size m = n\<rbrakk> \<Longrightarrow> \<lparr>s;f;[$EConstNum (ConstInt32 c),$(Grow_memory)]\<rparr> \<leadsto> \<lparr>s;f;[$EConstNum (ConstInt32 int32_minus_one)]\<rparr>"
  \<comment> \<open>\<open>block\<close>\<close>
| block:"\<lbrakk>length vs = n; tb_tf (f_inst f) tb = (t1s _> t2s); length t1s = n; length t2s = m\<rbrakk> \<Longrightarrow> \<lparr>s;f;($C* vs) @ [$(Block tb es)]\<rparr> \<leadsto> \<lparr>s;f;[Label m [] (($C* vs) @ ($* es))]\<rparr>"
  \<comment> \<open>\<open>loop\<close>\<close>
| loop:"\<lbrakk>length vs = n; tb_tf (f_inst f) tb = (t1s _> t2s); length t1s = n; length t2s = m\<rbrakk> \<Longrightarrow> \<lparr>s;f;($C* vs) @ [$(Loop tb es)]\<rparr> \<leadsto> \<lparr>s;f;[Label n [$(Loop tb es)] (($C* vs) @ ($* es))]\<rparr>"
  (* The bad ones *)
  \<comment> \<open>\<open>inductive label reduction\<close>\<close>
| label:"\<lbrakk>\<lparr>s;f;es\<rparr> \<leadsto> \<lparr>s';f';es'\<rparr>; Lfilled k lholed es les; Lfilled k lholed es' les'\<rbrakk> \<Longrightarrow> \<lparr>s;f;les\<rparr> \<leadsto> \<lparr>s';f';les'\<rparr>"
  \<comment> \<open>\<open>inductive local reduction\<close>\<close>
| local:"\<lbrakk>\<lparr>s;f;es\<rparr> \<leadsto> \<lparr>s';f';es'\<rparr>\<rbrakk> \<Longrightarrow> \<lparr>s;f0;[Frame n f es]\<rparr> \<leadsto> \<lparr>s';f0;[Frame n f' es']\<rparr>"
  (* instantiation helpers *)
| init_mem_Some:"\<lbrakk>smem_ind (f_inst f) = Some j; ((mems s)!j) = m; store m n 0 bs (length bs) = Some mem'\<rbrakk> \<Longrightarrow> \<lparr>s;f;[Init_mem n bs]\<rparr> \<leadsto> \<lparr>s\<lparr>mems:= ((mems s)[j := mem'])\<rparr>;f;[]\<rparr>"
| init_mem_None:"\<lbrakk>smem_ind (f_inst f) = Some j; ((mems s)!j) = m; store m n 0 bs (length bs) = None\<rbrakk> \<Longrightarrow> \<lparr>s;f;[Init_mem n bs]\<rparr> \<leadsto> \<lparr>s;f;[Trap]\<rparr>"
| init_tab_Some:"\<lbrakk>stab_ind (f_inst f) = Some j; ((tabs s)!j) = t; store_tab t n icls = Some tab'\<rbrakk> \<Longrightarrow> \<lparr>s;f;[Init_tab n icls]\<rparr> \<leadsto> \<lparr>s\<lparr>tabs:= ((tabs s)[j := tab'])\<rparr>;f;[]\<rparr>"
| init_tab_None:"\<lbrakk>stab_ind (f_inst f) = Some j; ((tabs s)!j) = t; store_tab t n icls = None\<rbrakk> \<Longrightarrow> \<lparr>s;f;[Init_tab n icls]\<rparr> \<leadsto> \<lparr>s;f;[Trap]\<rparr>"

definition reduce_trans where
  "reduce_trans \<equiv> (\<lambda>(s,f,es) (s',f',es'). \<lparr>s;f;es\<rparr> \<leadsto> \<lparr>s';f';es'\<rparr>)^**"

definition reduce_irrtrans where
  "reduce_irrtrans \<equiv> (\<lambda>(s,f,es) (s',f',es'). \<lparr>s;f;es\<rparr> \<leadsto> \<lparr>s';f';es'\<rparr>)^++"

lemma reduce_irrtrans_trans:"reduce_irrtrans a b \<Longrightarrow> reduce_trans a b"
  unfolding reduce_irrtrans_def reduce_trans_def
  by simp

type_synonym v_stack = "v list"

abbreviation v_stack_to_es :: " v_stack \<Rightarrow> e list"
  where "v_stack_to_es v \<equiv> $C* (rev v)"


definition "computes cfg s' vs \<equiv> \<exists>f'. reduce_trans cfg (s', f', v_stack_to_es vs)"
  
definition "traps cfg s' \<equiv> \<exists>f'. reduce_trans cfg (s',f',[Trap])"

definition "empty_frame \<equiv> \<lparr>f_locs = [],f_inst = \<lparr> types = [], funcs = [], tabs = [], mems = [], globs = []\<rparr>\<rparr>"

definition "invoke_config s vargs i \<equiv> (s, empty_frame, ($C* vargs) @ [Invoke i])"

end
