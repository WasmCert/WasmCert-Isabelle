section \<open>WebAssembly Interpreter\<close>

theory Wasm_Interpreter imports Wasm begin

abbreviation expect :: "'a option \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'b" where
  "expect a f b \<equiv> (case a of
                     Some a' \<Rightarrow> f a'
                   | None \<Rightarrow> b)"

definition name :: "'a :: typerep \<Rightarrow> String.literal" where
  "name a = (case (typerep_of a) of Typerep.Typerep s _ \<Rightarrow> s)"

type_synonym v_stack = "v list"

datatype res_error =
  Error_invalid String.literal
| Error_invariant String.literal
| Error_exhaustion String.literal

datatype res_step =
  Res_crash res_error
| Res_trap String.literal
| Step_normal

datatype res =
  RCrash res_error
| RTrap String.literal
| RValue "v_stack"

definition crash_invalid where "crash_invalid \<equiv> Res_crash (Error_invalid (STR ''type system violation''))"
definition crash_invariant where "crash_invariant \<equiv> Res_crash (Error_invariant (STR ''interpreter invariant violation''))"
definition crash_exhaustion where "crash_exhaustion \<equiv> Res_crash (Error_exhaustion (STR ''call stack exhausted''))"

definition res_crash_fuel where "res_crash_fuel \<equiv> RCrash (Error_invariant (STR ''fuel exhausted''))"

lemmas[simp] = crash_invalid_def crash_invariant_def crash_exhaustion_def res_crash_fuel_def

definition app_v_s_drop :: "v_stack \<Rightarrow> (v_stack \<times> res_step)" where
  "app_v_s_drop v_s =
     (case v_s of
       v1#v_s' \<Rightarrow> (v_s', Step_normal)
     | _ \<Rightarrow> (v_s, crash_invalid))"

definition app_v_s_unop :: "unop \<Rightarrow> v_stack \<Rightarrow> (v_stack \<times> res_step)" where
  "app_v_s_unop unop v_s =
     (case v_s of
       v1#v_s' \<Rightarrow> ((app_unop unop v1)#v_s', Step_normal)
     | _ \<Rightarrow> (v_s, crash_invalid))"

definition app_v_s_testop :: "testop \<Rightarrow> v_stack \<Rightarrow> (v_stack \<times> res_step)" where
  "app_v_s_testop testop v_s =
     (case v_s of
       v1#v_s' \<Rightarrow> ((app_testop testop v1)#v_s', Step_normal)
     | _ \<Rightarrow> (v_s, crash_invalid))"

definition app_v_s_binop :: "binop \<Rightarrow> v_stack \<Rightarrow> (v_stack \<times> res_step)" where
  "app_v_s_binop binop v_s =
     (case v_s of
       v2#v1#v_s' \<Rightarrow>
         expect (app_binop binop v1 v2)
                (\<lambda>v. (v#v_s', Step_normal))
                (v_s', Res_trap (name binop))
     | _ \<Rightarrow> (v_s, crash_invalid))"

definition app_v_s_relop :: "relop \<Rightarrow> v_stack \<Rightarrow> (v_stack \<times> res_step)" where
  "app_v_s_relop relop v_s =
     (case v_s of
       v2#v1#v_s' \<Rightarrow> ((app_relop relop v1 v2)#v_s', Step_normal)
     | _ \<Rightarrow> (v_s, crash_invalid))"

definition app_v_s_cvtop :: "cvtop \<Rightarrow> t \<Rightarrow> t \<Rightarrow> (sat \<times> sx) option \<Rightarrow> v_stack \<Rightarrow> (v_stack \<times> res_step)" where
  "app_v_s_cvtop cvtop t1 t2 tp_sx v_s =
     (case v_s of
       v1#v_s' \<Rightarrow>
       (if types_agree t1 v1 then
         (case cvtop of
            Convert \<Rightarrow>
              expect (cvt t2 tp_sx v1)
                     (\<lambda>v. (v#v_s', Step_normal))
                     (v_s', Res_trap (name cvtop))
          | Reinterpret \<Rightarrow> if tp_sx = None then
                             ((wasm_deserialise (bits v1) t2)#v_s', Step_normal)
                           else (v_s, crash_invalid))
        else (v_s, crash_invalid))
     | _ \<Rightarrow> (v_s, crash_invalid))"

definition app_v_s_select :: "v_stack \<Rightarrow> (v_stack \<times> res_step)" where
  "app_v_s_select v_s =
     (case v_s of
       (ConstInt32 c)#v2#v1#v_s' \<Rightarrow>
         (if int_eq c 0 then (v2#v_s', Step_normal) else (v1#v_s', Step_normal))
     | _ \<Rightarrow> (v_s, crash_invalid))"

definition app_f_v_s_get_local :: "nat \<Rightarrow> f \<Rightarrow> v_stack \<Rightarrow> (v_stack \<times> res_step)" where
  "app_f_v_s_get_local k f v_s =
     (let locs = (f_locs f) in
     (if k < length locs
        then ((locs!k)#v_s, Step_normal)
        else (v_s, crash_invalid)))"

definition app_f_v_s_set_local :: "nat \<Rightarrow> f \<Rightarrow> v_stack \<Rightarrow> (f \<times> v_stack \<times> res_step)" where
  "app_f_v_s_set_local k f v_s =
     (let locs = (f_locs f) in
     (case v_s of
       v1#v_s' \<Rightarrow> if k < length locs
                  then (\<lparr> f_locs = locs[k := v1], f_inst = (f_inst f) \<rparr>, v_s', Step_normal)
                  else (f, v_s, crash_invalid)
     | _ \<Rightarrow> (f, v_s, crash_invalid)))"

definition app_v_s_tee_local :: "nat \<Rightarrow> v_stack \<Rightarrow> (v_stack \<times> e list \<times> res_step)" where
  "app_v_s_tee_local k v_s =
     (case v_s of
       v1#v_s' \<Rightarrow> (v1#v1#v_s', [$Set_local k], Step_normal)
     | _ \<Rightarrow> (v_s, [], crash_invalid))"

definition app_v_s_if :: "tf \<Rightarrow> b_e list \<Rightarrow> b_e list \<Rightarrow> v_stack \<Rightarrow> (v_stack \<times> e list \<times> res_step)" where
  "app_v_s_if tf es1 es2 v_s =
     (case v_s of
       (ConstInt32 c)#v_s' \<Rightarrow>
         (if int_eq c 0 then (v_s', [$(Block tf es2)], Step_normal) else (v_s', [$(Block tf es1)], Step_normal))
     | _ \<Rightarrow> (v_s, [], crash_invalid))"

definition app_v_s_br_if :: "nat \<Rightarrow> v_stack \<Rightarrow> (v_stack \<times> e list \<times> res_step)" where
  "app_v_s_br_if k v_s =
     (case v_s of
       (ConstInt32 c)#v_s' \<Rightarrow>
         (if int_eq c 0 then (v_s', [], Step_normal) else (v_s', [$(Br k)], Step_normal))
     | _ \<Rightarrow> (v_s, [], crash_invalid))"

definition app_v_s_br_table :: "nat list \<Rightarrow> nat \<Rightarrow> v_stack \<Rightarrow> (v_stack \<times> e list \<times> res_step)" where
  "app_v_s_br_table ks k v_s =
     (case v_s of
       (ConstInt32 c)#v_s' \<Rightarrow>
             let j = nat_of_int c in
                if j < length ks
                  then (v_s', [$Br (ks!j)], Step_normal)
                  else (v_s', [$Br k], Step_normal)
     | _ \<Rightarrow> (v_s, [], crash_invalid))"

definition app_f_call :: "nat \<Rightarrow> f \<Rightarrow> (e list \<times> res_step)" where
  "app_f_call k f = ([Invoke (sfunc_ind (f_inst f) k)], Step_normal)"

definition app_s_f_v_s_call_indirect :: "nat \<Rightarrow> tabinst list \<Rightarrow> cl list \<Rightarrow> f \<Rightarrow> v_stack \<Rightarrow> (v_stack \<times> e list \<times> res_step)" where
  "app_s_f_v_s_call_indirect k tinsts cls f v_s = 
          (let i = (f_inst f) in
           case v_s of
             (ConstInt32 c)#v_s' \<Rightarrow>
               (case (inst.tabs i) of
                  (j#_) => (case (tab_cl_ind tinsts j (nat_of_int c)) of
                             Some i_cl \<Rightarrow> (if (stypes i k = cl_type (cls!i_cl))
                                            then  (v_s', [(Invoke i_cl)], Step_normal)
                                            else (v_s', [], (Res_trap (STR ''call_indirect''))))
                           | None \<Rightarrow> (v_s', [], (Res_trap (STR ''call_indirect''))))
                | [] => (v_s, [], crash_invalid))
           | _ \<Rightarrow> (v_s, [], crash_invalid))"

definition app_s_f_v_s_get_global :: "nat \<Rightarrow> global list \<Rightarrow> f \<Rightarrow> v_stack \<Rightarrow> (v_stack \<times> res_step)" where
  "app_s_f_v_s_get_global k gs f v_s =  ((g_val (gs!(sglob_ind (f_inst f) k)))#v_s, Step_normal)"

definition app_s_f_v_s_set_global :: "nat \<Rightarrow> global list \<Rightarrow> f \<Rightarrow> v_stack \<Rightarrow> (global list \<times>  v_stack \<times> res_step)" where
  "app_s_f_v_s_set_global k gs f v_s =
     (case v_s of
        v1#v_s' \<Rightarrow> (update_glob gs (f_inst f) k v1, v_s', Step_normal)
      | _ \<Rightarrow> (gs, v_s, crash_invalid))"

definition app_s_f_v_s_load :: "t \<Rightarrow> nat \<Rightarrow> mem list \<Rightarrow> f \<Rightarrow>  v_stack \<Rightarrow> (v_stack \<times> res_step)" where
  "app_s_f_v_s_load t off ms f v_s = 
          (let i = (f_inst f) in
           case v_s of
             (ConstInt32 c)#v_s' \<Rightarrow>
               (case smem_ind i of
                  Some j => expect (load (ms!j) (nat_of_int c) off (t_length t))
                                  (\<lambda>bs. ((wasm_deserialise bs t)#v_s', Step_normal))
                                  (v_s', (Res_trap (STR ''load'')))
                | None => (v_s, crash_invalid))
           | _ \<Rightarrow> (v_s, crash_invalid))"

definition app_s_f_v_s_load_packed :: "t \<Rightarrow> tp \<Rightarrow> sx \<Rightarrow> nat \<Rightarrow> mem list \<Rightarrow> f \<Rightarrow>  v_stack \<Rightarrow> (v_stack \<times> res_step)" where
  "app_s_f_v_s_load_packed t tp sx off ms f v_s = 
          (let i = (f_inst f) in
           case v_s of
             (ConstInt32 c)#v_s' \<Rightarrow>
               (case smem_ind i of
                  Some j => expect (load_packed sx (ms!j) (nat_of_int c) off (tp_length tp) (t_length t))
                                  (\<lambda>bs. ((wasm_deserialise bs t)#v_s', Step_normal))
                                  (v_s', (Res_trap (STR ''load'')))
                | None => (v_s, crash_invalid))
           | _ \<Rightarrow> (v_s, crash_invalid))"

definition app_s_f_v_s_load_maybe_packed :: "t \<Rightarrow> (tp \<times> sx) option \<Rightarrow> nat \<Rightarrow> mem list \<Rightarrow> f \<Rightarrow>  v_stack \<Rightarrow> (v_stack \<times> res_step)" where
  "app_s_f_v_s_load_maybe_packed t tp_sx off ms f v_s =
     (case tp_sx of
        Some (tp, sx) \<Rightarrow> app_s_f_v_s_load_packed t tp sx off ms f v_s
      | None \<Rightarrow> app_s_f_v_s_load t off ms f v_s)"


definition app_s_f_v_s_store :: "t \<Rightarrow> nat \<Rightarrow> mem list \<Rightarrow> f \<Rightarrow>  v_stack \<Rightarrow> (mem list \<times> v_stack \<times> res_step)" where
  "app_s_f_v_s_store t off ms f v_s = 
          (let i = (f_inst f) in
           case v_s of
             v#(ConstInt32 c)#v_s' \<Rightarrow>
               (if (types_agree t v) then
                 (case smem_ind i of
                    Some j => expect (store (ms!j) (nat_of_int c) off (bits v) (t_length t))
                                    (\<lambda>mem'. ((ms[j := mem']), v_s', Step_normal))
                                    (ms, v_s', Res_trap (STR ''store''))
                  | None => (ms, v_s, crash_invalid))
                else (ms, v_s, crash_invalid))
           | _ \<Rightarrow> (ms, v_s, crash_invalid))"

definition app_s_f_v_s_store_packed :: "t \<Rightarrow> tp \<Rightarrow> nat \<Rightarrow> mem list \<Rightarrow> f \<Rightarrow>  v_stack \<Rightarrow> (mem list \<times> v_stack \<times> res_step)" where
  "app_s_f_v_s_store_packed t tp off ms f v_s = 
          (let i = (f_inst f) in
           case v_s of
             v#(ConstInt32 c)#v_s' \<Rightarrow>
               (if (types_agree t v) then
                 (case smem_ind i of
                    Some j => expect (store_packed (ms!j) (nat_of_int c) off (bits v) (tp_length tp))
                                    (\<lambda>mem'. ((ms[j := mem']), v_s', Step_normal))
                                    (ms, v_s', Res_trap (STR ''store''))
                  | None => (ms, v_s, crash_invalid))
                else (ms, v_s, crash_invalid))
           | _ \<Rightarrow> (ms, v_s, crash_invalid))"

definition app_s_f_v_s_store_maybe_packed :: "t \<Rightarrow> tp option \<Rightarrow> nat \<Rightarrow> mem list \<Rightarrow> f \<Rightarrow>  v_stack \<Rightarrow> (mem list \<times> v_stack \<times> res_step)" where
  "app_s_f_v_s_store_maybe_packed t tp_opt off ms f v_s =
     (case tp_opt of
        Some tp \<Rightarrow> app_s_f_v_s_store_packed t tp off ms f v_s
      | None \<Rightarrow> app_s_f_v_s_store t off ms f v_s)"

definition app_s_f_v_s_mem_size :: "mem list \<Rightarrow> f \<Rightarrow>  v_stack \<Rightarrow> (v_stack \<times> res_step)" where
  "app_s_f_v_s_mem_size ms f v_s = 
          (let i = (f_inst f) in
          (case smem_ind i of
             Some j => (((ConstInt32 (int_of_nat (mem_size (ms!j))))#v_s), Step_normal)
           | None => (v_s, crash_invalid)))"

definition app_s_f_v_s_mem_grow :: "mem list \<Rightarrow> f \<Rightarrow> v_stack \<Rightarrow> (mem list \<times> v_stack \<times> res_step)" where
  "app_s_f_v_s_mem_grow ms f v_s = 
          (let i = (f_inst f) in
           case v_s of
             (ConstInt32 c)#v_s' \<Rightarrow>
               (case smem_ind i of
                  Some j => let l = (mem_size (ms!j)) in
                           expect (mem_grow (ms!j) (nat_of_int c))
                                  (\<lambda>mem'. ((ms[j := mem']), (ConstInt32 (int_of_nat l))#v_s', Step_normal))
                                  (ms, (ConstInt32 int32_minus_one)#v_s', Step_normal)
                | None => (ms, v_s, crash_invalid))
           | _ \<Rightarrow> (ms, v_s, crash_invalid))"

definition app_s_f_init_mem :: "nat \<Rightarrow> byte list \<Rightarrow> mem list \<Rightarrow> f \<Rightarrow> (mem list \<times> res_step)" where
  "app_s_f_init_mem off bs ms f = 
     (let i = (f_inst f) in
     (case smem_ind i of
        Some j => expect (store (ms!j) off 0 bs (length bs))
                        (\<lambda>mem'. ((ms[j := mem']), Step_normal))
                        (ms, Res_trap (STR ''init_mem''))
      | None => (ms, crash_invalid)))"

definition app_s_f_init_tab :: "nat \<Rightarrow> i list \<Rightarrow> tabinst list \<Rightarrow> f \<Rightarrow> (tabinst list \<times> res_step)" where
  "app_s_f_init_tab off icls ts f = 
     (let i = (f_inst f) in
     (case stab_ind i of
        Some j => expect (store_tab (ts!j) off icls)
                        (\<lambda>t'. ((ts[j := t']), Step_normal))
                        (ts, Res_trap (STR ''init_tab''))
      | None => (ts, crash_invalid)))"

(* 0: local value stack, 1: current redex, 2: tail of redex *)
datatype redex = Redex v_stack "e list" "b_e list"

(* 0: outer value stack, 1: outer tail of redex, 2: label arity, 3: label continuation *)
(* corresponds to <0> label <2> <3> ... end <1>  *)
datatype label_context = Label_context v_stack "b_e list" (label_arity:nat) "b_e list"

(* 0: redex, 1: label contexts, 2: frame arity, 3: frame *)
datatype frame_context = Frame_context redex "label_context list" (frame_arity:nat) f

definition frame_arity_outer :: "frame_context \<Rightarrow> frame_context list \<Rightarrow> nat" where
  "frame_arity_outer fc fcs \<equiv> if fcs = [] then (frame_arity fc) else (frame_arity (last fcs))"

type_synonym depth = nat
type_synonym fuel = nat

datatype config = Config depth s frame_context "frame_context list"

type_synonym res_step_tuple = "config \<times> res_step"

type_synonym res_tuple = "config \<times> res"

fun split_vals :: "b_e list \<Rightarrow> v list \<times> b_e list" where
  "split_vals ((C v)#es) = (let (vs', es') = split_vals es in (v#vs', es'))"
| "split_vals es = ([], es)"

fun split_vals_e :: "e list \<Rightarrow> v list \<times> e list" where
  "split_vals_e (($ C v)#es) = (let (vs', es') = split_vals_e es in (v#vs', es'))"
| "split_vals_e es = ([], es)"

fun split_v_s_b_s_aux :: "v_stack \<Rightarrow> b_e list \<Rightarrow> v_stack \<times> b_e list" where
  "split_v_s_b_s_aux v_s ((C v)#b_es) = split_v_s_b_s_aux (v#v_s) b_es"
| "split_v_s_b_s_aux v_s es = (v_s, es)"

fun split_v_s_b_s :: "b_e list \<Rightarrow> v_stack \<times> b_e list" where
  "split_v_s_b_s es = split_v_s_b_s_aux [] es"

fun split_n :: "v list \<Rightarrow> nat \<Rightarrow> v list \<times> v list" where
  "split_n [] n = ([], [])"
| "split_n es 0 = ([], es)"
| "split_n (e#es) (Suc n) = (let (es', es'') = split_n es n in (e#es', es''))"

lemma split_n_conv_take_drop: "split_n es n = (take n es, drop n es)"
  by (induction es n rule: split_n.induct, simp_all)

lemma split_n_length:
  assumes "split_n es n = (es1, es2)" "length es \<ge> n"
  shows "length es1 = n"
  using assms
  unfolding split_n_conv_take_drop
  by fastforce

lemma split_n_conv_app:
  assumes "split_n es n = (es1, es2)"
  shows "es = es1@es2"
  using assms
  unfolding split_n_conv_take_drop
  by auto

lemma app_conv_split_n:
  assumes "es = es1@es2"
  shows "split_n es (length es1) = (es1, es2)"
  using assms
  unfolding split_n_conv_take_drop
  by auto

lemma split_vals_const_list: "split_vals (map EConst vs) = (vs, [])"
  by (induction vs, simp_all)

lemma split_vals_e_const_list: "split_vals_e ($C* vs) = (vs, [])"
  by (induction vs, simp_all)

lemma split_v_s_b_s_aux_conv_app:
  assumes "split_v_s_b_s_aux v_s_aux b_es = (v_s, b_es')"
  shows "(map EConst (rev v_s_aux))@b_es = (map EConst (rev v_s))@b_es'"
  using assms
  by (induction v_s_aux b_es rule: split_v_s_b_s_aux.induct) auto

lemma split_v_s_b_s_conv_app:
  assumes "split_v_s_b_s b_es = (v_s, b_es')"
  shows "b_es = (map EConst (rev v_s))@b_es'"
  using assms split_v_s_b_s_aux_conv_app
  by fastforce

lemma split_vals_e_conv_app:
  assumes "split_vals_e xs = (as, bs)"
  shows "xs = ($C* as)@bs"
  using assms
proof (induction xs arbitrary: as rule: split_vals_e.induct)
  case (1 v es)
  obtain as' bs' where "split_vals_e es = (as', bs')"
    by (meson surj_pair)
  thus ?case
    using 1
    by fastforce
qed simp_all

abbreviation v_stack_to_b_es :: " v_stack \<Rightarrow> b_e list"
  where "v_stack_to_b_es v \<equiv> map (\<lambda>v. C v) (rev v)"

abbreviation v_stack_to_es :: " v_stack \<Rightarrow> e list"
  where "v_stack_to_es v \<equiv> $C* (rev v)"

definition e_is_trap :: "e \<Rightarrow> bool" where
  "e_is_trap e = (case e of Trap \<Rightarrow> True | _ \<Rightarrow> False)"

definition es_is_trap :: "e list \<Rightarrow> bool" where
  "es_is_trap es = (case es of [e] \<Rightarrow> e_is_trap e | _ \<Rightarrow> False)"

lemma[simp]: "e_is_trap e = (e = Trap)"
  using e_is_trap_def
  by (cases "e") auto

lemma[simp]: "es_is_trap es = (es = [Trap])"
proof (cases es)
  case Nil
  thus ?thesis
    using es_is_trap_def
    by auto
next
  case outer_Cons:(Cons a list)
  thus ?thesis
  proof (cases list)
    case Nil
    thus ?thesis
      using outer_Cons es_is_trap_def
      by auto
  next
    case (Cons a' list')
    thus ?thesis
      using es_is_trap_def outer_Cons
      by auto
  qed
qed
(*
definition mem_grow_impl:: "mem \<Rightarrow> nat \<Rightarrow> mem option" where
  "mem_grow_impl m n = Some (mem_grow m n)"

lemma mem_grow_impl_correct:
  "(mem_grow_impl m n = Some m') \<Longrightarrow> (mem_grow m n = m')"
  unfolding mem_grow_impl_def
*)
axiomatization 
  host_apply_impl:: "s \<Rightarrow> tf \<Rightarrow> host \<Rightarrow> v list \<Rightarrow> (s \<times> v list) option" where
  host_apply_impl_correct:"(host_apply_impl s tf h vs = Some m') \<Longrightarrow> (\<exists>hs. host_apply s tf h vs hs (Some m'))"

fun update_redex_step :: "redex \<Rightarrow> v_stack \<Rightarrow> e list \<Rightarrow> redex" where
  "update_redex_step (Redex v_s es b_es) v_s' es_cont = (Redex v_s' (es_cont@es) b_es)"

fun update_fc_step :: "frame_context \<Rightarrow> v_stack \<Rightarrow> e list \<Rightarrow> frame_context" where
  "update_fc_step (Frame_context rdx lcs nf f) v_s' es_cont = (Frame_context (update_redex_step rdx v_s' es_cont) lcs nf f)"

fun update_redex_return :: "redex \<Rightarrow> v_stack \<Rightarrow> redex" where
  "update_redex_return (Redex v_s es b_es) v_s' = (Redex (v_s'@v_s) es b_es)"

fun update_fc_return :: "frame_context \<Rightarrow> v_stack \<Rightarrow> frame_context" where
  "update_fc_return (Frame_context rdx lcs nf f) v_s' = (Frame_context (update_redex_return rdx v_s') lcs nf f)"

fun update_fcs_return :: "frame_context list \<Rightarrow> v_stack \<Rightarrow> frame_context list" where
  "update_fcs_return [] v_s = []"
| "update_fcs_return (fc#fcs) v_s = (update_fc_return fc v_s)#fcs"

fun update_redex_trap :: "redex \<Rightarrow> redex" where
  "update_redex_trap (Redex v_s es b_es) = (Redex [] es b_es)"

fun update_fc_trap :: "frame_context \<Rightarrow> frame_context" where
  "update_fc_trap (Frame_context rdx lcs nf f) = (Frame_context (update_redex_trap rdx) lcs nf f)"

fun update_fcs_trap :: "frame_context list \<Rightarrow> frame_context list" where
  "update_fcs_trap [] = []"
| "update_fcs_trap (fc#fcs) = (update_fc_trap fc)#fcs"

fun run_step_b_e :: "b_e \<Rightarrow> config \<Rightarrow> res_step_tuple" where
  "run_step_b_e b_e (Config d s fc fcs) =
    (case fc of (Frame_context (Redex v_s es b_es) lcs nf f) \<Rightarrow>
    (case b_e of
      (Unop t op) \<Rightarrow>
        let (v_s', res) = (app_v_s_unop op v_s) in
        ((Config d s (update_fc_step fc v_s' []) fcs), res)

    | (Binop t op) \<Rightarrow>
        let (v_s', res) = (app_v_s_binop op v_s) in
        ((Config d s (update_fc_step fc v_s' []) fcs), res)

    | (Testop t op) \<Rightarrow>
        let (v_s', res) = (app_v_s_testop op v_s) in
        ((Config d s (update_fc_step fc v_s' []) fcs), res)

    | (Relop t op) \<Rightarrow>
        let (v_s', res) = (app_v_s_relop op v_s) in
        ((Config d s (update_fc_step fc v_s' []) fcs), res)

    | (Cvtop t2 op t1 tp_sx) \<Rightarrow>
        let (v_s', res) = (app_v_s_cvtop op t1 t2 tp_sx v_s) in
        ((Config d s (update_fc_step fc v_s' []) fcs), res)

    | (Unreachable) \<Rightarrow>
        (Config d s fc fcs, Res_trap (STR ''unreachable''))

    | (Nop) \<Rightarrow>
        (Config d s fc fcs, Step_normal)

    | (Drop) \<Rightarrow>
        let (v_s', res) = (app_v_s_drop v_s) in
        ((Config d s (update_fc_step fc v_s' []) fcs), res)

    | (Select) \<Rightarrow>
        let (v_s', res) = (app_v_s_select v_s) in
        ((Config d s (update_fc_step fc v_s' []) fcs), res)

    | (Block (t1s _> t2s) b_ebs) \<Rightarrow>
        if es \<noteq> [] then (Config d s fc fcs, crash_invariant)
        else
          let n = length t1s in
          let m = length t2s in
          if (length v_s \<ge> n) then
            let (v_bs, v_s') = split_n v_s n in
            let lc = Label_context v_s' b_es m [] in 
            let fc' = Frame_context (Redex v_bs [] b_ebs) (lc#lcs) nf f in
            (Config d s fc' fcs, Step_normal)
          else (Config d s fc fcs, crash_invalid)

    | (Loop (t1s _> t2s) b_els) \<Rightarrow>
        if es \<noteq> [] then (Config d s fc fcs, crash_invariant)
        else
          let n = length t1s in
          let m = length t2s in
          if (length v_s \<ge> n) then
            let (v_bs, v_s') = split_n v_s n in
            let lc = Label_context v_s' b_es n [(Loop (t1s _> t2s) b_els)] in 
            let fc' = Frame_context (Redex v_bs [] b_els) (lc#lcs) nf f in
            (Config d s fc' fcs, Step_normal)
          else (Config d s fc fcs, crash_invalid)

    | (If tf es1 es2) \<Rightarrow>
        let (v_s', es_cont, res) = (app_v_s_if tf es1 es2 v_s) in
        (Config d s (update_fc_step fc v_s' es_cont) fcs, res)

    | (Br k) \<Rightarrow>
        if (length lcs > k) then
          case (lcs!k) of (Label_context v_ls b_els nl b_ecls) \<Rightarrow>
          if (length v_s \<ge> nl) then
            let v_s' = (take nl v_s) in
            let fc' = Frame_context (Redex (v_s'@v_ls) [] (b_ecls@b_els)) (drop (Suc k) lcs) nf f in
            (Config d s fc' fcs, Step_normal)
          else
            (Config d s fc fcs, crash_invalid)
        else
          (Config d s fc fcs, crash_invalid)

    | (Br_if k) \<Rightarrow>
        let (v_s', es_cont, res) = (app_v_s_br_if k v_s) in
        (Config d s (update_fc_step fc v_s' es_cont) fcs, res)

    | (Br_table ks k) \<Rightarrow>
        let (v_s', es_cont, res) = (app_v_s_br_table ks k v_s) in
        (Config d s (update_fc_step fc v_s' es_cont) fcs, res)

    | (Call k) \<Rightarrow>
        let (es_cont, res) = (app_f_call k f) in
        (Config d s (update_fc_step fc v_s es_cont) fcs, res)

    | (Call_indirect k) \<Rightarrow>
        let (v_s', es_cont, res) = (app_s_f_v_s_call_indirect k (tabs s) (funcs s) f v_s) in
        (Config d s (update_fc_step fc v_s' es_cont) fcs, res)

    | (Return) \<Rightarrow>
        (case fcs of
           [] \<Rightarrow> (Config d s fc fcs, crash_invalid)
         | fc'#fcs' \<Rightarrow> if (length v_s \<ge> nf) then
                         (Config (Suc d) s (update_fc_return fc' (take nf v_s)) fcs', Step_normal)
                       else (Config d s fc fcs, crash_invalid))

    | (Get_local k) \<Rightarrow>
        let (v_s', res) = (app_f_v_s_get_local k f v_s) in
        (Config d s (update_fc_step fc v_s' []) fcs, res)

    | (Set_local k) \<Rightarrow>
        let (f', v_s', res) = (app_f_v_s_set_local k f v_s) in
        let fc' = Frame_context (Redex v_s' es b_es) lcs nf f' in
        (Config d s fc' fcs, res)

    | (Tee_local k) \<Rightarrow>
        let (v_s', es_cont, res) = (app_v_s_tee_local k v_s) in
        (Config d s (update_fc_step fc v_s' es_cont) fcs, res)

    | (Get_global k) \<Rightarrow>
        let (v_s', res) = (app_s_f_v_s_get_global k (globs s) f v_s) in
        (Config d s (update_fc_step fc v_s' []) fcs, res)

    | (Set_global k) \<Rightarrow>
        let (gs', v_s', res) = (app_s_f_v_s_set_global k (globs s) f v_s) in
        (Config d (s\<lparr>globs:=gs'\<rparr>) (update_fc_step fc v_s' []) fcs, res)

    | (Load t tp_sx a off) \<Rightarrow>
        let (v_s', res) = (app_s_f_v_s_load_maybe_packed t tp_sx off (mems s) f v_s) in
        (Config d s (update_fc_step fc v_s' []) fcs, res)

    | (Store t tp a off) \<Rightarrow>
        let (ms', v_s', res) = (app_s_f_v_s_store_maybe_packed t tp off (mems s) f v_s) in
        (Config d (s\<lparr>mems:=ms'\<rparr>) (update_fc_step fc v_s' []) fcs, res)

    | (Current_memory) \<Rightarrow>
        let (v_s', res) = (app_s_f_v_s_mem_size (mems s) f v_s) in
        (Config d s (update_fc_step fc v_s' []) fcs, res)

    | (Grow_memory) \<Rightarrow>
        let (ms', v_s', res) = (app_s_f_v_s_mem_grow (mems s) f v_s) in
        (Config d (s\<lparr>mems:=ms'\<rparr>) (update_fc_step fc v_s' []) fcs, res)

    | _ \<Rightarrow> (Config d s fc fcs, crash_invariant)))"

fun run_step_e :: "e \<Rightarrow> config \<Rightarrow> res_step_tuple" where
  "run_step_e e (Config d s fc fcs) =
    (case fc of Frame_context (Redex v_s es b_es) lcs nf f \<Rightarrow>
    (case e of
       Basic b_e \<Rightarrow> run_step_b_e b_e (Config d s fc fcs)
     | Invoke i_cl \<Rightarrow>
         (case (funcs s!i_cl) of
             Func_native i' (t1s _> t2s) ts es_f \<Rightarrow>
               (case d of
                 Suc d' \<Rightarrow>
                   (let n = length t1s in
                    let m = length t2s in
                    if (length v_s \<ge> n) then
                      let (v_fs, v_s') = split_n v_s n in
                      let fc' = Frame_context (Redex v_s' es b_es) lcs nf f in
                      let zs = n_zeros ts in
                      let ff = \<lparr> f_locs = ((rev v_fs)@zs), f_inst = i'\<rparr> in
                      let fcf = Frame_context (Redex [] [] [Block ([] _> t2s) es_f]) [] m ff in
                      (Config d' s fcf (fc'#fcs), Step_normal)
                    else
                      (Config d s fc fcs, crash_invalid))
               | 0 \<Rightarrow> (Config d s fc fcs, crash_exhaustion))
           | Func_host (t1s _> t2s) h \<Rightarrow>
               let n = length t1s in
               let m = length t2s in
               if length v_s \<ge> n
                 then
                   let (v_fs, v_s') = split_n v_s n in
                   case host_apply_impl s (t1s _> t2s) h (rev v_fs) of
                     Some (s',rvs) \<Rightarrow> 
                       if list_all2 types_agree t2s rvs
                         then
                           let fc' = Frame_context (Redex ((rev rvs)@v_s') es b_es) lcs nf f in
                           (Config d s' fc' fcs, Step_normal)
                         else
                           (Config d s' fc fcs, crash_invalid)
                   | None \<Rightarrow> (Config d s (Frame_context (Redex v_s' es b_es) lcs nf f) fcs, Res_trap (STR ''host_apply''))
                 else
                    (Config d s fc fcs, crash_invalid))
     | Init_mem n bs \<Rightarrow>
        let (ms', res) = (app_s_f_init_mem n bs (mems s) f) in
        (Config d (s\<lparr>mems:=ms'\<rparr>) fc fcs, res)
     | Init_tab n icls \<Rightarrow>
        let (ts', res) = (app_s_f_init_tab n icls (tabs s) f) in
        (Config d (s\<lparr>tabs:=ts'\<rparr>) fc fcs, res)
     | _ \<Rightarrow> (Config d s fc fcs, crash_invariant)))"
(* should never produce Label, Frame, or Trap *)

function(sequential) run_iter :: "fuel \<Rightarrow> config \<Rightarrow> res_tuple" where
  "run_iter (Suc n) cfg =
     (case cfg of
        (Config d s (Frame_context (Redex v_s es b_es) lcs nf f) fcs) \<Rightarrow>
     (case es of
        [] \<Rightarrow> (case b_es of
                 [] \<Rightarrow> (case lcs of
                          [] \<Rightarrow> (case fcs of
\<comment> \<open> stack values in the outermost frame \<close>
                                   [] \<Rightarrow> ((Config d s (Frame_context (Redex v_s [] []) [] nf f) []), RValue v_s)
\<comment> \<open> stack values returned from an inner frame \<close>
                                 | fc'#fcs' \<Rightarrow> run_iter n (Config (Suc d) s (update_fc_return fc' v_s) fcs'))
\<comment> \<open> stack values returned from an inner label \<close>
                        | (Label_context v_ls b_els nl b_elcs)#lcs' \<Rightarrow> (let f_new = Frame_context (Redex (v_s@v_ls) [] b_els) lcs' nf f in
                                                             run_iter n (Config d s f_new fcs)))
\<comment> \<open> run a step of regular code \<close>
               | b_es \<Rightarrow> (case split_v_s_b_s b_es of
                            (v_s',[]) \<Rightarrow> run_iter n (Config d s (Frame_context (Redex (v_s'@v_s) [] []) lcs nf f) fcs)
                          | (v_s',b_e#b_es') \<Rightarrow> (let (cfg', res) = run_step_b_e b_e (Config d s (Frame_context (Redex (v_s'@v_s) [] b_es') lcs nf f) fcs) in
                                                (case res of
                                                   Step_normal \<Rightarrow> run_iter n cfg'
                                                 | Res_trap str \<Rightarrow> (cfg', RTrap str)
                                                 | Res_crash str \<Rightarrow> (cfg', RCrash str)))))
\<comment> \<open> run a step of the intermediate reduct \<close>
      | e#es' \<Rightarrow> (let (cfg', res) = run_step_e e (Config d s (Frame_context (Redex v_s es' b_es) lcs nf f) fcs) in
                      (case res of
                         Step_normal \<Rightarrow> run_iter n cfg'
                       | Res_trap str \<Rightarrow> (cfg', RTrap str)
                       | Res_crash str \<Rightarrow> (cfg', RCrash str)))))"

\<comment> \<open> out of fuel \<close>
| "run_iter 0 cfg = (cfg, res_crash_fuel)"

  by pat_completeness auto
termination
  by (relation "measure (\<lambda>p. fst p)") auto

fun run_v :: "fuel \<Rightarrow> depth \<Rightarrow> (s \<times> f \<times> b_e list) \<Rightarrow> (s \<times> res)" where
  "run_v n d (s, f, b_es) =
     (let (cfg',res) = run_iter n (Config d s (Frame_context (Redex [] [] b_es) [] 0 f) []) in
      case cfg' of (Config d s fc fcs) \<Rightarrow> (s,res))"

definition "empty_frame \<equiv> \<lparr>f_locs = [],f_inst = \<lparr> types = [], funcs = [], tabs = [], mems = [], globs = []\<rparr>\<rparr>"

fun run_invoke_v :: "fuel \<Rightarrow> depth \<Rightarrow> (s \<times> v list \<times> i) \<Rightarrow> (s \<times> res)" where
  "run_invoke_v n d (s, vs, i) =
     (let (cfg',res) = run_iter n (Config d s (Frame_context (Redex (rev vs) [Invoke i] []) [] 0 empty_frame) []) in
      case cfg' of (Config d s fc fcs) \<Rightarrow> (s,res))"

end
