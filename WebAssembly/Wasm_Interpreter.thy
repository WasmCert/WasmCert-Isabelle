section \<open>WebAssembly Interpreter\<close>

theory Wasm_Interpreter imports Wasm begin

abbreviation expect :: "'a option \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'b" where
  "expect a f b \<equiv> (case a of
                     Some a' \<Rightarrow> f a'
                   | None \<Rightarrow> b)"

definition name :: "'a :: typerep \<Rightarrow> String.literal" where
  "name a = (case (typerep_of a) of Typerep.Typerep s _ \<Rightarrow> s)"

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
       (V_num v1)#v_s' \<Rightarrow> ((V_num (app_unop unop v1))#v_s', Step_normal)
     | _ \<Rightarrow> (v_s, crash_invalid))"

definition app_v_s_testop :: "testop \<Rightarrow> v_stack \<Rightarrow> (v_stack \<times> res_step)" where
  "app_v_s_testop testop v_s =
     (case v_s of
       (V_num v1)#v_s' \<Rightarrow> ((V_num (app_testop testop v1))#v_s', Step_normal)
     | _ \<Rightarrow> (v_s, crash_invalid))"

definition app_v_s_binop :: "binop \<Rightarrow> v_stack \<Rightarrow> (v_stack \<times> res_step)" where
  "app_v_s_binop binop v_s =
     (case v_s of
       (V_num v2)#(V_num v1)#v_s' \<Rightarrow>
         expect (app_binop binop v1 v2)
                (\<lambda>v. ((V_num v)#v_s', Step_normal))
                (v_s', Res_trap (name binop))
     | _ \<Rightarrow> (v_s, crash_invalid))"

definition app_v_s_relop :: "relop \<Rightarrow> v_stack \<Rightarrow> (v_stack \<times> res_step)" where
  "app_v_s_relop relop v_s =
     (case v_s of
       (V_num v2)#(V_num v1)#v_s' \<Rightarrow> ((V_num (app_relop relop v1 v2))#v_s', Step_normal)
     | _ \<Rightarrow> (v_s, crash_invalid))"

definition app_v_s_cvtop :: "cvtop \<Rightarrow> t_num \<Rightarrow> t_num \<Rightarrow> (sat \<times> sx) option \<Rightarrow> v_stack \<Rightarrow> (v_stack \<times> res_step)" where
  "app_v_s_cvtop cvtop t1 t2 tp_sx v_s =
     (case v_s of
       (V_num v1)#v_s' \<Rightarrow>
       (if (typeof_num v1 = t1) then
         (case cvtop of
            Convert \<Rightarrow>
              expect (cvt t2 tp_sx v1)
                     (\<lambda>v. ((V_num v)#v_s', Step_normal))
                     (v_s', Res_trap (name cvtop))
          | Reinterpret \<Rightarrow> if tp_sx = None then
                             ((V_num (wasm_reinterpret t2 v1))#v_s', Step_normal)
                           else (v_s, crash_invalid))
        else (v_s, crash_invalid))
     | _ \<Rightarrow> (v_s, crash_invalid))"

definition app_v_s_unop_vec :: "unop_vec \<Rightarrow> v_stack \<Rightarrow> (v_stack \<times> res_step)" where
  "app_v_s_unop_vec op v_s =
     (case v_s of
       (V_vec v1)#v_s' \<Rightarrow> ((V_vec (app_unop_vec op v1))#v_s', Step_normal)
     | _ \<Rightarrow> (v_s, crash_invalid))"

definition app_v_s_binop_vec :: "binop_vec \<Rightarrow> v_stack \<Rightarrow> (v_stack \<times> res_step)" where
  "app_v_s_binop_vec op v_s =
     (case v_s of
       (V_vec v2)#(V_vec v1)#v_s' \<Rightarrow>
         expect (app_binop_vec op v1 v2)
                (\<lambda>v. ((V_vec v)#v_s', Step_normal))
                (v_s', Res_trap (STR ''binop_vec''))
     | _ \<Rightarrow> (v_s, crash_invalid))"

definition app_v_s_ternop_vec :: "ternop_vec \<Rightarrow> v_stack \<Rightarrow> (v_stack \<times> res_step)" where
  "app_v_s_ternop_vec op v_s =
     (case v_s of
       (V_vec v3)#(V_vec v2)#(V_vec v1)#v_s' \<Rightarrow> ((V_vec (app_ternop_vec op v1 v2 v3))#v_s', Step_normal)
     | _ \<Rightarrow> (v_s, crash_invalid))"

definition app_v_s_test_vec :: "testop_vec \<Rightarrow> v_stack \<Rightarrow> (v_stack \<times> res_step)" where
  "app_v_s_test_vec op v_s =
     (case v_s of
       (V_vec v1)#v_s' \<Rightarrow> ((V_num (ConstInt32  (app_test_vec op v1)))#v_s', Step_normal)
     | _ \<Rightarrow> (v_s, crash_invalid))"

definition app_v_s_shift_vec :: "shiftop_vec \<Rightarrow> v_stack \<Rightarrow> (v_stack \<times> res_step)" where
  "app_v_s_shift_vec op v_s =
     (case v_s of
       (V_num (ConstInt32 v2))#(V_vec v1)#v_s' \<Rightarrow> ((V_vec (app_shift_vec op v1 v2))#v_s', Step_normal)
     | _ \<Rightarrow> (v_s, crash_invalid))"

definition app_v_s_splat_vec :: "shape_vec \<Rightarrow> v_stack \<Rightarrow> (v_stack \<times> res_step)" where
  "app_v_s_splat_vec sv v_s =
     (case v_s of
       (V_num v1)#v_s' \<Rightarrow> ((V_vec (app_splat_vec sv v1))#v_s', Step_normal)
     | _ \<Rightarrow> (v_s, crash_invalid))"

definition app_v_s_extract_vec :: "shape_vec \<Rightarrow> sx \<Rightarrow> i \<Rightarrow> v_stack \<Rightarrow> (v_stack \<times> res_step)" where
  "app_v_s_extract_vec sv sx i v_s =
     (case v_s of
       (V_vec v1)#v_s' \<Rightarrow> ((V_num (app_extract_vec sv sx i v1))#v_s', Step_normal)
     | _ \<Rightarrow> (v_s, crash_invalid))"

definition app_v_s_replace_vec :: "shape_vec \<Rightarrow> i \<Rightarrow> v_stack \<Rightarrow> (v_stack \<times> res_step)" where
  "app_v_s_replace_vec sv i v_s =
     (case v_s of
       (V_num v2)#(V_vec v1)#v_s' \<Rightarrow> ((V_vec (app_replace_vec sv i v1 v2))#v_s', Step_normal)
     | _ \<Rightarrow> (v_s, crash_invalid))"

fun select_types_agree :: "t option \<Rightarrow> v \<Rightarrow> v \<Rightarrow> bool" where
  "select_types_agree None v1 v2 = (typeof v1 = typeof v2)"
| "select_types_agree (Some t) v1 v2 = (typeof v1 = t \<and> typeof v2 = t)"

definition app_v_s_select :: "t option \<Rightarrow> v_stack \<Rightarrow> (v_stack \<times> res_step)" where
  "app_v_s_select t_tag v_s =
    (case v_s of
      (V_num (ConstInt32 c))#v2#v1#v_s' \<Rightarrow>
        (if select_types_agree t_tag v1 v2 then
          (if int_eq c 0 then
            (v2#v_s', Step_normal)
          else
            (v1#v_s', Step_normal))
        else
          (v_s, crash_invalid))
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

definition app_v_s_if :: "tb \<Rightarrow> b_e list \<Rightarrow> b_e list \<Rightarrow> v_stack \<Rightarrow> (v_stack \<times> e list \<times> res_step)" where
  "app_v_s_if tb es1 es2 v_s =
     (case v_s of
       (V_num (ConstInt32 c))#v_s' \<Rightarrow>
         (if int_eq c 0 then (v_s', [$(Block tb es2)], Step_normal) else (v_s', [$(Block tb es1)], Step_normal))
     | _ \<Rightarrow> (v_s, [], crash_invalid))"

definition app_v_s_br_if :: "nat \<Rightarrow> v_stack \<Rightarrow> (v_stack \<times> e list \<times> res_step)" where
  "app_v_s_br_if k v_s =
     (case v_s of
       (V_num (ConstInt32 c))#v_s' \<Rightarrow>
         (if int_eq c 0 then (v_s', [], Step_normal) else (v_s', [$(Br k)], Step_normal))
     | _ \<Rightarrow> (v_s, [], crash_invalid))"

definition app_v_s_br_table :: "nat list \<Rightarrow> nat \<Rightarrow> v_stack \<Rightarrow> (v_stack \<times> e list \<times> res_step)" where
  "app_v_s_br_table ks k v_s =
     (case v_s of
       (V_num (ConstInt32 c))#v_s' \<Rightarrow>
             let j = nat_of_int c in
                if j < length ks
                  then (v_s', [$Br (ks!j)], Step_normal)
                  else (v_s', [$Br k], Step_normal)
     | _ \<Rightarrow> (v_s, [], crash_invalid))"

definition app_f_call :: "nat \<Rightarrow> f \<Rightarrow> (e list \<times> res_step)" where
  "app_f_call k f = ([Invoke (sfunc_ind (f_inst f) k)], Step_normal)"

(* TODO: review this *)
definition app_s_f_v_s_call_indirect :: "nat \<Rightarrow> nat \<Rightarrow> tabinst list \<Rightarrow> cl list \<Rightarrow> f \<Rightarrow> v_stack \<Rightarrow> (v_stack \<times> e list \<times> res_step)" where
  "app_s_f_v_s_call_indirect x y tinsts cls f v_s =
    (let i = f_inst f in 
      case v_s of
        (V_num (ConstInt32 c))#v_s' \<Rightarrow>
          (if (x < length (inst.tabs i)) then
            (case (tab_cl_ind tinsts (inst.tabs i!x) (nat_of_int c)) of
              Some v_r \<Rightarrow> (case v_r of
                ConstRefFunc a \<Rightarrow> (if (stypes i y = cl_type (cls!a))
                  then (v_s', [(Invoke a)], Step_normal)
                  else (v_s', [], (Res_trap (STR ''call_indirect''))))
              | ConstNull t \<Rightarrow> (v_s', [], (Res_trap (STR ''call_indirect'')))
              | ConstRefExtern a \<Rightarrow> (v_s, [], crash_invalid))
            | None \<Rightarrow> (v_s', [], (Res_trap (STR ''call_indirect''))))
          else
            (v_s, [], crash_invalid))
        | _ \<Rightarrow> (v_s, [], crash_invalid))"

definition app_s_f_v_s_get_global :: "nat \<Rightarrow> global list \<Rightarrow> f \<Rightarrow> v_stack \<Rightarrow> (v_stack \<times> res_step)" where
  "app_s_f_v_s_get_global k gs f v_s =  ((g_val (gs!(sglob_ind (f_inst f) k)))#v_s, Step_normal)"

definition app_s_f_v_s_set_global :: "nat \<Rightarrow> global list \<Rightarrow> f \<Rightarrow> v_stack \<Rightarrow> (global list \<times>  v_stack \<times> res_step)" where
  "app_s_f_v_s_set_global k gs f v_s =
     (case v_s of
        v1#v_s' \<Rightarrow> (update_glob gs (f_inst f) k v1, v_s', Step_normal)
      | _ \<Rightarrow> (gs, v_s, crash_invalid))"

definition app_s_f_v_s_load :: "t_num \<Rightarrow> nat \<Rightarrow> mem list \<Rightarrow> f \<Rightarrow>  v_stack \<Rightarrow> (v_stack \<times> res_step)" where
  "app_s_f_v_s_load t off ms f v_s = 
          (let i = (f_inst f) in
           case v_s of
             (V_num (ConstInt32 c))#v_s' \<Rightarrow>
               (case smem_ind i of
                  Some j => expect (load (ms!j) (nat_of_int c) off (t_num_length t))
                                  (\<lambda>bs. ((V_num (wasm_deserialise_num bs t))#v_s', Step_normal))
                                  (v_s', (Res_trap (STR ''load'')))
                | None => (v_s, crash_invalid))
           | _ \<Rightarrow> (v_s, crash_invalid))"

definition app_s_f_v_s_load_packed :: "t_num \<Rightarrow> tp_num \<Rightarrow> sx \<Rightarrow> nat \<Rightarrow> mem list \<Rightarrow> f \<Rightarrow>  v_stack \<Rightarrow> (v_stack \<times> res_step)" where
  "app_s_f_v_s_load_packed t tp sx off ms f v_s = 
          (let i = (f_inst f) in
           case v_s of
             (V_num (ConstInt32 c))#v_s' \<Rightarrow>
               (case smem_ind i of
                  Some j => expect (load_packed sx (ms!j) (nat_of_int c) off (tp_num_length tp) (t_num_length t))
                                  (\<lambda>bs. ((V_num (wasm_deserialise_num bs t))#v_s', Step_normal))
                                  (v_s', (Res_trap (STR ''load'')))
                | None => (v_s, crash_invalid))
           | _ \<Rightarrow> (v_s, crash_invalid))"

definition app_s_f_v_s_load_maybe_packed :: "t_num \<Rightarrow> (tp_num \<times> sx) option \<Rightarrow> nat \<Rightarrow> mem list \<Rightarrow> f \<Rightarrow>  v_stack \<Rightarrow> (v_stack \<times> res_step)" where
  "app_s_f_v_s_load_maybe_packed t tp_sx off ms f v_s =
     (case tp_sx of
        Some (tp, sx) \<Rightarrow> app_s_f_v_s_load_packed t tp sx off ms f v_s
      | None \<Rightarrow> app_s_f_v_s_load t off ms f v_s)"

definition app_s_f_v_s_store :: "t_num \<Rightarrow> nat \<Rightarrow> mem list \<Rightarrow> f \<Rightarrow>  v_stack \<Rightarrow> (mem list \<times> v_stack \<times> res_step)" where
  "app_s_f_v_s_store t off ms f v_s = 
          (let i = (f_inst f) in
           case v_s of
             (V_num v)#(V_num (ConstInt32 c))#v_s' \<Rightarrow>
               (if typeof_num v = t then
                 (case smem_ind i of
                    Some j => expect (store (ms!j) (nat_of_int c) off (bits_num v) (t_num_length t))
                                    (\<lambda>mem'. ((ms[j := mem']), v_s', Step_normal))
                                    (ms, v_s', Res_trap (STR ''store''))
                  | None => (ms, v_s, crash_invalid))
                else (ms, v_s, crash_invalid))
           | _ \<Rightarrow> (ms, v_s, crash_invalid))"

definition app_s_f_v_s_store_packed :: "t_num \<Rightarrow> tp_num \<Rightarrow> nat \<Rightarrow> mem list \<Rightarrow> f \<Rightarrow>  v_stack \<Rightarrow> (mem list \<times> v_stack \<times> res_step)" where
  "app_s_f_v_s_store_packed t tp off ms f v_s = 
          (let i = (f_inst f) in
           case v_s of
             (V_num v)#(V_num (ConstInt32 c))#v_s' \<Rightarrow>
               (if typeof_num v = t then
                 (case smem_ind i of
                    Some j => expect (store_packed (ms!j) (nat_of_int c) off (bits_num v) (tp_num_length tp))
                                    (\<lambda>mem'. ((ms[j := mem']), v_s', Step_normal))
                                    (ms, v_s', Res_trap (STR ''store''))
                  | None => (ms, v_s, crash_invalid))
                else (ms, v_s, crash_invalid))
           | _ \<Rightarrow> (ms, v_s, crash_invalid))"

definition app_s_f_v_s_store_maybe_packed :: "t_num \<Rightarrow> tp_num option \<Rightarrow> nat \<Rightarrow> mem list \<Rightarrow> f \<Rightarrow>  v_stack \<Rightarrow> (mem list \<times> v_stack \<times> res_step)" where
  "app_s_f_v_s_store_maybe_packed t tp_opt off ms f v_s =
     (case tp_opt of
        Some tp \<Rightarrow> app_s_f_v_s_store_packed t tp off ms f v_s
      | None \<Rightarrow> app_s_f_v_s_store t off ms f v_s)"

definition app_s_f_v_s_load_vec :: "loadop_vec \<Rightarrow> nat \<Rightarrow> mem list \<Rightarrow> f \<Rightarrow>  v_stack \<Rightarrow> (v_stack \<times> res_step)" where
  "app_s_f_v_s_load_vec lv off ms f v_s = 
          (let i = (f_inst f) in
           case v_s of
             (V_num (ConstInt32 c))#v_s' \<Rightarrow>
               (case smem_ind i of
                  Some j => expect (load_vec lv (ms!j) (nat_of_int c) off)
                                  (\<lambda>bs. ((V_vec (ConstVec128 (deserialise_v128 bs)))#v_s', Step_normal))
                                  (v_s', (Res_trap (STR ''load_vec'')))
                | None => (v_s, crash_invalid))
           | _ \<Rightarrow> (v_s, crash_invalid))"

definition app_s_f_v_s_load_lane_vec :: "shape_vec_i \<Rightarrow> i \<Rightarrow> nat \<Rightarrow> mem list \<Rightarrow> f \<Rightarrow>  v_stack \<Rightarrow> (v_stack \<times> res_step)" where
  "app_s_f_v_s_load_lane_vec svi i_n off ms f v_s = 
          (let i = (f_inst f) in
           case v_s of
             (V_vec (ConstVec128 v))#(V_num (ConstInt32 c))#v_s' \<Rightarrow>
               (case smem_ind i of
                  Some j => expect (load (ms!j) (nat_of_int c) off (vec_i_length svi))
                                  (\<lambda>bs. ((V_vec (ConstVec128 (insert_lane_vec svi i_n bs v)))#v_s', Step_normal))
                                  (v_s', (Res_trap (STR ''load_lane_vec'')))
                | None => (v_s, crash_invalid))
           | _ \<Rightarrow> (v_s, crash_invalid))"

definition app_s_f_v_s_store_vec :: "storeop_vec \<Rightarrow> nat \<Rightarrow> mem list \<Rightarrow> f \<Rightarrow>  v_stack \<Rightarrow> (mem list \<times> v_stack \<times> res_step)" where
  "app_s_f_v_s_store_vec sv off ms f v_s = 
          (let i = (f_inst f) in
           case v_s of
             (V_vec (ConstVec128 v))#(V_num (ConstInt32 c))#v_s' \<Rightarrow>
               (case smem_ind i of
                  Some j => let bs = (store_serialise_vec sv v) in
                            expect (store (ms!j) (nat_of_int c) off bs (length bs))
                              (\<lambda>mem'. ((ms[j := mem']), v_s', Step_normal))
                              (ms, v_s', Res_trap (STR ''store_vec''))
                | None => (ms, v_s, crash_invalid))
           | _ \<Rightarrow> (ms, v_s, crash_invalid))"

definition app_s_f_v_s_mem_size :: "mem list \<Rightarrow> f \<Rightarrow>  v_stack \<Rightarrow> (v_stack \<times> res_step)" where
  "app_s_f_v_s_mem_size ms f v_s = 
          (let i = (f_inst f) in
          (case smem_ind i of
             Some j => (((V_num (ConstInt32 (int_of_nat (mem_size (ms!j)))))#v_s), Step_normal)
           | None => (v_s, crash_invalid)))"

definition app_s_f_v_s_mem_grow :: "mem list \<Rightarrow> f \<Rightarrow> v_stack \<Rightarrow> (mem list \<times> v_stack \<times> res_step)" where
  "app_s_f_v_s_mem_grow ms f v_s = 
          (let i = (f_inst f) in
           case v_s of
             (V_num (ConstInt32 c))#v_s' \<Rightarrow>
               (case smem_ind i of
                  Some j => let l = (mem_size (ms!j)) in
                           expect (mem_grow (ms!j) (nat_of_int c))
                                  (\<lambda>mem'. ((ms[j := mem']), (V_num (ConstInt32 (int_of_nat l)))#v_s', Step_normal))
                                  (ms, (V_num (ConstInt32 int32_minus_one))#v_s', Step_normal)
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

definition app_s_f_v_s_table_set :: "i \<Rightarrow> tabinst list  \<Rightarrow> f \<Rightarrow>  v_stack \<Rightarrow> (tabinst list \<times> v_stack \<times> res_step)" where
  "app_s_f_v_s_table_set x tabinsts f v_s = 
    (let i = (f_inst f) in
      case v_s of
        (V_ref v_r)#(V_num (ConstInt32 c))#v_s' \<Rightarrow>
          (case stab_ind i x of
            Some a => expect (store_tabs1 tabinsts a (nat_of_int c) v_r)
                              (\<lambda>tabinsts'. (tabinsts', v_s', Step_normal))
                              (tabinsts, v_s', Res_trap (STR ''table_set''))
          | None => (tabinsts, v_s, crash_invalid))
      | _ \<Rightarrow> (tabinsts, v_s, crash_invalid))"

definition app_s_f_v_s_table_get :: "i \<Rightarrow> tabinst list  \<Rightarrow> f \<Rightarrow>  v_stack \<Rightarrow> (v_stack \<times> res_step)" where
  "app_s_f_v_s_table_get x tabinsts f v_s =
    (let i = f_inst f in
      case v_s of
        V_num (ConstInt32 c)#v_s' \<Rightarrow>
        (case stab_ind i x of
          Some a \<Rightarrow>
            expect (load_tabs1 tabinsts a (nat_of_int c))
              (\<lambda> val. ((V_ref val)#v_s', Step_normal))
              (v_s', Res_trap (STR ''table_get''))
        | None \<Rightarrow> (v_s, crash_invalid))
      | _ \<Rightarrow> (v_s, crash_invalid))"

definition app_s_f_v_s_table_init :: "i \<Rightarrow> i \<Rightarrow> tabinst list \<Rightarrow> eleminst list \<Rightarrow> f \<Rightarrow> v_stack \<Rightarrow> (v_stack \<times> e list \<times> res_step)" where
  "app_s_f_v_s_table_init x y tabinsts eleminsts f v_s =
    (case v_s of
      (V_num (ConstInt32 n))#(V_num (ConstInt32 src))#(V_num (ConstInt32 dest))#v_s' \<Rightarrow> 
        (case (stab_ind (f_inst f) x) of
          Some ta \<Rightarrow>
          let
            ndest = nat_of_int dest;
            nsrc = nat_of_int src;
            nn = nat_of_int n;
            tab = (tabinsts)!ta;
            ea = (inst.elems (f_inst f))!y;
            el = eleminsts!ea
            in
              if (nsrc+nn > length (snd el) \<or> ndest+nn > length (snd tab)) then
                (v_s', [], Res_trap (STR ''table_init''))
              else
                (case nn of
                  0 \<Rightarrow> (v_s', [], Step_normal)
                | Suc nn_pred \<Rightarrow>
                  let val = (snd el)!nsrc in
                   (v_s', [$EConstNum (ConstInt32 dest), $C (V_ref val), $Table_set x, $EConstNum (ConstInt32 (int_of_nat (ndest+1))), $EConstNum (ConstInt32 (int_of_nat (nsrc+1))), $EConstNum (ConstInt32 (int_of_nat nn_pred)), $Table_init x y],
                   Step_normal))
        | None \<Rightarrow> (v_s, [], crash_invalid))
    |  _ \<Rightarrow> (v_s, [], crash_invalid))"

definition app_s_f_v_s_table_fill :: "i \<Rightarrow>  tabinst list  \<Rightarrow> f \<Rightarrow> v_stack \<Rightarrow> (v_stack \<times> e list \<times> res_step)" where
  "app_s_f_v_s_table_fill x  tabinsts f v_s =
    (case v_s of
      (V_num (ConstInt32 n))#(V_ref vr)#(V_num (ConstInt32 i))#v_s' \<Rightarrow> 
        (case (stab_ind (f_inst f) x) of
          Some ta \<Rightarrow>
          let
            ni = nat_of_int i;
            nn = nat_of_int n;
            tab = (tabinsts)!ta
            in
              if (ni+nn > length (snd tab)) then
                (v_s', [], Res_trap (STR ''table_fill''))
              else
                (case nn of
                  0 \<Rightarrow> (v_s', [], Step_normal)
                | Suc nn_pred \<Rightarrow>
                  
                   (v_s', [$EConstNum (ConstInt32 i), $C (V_ref vr), $Table_set x, $EConstNum (ConstInt32 (int_of_nat (ni+1))), $C (V_ref vr), $EConstNum (ConstInt32 (int_of_nat nn_pred)), $Table_fill x],
                   Step_normal))
        | None \<Rightarrow> (v_s, [], crash_invalid))
    |  _ \<Rightarrow> (v_s, [], crash_invalid))"

definition app_s_f_v_s_table_copy :: "i \<Rightarrow> i \<Rightarrow> tabinst list  \<Rightarrow> f \<Rightarrow> v_stack \<Rightarrow> (v_stack \<times> e list \<times> res_step)" where
  "app_s_f_v_s_table_copy x y tabinsts f v_s =
    (case v_s of
      (V_num (ConstInt32 n))#(V_num (ConstInt32 src))#(V_num (ConstInt32 dest))#v_s' \<Rightarrow> 
        (case (stab_ind (f_inst f) x, stab_ind (f_inst f) y) of
          (Some tax, Some tay) \<Rightarrow>
          let
            ndest = nat_of_int dest;
            nsrc = nat_of_int src;
            nn = nat_of_int n;
            tabx = (tabinsts)!tax;
            taby = (tabinsts)!tay
            in
              if (nsrc+nn > length (snd tabx) \<or> ndest+nn > length (snd taby)) then
                (v_s', [], Res_trap (STR ''table_copy''))
              else
                (case nn of
                  0 \<Rightarrow> (v_s', [], Step_normal)
                | Suc nn_pred \<Rightarrow>
                  (if ndest \<le> nsrc then
                    (v_s', [$EConstNum (ConstInt32 dest), $EConstNum (ConstInt32 src), $Table_get y, $Table_set x, $EConstNum (ConstInt32 (int_of_nat (ndest+1))), $EConstNum (ConstInt32 (int_of_nat (nsrc+1))), $EConstNum (ConstInt32 (int_of_nat nn_pred)), $Table_copy x y], Step_normal)
                  else
                    (v_s', [$EConstNum (ConstInt32 (int_of_nat (ndest+nn_pred))), $EConstNum (ConstInt32 (int_of_nat (nsrc+nn))), $Table_get y, $Table_set x, $EConstNum (ConstInt32 dest), $EConstNum (ConstInt32 src), $EConstNum (ConstInt32 (int_of_nat nn_pred)), $Table_copy x y], Step_normal)))
        | (_, _) \<Rightarrow> (v_s, [], crash_invalid))
    |  _ \<Rightarrow> (v_s, [], crash_invalid))"

definition app_s_f_v_s_table_size :: "i \<Rightarrow> tabinst list \<Rightarrow> f \<Rightarrow>  v_stack \<Rightarrow> (v_stack \<times> res_step)" where
  "app_s_f_v_s_table_size x tabinsts f v_s = 
          (case stab_ind (f_inst f) x of
             Some a => (((V_num (ConstInt32 (int_of_nat (tab_size (tabinsts!a)))))#v_s), Step_normal)
           | None => (v_s, crash_invalid))"

definition app_s_f_v_s_table_grow :: "i \<Rightarrow> tabinst list \<Rightarrow> f \<Rightarrow> v_stack \<Rightarrow> (tabinst list \<times> v_stack \<times> res_step)" where
  "app_s_f_v_s_table_grow ti tabinsts f v_s = 
          (case v_s of
             (V_num (ConstInt32 n))#(V_ref vr)#v_s' \<Rightarrow>
               (case stab_ind (f_inst f) ti of
                  Some a => let tab = tabinsts!a; sz = tab_size tab in
                    expect (grow_tab tab (nat_of_int n) vr)
                    (\<lambda>tab'. ((tabinsts[a := tab']), (V_num (ConstInt32 (int_of_nat sz)))#v_s', Step_normal))
                    (tabinsts, (V_num (ConstInt32 int32_minus_one))#v_s', Step_normal)

                | None => (tabinsts, v_s, crash_invalid))
           | _ \<Rightarrow> (tabinsts, v_s, crash_invalid))"

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

fun b_e_to_val:: "b_e \<Rightarrow> v option" where
  "b_e_to_val (EConstNum n) = Some (V_num n)"
| "b_e_to_val (EConstVec v) = Some (V_vec v)"
| "b_e_to_val _ = None"

fun split_vals:: "b_e list \<Rightarrow> v list \<times> b_e list" where
  "split_vals [] = ([], [])"
| "split_vals (e#es) = (case (b_e_to_val e) of
    Some v \<Rightarrow> (let (vs', es') = split_vals es in (v#vs', es'))
  | None \<Rightarrow> ([], es))"

(*
fun split_vals :: "b_e list \<Rightarrow> v list \<times> b_e list" where
  "split_vals ((C v)#es) = (let (vs', es') = split_vals es in (v#vs', es'))"
| "split_vals es = ([], es)"
*)

fun e_to_v:: "e \<Rightarrow> v option" where
  "e_to_v ($EConstNum n) = Some (V_num n)"
| "e_to_v ($EConstVec v) = Some (V_vec v)"
| "e_to_v (Ref r) = Some (V_ref r)"
| "e_to_v _ = None"

fun split_vals_e :: "e list \<Rightarrow> v list \<times> e list" where
  "split_vals_e [] = ([], [])"
| "split_vals_e (e#es) = (case (e_to_v e) of
    Some v \<Rightarrow> (let (vs', es') = split_vals_e es in (v#vs', es'))
  | None \<Rightarrow> ([], (e#es)))"

(*
fun split_vals_e :: "e list \<Rightarrow> v list \<times> e list" where
  "split_vals_e (($ C v)#es) = (let (vs', es') = split_vals_e es in (v#vs', es'))"
| "split_vals_e es = ([], es)"
*)

fun split_v_s_b_s_aux :: "v_stack \<Rightarrow> b_e list \<Rightarrow> v_stack \<times> b_e list" where
  "split_v_s_b_s_aux v_s ((EConstNum n)#b_es) = split_v_s_b_s_aux ((V_num n)#v_s) b_es"
| "split_v_s_b_s_aux v_s ((EConstVec v)#b_es) = split_v_s_b_s_aux ((V_vec v)#v_s) b_es"
| "split_v_s_b_s_aux v_s es = (v_s, es)"

(*
fun split_v_s_b_s_aux :: "v_stack \<Rightarrow> b_e list \<Rightarrow> v_stack \<times> b_e list" where
  "split_v_s_b_s_aux v_s ((C v)#b_es) = split_v_s_b_s_aux (v#v_s) b_es"
| "split_v_s_b_s_aux v_s es = (v_s, es)"
*)
fun split_v_s_b_s :: "b_e list \<Rightarrow> v_stack \<times> b_e list" where
  "split_v_s_b_s es = split_v_s_b_s_aux [] es"

fun split_v_s_es_aux :: "v_stack \<Rightarrow> e list \<Rightarrow> v_stack \<times> e list" where
  "split_v_s_es_aux v_s (($EConstNum n)#es) = split_v_s_es_aux ((V_num n)#v_s) es"
| "split_v_s_es_aux v_s (($EConstVec v)#es) = split_v_s_es_aux ((V_vec v)#v_s) es"
| "split_v_s_es_aux v_s ((Ref r)#es) = split_v_s_es_aux ((V_ref r)#v_s) es"
| "split_v_s_es_aux v_s es = (v_s, es)"

fun split_v_s_es :: "e list \<Rightarrow> v_stack \<times> e list" where
  "split_v_s_es es = split_v_s_es_aux [] es"

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

(*
lemma split_vals_const_list: "split_vals (map EConst vs) = (vs, [])"
  by (induction vs, simp_all)
*)

lemma split_vals_e_const_list: "split_vals_e ($C* vs) = (vs, [])"
  apply(induction vs)
  using v_to_e_def by (auto split: v.splits)

lemma split_v_s_b_s_aux_conv_app:
  assumes "split_v_s_b_s_aux v_s_aux b_es = (v_s, b_es')"
  shows "($C* (rev v_s_aux))@($* b_es) = ($C* (rev v_s))@($* b_es')"
  using assms v_to_e_def
  by (induction v_s_aux b_es rule: split_v_s_b_s_aux.induct) auto

lemma split_v_s_b_s_conv_app:
  assumes "split_v_s_b_s b_es = (v_s, b_es')"
  shows "$* b_es = ($C* (rev v_s))@($* b_es')"
  using assms split_v_s_b_s_aux_conv_app
  by fastforce


lemma e_to_v_v_to_e:
  assumes "e_to_v e = Some a"
  shows "e = $C a"
  using assms
proof (cases e rule: e_to_v.cases)
qed (auto simp add: v_to_e_def)

lemma split_vals_e_conv_app:
  assumes "split_vals_e xs = (as, bs)"
  shows "xs = ($C* as)@bs"
  using assms
proof (induction xs arbitrary: as rule: split_vals_e.induct)
  case 1
  then show ?case by simp
next
  case (2 e es)
  then show ?case
  proof(cases "e_to_v e")
    case None
    then show ?thesis using 2 by auto
  next
    case (Some a)
    then obtain a' as' where "split_vals_e (e # es) = (a'#as', bs)" "split_vals_e es = (as', bs)"
      using 2 apply simp
      by (metis Pair_inject old.prod.case old.prod.exhaust)
    then show ?thesis using 2 Some e_to_v_v_to_e by auto
  qed
qed
(*
abbreviation v_stack_to_b_es :: " v_stack \<Rightarrow> b_e list"
  where "v_stack_to_b_es v \<equiv> map (\<lambda>v. C v) (rev v)"
*)
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

    | (Unop_vec op) \<Rightarrow>
        let (v_s', res) = (app_v_s_unop_vec op v_s) in
        ((Config d s (update_fc_step fc v_s' []) fcs), res)

    | (Binop_vec op) \<Rightarrow>
        let (v_s', res) = (app_v_s_binop_vec op v_s) in
        ((Config d s (update_fc_step fc v_s' []) fcs), res)

    | (Ternop_vec op) \<Rightarrow>
        let (v_s', res) = (app_v_s_ternop_vec op v_s) in
        ((Config d s (update_fc_step fc v_s' []) fcs), res)

    | (Test_vec op) \<Rightarrow>
        let (v_s', res) = (app_v_s_test_vec op v_s) in
        ((Config d s (update_fc_step fc v_s' []) fcs), res)

    | (Shift_vec vs) \<Rightarrow>
        let (v_s', res) = (app_v_s_shift_vec vs v_s) in
        ((Config d s (update_fc_step fc v_s' []) fcs), res)

    | (Splat_vec is) \<Rightarrow>
        let (v_s', res) = (app_v_s_splat_vec is v_s) in
        ((Config d s (update_fc_step fc v_s' []) fcs), res)

    | (Extract_vec sv sx i) \<Rightarrow>
        let (v_s', res) = (app_v_s_extract_vec sv sx i v_s) in
        ((Config d s (update_fc_step fc v_s' []) fcs), res)

    | (Replace_vec sv i) \<Rightarrow>
        let (v_s', res) = (app_v_s_replace_vec sv i v_s) in
        ((Config d s (update_fc_step fc v_s' []) fcs), res)

    | (Unreachable) \<Rightarrow>
        (Config d s fc fcs, Res_trap (STR ''unreachable''))

    | (Nop) \<Rightarrow>
        (Config d s fc fcs, Step_normal)

    | (Drop) \<Rightarrow>
        let (v_s', res) = (app_v_s_drop v_s) in
        ((Config d s (update_fc_step fc v_s' []) fcs), res)

    | (Select t_tag) \<Rightarrow>
        let (v_s', res) = (app_v_s_select t_tag v_s) in
        ((Config d s (update_fc_step fc v_s' []) fcs), res)

    | (Block tb b_ebs) \<Rightarrow>
        if es \<noteq> [] then (Config d s fc fcs, crash_invariant)
        else
          (case tb_tf (f_inst f) tb of (t1s _> t2s) \<Rightarrow>
           let n = length t1s in
           let m = length t2s in
           if (length v_s \<ge> n) then
             let (v_bs, v_s') = split_n v_s n in
             let lc = Label_context v_s' b_es m [] in 
             let fc' = Frame_context (Redex v_bs [] b_ebs) (lc#lcs) nf f in
             (Config d s fc' fcs, Step_normal)
           else (Config d s fc fcs, crash_invalid))

    | (Loop tb b_els) \<Rightarrow>
        if es \<noteq> [] then (Config d s fc fcs, crash_invariant)
        else
          (case tb_tf (f_inst f) tb of (t1s _> t2s) \<Rightarrow>
           let n = length t1s in
           let m = length t2s in
           if (length v_s \<ge> n) then
             let (v_bs, v_s') = split_n v_s n in
             let lc = Label_context v_s' b_es n [(Loop tb b_els)] in 
             let fc' = Frame_context (Redex v_bs [] b_els) (lc#lcs) nf f in
             (Config d s fc' fcs, Step_normal)
           else (Config d s fc fcs, crash_invalid))

    | (If tb es1 es2) \<Rightarrow>
        let (v_s', es_cont, res) = (app_v_s_if tb es1 es2 v_s) in
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

    | (Call_indirect x y) \<Rightarrow>
        let (v_s', es_cont, res) = (app_s_f_v_s_call_indirect x y (tabs s) (funcs s) f v_s) in
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

    | (Load_vec lv a off) \<Rightarrow>
        let (v_s', res) = (app_s_f_v_s_load_vec lv off (mems s) f v_s) in
        (Config d s (update_fc_step fc v_s' []) fcs, res)

    | (Load_lane_vec svi i a off) \<Rightarrow>
        let (v_s', res) = (app_s_f_v_s_load_lane_vec svi i off (mems s) f v_s) in
        (Config d s (update_fc_step fc v_s' []) fcs, res)

    | (Store_vec sv a off) \<Rightarrow>
        let (ms', v_s', res) = (app_s_f_v_s_store_vec sv off (mems s) f v_s) in
        (Config d (s\<lparr>mems:=ms'\<rparr>) (update_fc_step fc v_s' []) fcs, res)

    | (Current_memory) \<Rightarrow>
        let (v_s', res) = (app_s_f_v_s_mem_size (mems s) f v_s) in
        (Config d s (update_fc_step fc v_s' []) fcs, res)

    | (Grow_memory) \<Rightarrow>
        let (ms', v_s', res) = (app_s_f_v_s_mem_grow (mems s) f v_s) in
        (Config d (s\<lparr>mems:=ms'\<rparr>) (update_fc_step fc v_s' []) fcs, res)

    | (Table_set x) \<Rightarrow>
      let (tabinsts', v_s', res) = (app_s_f_v_s_table_set x (tabs s) f v_s) in
      ((Config d (s\<lparr>tabs:=tabinsts'\<rparr>)) (update_fc_step fc v_s' []) fcs, res)

    | (Table_get x) \<Rightarrow>
      let (v_s', res) = (app_s_f_v_s_table_get x (tabs s) f v_s) in
      ((Config d s) (update_fc_step fc v_s' []) fcs, res)

    | (Table_init x y) \<Rightarrow>
      let (v_s', es, res) = (app_s_f_v_s_table_init x y (tabs s) (elems s) f v_s) in
      ((Config d s) (update_fc_step fc v_s' es) fcs, res)

    | (Table_copy x y) \<Rightarrow>
      let (v_s', es, res) = (app_s_f_v_s_table_copy x y (tabs s) f v_s) in
      ((Config d s) (update_fc_step fc v_s' es) fcs, res)

    | (Table_fill x) \<Rightarrow>
      let (v_s', es, res) = (app_s_f_v_s_table_fill x (tabs s) f v_s) in
      ((Config d s) (update_fc_step fc v_s' es) fcs, res)

    | (Table_grow x) \<Rightarrow>
      let (tabinsts', v_s', res) = (app_s_f_v_s_table_grow x (tabs s) f v_s) in
      ((Config d (s\<lparr>tabs:=tabinsts'\<rparr>)) (update_fc_step fc v_s' []) fcs, res)

    | (Table_size x) \<Rightarrow>
        let (v_s', res) = (app_s_f_v_s_table_size x (tabs s) f v_s) in
        (Config d s (update_fc_step fc v_s' []) fcs, res)

    | _ \<Rightarrow> (Config d s fc fcs, crash_invariant)))"

fun run_step_e :: "e \<Rightarrow> config \<Rightarrow> res_step_tuple" where
  "run_step_e e (Config d s fc fcs) =
    (case fc of Frame_context (Redex v_s es b_es) lcs nf f \<Rightarrow>
      (case e of
        Basic b_e \<Rightarrow> run_step_b_e b_e (Config d s fc fcs)
      | Invoke i_cl \<Rightarrow>
        (case (funcs s!i_cl) of
          Func_native i' (t1s _> t2s) ts es_f \<Rightarrow>
            (case n_zeros ts of
              None \<Rightarrow> (Config d s fc fcs, crash_invalid)
            | Some zs \<Rightarrow>
              (case d of
                Suc d' \<Rightarrow>
                 (let n = length t1s in
                  let m = length t2s in
                  if (length v_s \<ge> n) then
                    let (v_fs, v_s') = split_n v_s n in
                    let fc' = Frame_context (Redex v_s' es b_es) lcs nf f in
                    let ff = \<lparr> f_locs = ((rev v_fs)@zs), f_inst = i'\<rparr> in
                    let lc = Label_context [] [] m [] in 
                    let fcf = Frame_context (Redex [] [] es_f) [lc] m ff in
                    (Config d' s fcf (fc'#fcs), Step_normal)
                  else
                    (Config d s fc fcs, crash_invalid))
             | 0 \<Rightarrow> (Config d s fc fcs, crash_exhaustion)))
           | Func_host (t1s _> t2s) h \<Rightarrow>
             let n = length t1s in
             let m = length t2s in
             if length v_s \<ge> n
               then
                 let (v_fs, v_s') = split_n v_s n in
                 case host_apply_impl s (t1s _> t2s) h (rev v_fs) of
                   Some (s',rvs) \<Rightarrow> 
                     if list_all2 (\<lambda>t v. typeof v = t) t2s rvs
                       then
                         let fc' = Frame_context (Redex ((rev rvs)@v_s') es b_es) lcs nf f in
                         (Config d s' fc' fcs, Step_normal)
                       else
                         (Config d s' fc fcs, crash_invalid)
                 | None \<Rightarrow> (Config d s (Frame_context (Redex v_s' es b_es) lcs nf f) fcs, Res_trap (STR ''host_apply''))
               else
                  (Config d s fc fcs, crash_invalid))
            | _ \<Rightarrow> (Config d s fc fcs, crash_invariant)))"
         (* | Ref v_r \<Rightarrow>
              let fc' = Frame_context (Redex (V_ref v_r#v_s) es b_es) lcs nf f in
              (Config d s fc' fcs, Step_normal) *)
(* should never produce Label, Frame, or Trap *)
(* should never produce Ref as well, as produced references are pushed to stack *)

function(sequential) run_iter :: "fuel \<Rightarrow> config \<Rightarrow> res_tuple" where
  "run_iter (Suc n) cfg =
     (case cfg of
        (Config d s (Frame_context (Redex v_s'' es b_es) lcs nf f) fcs) \<Rightarrow>
     (case split_v_s_es es of
        (v_s''', []) \<Rightarrow>
          let v_s = v_s'''@v_s'' in
             (case b_es of
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
      | (v_s''', e#es') \<Rightarrow> let v_s = v_s'''@v_s'' in
          (let (cfg', res) = run_step_e e (Config d s (Frame_context (Redex v_s es' b_es) lcs nf f) fcs) in
                      (case res of
                         Step_normal \<Rightarrow> run_iter n cfg'
                       | Res_trap str \<Rightarrow> (cfg', RTrap str)
                       | Res_crash str \<Rightarrow> (cfg', RCrash str)))))"

\<comment> \<open> out of fuel \<close>
| "run_iter 0 cfg = (cfg, res_crash_fuel)"

  by pat_completeness auto
termination
  by (relation "measure (\<lambda>p. fst p)") auto

fun run_instantiate :: "fuel \<Rightarrow> depth \<Rightarrow> (s \<times> inst \<times> e list) \<Rightarrow> (s \<times> res)" where
  "run_instantiate n d (s, inst, es) =
     (let (cfg',res) = run_iter n (Config d s (Frame_context (Redex [] es []) [] 0 \<lparr>f_locs=[],f_inst=inst\<rparr>) []) in
      case cfg' of (Config d s fc fcs) \<Rightarrow> (s,res))"

fun run_v :: "fuel \<Rightarrow> depth \<Rightarrow> (s \<times> f \<times> b_e list) \<Rightarrow> (s \<times> res)" where
  "run_v n d (s, f, b_es) =
     (let (cfg',res) = run_iter n (Config d s (Frame_context (Redex [] [] b_es) [] 0 f) []) in
      case cfg' of (Config d s fc fcs) \<Rightarrow> (s,res))"

fun run_invoke_v :: "fuel \<Rightarrow> depth \<Rightarrow> (s \<times> v list \<times> i) \<Rightarrow> (s \<times> res)" where
  "run_invoke_v n d (s, vs, i) =
     (let (cfg',res) = run_iter n (Config d s (Frame_context (Redex (rev vs) [Invoke i] []) [] 0 empty_frame) []) in
      case cfg' of (Config d s fc fcs) \<Rightarrow> (s,res))"

definition "make_invoke_config \<equiv> \<lambda>d (s, vs, i). (Config d s (Frame_context (Redex (rev vs) [Invoke i] []) [] 0 empty_frame) [])"

lemma run_invoke_v_alt:
  "run_invoke_v n d (s, vs, i) =
     (let (cfg',res) = run_iter n (make_invoke_config d (s,vs,i)) in
      case cfg' of (Config d s fc fcs) \<Rightarrow> (s,res))"
  by (simp add: make_invoke_config_def)
      
abbreviation "empty_store \<equiv> \<lparr>s.funcs = [], tabs = [], mems = [], globs = [], elems = [], datas = []\<rparr>"
      
end
