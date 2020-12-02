section \<open>WebAssembly Interpreter\<close>

theory Wasm_Interpreter imports Wasm begin

datatype res_crash =
  CError
| CExhaustion

datatype res =
  RCrash res_crash
| RTrap
| RValue "v list"  

datatype res_step =
  RSCrash res_crash
| RSBreak nat "v list"
| RSReturn "v list"
| RSNormal "v list" "e list"

abbreviation crash_error where "crash_error \<equiv> RSCrash CError"

abbreviation res_trap where "res_trap vs es \<equiv> RSNormal vs (Trap#es)"

type_synonym depth = nat
type_synonym fuel = nat

type_synonym config_tuple = "s \<times> f \<times> (v list \<times> e list)"

type_synonym res_tuple = "s \<times> f \<times> res_step"

fun split_vals :: "b_e list \<Rightarrow> v list \<times> b_e list" where
  "split_vals ((C v)#es) = (let (vs', es') = split_vals es in (v#vs', es'))"
| "split_vals es = ([], es)"

fun split_vals_e :: "e list \<Rightarrow> v list \<times> e list" where
  "split_vals_e (($ C v)#es) = (let (vs', es') = split_vals_e es in (v#vs', es'))"
| "split_vals_e es = ([], es)"

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

abbreviation expect :: "'a option \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'b" where
  "expect a f b \<equiv> (case a of
                     Some a' \<Rightarrow> f a'
                   | None \<Rightarrow> b)"

abbreviation vs_to_es :: " v list \<Rightarrow> e list"
  where "vs_to_es v \<equiv> $C* (rev v)"

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

function (sequential)
  run_step :: "depth \<Rightarrow> config_tuple \<Rightarrow> res_tuple" where
  "run_step d (s,f,(ves, es)) = (case es of
                               [] \<Rightarrow> (s,f, crash_error)
                             | e#es' \<Rightarrow>
                               if e_is_trap e
                                 then
                                   if (es' \<noteq> [] \<or> ves \<noteq> [])
                                     then
                                       (s, f, RSNormal [] [Trap])
                                     else
                                       (s, f, crash_error)
                                 else
  case e of
    \<comment> \<open>\<open>B_E\<close>\<close>
      \<comment> \<open>\<open>UNOPS\<close>\<close>
        $(Unop t op) \<Rightarrow>
         (case ves of
            v#ves' \<Rightarrow>
              (s, f, RSNormal ((app_unop op v)#ves') es')
          | _ \<Rightarrow> (s, f, crash_error))
      \<comment> \<open>\<open>BINOPS\<close>\<close>
      | $(Binop t op) \<Rightarrow>
          (case ves of
             v2#v1#ves' \<Rightarrow>
                expect (app_binop op v1 v2) (\<lambda>v. (s, f, RSNormal (v#ves') es')) (s, f, res_trap ves' es')
           | _ \<Rightarrow> (s, f, crash_error))
      \<comment> \<open>\<open>TESTOPS\<close>\<close>
      | $(Testop t testop) \<Rightarrow>
          (case ves of
             v#ves' \<Rightarrow>
               (s, f, RSNormal ((app_testop testop v)#ves') es')
           | _ \<Rightarrow> (s, f, crash_error))
      \<comment> \<open>\<open>RELOPS\<close>\<close>
      | $(Relop t op) \<Rightarrow>
          (case ves of
             v2#v1#ves' \<Rightarrow>
               (s, f, RSNormal ((app_relop op v1 v2)#ves') es')
           | _ \<Rightarrow> (s, f, crash_error))
      \<comment> \<open>\<open>CONVERT\<close>\<close>
      | $(Cvtop t2 Convert t1 sx) \<Rightarrow>
          (case ves of
             v#ves' \<Rightarrow>
               (if (types_agree t1 v)
                  then
                    expect (cvt t2 sx v) (\<lambda>v'. (s, f, RSNormal (v'#ves') es')) (s, f, res_trap ves' es')
                  else
                    (s, f, crash_error))
           | _ \<Rightarrow> (s, f, crash_error))
      | $(Cvtop t2 Reinterpret t1 sx) \<Rightarrow>
          (case ves of
             v#ves' \<Rightarrow>
               (if (types_agree t1 v \<and> sx = None)
                  then
                    (s, f, RSNormal ((wasm_deserialise (bits v) t2)#ves') es')
                  else
                    (s, f, crash_error))
           | _ \<Rightarrow> (s, f, crash_error))
      \<comment> \<open>\<open>UNREACHABLE\<close>\<close>
      | $Unreachable \<Rightarrow>
          (s, f, res_trap ves es')
      \<comment> \<open>\<open>NOP\<close>\<close>
      | $Nop \<Rightarrow>
          (s, f, RSNormal ves es')
      \<comment> \<open>\<open>DROP\<close>\<close>
      | $Drop \<Rightarrow>
          (case ves of
             v#ves' \<Rightarrow>
               (s, f, RSNormal ves' es')
           | _ \<Rightarrow> (s, f, crash_error))
      \<comment> \<open>\<open>SELECT\<close>\<close>
      | $Select \<Rightarrow>
          (case ves of
             (ConstInt32 c)#v2#v1#ves' \<Rightarrow>
               (if int_eq c 0 then (s, f, RSNormal (v2#ves') es') else (s, f, RSNormal (v1#ves') es'))
           | _ \<Rightarrow> (s, f, crash_error))
      \<comment> \<open>\<open>BLOCK\<close>\<close>
      | $(Block (t1s _> t2s) es) \<Rightarrow>
          (if length ves \<ge> length t1s
             then
               let (ves', ves'') = split_n ves (length t1s) in
               (s, f, RSNormal ves'' ((Label (length t2s) [] ((vs_to_es ves')@($* es)))#es'))
             else
               (s, f, crash_error))
      \<comment> \<open>\<open>LOOP\<close>\<close>
      | $(Loop (t1s _> t2s) es) \<Rightarrow>
          (if length ves \<ge> length t1s
             then
               let (ves', ves'') = split_n ves (length t1s) in
               (s, f, RSNormal ves'' ((Label (length t1s) [$(Loop (t1s _> t2s) es)] ((vs_to_es ves')@($* es)))#es'))
             else
               (s, f, crash_error))
      \<comment> \<open>\<open>IF\<close>\<close>
      | $(If tf es1 es2) \<Rightarrow>
          (case ves of
             (ConstInt32 c)#ves' \<Rightarrow>
                if int_eq c 0
                  then
                    (s, f, RSNormal (ves') (($(Block tf es2))#es'))
                  else
                    (s, f, RSNormal (ves') (($(Block tf es1))#es'))
           | _ \<Rightarrow> (s, f, crash_error))
      \<comment> \<open>\<open>BR\<close>\<close>
      | $Br j \<Rightarrow>
          (s, f, RSBreak j ves)
      \<comment> \<open>\<open>BR_IF\<close>\<close>
      | $Br_if j \<Rightarrow>
          (case ves of
             (ConstInt32 c)#ves' \<Rightarrow>
                if int_eq c 0
                  then
                    (s, f, RSNormal ves' es')
                  else
                    (s, f, RSNormal ves' (($Br j) # es'))
           | _ \<Rightarrow> (s, f, crash_error))
      \<comment> \<open>\<open>BR_TABLE\<close>\<close>
      | $Br_table js j \<Rightarrow>
          (case ves of
             (ConstInt32 c)#ves' \<Rightarrow>
             let k = nat_of_int c in
                if k < length js
                  then
                    (s, f, RSNormal ves' (($Br (js!k)) # es'))
                  else
                    (s, f, RSNormal ves' (($Br j) # es'))
           | _ \<Rightarrow> (s, f, crash_error))
      \<comment> \<open>\<open>CALL\<close>\<close>
      | $Call j \<Rightarrow>
          (s, f, RSNormal ves (Invoke (sfunc_ind (f_inst f) j) # es'))
      \<comment> \<open>\<open>CALL_INDIRECT\<close>\<close>
      | $Call_indirect j \<Rightarrow>
          (let i = (f_inst f) in
           case ves of
             (ConstInt32 c)#ves' \<Rightarrow>
               (case (stab s i (nat_of_int c)) of
                  Some i_cl \<Rightarrow>
                    if (stypes s i j = cl_type (funcs s!i_cl))
                      then
                        (s, f, RSNormal ves' (Invoke i_cl # es'))
                      else
                        (s, f, res_trap ves' es')
                | _ \<Rightarrow> (s, f, res_trap ves' es'))
           | _ \<Rightarrow> (s, f, crash_error))
      \<comment> \<open>\<open>RETURN\<close>\<close>
      | $Return \<Rightarrow>
          (s, f, RSReturn ves)
      \<comment> \<open>\<open>GET_LOCAL\<close>\<close>
      | $Get_local j \<Rightarrow>
          (let vs = (f_locs f) in
           if j < length vs
             then (s, f, RSNormal ((vs!j)#ves) es')
             else (s, f, crash_error))
      \<comment> \<open>\<open>SET_LOCAL\<close>\<close>
      | $Set_local j \<Rightarrow>
          (let vs = (f_locs f) in
           case ves of
             v#ves' \<Rightarrow>
               if j < length vs
                 then (s, \<lparr> f_locs = vs[j := v], f_inst = (f_inst f) \<rparr>, RSNormal ves' es')
                 else (s, f, crash_error)
           | _ \<Rightarrow> (s, f, crash_error))
      \<comment> \<open>\<open>TEE_LOCAL\<close>\<close>
      | $Tee_local j \<Rightarrow>
          (case ves of
             v#ves' \<Rightarrow>
               (s, f, RSNormal (v#ves) (($(Set_local j))#es'))
           | _ \<Rightarrow> (s, f, crash_error))
      \<comment> \<open>\<open>GET_GLOBAL\<close>\<close>
      | $Get_global j \<Rightarrow>
          (s, f, RSNormal ((sglob_val s (f_inst f) j)#ves) es')
      \<comment> \<open>\<open>SET_GLOBAL\<close>\<close>
      | $Set_global j \<Rightarrow>
          (case ves of
             v#ves' \<Rightarrow> ((supdate_glob s (f_inst f) j v), f, RSNormal ves' es')
           | _ \<Rightarrow> (s, f, crash_error))
      \<comment> \<open>\<open>LOAD\<close>\<close>
      | $(Load t None a off) \<Rightarrow>
          (let i = (f_inst f) in
           case ves of
             (ConstInt32 k)#ves' \<Rightarrow>
               expect (smem_ind s i)
                  (\<lambda>j.
                    expect (load ((mems s)!j) (nat_of_int k) off (t_length t))
                      (\<lambda>bs. (s, f, RSNormal ((wasm_deserialise bs t)#ves') es'))
                      (s, f, res_trap ves' es'))
                  (s, f, crash_error)
           | _ \<Rightarrow> (s, f, crash_error))
      \<comment> \<open>\<open>LOAD PACKED\<close>\<close>
      | $(Load t (Some (tp, sx)) a off) \<Rightarrow>
          (let i = (f_inst f) in
           case ves of
             (ConstInt32 k)#ves' \<Rightarrow>
               expect (smem_ind s i)
                  (\<lambda>j.
                    expect (load_packed sx ((mems s)!j) (nat_of_int k) off (tp_length tp) (t_length t))
                      (\<lambda>bs. (s, f, RSNormal ((wasm_deserialise bs t)#ves') es'))
                      (s, f, res_trap ves' es'))
                  (s, f, crash_error)
           | _ \<Rightarrow> (s, f, crash_error))
      \<comment> \<open>\<open>STORE\<close>\<close>
      | $(Store t None a off) \<Rightarrow>
          (let i = (f_inst f) in
           case ves of
             v#(ConstInt32 k)#ves' \<Rightarrow>
               (if (types_agree t v)
                 then
                   expect (smem_ind s i)
                      (\<lambda>j.
                         expect (store ((mems s)!j) (nat_of_int k) off (bits v) (t_length t))
                           (\<lambda>mem'. (s\<lparr>mems:= ((mems s)[j := mem'])\<rparr>, f, RSNormal ves' es'))
                           (s, f, res_trap ves' es'))
                      (s, f, crash_error)
                 else
                   (s, f, crash_error))
           | _ \<Rightarrow> (s, f, crash_error))
      \<comment> \<open>\<open>STORE_PACKED\<close>\<close>
      | $(Store t (Some tp) a off) \<Rightarrow>
          (let i = (f_inst f) in
           case ves of
                  v#(ConstInt32 k)#ves' \<Rightarrow>
                    (if (types_agree t v)
                      then
                        expect (smem_ind s i)
                           (\<lambda>j.
                              expect (store_packed ((mems s)!j) (nat_of_int k) off (bits v) (tp_length tp))
                                (\<lambda>mem'. (s\<lparr>mems:= ((mems s)[j := mem'])\<rparr>, f, RSNormal ves' es'))
                                (s, f, res_trap ves' es'))
                           (s, f, crash_error)
                      else
                        (s, f, crash_error))
                | _ \<Rightarrow> (s, f, crash_error))
      \<comment> \<open>\<open>CURRENT_MEMORY\<close>\<close>
      | $Current_memory \<Rightarrow>
          expect (smem_ind s (f_inst f))
            (\<lambda>j. (s, f, RSNormal ((ConstInt32 (int_of_nat (mem_size ((s.mems s)!j))))#ves) es'))
            (s, f, crash_error)
      \<comment> \<open>\<open>GROW_MEMORY\<close>\<close>
      | $Grow_memory \<Rightarrow>
          (case ves of
             (ConstInt32 c)#ves' \<Rightarrow>
                expect (smem_ind s (f_inst f))
                  (\<lambda>j.
                     let l = (mem_size ((s.mems s)!j)) in
                     (expect (mem_grow ((mems s)!j) (nat_of_int c))
                        (\<lambda>mem'. (s\<lparr>mems:= ((mems s)[j := mem'])\<rparr>, f, RSNormal ((ConstInt32 (int_of_nat l))#ves') es'))
                        (s, f, RSNormal ((ConstInt32 int32_minus_one)#ves') es')))
                  (s, f, crash_error)
           | _ \<Rightarrow> (s, f, crash_error))
      \<comment> \<open>\<open>VAL\<close> - should not be executed\<close>
      | $C v \<Rightarrow> (s, f, crash_error)
    \<comment> \<open>\<open>E\<close>\<close>
      \<comment> \<open>\<open>CALLCL\<close>\<close>
      | Invoke i_cl \<Rightarrow>
          (case (funcs s!i_cl) of
             Func_native i' (t1s _> t2s) ts es \<Rightarrow>
               let n = length t1s in
               let m = length t2s in
               if length ves \<ge> n
                 then
                   let (ves', ves'') = split_n ves n in
                   let zs = n_zeros ts in
                     (s, f, RSNormal ves'' ((Frame m \<lparr> f_locs = ((rev ves')@zs), f_inst = i'\<rparr> [$(Block ([] _> t2s) es)]) # es'))
                 else
                   (s, f, crash_error)
           | Func_host (t1s _> t2s) h \<Rightarrow>
               let n = length t1s in
               let m = length t2s in
               if length ves \<ge> n
                 then
                   let (ves', ves'') = split_n ves n in
                   case host_apply_impl s (t1s _> t2s) h (rev ves') of
                     Some (s',rves) \<Rightarrow> 
                       if list_all2 types_agree t2s rves
                         then
                           (s', f, RSNormal ((rev rves)@ves'') es')
                         else
                           (s', f, crash_error)
                   | None \<Rightarrow> (s, f, res_trap ves'' es')
                 else
                   (s, f, crash_error))
      \<comment> \<open>\<open>LABEL\<close>\<close>
      | Label ln les es \<Rightarrow>
          if es_is_trap es
            then
              (s, f, res_trap ves es')
             else
               (case (split_vals_e es) of
                  (lsves, []) \<Rightarrow> (s, f, RSNormal ((rev lsves)@ves) es')
                | (lsves, lses) \<Rightarrow> 
                    let (s', f', res) = run_step d (s, f, (rev lsves, lses)) in
                    (case res of
                       RSBreak 0 bvs \<Rightarrow>
                         if (length bvs \<ge> ln)
                           then (s', f', RSNormal ((take ln bvs)@ves) (les@es'))
                           else (s', f', crash_error)
                     | RSBreak (Suc n) bvs \<Rightarrow>
                         (s', f', RSBreak n bvs)
                     | RSReturn rvs \<Rightarrow>
                         (s', f', RSReturn rvs)
                     | RSNormal lsves' lses' \<Rightarrow>
                         (s', f', RSNormal ves ((Label ln les ((vs_to_es lsves')@lses'))#es'))
                     | RSCrash c \<Rightarrow> (s', f', RSCrash c)))
     \<comment> \<open>\<open>LOCAL\<close>\<close>
     | Frame ln fls es \<Rightarrow>
          if es_is_trap es
            then
              (s, f, res_trap ves es')
             else
               (case (split_vals_e es) of
                  (fsves, []) \<Rightarrow> (s, f, RSNormal ((rev fsves)@ves) es')
                | (fsves, fses) \<Rightarrow> 
                    case d of
                      0 \<Rightarrow> (s, f, RSCrash CExhaustion)
                    | Suc d' \<Rightarrow>
                        let (s', fls', res) = run_step d' (s, fls, (rev fsves, fses)) in
                        (case res of
                           RSReturn rvs \<Rightarrow>
                             if (length rvs \<ge> ln)
                               then (s', f, RSNormal ((take ln rvs)@ves) (es'))
                               else (s', f, crash_error)
                         | RSNormal fsves' fses' \<Rightarrow>
                             (s', f, RSNormal ves ((Frame ln fls' ((vs_to_es fsves')@fses')) # es'))
                         | RSBreak _ _ \<Rightarrow> (s', f, crash_error)
                         | RSCrash c \<Rightarrow> (s', f, RSCrash c)))
     \<comment> \<open>\<open>TRAP\<close> - should not be executed\<close>
     | Trap \<Rightarrow> (s, f, crash_error))"
  by pat_completeness auto
termination
proof -
  {
    fix xs::"e list" and as b bs
    assume local_assms:"(as,b#bs) = split_vals_e xs"
    have "(size b + size_list size bs) \<le> (size_list size xs)"
      using split_vals_e_conv_app
            local_assms[symmetric]
            size_list_append[of size _ bs]
      by fastforce
  }
  thus ?thesis
    apply (relation "measure (\<lambda>p. size_list size (snd (snd (snd (snd p)))))")
    apply fastforce+
    done
qed

fun run_vs_es :: "fuel \<Rightarrow> depth \<Rightarrow> config_tuple \<Rightarrow> (s \<times> res)" where
  "run_vs_es (Suc n) d (s,f,(ves,es)) = (if (es_is_trap es)
                                    then (s, RTrap)
                                    else if (es = [])
                                           then (s, RValue (rev ves))
                                           else (let (s',f',res) = (run_step d (s,f,(ves,es))) in
                                                 case res of
                                                   RSNormal ves' es' \<Rightarrow> run_vs_es n d (s',f',(ves',es'))
                                                 | RSCrash error \<Rightarrow> (s, RCrash error)
                                                 | _ \<Rightarrow> (s, RCrash CError)))"
| "run_vs_es 0 d (s,f,(ves,es)) = (s, RCrash CExhaustion)"

fun run_v :: "fuel \<Rightarrow> depth \<Rightarrow> (s \<times> f \<times> e list) \<Rightarrow> (s \<times> res)" where
  "run_v n d (s,f,es) = (let (ves, es') = split_vals_e es in run_vs_es n d (s,f,(rev ves, es')))"

end
