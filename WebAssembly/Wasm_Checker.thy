section \<open>Executable Type Checker\<close>

theory Wasm_Checker imports Wasm_Checker_Types begin

fun convert_cond :: "t_num \<Rightarrow> t_num \<Rightarrow> (sat \<times> sx) option \<Rightarrow> bool" where
  "convert_cond t1 t2 sat_sx = ((t1 \<noteq> t2) \<and> (sat_sx = None) = ((is_float_t_num t1 \<and> is_float_t_num t2)
                                                                 \<or> (is_int_t_num t1 \<and> is_int_t_num t2 \<and> (t_num_length t1 < t_num_length t2))))"

fun same_lab_h :: "nat list \<Rightarrow> (t list) list \<Rightarrow> t list \<Rightarrow> (t list) option" where
  "same_lab_h [] _ ts = Some ts"
| "same_lab_h (i#is) lab_c ts = (if i \<ge> length lab_c
                                 then None
                                 else (if lab_c!i = ts
                                       then same_lab_h is lab_c (lab_c!i)
                                       else None))" 

fun same_lab :: "nat list \<Rightarrow> (t list) list \<Rightarrow> (t list) option" where
  "same_lab [] lab_c = None"
| "same_lab (i#is) lab_c = (if i \<ge> length lab_c
                            then None
                            else same_lab_h is lab_c (lab_c!i))"

lemma same_lab_h_conv_list_all:
  assumes "same_lab_h ils ls ts' = Some ts"
  shows "list_all (\<lambda>i. i < length ls \<and> ls!i = ts) ils \<and> ts' = ts"
  using assms
proof(induction ils)
  case (Cons a ils)
  thus ?case
    apply (simp,safe)
       apply (metis not_less option.distinct(1))+
    done
qed simp

lemma same_lab_conv_list_all:
  assumes "same_lab ils ls = Some ts"
  shows "list_all (\<lambda>i. i < length ls \<and> ls!i = ts) ils"
  using assms
proof (induction rule: same_lab.induct)
case (2 i "is" lab_c)
  thus ?case
    using same_lab_h_conv_list_all
    by (metis (mono_tags, lifting) list_all_simps(1) not_less option.distinct(1) same_lab.simps(2))
qed simp

lemma list_all_conv_same_lab_h:
  assumes "list_all (\<lambda>i. i < length ls \<and> ls!i = ts) ils"
  shows "same_lab_h ils ls ts = Some ts"
  using assms
  by (induction ils, simp_all)

lemma list_all_conv_same_lab:
  assumes "list_all (\<lambda>i. i < length ls \<and>ls!i = ts) (is@[i])"
  shows "same_lab (is@[i]) ls = Some ts"                      
  using assms
proof (induction "(is@[i])")
  case (Cons a x)
  thus ?case
    using list_all_conv_same_lab_h[OF Cons(3)]
    by (metis option.distinct(1) same_lab.simps(2) same_lab_h.simps(2))
qed auto

fun b_e_type_checker :: "t_context \<Rightarrow>  b_e list \<Rightarrow> tf \<Rightarrow> bool"
and check :: "t_context \<Rightarrow> b_e list \<Rightarrow> c_t \<Rightarrow> c_t option"
and check_single :: "t_context \<Rightarrow>  b_e \<Rightarrow> c_t \<Rightarrow> c_t option" where
  check_top:"b_e_type_checker \<C> es (tn _> tm) =
    (case (check \<C> es (tn, Reach)) of
      None \<Rightarrow> False
    | Some ts \<Rightarrow>  c_types_agree ts tm)"
| check_iter:"check \<C> es ts = (case es of
                                 [] \<Rightarrow> Some ts
                               | (e#es) \<Rightarrow> (case (check_single \<C> e ts) of 
                                              Some ts' \<Rightarrow> check \<C> es ts'))
                                           "
  (* num ops *)
| check_const_num:"check_single \<C> (EConstNum v) ts = type_update ts [] ([T_num (typeof_num v)])"
| check_const_vec:"check_single \<C> (EConstVec v) ts = type_update ts [] ([T_vec (typeof_vec v)])"
| check_unop:"check_single \<C> (Unop t op) ts = (if unop_t_num_agree op t
                                                then type_update ts [T_num t] [T_num t]
                                                else None)"
| check_binop:"check_single \<C> (Binop t op) ts = (if binop_t_num_agree op t
                                                   then type_update ts [(T_num t), (T_num t)] ([T_num t])
                                                   else None)"
| check_testop:"check_single \<C> (Testop t _) ts = (if is_int_t_num t
                                                    then type_update ts [(T_num t)] ([T_num T_i32])
                                                    else None)"
| check_relop:"check_single \<C> (Relop t op) ts = (if relop_t_num_agree op t
                                                   then type_update ts [(T_num t), (T_num t)] ([T_num T_i32])
                                                   else None)"
  (* vector ops *)
| check_unop_vec:"check_single \<C> (Unop_vec op) ts = (type_update ts [(T_vec T_v128)] ([T_vec T_v128]))"
| check_binop_vec:"check_single \<C> (Binop_vec op) ts = (if binop_vec_wf op
                                                               then type_update ts [(T_vec T_v128), (T_vec T_v128)] ([T_vec T_v128])
                                                               else None)"
| check_ternop_vec:"check_single \<C> (Ternop_vec op) ts = (type_update ts [(T_vec T_v128), (T_vec T_v128), (T_vec T_v128)] ([T_vec T_v128]))"
| check_test_vec:"check_single \<C> (Test_vec op) ts = (type_update ts [(T_vec T_v128)] ([T_num T_i32]))"
| check_shift_vec:"check_single \<C> (Shift_vec op) ts = (type_update ts [(T_vec T_v128), (T_num T_i32)] ([T_vec T_v128]))"
| check_splat_vec:"check_single \<C> (Splat_vec sv) ts = (type_update ts [(T_num (vec_lane_t sv))] ([T_vec T_v128]))"
| check_extract_vec:"check_single \<C> (Extract_vec sv sx i) ts = (if i < vec_num sv \<and> (sx = U \<or> vec_length sv \<le> 2)
                                                                 then type_update ts [(T_vec T_v128)] ([T_num (vec_lane_t sv)])
                                                                 else None)"
| check_replace_vec:"check_single \<C> (Replace_vec sv i) ts = (if i < vec_num sv
                                                               then type_update ts [(T_vec T_v128), (T_num (vec_lane_t sv))] ([T_vec T_v128])
                                                               else None)"
  \<comment> \<open>\<open>references\<close>\<close>
| check_null_ref: "check_single \<C> (Null_ref t) ts = type_update ts [] [T_ref t]"
| check_is_null_ref: "check_single \<C> (Is_null_ref) ts = type_update_is_null_ref ts"
| check_ref_func: "check_single \<C> (Ref_func j) ts = (if j < length (func_t \<C>) \<and> j \<in> set (refs \<C>) then type_update ts [] [T_ref T_func_ref] else None)"
(* convert *)
| check_convert:"check_single \<C> (Cvtop t1 Convert t2 sat_sx) ts = (if (convert_cond t1 t2 sat_sx)
                                                                     then type_update ts [(T_num t2)] ([T_num t1])
                                                                     else None)"
  (* reinterpret *)
| check_reinterpret:"check_single \<C> (Cvtop t1 Reinterpret t2 sx) ts = (if ((t1 \<noteq> t2) \<and> t_num_length t1 = t_num_length t2 \<and> sx = None)
                                                                         then type_update ts [(T_num t2)] ([T_num t1])
                                                                         else None)"
  (* unreachable, nop, drop, select *)
| check_unreachable:"check_single \<C> (Unreachable) ts = Some ([], Unreach)"
| check_nop:"check_single \<C> (Nop) ts = Some ts"
| check_drop:"check_single \<C> (Drop) ts = type_update_drop ts"
| check_select:"check_single \<C> (Select t_tag) ts = type_update_select ts t_tag"
  (* block *)                                 
| check_block:"check_single \<C> (Block tb es) ts = (case tb_tf_t \<C> tb of
                                                    Some (tn _> tm) \<Rightarrow>
                                                      (if (b_e_type_checker (\<C>\<lparr>label := ([tm] @ (label \<C>))\<rparr>) es (tn _> tm))
                                                        then type_update ts tn tm
                                                        else None)
                                                  | None \<Rightarrow> None)"
  (* loop *)
| check_loop:"check_single \<C> (Loop tb es) ts = (case tb_tf_t \<C> tb of
                                                  Some (tn _> tm) \<Rightarrow>
                                                    (if (b_e_type_checker (\<C>\<lparr>label := ([tn] @ (label \<C>))\<rparr>) es (tn _> tm))
                                                      then type_update ts tn tm
                                                      else None)
                                                | None \<Rightarrow> None)"
  (* if *)
| check_if:"check_single \<C> (If tb es1 es2) ts = (case tb_tf_t \<C> tb of
                                                   Some (tn _> tm) \<Rightarrow> (if (b_e_type_checker (\<C>\<lparr>label := ([tm] @ (label \<C>))\<rparr>) es1 (tn _> tm)
                                                              \<and> b_e_type_checker (\<C>\<lparr>label := ([tm] @ (label \<C>))\<rparr>) es2 (tn _> tm))
                                                            then type_update ts (tn@[T_num T_i32]) tm
                                                            else None)
                                                 | None => None)"
  (* br *)
| check_br:"check_single \<C> (Br i) ts = (if i < length (label \<C>) \<and> (consume ts ((label \<C>)!i)) \<noteq> None
                                         then (Some ([], Unreach))
                                         else None)"
  (* br_if *)
| check_br_if:"check_single \<C> (Br_if i) ts = (if i < length (label \<C>)
                                                then type_update ts (((label \<C>)!i @ [T_num T_i32])) (((label \<C>)!i))
                                                else None)"
  (* br_table *)
| check_br_table:"check_single \<C> (Br_table is i) ts = (case (same_lab (is@[i]) (label \<C>)) of
                                                        None \<Rightarrow> None
                                                      | Some tls \<Rightarrow>  (if ((consume ts (tls @ [T_num T_i32])) \<noteq> None) then Some ([], Unreach) else None))"
  (* return *)
| check_return:"check_single \<C> (Return) ts = (case (return \<C>) of
                                               None \<Rightarrow> None
                                             | Some tls \<Rightarrow> (if ((consume ts tls) \<noteq> None) then Some ([], Unreach) else None))"
  (* call *)
| check_call:"check_single \<C> (Call i) ts = (if i < length (func_t \<C>)
                                              then (case ((func_t \<C>)!i) of
                                                      (tn _> tm) \<Rightarrow> type_update ts tn tm)
                                              else None)"
  (* | call_indirect:"\<lbrakk>i < length(types_t \<C>); (types_t \<C>)!i = (t1s _> t2s); ti < length (table \<C>); (table \<C>)!ti = T_tab _  T_func_ref\<rbrakk> \<Longrightarrow> \<C> \<turnstile> [Call_indirect ti i] : (t1s @ [T_num T_i32] _> t2s)" *)
  (* call_indirect *)
| check_call_indirect:"check_single \<C> (Call_indirect ti i) ts = (if i < length (types_t \<C>) \<and> ti < length (table \<C>)
                                                                then
                                                                  (case ((types_t \<C>)!i, (table \<C>)!ti) of
                                                                    ((tn _> tm), T_tab _  T_func_ref) \<Rightarrow> type_update ts ((tn@[T_num T_i32])) (tm)
                                                                  | _ \<Rightarrow> None)
                                                                else None)"
  (* get_local *)
| check_get_local:"check_single \<C> (Get_local i) ts = (if i < length (local \<C>)
                                                        then type_update ts [] [(local \<C>)!i]
                                                        else None)"
  (* set_local *)
| check_set_local:"check_single \<C> (Set_local i) ts = (if i < length (local \<C>)
                                                        then type_update ts [(local \<C>)!i] []
                                                        else None)"
  (* tee_local *)
| check_tee_local:"check_single \<C> (Tee_local i) ts = (if i < length (local \<C>)
                                                       then type_update ts [(local \<C>)!i] [(local \<C>)!i]
                                                       else None)"
  (* get_global *)
| check_get_global:"check_single \<C> (Get_global i) ts = (if i < length (global \<C>)
                                                         then type_update ts [] [tg_t ((global \<C>)!i)]
                                                         else None)"
  (* set_global *)
| check_set_global:"check_single \<C> (Set_global i) ts = (if i < length (global \<C>) \<and> is_mut (global \<C> ! i)
                                                         then type_update ts [tg_t ((global \<C>)!i)] []
                                                         else None)"
  (* load *)
| check_load:"check_single \<C> (Load t tp_sx a off) ts = (if length (memory \<C>) \<ge> 1 \<and> load_store_t_bounds a (option_projl tp_sx) t
                                                         then type_update ts [T_num T_i32] [T_num t]
                                                         else None)"
  (* store *)
| check_store:"check_single \<C> (Store t tp a off) ts = (if length (memory \<C>) \<ge> 1 \<and> load_store_t_bounds a tp t
                                                         then type_update ts [T_num T_i32, T_num t] []
                                                         else None)"
  (* load_vec *)
| check_load_vec:"check_single \<C> (Load_vec lv a off) ts = (if length (memory \<C>) \<ge> 1 \<and> load_vec_t_bounds lv a
                                                             then type_update ts [T_num T_i32] [T_vec T_v128]
                                                             else None)"
  (* load_lane_vec *)
| check_load_lane_vec:"check_single \<C> (Load_lane_vec svi i a off) ts = (if length (memory \<C>) \<ge> 1 \<and> (i < vec_i_num svi \<and> 2^a \<le> (vec_i_length svi))
                                                                         then type_update ts [T_num T_i32, T_vec T_v128] [T_vec T_v128]
                                                                         else None)"
  (* store_vec *)
| check_store_vec:"check_single \<C> (Store_vec sv a off) ts = (if length (memory \<C>) \<ge> 1 \<and> store_vec_t_bounds sv a
                                                               then type_update ts [T_num T_i32, T_vec T_v128]  []
                                                               else None)"
  (* current_memory *)
| check_current_memory:"check_single \<C> Current_memory ts = (if length (memory \<C>) \<ge> 1
                                                             then type_update ts []  [T_num T_i32]
                                                             else None)"
  (* grow_memory *)
| check_grow_memory:"check_single \<C> Grow_memory ts = (if length (memory \<C>) \<ge> 1
                                                        then type_update ts [T_num T_i32] [T_num T_i32]
                                                        else None)"
  (* memory_init *)
| check_memory_init: "check_single \<C> (Memory_init i) ts = (if length (memory \<C>) \<ge> 1 \<and> i < length (data \<C>)
                                                        then type_update ts [T_num T_i32, T_num T_i32, T_num T_i32] []
                                                        else None)"
  (* memory_copy *)
| check_memory_copy:"check_single \<C> Memory_copy ts = (if length (memory \<C>) \<ge> 1
                                                        then type_update ts [T_num T_i32, T_num T_i32, T_num T_i32] []
                                                        else None)"
  (* memory_fill *)
| check_memory_fill:"check_single \<C> Memory_fill ts = (if length (memory \<C>) \<ge> 1
                                                        then type_update ts [T_num T_i32, T_num T_i32, T_num T_i32] []
                                                        else None)"
  (* table set *)
| check_table_set:"check_single \<C> (Table_set ti) ts = (if ti < length (table \<C>)
                                                            then type_update ts [T_num T_i32, T_ref (tab_t_reftype (table \<C>!ti))] []
                                                            else None)"
  (* table get *)
| check_table_get:"check_single \<C> (Table_get ti) ts = (if ti < length (table \<C>)
                                                            then type_update ts [T_num T_i32] [T_ref (tab_t_reftype (table \<C>!ti))]
                                                            else None)"
  (* table size *)
| check_table_size:"check_single \<C> (Table_size ti) ts = (if ti < length (table \<C>)
                                                            then type_update ts [] [T_num T_i32]
                                                            else None)"
  (* table grow *)
| check_table_grow:"check_single \<C> (Table_grow ti) ts = (if ti < length (table \<C>)
                                                            then type_update ts [T_ref (tab_t_reftype (table \<C>!ti)), T_num T_i32] []
                                                            else None)"
| check_table_init:"check_single \<C> (Table_init x y) ts = (if x < length (table \<C>) \<and> y < length (elem \<C>) \<and> tab_t_reftype (table \<C>!x) = elem \<C>!y
                                                            then type_update ts [T_num T_i32, T_num T_i32, T_num T_i32] []
                                                            else None)"
  (* table_init *)
| check_table_copy:"check_single \<C> (Table_copy x y) ts = (if x < length (table \<C>) \<and> y < length (table \<C>) \<and> tab_t_reftype (table \<C>!x) = elem \<C>!y
                                                            then type_update ts [T_num T_i32, T_num T_i32, T_num T_i32] []
                                                            else None)"
  (* table_fill *)
| check_table_fill:"check_single \<C> (Table_fill x) ts = (if x < length (table \<C>)
                                                            then type_update ts [T_num T_i32, T_ref (tab_t_reftype (table \<C>!x)), T_num T_i32] []
                                                            else None)"
  (* elem_drop *)
| check_elem_drop:"check_single \<C> (Elem_drop x) ts = (if x < length (elem \<C>) then type_update ts [] [] else None)"
  (* data_drop *)
| check_data_drop:"check_single \<C> (Data_drop x) ts = (if x < length (data \<C>) then type_update ts [] [] else None)"


(*
fun b_e_type_checker :: "t_context \<Rightarrow>  b_e list \<Rightarrow> tf \<Rightarrow> bool"
and check :: "t_context \<Rightarrow> b_e list \<Rightarrow> checker_type \<Rightarrow> checker_type"
and check_single :: "t_context \<Rightarrow>  b_e \<Rightarrow> checker_type \<Rightarrow> checker_type" where
  check_top:"b_e_type_checker \<C> es (tn _> tm) = c_types_agree (check \<C> es (Type tn)) tm"
| check_iter:"check \<C> es ts = (case es of
                                 [] \<Rightarrow> ts
                               | (e#es) \<Rightarrow> (case ts of 
                                              Bot \<Rightarrow> Bot
                                           | _ \<Rightarrow> check \<C> es (check_single \<C> e ts)))"
(*
foldl (\<lambda> ts e. (case ts of Bot \<Rightarrow> Bot | _ \<Rightarrow> check_single \<C> e ts)) es



primrec foldl :: "('b \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'a list \<Rightarrow> 'b" where
foldl_Nil:  "foldl f a [] = a" |
foldl_Cons: "foldl f a (x # xs) = foldl f (f a x) xs"
*)
  (* num ops *)
| check_const:"check_single \<C> (C v) ts = type_update ts [] (Type [typeof v])"
| check_unop:"check_single \<C> (Unop t op) ts = (if unop_t_num_agree op t
                                                then type_update ts [TSome (T_num t)] (Type [T_num t])
                                                else Bot)"
| check_binop:"check_single \<C> (Binop t op) ts = (if binop_t_num_agree op t
                                                   then type_update ts [TSome (T_num t), TSome (T_num t)] (Type [T_num t])
                                                   else Bot)"
| check_testop:"check_single \<C> (Testop t _) ts = (if is_int_t_num t
                                                    then type_update ts [TSome (T_num t)] (Type [T_num T_i32])
                                                    else Bot)"
| check_relop:"check_single \<C> (Relop t op) ts = (if relop_t_num_agree op t
                                                   then type_update ts [TSome (T_num t), TSome (T_num t)] (Type [T_num T_i32])
                                                   else Bot)"
  (* vector ops *)
| check_unop_vec:"check_single \<C> (Unop_vec op) ts = (type_update ts [TSome (T_vec T_v128)] (Type [T_vec T_v128]))"
| check_binop_vec:"check_single \<C> (Binop_vec op) ts = (if binop_vec_wf op
                                                               then type_update ts [TSome (T_vec T_v128), TSome (T_vec T_v128)] (Type [T_vec T_v128])
                                                               else Bot)"
| check_ternop_vec:"check_single \<C> (Ternop_vec op) ts = (type_update ts [TSome (T_vec T_v128), TSome (T_vec T_v128), TSome (T_vec T_v128)] (Type [T_vec T_v128]))"
| check_test_vec:"check_single \<C> (Test_vec op) ts = (type_update ts [TSome (T_vec T_v128)] (Type [T_num T_i32]))"
| check_shift_vec:"check_single \<C> (Shift_vec op) ts = (type_update ts [TSome (T_vec T_v128), TSome (T_num T_i32)] (Type [T_vec T_v128]))"
| check_splat_vec:"check_single \<C> (Splat_vec sv) ts = (type_update ts [TSome (T_num (vec_lane_t sv))] (Type [T_vec T_v128]))"
| check_extract_vec:"check_single \<C> (Extract_vec sv sx i) ts = (if i < vec_num sv \<and> (sx = U \<or> vec_length sv \<le> 2)
                                                                 then type_update ts [TSome (T_vec T_v128)] (Type [T_num (vec_lane_t sv)])
                                                                 else Bot)"
| check_replace_vec:"check_single \<C> (Replace_vec sv i) ts = (if i < vec_num sv
                                                               then type_update ts [TSome (T_vec T_v128), TSome (T_num (vec_lane_t sv))] (Type [T_vec T_v128])
                                                               else Bot)"
  (* convert *)
| check_convert:"check_single \<C> (Cvtop t1 Convert t2 sat_sx) ts = (if (convert_cond t1 t2 sat_sx)
                                                                     then type_update ts [TSome (T_num t2)] (Type [T_num t1])
                                                                     else Bot)"
  (* reinterpret *)
| check_reinterpret:"check_single \<C> (Cvtop t1 Reinterpret t2 sx) ts = (if ((t1 \<noteq> t2) \<and> t_num_length t1 = t_num_length t2 \<and> sx = None)
                                                                         then type_update ts [TSome (T_num t2)] (Type [T_num t1])
                                                                         else Bot)"
  (* unreachable, nop, drop, select *)
| check_unreachable:"check_single \<C> (Unreachable) ts = type_update ts [] (TopType [])"
| check_nop:"check_single \<C> (Nop) ts = ts"
| check_drop:"check_single \<C> (Drop) ts = type_update ts [TAny] (Type [])"
| check_select:"check_single \<C> (Select) ts = type_update_select ts"
  (* block *)                                 
| check_block:"check_single \<C> (Block tb es) ts = (case tb_tf_t \<C> tb of
                                                    Some (tn _> tm) \<Rightarrow>
                                                      (if (b_e_type_checker (\<C>\<lparr>label := ([tm] @ (label \<C>))\<rparr>) es (tn _> tm))
                                                        then type_update ts (to_ct_list tn) (Type tm)
                                                        else Bot)
                                                  | None \<Rightarrow> Bot)"
  (* loop *)
| check_loop:"check_single \<C> (Loop tb es) ts = (case tb_tf_t \<C> tb of
                                                  Some (tn _> tm) \<Rightarrow>
                                                    (if (b_e_type_checker (\<C>\<lparr>label := ([tn] @ (label \<C>))\<rparr>) es (tn _> tm))
                                                      then type_update ts (to_ct_list tn) (Type tm)
                                                      else Bot)
                                                | None \<Rightarrow> Bot)"
  (* if *)
| check_if:"check_single \<C> (If tb es1 es2) ts = (case tb_tf_t \<C> tb of
                                                   Some (tn _> tm) \<Rightarrow> (if (b_e_type_checker (\<C>\<lparr>label := ([tm] @ (label \<C>))\<rparr>) es1 (tn _> tm)
                                                              \<and> b_e_type_checker (\<C>\<lparr>label := ([tm] @ (label \<C>))\<rparr>) es2 (tn _> tm))
                                                            then type_update ts (to_ct_list (tn@[T_num T_i32])) (Type tm)
                                                            else Bot)
                                                 | None => Bot)"
  (* br *)
| check_br:"check_single \<C> (Br i) ts = (if i < length (label \<C>)
                                         then type_update ts (to_ct_list ((label \<C>)!i)) (TopType [])
                                         else Bot)"
  (* br_if *)
| check_br_if:"check_single \<C> (Br_if i) ts = (if i < length (label \<C>)
                                                then type_update ts (to_ct_list ((label \<C>)!i @ [T_num T_i32])) (Type ((label \<C>)!i))
                                                else Bot)"
  (* br_table *)
| check_br_table:"check_single \<C> (Br_table is i) ts = (case (same_lab (is@[i]) (label \<C>)) of
                                                        None \<Rightarrow> Bot
                                                      | Some tls \<Rightarrow> type_update ts (to_ct_list (tls @ [T_num T_i32])) (TopType []))"
  (* return *)
| check_return:"check_single \<C> (Return) ts = (case (return \<C>) of
                                               None \<Rightarrow> Bot
                                             | Some tls \<Rightarrow> type_update ts (to_ct_list tls) (TopType []))"
  (* call *)
| check_call:"check_single \<C> (Call i) ts = (if i < length (func_t \<C>)
                                              then (case ((func_t \<C>)!i) of
                                                      (tn _> tm) \<Rightarrow> type_update ts (to_ct_list tn) (Type tm))
                                              else Bot)"
  (* call_indirect *)
| check_call_indirect:"check_single \<C> (Call_indirect i) ts = (if length (table \<C>) \<ge> 1  \<and> i < length (types_t \<C>)
                                                                then (case ((types_t \<C>)!i) of
                                                                        (tn _> tm) \<Rightarrow> type_update ts (to_ct_list (tn@[T_num T_i32])) (Type tm))
                                                                else Bot)"
  (* get_local *)
| check_get_local:"check_single \<C> (Get_local i) ts = (if i < length (local \<C>)
                                                        then type_update ts [] (Type [(local \<C>)!i])
                                                        else Bot)"
  (* set_local *)
| check_set_local:"check_single \<C> (Set_local i) ts = (if i < length (local \<C>)
                                                        then type_update ts [TSome ((local \<C>)!i)] (Type [])
                                                        else Bot)"
  (* tee_local *)
| check_tee_local:"check_single \<C> (Tee_local i) ts = (if i < length (local \<C>)
                                                       then type_update ts [TSome ((local \<C>)!i)] (Type [(local \<C>)!i])
                                                       else Bot)"
  (* get_global *)
| check_get_global:"check_single \<C> (Get_global i) ts = (if i < length (global \<C>)
                                                         then type_update ts [] (Type [tg_t ((global \<C>)!i)])
                                                         else Bot)"
  (* set_global *)
| check_set_global:"check_single \<C> (Set_global i) ts = (if i < length (global \<C>) \<and> is_mut (global \<C> ! i)
                                                         then type_update ts [TSome (tg_t ((global \<C>)!i))] (Type [])
                                                         else Bot)"
  (* load *)
| check_load:"check_single \<C> (Load t tp_sx a off) ts = (if length (memory \<C>) \<ge> 1 \<and> load_store_t_bounds a (option_projl tp_sx) t
                                                         then type_update ts [TSome (T_num T_i32)] (Type [T_num t])
                                                         else Bot)"
  (* store *)
| check_store:"check_single \<C> (Store t tp a off) ts = (if length (memory \<C>) \<ge> 1 \<and> load_store_t_bounds a tp t
                                                         then type_update ts [TSome (T_num T_i32),TSome (T_num t)] (Type [])
                                                         else Bot)"
  (* load_vec *)
| check_load_vec:"check_single \<C> (Load_vec lv a off) ts = (if length (memory \<C>) \<ge> 1 \<and> load_vec_t_bounds lv a
                                                             then type_update ts [TSome (T_num T_i32)] (Type [T_vec T_v128])
                                                             else Bot)"
  (* load_lane_vec *)
| check_load_lane_vec:"check_single \<C> (Load_lane_vec svi i a off) ts = (if length (memory \<C>) \<ge> 1 \<and> (i < vec_i_num svi \<and> 2^a \<le> (vec_i_length svi))
                                                                         then type_update ts [TSome (T_num T_i32), TSome (T_vec T_v128)] (Type [T_vec T_v128])
                                                                         else Bot)"
  (* store_vec *)
| check_store_vec:"check_single \<C> (Store_vec sv a off) ts = (if length (memory \<C>) \<ge> 1 \<and> store_vec_t_bounds sv a
                                                               then type_update ts [TSome (T_num T_i32),TSome (T_vec T_v128)] (Type [])
                                                               else Bot)"
  (* current_memory *)
| check_current_memory:"check_single \<C> Current_memory ts = (if length (memory \<C>) \<ge> 1
                                                             then type_update ts [] (Type [T_num T_i32])
                                                             else Bot)"
  (* grow_memory *)
| check_grow_memory:"check_single \<C> Grow_memory ts = (if length (memory \<C>) \<ge> 1
                                                        then type_update ts [TSome (T_num T_i32)] (Type [T_num T_i32])
                                                        else Bot)"
*)
end
