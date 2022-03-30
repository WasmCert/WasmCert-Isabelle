section {* Executable Type Checker *}

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
| check_block:"check_single \<C> (Block (tn _> tm) es) ts = (if (b_e_type_checker (\<C>\<lparr>label := ([tm] @ (label \<C>))\<rparr>) es (tn _> tm))
                                                            then type_update ts (to_ct_list tn) (Type tm)
                                                            else Bot)"
  (* loop *)
| check_loop:"check_single \<C> (Loop (tn _> tm) es) ts = (if (b_e_type_checker (\<C>\<lparr>label := ([tn] @ (label \<C>))\<rparr>) es (tn _> tm))
                                                          then type_update ts (to_ct_list tn) (Type tm)
                                                          else Bot)"
  (* if *)
| check_if:"check_single \<C> (If (tn _> tm) es1 es2) ts = (if (b_e_type_checker (\<C>\<lparr>label := ([tm] @ (label \<C>))\<rparr>) es1 (tn _> tm)
                                                              \<and> b_e_type_checker (\<C>\<lparr>label := ([tm] @ (label \<C>))\<rparr>) es2 (tn _> tm))
                                                            then type_update ts (to_ct_list (tn@[T_num T_i32])) (Type tm)
                                                            else Bot)"
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

end
