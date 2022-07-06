theory Wasm_Interpreter_Monad imports Wasm_Interpreter_Monad_Config 
  Wasm_Native_Word_Entry   begin



definition mem_m_to_m :: "heap \<Rightarrow> mem_m \<Rightarrow> mem" where
"mem_m_to_m h mem_m \<equiv>
  (Abs_mem_rep (Array.get h (Rep_byte_array (fst mem_m))), snd mem_m)"

definition inst_m_to_inst :: "heap \<Rightarrow> inst_m \<Rightarrow> inst" where
"inst_m_to_inst h inst_m \<equiv>
   \<lparr>inst.types = Array.get h (inst_m.types inst_m),
    inst.funcs = Array.get h (inst_m.funcs inst_m),
    inst.tabs = Array.get h (inst_m.tabs inst_m),
    inst.mems = Array.get h (inst_m.mems inst_m),
    inst.globs = Array.get h (inst_m.globs inst_m)\<rparr>"

definition cl_m_to_cl :: "heap \<Rightarrow> cl_m \<Rightarrow> cl" where
"cl_m_to_cl h cl_m \<equiv>
  case cl_m of
    (cl_m.Func_host tf host) \<Rightarrow>
        cl.Func_host tf host
  | (cl_m.Func_native i_m tf tlocs b_es) \<Rightarrow>
       cl.Func_native (inst_m_to_inst h i_m) tf tlocs b_es"

definition tabinst_m_to_tabinst :: "heap \<Rightarrow> tabinst_m \<Rightarrow> tabinst" where
"tabinst_m_to_tabinst h tab_m \<equiv>
   (Array.get h (fst tab_m), snd tab_m)"

definition s_m_to_s :: "heap \<Rightarrow> s_m \<Rightarrow> s" where
"s_m_to_s h s_m \<equiv>
  \<lparr> s.funcs = map (cl_m_to_cl h) (Array.get h (s_m.funcs s_m)),
    s.tabs = map (tabinst_m_to_tabinst h) (Array.get h (s_m.tabs s_m)),
    s.mems = map (mem_m_to_m h) (Array.get h (s_m.mems s_m)),
    s.globs = (Array.get h (s_m.globs s_m)) \<rparr>"

definition frame_m_to_frame :: "heap \<Rightarrow> v array \<Rightarrow> inst_m \<Rightarrow> f" where
"frame_m_to_frame h varr inst_m \<equiv>
   \<lparr> f_locs = Array.get h varr, f_inst = (inst_m_to_inst h inst_m) \<rparr>"

definition frame_context_m_to_frame_context :: "heap \<Rightarrow> frame_context_m \<Rightarrow> frame_context" where
"frame_context_m_to_frame_context h fc_m \<equiv>
   case fc_m of
     (Frame_context_m rdx lcs n fc_locs fc_inst) \<Rightarrow>
       Frame_context rdx lcs n (frame_m_to_frame h fc_locs fc_inst)"

definition config_m_to_config :: "heap \<Rightarrow> config_m \<Rightarrow> config" where
"config_m_to_config h cfg_m \<equiv>
   case (cfg_m) of
     (Config_m d s_m fc_m fcs_m) \<Rightarrow>
        Config d (s_m_to_s h s_m) (frame_context_m_to_frame_context h fc_m) (map (frame_context_m_to_frame_context h) fcs_m)"

definition tb_tf_m :: "inst_m \<Rightarrow> tb \<Rightarrow> tf Heap" where
  "tb_tf_m tfa tb = (case tb of
                       Tbf i \<Rightarrow> Array.nth (inst_m.types tfa) i
                     | Tbv (Some t) \<Rightarrow> return ([] _> [t])
                     | Tbv None \<Rightarrow> return ([] _> []))"

fun list_blit_array :: "'a::heap list \<Rightarrow> 'a array \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "list_blit_array src_list dst dst_pos =
   (case src_list of
      [] \<Rightarrow> return ()
    | y#ys \<Rightarrow>
        do {
          Array.upd dst_pos y dst;
          list_blit_array ys dst (dst_pos+1)
        })"

fun array_blit_map :: "'b list \<Rightarrow> ('b \<Rightarrow> ('a::heap) Heap) \<Rightarrow> 'a array \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "array_blit_map src_list src_f dst dst_pos = do {
     ys \<leftarrow> Heap_Monad.fold_map src_f src_list;
     list_blit_array ys dst dst_pos
  }"

definition app_f_v_s_get_local_m :: "nat \<Rightarrow> v array \<Rightarrow> v_stack \<Rightarrow> (v_stack \<times> res_step) Heap" where
  "app_f_v_s_get_local_m k loc_arr v_s =
     do {
       v \<leftarrow> Array.nth loc_arr k;
       return (v#v_s, Step_normal) }"

definition app_f_v_s_set_local_m :: "nat \<Rightarrow> v array \<Rightarrow> v_stack \<Rightarrow> (v_stack \<times> res_step) Heap" where
  "app_f_v_s_set_local_m k loc_arr v_s =
     (case v_s of
        v1#v_s' \<Rightarrow>
          do {
            Array.upd k v1 loc_arr;
            return (v_s', Step_normal) }
      | _ \<Rightarrow> return (v_s, crash_invalid))"

definition app_f_call_m :: "nat \<Rightarrow> inst_m \<Rightarrow> (e list \<times> res_step) Heap" where
  "app_f_call_m k inst_m =
     do {
       i_cl \<leftarrow> Array.nth (inst_m.funcs inst_m) k;
       return ([Invoke i_cl], Step_normal) }"

definition app_s_f_v_s_call_indirect_m :: "nat \<Rightarrow> tabinst_m array \<Rightarrow> cl_m array \<Rightarrow> inst_m \<Rightarrow> v_stack \<Rightarrow> (v_stack \<times> e list \<times> res_step) Heap" where
  "app_s_f_v_s_call_indirect_m k tinsts cls inst_m v_s = 
          (case v_s of
             (V_num (ConstInt32 c))#v_s' \<Rightarrow>
               do {
                 j \<leftarrow> Array.nth (inst_m.tabs inst_m) 0;
                 tab_j \<leftarrow> Array.nth tinsts j;
                 tab_j_len \<leftarrow> Array.len (fst tab_j);
                 if (tab_j_len > (nat_of_int c)) then do {
                   cl_maybe \<leftarrow> Array.nth (fst tab_j) (nat_of_int c);
                   case (cl_maybe) of
                     Some i_cl \<Rightarrow> do {
                       cl_i \<leftarrow> Array.nth cls i_cl;
                       t_k \<leftarrow> Array.nth (inst_m.types inst_m) k;
                       if (t_k = cl_m_type cl_i) then
                         return (v_s', [Invoke i_cl], Step_normal)
                       else
                         return (v_s', [], (Res_trap (STR ''call_indirect''))) }
                   | None \<Rightarrow> return (v_s', [], (Res_trap (STR ''call_indirect''))) }
                 else return (v_s', [], (Res_trap (STR ''call_indirect''))) }
           | _ \<Rightarrow> return (v_s, [], crash_invalid))"

definition app_s_f_v_s_get_global_m :: "nat \<Rightarrow> global array \<Rightarrow> inst_m \<Rightarrow> v_stack \<Rightarrow> (v_stack \<times> res_step) Heap" where
  "app_s_f_v_s_get_global_m k gs inst_m v_s =
     do {
       g_ind \<leftarrow> Array.nth (inst_m.globs inst_m) k;
       g \<leftarrow> Array.nth gs g_ind;
       return ((g_val g)#v_s, Step_normal) }"

definition app_s_f_v_s_set_global_m :: "nat \<Rightarrow> global array \<Rightarrow> inst_m \<Rightarrow> v_stack \<Rightarrow> (v_stack \<times> res_step) Heap" where
  "app_s_f_v_s_set_global_m k gs inst_m v_s =
     (case v_s of
        v1#v_s' \<Rightarrow>
          do {
            g_ind \<leftarrow> Array.nth (inst_m.globs inst_m) k;
            g \<leftarrow> Array.nth gs g_ind;
            Array.upd g_ind (g\<lparr>g_val := v1\<rparr>) gs;
            return (v_s', Step_normal) }
      | _ \<Rightarrow> return (v_s, crash_invalid))"

definition load_uint32_packed :: "byte_array \<Rightarrow> nat \<Rightarrow> tp_num \<Rightarrow> sx \<Rightarrow> uint32 Heap" where
  "load_uint32_packed a n tp sx \<equiv> do {
     v \<leftarrow> (case (tp,sx) of
            (Tp_i8,U) \<Rightarrow> load_uint32_of_uint8 a n
          | (Tp_i8,S) \<Rightarrow> load_uint32_of_sint8 a n
          | (Tp_i16,U) \<Rightarrow> load_uint32_of_uint16 a n
          | (Tp_i16,S) \<Rightarrow> load_uint32_of_sint16 a n
          | (Tp_i32,U) \<Rightarrow> load_uint32 a n
          | (Tp_i32,S) \<Rightarrow> load_uint32 a n);
     return v
  }"

definition load_uint64_packed :: "byte_array \<Rightarrow> nat \<Rightarrow> tp_num \<Rightarrow> sx \<Rightarrow> uint64 Heap" where
  "load_uint64_packed a n tp sx \<equiv> do {
     v \<leftarrow> (case (tp,sx) of
            (Tp_i8,U) \<Rightarrow> load_uint64_of_uint8 a n
          | (Tp_i8,S) \<Rightarrow> load_uint64_of_sint8 a n
          | (Tp_i16,U) \<Rightarrow> load_uint64_of_uint16 a n
          | (Tp_i16,S) \<Rightarrow> load_uint64_of_sint16 a n
          | (Tp_i32,U) \<Rightarrow> load_uint64_of_uint32 a n
          | (Tp_i32,S) \<Rightarrow> load_uint64_of_sint32 a n);
     return v
  }"

definition load_m_v :: "mem_m \<Rightarrow> nat \<Rightarrow> off \<Rightarrow> t_num \<Rightarrow> (v_num option) Heap" where
  "load_m_v m n off t =
     do {
       m_len \<leftarrow> len_byte_array (fst m);
       (if (m_len \<ge> (n+off+(t_num_length t))) then do {
          (case t of
            T_i32 \<Rightarrow> do { v \<leftarrow> load_uint32 (fst m) (n+off);
                          return (Some (ConstInt32 (i32_impl_abs v))) }
          | T_i64 \<Rightarrow> do { v \<leftarrow> load_uint64 (fst m) (n+off);
                          return (Some (ConstInt64 (i64_impl_abs v))) }
          | T_f32 \<Rightarrow> do { v \<leftarrow> load_uint32 (fst m) (n+off);
                          return (Some (ConstFloat32 (deserialise_f32 (serialise_i32 (i32_impl_abs v))))) }
          | T_f64 \<Rightarrow> do { v \<leftarrow> load_uint64 (fst m) (n+off);
                          return (Some (ConstFloat64 (deserialise_f64 (serialise_i64 (i64_impl_abs v))))) }
          )}
        else
          return None)
     }"

definition load_packed_m_v :: "mem_m \<Rightarrow> nat \<Rightarrow> off \<Rightarrow> t_num \<Rightarrow> tp_num \<Rightarrow> sx \<Rightarrow> (v_num option) Heap" where
  "load_packed_m_v m n off t tp sx =
     do {
       m_len \<leftarrow> len_byte_array (fst m);
       (if (m_len \<ge> (n+off+(tp_num_length tp))) then do {
          (case t of
            T_i32 \<Rightarrow> do { v \<leftarrow> load_uint32_packed (fst m) (n+off) tp sx;
                          return (Some (ConstInt32 (i32_impl_abs v))) }
          | T_i64 \<Rightarrow> do { v \<leftarrow> load_uint64_packed (fst m) (n+off) tp sx;
                          return (Some (ConstInt64 (i64_impl_abs v))) }
          | T_f32 \<Rightarrow> do { v \<leftarrow> load_uint32_packed (fst m) (n+off) tp sx;
                          return (Some (ConstFloat32 (deserialise_f32 (serialise_i32 (i32_impl_abs v))))) }
          | T_f64 \<Rightarrow> do { v \<leftarrow> load_uint64_packed (fst m) (n+off) tp sx;
                          return (Some (ConstFloat64 (deserialise_f64 (serialise_i64 (i64_impl_abs v))))) }
          )}
        else
          return None)
     }"

definition load_bytes_m_v :: "mem_m \<Rightarrow> nat \<Rightarrow> off \<Rightarrow> nat \<Rightarrow> (bytes option) Heap" where
  "load_bytes_m_v m n off l =
     do {
       m_len \<leftarrow> len_byte_array (fst m);
       let ind = n+off;
       (if (m_len \<ge> (ind+l)) then do {
          bs \<leftarrow> load_uint8_list (fst m) ind l;
          return (Some bs) }
        else
          return None)
     }"

definition app_s_f_v_s_load_maybe_packed_m :: "t_num \<Rightarrow> (tp_num \<times> sx) option \<Rightarrow> nat \<Rightarrow> mem_m array \<Rightarrow> inst_m \<Rightarrow> v_stack \<Rightarrow> (v_stack \<times> res_step) Heap" where
  "app_s_f_v_s_load_maybe_packed_m t tp_sx off ms i_m v_s =
    (case v_s of
        (V_num (ConstInt32 c))#v_s' \<Rightarrow> do {
             j \<leftarrow> Array.nth (inst_m.mems i_m) 0;
             m \<leftarrow> Array.nth ms j;
             v_maybe \<leftarrow> (case tp_sx of
                           None \<Rightarrow> load_m_v m (nat_of_int c) off t
                         | Some (tp,sx) \<Rightarrow> load_packed_m_v m (nat_of_int c) off t tp sx);
             (case v_maybe of
                Some v \<Rightarrow> return ((V_num v)#v_s', Step_normal)
              | None \<Rightarrow> return (v_s', (Res_trap (STR ''load'')))) }
         | _ \<Rightarrow> return (v_s, crash_invalid))"

definition store_uint32_packed :: "byte_array \<Rightarrow> nat \<Rightarrow> uint32 \<Rightarrow> tp_num \<Rightarrow> unit Heap" where
  "store_uint32_packed a n v tp \<equiv> do {
   (case tp of
      Tp_i8 \<Rightarrow> store_uint8_of_uint32 a n v
    | Tp_i16 \<Rightarrow> store_uint16_of_uint32 a n v
    | Tp_i32 \<Rightarrow> store_uint32 a n v)
  }"

definition store_uint64_packed :: "byte_array \<Rightarrow> nat \<Rightarrow> uint64 \<Rightarrow> tp_num \<Rightarrow> unit Heap" where
  "store_uint64_packed a n v tp \<equiv> do {
   (case tp of
      Tp_i8 \<Rightarrow> store_uint8_of_uint64 a n v
    | Tp_i16 \<Rightarrow> store_uint16_of_uint64 a n v
    | Tp_i32 \<Rightarrow> store_uint32_of_uint64 a n v)
  }"

definition store_m_v :: "mem_m \<Rightarrow> nat \<Rightarrow> off \<Rightarrow> v_num \<Rightarrow> (unit option) Heap" where
  "store_m_v m n off v =
     do {
       m_len \<leftarrow> len_byte_array (fst m);
       (if (m_len \<ge> (n+off+(t_num_length (typeof_num v)))) then do {
          (case v of
            ConstInt32 c \<Rightarrow> do { store_uint32 (fst m) (n+off) (i32_impl_rep c); return (Some ()) }
          | ConstInt64 c \<Rightarrow> do { store_uint64 (fst m) (n+off) (i64_impl_rep c); return (Some ()) }
          | ConstFloat32 c \<Rightarrow> do { store_uint32 (fst m) (n+off) (i32_impl_rep (deserialise_i32 (serialise_f32 c))); return (Some ()) }
          | ConstFloat64 c \<Rightarrow> do { store_uint64 (fst m) (n+off) (i64_impl_rep (deserialise_i64 (serialise_f64 c))); return (Some ()) }
          )}
        else
          return None)
     }"

definition store_packed_m_v :: "mem_m \<Rightarrow> nat \<Rightarrow> off \<Rightarrow> v_num \<Rightarrow> tp_num \<Rightarrow> (unit option) Heap" where
  "store_packed_m_v m n off v tp =
     do {
       m_len \<leftarrow> len_byte_array (fst m);
       (if (m_len \<ge> (n+off+(tp_num_length tp))) then do {
          (case v of
            ConstInt32 c \<Rightarrow> do { store_uint32_packed (fst m) (n+off) (i32_impl_rep c) tp; return (Some ()) }
          | ConstInt64 c \<Rightarrow> do { store_uint64_packed (fst m) (n+off) (i64_impl_rep c) tp; return (Some ()) }
          | ConstFloat32 c \<Rightarrow> do { store_uint32_packed (fst m) (n+off) (i32_impl_rep (deserialise_i32 (serialise_f32 c))) tp; return (Some ()) }
          | ConstFloat64 c \<Rightarrow> do { store_uint64_packed (fst m) (n+off) (i64_impl_rep (deserialise_i64 (serialise_f64 c))) tp; return (Some ()) }
          )}
        else
          return None)
     }"

definition app_s_f_v_s_store_maybe_packed_m :: "t_num \<Rightarrow> tp_num option \<Rightarrow> nat \<Rightarrow> mem_m array \<Rightarrow> inst_m \<Rightarrow>  v_stack \<Rightarrow> (v_stack \<times> res_step) Heap" where
  "app_s_f_v_s_store_maybe_packed_m t tp_opt off ms i_m v_s =
   (case v_s of
     (V_num v)#(V_num (ConstInt32 c))#v_s' \<Rightarrow>
       (if (typeof_num v = t) then
          do {
            j \<leftarrow> Array.nth (inst_m.mems i_m) 0;
            m \<leftarrow> Array.nth ms j;
            u_maybe \<leftarrow> (case tp_opt of
                          None \<Rightarrow> store_m_v m (nat_of_int c) off v
                        | Some tp \<Rightarrow> store_packed_m_v m (nat_of_int c) off v tp);
            (case u_maybe of
               Some _ \<Rightarrow> return (v_s', Step_normal)
             | None \<Rightarrow> return (v_s', (Res_trap (STR ''store'')))) }
        else return (v_s, crash_invalid))
   | _ \<Rightarrow> return (v_s, crash_invalid))"

fun load_bytes_vec_m_v :: "nat \<Rightarrow> nat \<Rightarrow> sx \<Rightarrow> byte_array \<Rightarrow> nat \<Rightarrow> bytes Heap" where
  "load_bytes_vec_m_v 0 len sx m ind = return []"
| "load_bytes_vec_m_v (Suc n) len sx m ind = do { bs \<leftarrow> (load_uint8_list m ind len);
                                                  bs' \<leftarrow> (load_bytes_vec_m_v n len sx m (ind+len));
                                                  return ((sign_extend sx (len*2) bs)@bs') }"

definition load_packed_vec_m_v :: "tp_vec \<Rightarrow> sx \<Rightarrow> mem_m \<Rightarrow> nat \<Rightarrow> off \<Rightarrow> (bytes option) Heap" where
  "load_packed_vec_m_v tp sx m n off =
   do {
     m_len \<leftarrow> len_byte_array (fst m);
     (if (m_len \<ge> (n+off+((tp_vec_num tp)*(tp_vec_length tp))))
       then do { bs \<leftarrow> load_bytes_vec_m_v (tp_vec_num tp) (tp_vec_length tp) sx (fst m) (n+off); return (Some bs) }
       else return None)
   }"

definition load_vec_m_v :: "loadop_vec \<Rightarrow> mem_m \<Rightarrow> nat \<Rightarrow> off \<Rightarrow> (bytes option) Heap" where
  "load_vec_m_v lv m n off =
    (case lv of
       Load_128 \<Rightarrow> load_bytes_m_v m n off (t_vec_length T_v128)
     | Load_packed_vec tp sx \<Rightarrow> load_packed_vec_m_v tp sx m n off
     | Load_32_zero \<Rightarrow> do { bs_maybe \<leftarrow> load_bytes_m_v m n off 4; return (map_option (\<lambda>bs. bytes_takefill zero_byte (t_vec_length T_v128) bs) bs_maybe) }
     | Load_64_zero \<Rightarrow> do { bs_maybe \<leftarrow> load_bytes_m_v m n off 8; return (map_option (\<lambda>bs. bytes_takefill zero_byte (t_vec_length T_v128) bs) bs_maybe) }
     | Load_splat svi \<Rightarrow> do { bs_maybe \<leftarrow> load_bytes_m_v m n off (vec_i_length svi); return (map_option (\<lambda>bs. concat (replicate (vec_i_num svi) bs)) bs_maybe) })"

definition app_s_f_v_s_load_vec_m :: "loadop_vec \<Rightarrow> nat \<Rightarrow> mem_m array \<Rightarrow> inst_m \<Rightarrow> v_stack \<Rightarrow> (v_stack \<times> res_step) Heap" where
  "app_s_f_v_s_load_vec_m lv off ms i_m v_s =
    (case v_s of
        (V_num (ConstInt32 c))#v_s' \<Rightarrow> do {
             j \<leftarrow> Array.nth (inst_m.mems i_m) 0;
             m \<leftarrow> Array.nth ms j;
             v_maybe \<leftarrow> load_vec_m_v lv m (nat_of_int c) off;
             (case v_maybe of
                Some v \<Rightarrow> return ((V_vec (ConstVec128 (deserialise_v128 v)))#v_s', Step_normal)
              | None \<Rightarrow> return (v_s', (Res_trap (STR ''load_vec'')))) }
         | _ \<Rightarrow> return (v_s, crash_invalid))"

definition app_s_f_v_s_load_lane_vec_m :: "shape_vec_i \<Rightarrow> i \<Rightarrow> nat \<Rightarrow> mem_m array \<Rightarrow> inst_m \<Rightarrow> v_stack \<Rightarrow> (v_stack \<times> res_step) Heap" where
  "app_s_f_v_s_load_lane_vec_m svi i_n off ms i_m v_s =
    (case v_s of
        (V_vec (ConstVec128 v))#(V_num (ConstInt32 c))#v_s' \<Rightarrow> do {
             j \<leftarrow> Array.nth (inst_m.mems i_m) 0;
             m \<leftarrow> Array.nth ms j;
             v_maybe \<leftarrow> load_bytes_m_v m (nat_of_int c) off (vec_i_length svi);
             (case v_maybe of
                Some bs \<Rightarrow> return ((V_vec (ConstVec128 (insert_lane_vec svi i_n bs v)))#v_s', Step_normal)
              | None \<Rightarrow> return (v_s', (Res_trap (STR ''load_lane_vec'')))) }
         | _ \<Rightarrow> return (v_s, crash_invalid))"

definition app_s_f_v_s_store_vec_m :: "storeop_vec \<Rightarrow> nat \<Rightarrow> mem_m array \<Rightarrow> inst_m \<Rightarrow>  v_stack \<Rightarrow> (v_stack \<times> res_step) Heap" where
  "app_s_f_v_s_store_vec_m sv off ms i_m v_s =
   (case v_s of
     (V_vec (ConstVec128 v))#(V_num (ConstInt32 c))#v_s' \<Rightarrow>
        do {
          j \<leftarrow> Array.nth (inst_m.mems i_m) 0;
          m \<leftarrow> Array.nth ms j;
          m_len \<leftarrow> len_byte_array (fst m);
          let bs = (store_serialise_vec sv v);
          let n = (nat_of_int c)+off;
          if (m_len \<ge> (n+(length bs))) then do {
            store_uint8_list (fst m) n bs;
            return (v_s', Step_normal) }
          else return (v_s', (Res_trap (STR ''store_vec'')))}
   | _ \<Rightarrow> return (v_s, crash_invalid))"

definition app_s_f_v_s_mem_size_m :: "mem_m array \<Rightarrow> inst_m \<Rightarrow> v_stack \<Rightarrow> (v_stack \<times> res_step) Heap" where
  "app_s_f_v_s_mem_size_m ms i_m v_s =
     do {
       j \<leftarrow> Array.nth (inst_m.mems i_m) 0;
       m \<leftarrow> Array.nth ms j;
       m_len \<leftarrow> len_byte_array (fst m);
       return (((V_num (ConstInt32 (int_of_nat (m_len div Ki64))))#v_s), Step_normal)
     }"

definition app_s_f_v_s_mem_grow_m :: "mem_m array \<Rightarrow> inst_m \<Rightarrow> v_stack \<Rightarrow> (v_stack \<times> res_step) Heap" where
  "app_s_f_v_s_mem_grow_m ms i_m v_s =
     (case v_s of
        (V_num (ConstInt32 c))#v_s' \<Rightarrow>
           do {
             j \<leftarrow> Array.nth (inst_m.mems i_m) 0;
             m \<leftarrow> Array.nth ms j;
             m_len \<leftarrow> len_byte_array (fst m);
             let new_m_len = (m_len div Ki64) + (nat_of_int c);
             if (new_m_len \<le> 2^16 \<and> pred_option (\<lambda>max. new_m_len \<le> max) (snd m)) then do {
               m_new_fst \<leftarrow> grow_zeroed_byte_array (fst m) ((nat_of_int c) * Ki64);
               Array.upd j (m_new_fst, snd m) ms;
               return (((V_num (ConstInt32 (int_of_nat (m_len div Ki64))))#v_s'), Step_normal) }
             else
               return (((V_num (ConstInt32 (int32_minus_one)))#v_s'), Step_normal)
           }
     | _ \<Rightarrow> return (v_s, crash_invalid))"

definition init_mem_m_v :: "mem_m \<Rightarrow> nat \<Rightarrow> byte list \<Rightarrow> (unit option) Heap" where
  "init_mem_m_v m n bs =
     do {
       m_len \<leftarrow> len_byte_array (fst m);
       (if (m_len \<ge> (n+(length bs))) then do {
          store_uint8_list (fst m) n bs; return (Some ()) }
        else
          return None)
     }"

definition init_tab_m_v :: "tabinst_m \<Rightarrow> nat \<Rightarrow> i list \<Rightarrow> (unit option) Heap" where
  "init_tab_m_v t n icls =
     do {
       t_len \<leftarrow> Array.len (fst t);
       (if (t_len \<ge> (n+(length icls))) then do {
          list_blit_array (map Some icls) (fst t) n; return (Some ()) }
        else
          return None)
     }"

definition app_s_f_init_mem_m :: "nat \<Rightarrow> byte list \<Rightarrow> mem_m array \<Rightarrow> inst_m \<Rightarrow> res_step Heap" where
  "app_s_f_init_mem_m off bs ms i_m =
   (do {
      j \<leftarrow> Array.nth (inst_m.mems i_m) 0;
      m \<leftarrow> Array.nth ms j;
      u_maybe \<leftarrow> init_mem_m_v m off bs;
      (case u_maybe of
         Some _ \<Rightarrow> return Step_normal
       | None \<Rightarrow> return (Res_trap (STR ''init_mem''))) })"

definition app_s_f_init_tab_m :: "nat \<Rightarrow> i list \<Rightarrow> tabinst_m array \<Rightarrow> inst_m \<Rightarrow> res_step Heap" where
  "app_s_f_init_tab_m off icls ts i_m =
   (do {
      j \<leftarrow> Array.nth (inst_m.tabs i_m) 0;
      t \<leftarrow> Array.nth ts j;
      u_maybe \<leftarrow> init_tab_m_v t off icls;
      (case u_maybe of
         Some _ \<Rightarrow> return Step_normal
       | None \<Rightarrow> return (Res_trap (STR ''init_tab''))) })"

fun update_fc_step_m :: "frame_context_m \<Rightarrow> v_stack \<Rightarrow> e list \<Rightarrow> frame_context_m" where
  "update_fc_step_m (Frame_context_m rdx lcs nf f1 f2) v_s' es_cont = (Frame_context_m (update_redex_step rdx v_s' es_cont) lcs nf f1 f2)"

fun update_fc_return_m :: "frame_context_m \<Rightarrow> v_stack \<Rightarrow> frame_context_m" where
  "update_fc_return_m (Frame_context_m rdx lcs nf f1 f2) v_s' = (Frame_context_m (update_redex_return rdx v_s') lcs nf f1 f2)"

fun update_fcs_return_m :: "frame_context_m list \<Rightarrow> v_stack \<Rightarrow> frame_context_m list" where
  "update_fcs_return_m [] v_s = []"
| "update_fcs_return_m (fc#fcs) v_s = (update_fc_return_m fc v_s)#fcs"

fun update_redex_trap :: "redex \<Rightarrow> redex" where
  "update_redex_trap (Redex v_s es b_es) = (Redex [] es b_es)"

fun update_fc_trap_m :: "frame_context_m \<Rightarrow> frame_context_m" where
  "update_fc_trap_m (Frame_context_m rdx lcs nf f1 f2) = (Frame_context_m (update_redex_trap rdx) lcs nf f1 f2)"

fun update_fcs_trap_m :: "frame_context_m list \<Rightarrow> frame_context_m list" where
  "update_fcs_trap_m [] = []"
| "update_fcs_trap_m (fc#fcs) = (update_fc_trap_m fc)#fcs"

type_synonym res_step_tuple_m = "config_m \<times> res_step"

type_synonym res_tuple_m = "config_m \<times> res"

abbreviation "s_m_vs_pair_assn i_s \<equiv> \<lambda>(s, vs) (s_m, vs_m). s_m_assn i_s s s_m * \<up>(vs=vs_m)"

axiomatization 
  host_apply_impl_m:: "s_m \<Rightarrow> tf \<Rightarrow> host \<Rightarrow> v list \<Rightarrow> ((s_m \<times> v list) option) Heap"
  where host_apply_impl_m_triple:
   "< s_m_assn ias s s_m * inst_assocs_assn ias>
   host_apply_impl_m s_m tf h vs
   <\<lambda>r_opt. expect_assn 
    (\<lambda>r r_m. \<exists>\<^sub>A ias'. s_m_vs_pair_assn ias' r r_m * inst_assocs_assn ias' 
      * \<up>(inst_assocs_extension ias ias')) 
    (\<exists>\<^sub>A ias'. s_m_assn ias' s s_m * inst_assocs_assn ias' * \<up>(inst_assocs_extension ias ias'))              
  (host_apply_impl s tf h vs) r_opt >"


fun run_step_b_e_m :: "b_e \<Rightarrow> config_m \<Rightarrow> res_step_tuple_m Heap" where
  "run_step_b_e_m b_e (Config_m d s fc fcs) =
    (case fc of (Frame_context_m (Redex v_s es b_es) lcs nf f_locs1 f_inst2) \<Rightarrow>
    (case b_e of
      (Unop t op) \<Rightarrow>
        let (v_s', res) = (app_v_s_unop op v_s) in
        return ((Config_m d s (update_fc_step_m fc v_s' []) fcs), res)

    | (Binop t op) \<Rightarrow>
        let (v_s', res) = (app_v_s_binop op v_s) in
        return ((Config_m d s (update_fc_step_m fc v_s' []) fcs), res)

    | (Testop t op) \<Rightarrow>
        let (v_s', res) = (app_v_s_testop op v_s) in
        return ((Config_m d s (update_fc_step_m fc v_s' []) fcs), res)

    | (Relop t op) \<Rightarrow>
        let (v_s', res) = (app_v_s_relop op v_s) in
        return ((Config_m d s (update_fc_step_m fc v_s' []) fcs), res)

    | (Cvtop t2 op t1 tp_sx) \<Rightarrow>
        let (v_s', res) = (app_v_s_cvtop op t1 t2 tp_sx v_s) in
        return ((Config_m d s (update_fc_step_m fc v_s' []) fcs), res)

    | (Unop_vec op) \<Rightarrow>
        let (v_s', res) = (app_v_s_unop_vec op v_s) in
        return ((Config_m d s (update_fc_step_m fc v_s' []) fcs), res)

    | (Binop_vec op) \<Rightarrow>
        let (v_s', res) = (app_v_s_binop_vec op v_s) in
        return ((Config_m d s (update_fc_step_m fc v_s' []) fcs), res)

    | (Ternop_vec op) \<Rightarrow>
        let (v_s', res) = (app_v_s_ternop_vec op v_s) in
        return ((Config_m d s (update_fc_step_m fc v_s' []) fcs), res)

    | (Test_vec op) \<Rightarrow>
        let (v_s', res) = (app_v_s_test_vec op v_s) in
        return ((Config_m d s (update_fc_step_m fc v_s' []) fcs), res)

    | (Shift_vec op) \<Rightarrow>
        let (v_s', res) = (app_v_s_shift_vec op v_s) in
        return ((Config_m d s (update_fc_step_m fc v_s' []) fcs), res)

    | (Splat_vec sv) \<Rightarrow>
        let (v_s', res) = (app_v_s_splat_vec sv v_s) in
        return ((Config_m d s (update_fc_step_m fc v_s' []) fcs), res)

    | (Extract_vec sv sx i) \<Rightarrow>
        let (v_s', res) = (app_v_s_extract_vec sv sx i v_s) in
        return ((Config_m d s (update_fc_step_m fc v_s' []) fcs), res)

    | (Replace_vec sv i) \<Rightarrow>
        let (v_s', res) = (app_v_s_replace_vec sv i v_s) in
        return ((Config_m d s (update_fc_step_m fc v_s' []) fcs), res)

    | (Unreachable) \<Rightarrow>
        return (Config_m d s fc fcs, Res_trap (STR ''unreachable''))

    | (Nop) \<Rightarrow>
        return (Config_m d s fc fcs, Step_normal)

    | (Drop) \<Rightarrow>
        let (v_s', res) = (app_v_s_drop v_s) in
        return ((Config_m d s (update_fc_step_m fc v_s' []) fcs), res)

    | (Select) \<Rightarrow>
        let (v_s', res) = (app_v_s_select v_s) in
        return ((Config_m d s (update_fc_step_m fc v_s' []) fcs), res)

    | (Block tb b_ebs) \<Rightarrow>
        if es \<noteq> [] then return (Config_m d s fc fcs, crash_invariant)
        else do {
          tf \<leftarrow> tb_tf_m f_inst2 tb;
          case tf of (t1s _> t2s) \<Rightarrow> do {
          let n = length t1s;
          let m = length t2s;
          if (length v_s \<ge> n) then
            let (v_bs, v_s') = split_n v_s n in
            let lc = Label_context v_s' b_es m [] in 
            let fc' = Frame_context_m (Redex v_bs [] b_ebs) (lc#lcs) nf f_locs1 f_inst2 in
            return (Config_m d s fc' fcs, Step_normal)
          else return (Config_m d s fc fcs, crash_invalid) }}

    | (Loop tb b_els) \<Rightarrow>
        if es \<noteq> [] then return (Config_m d s fc fcs, crash_invariant)
        else do {
          tf \<leftarrow> tb_tf_m f_inst2 tb;
          case tf of (t1s _> t2s) \<Rightarrow> do {
          let n = length t1s;
          let m = length t2s;
          if (length v_s \<ge> n) then
            let (v_bs, v_s') = split_n v_s n in
            let lc = Label_context v_s' b_es n [(Loop tb b_els)] in 
            let fc' = Frame_context_m (Redex v_bs [] b_els) (lc#lcs) nf f_locs1 f_inst2 in
            return (Config_m d s fc' fcs, Step_normal)
          else return (Config_m d s fc fcs, crash_invalid) }}

    | (If tb es1 es2) \<Rightarrow>
        let (v_s', es_cont, res) = (app_v_s_if tb es1 es2 v_s) in
        return (Config_m d s (update_fc_step_m fc v_s' es_cont) fcs, res)

    | (Br k) \<Rightarrow>
        if (length lcs > k) then
          case (lcs!k) of (Label_context v_ls b_els nl b_ecls) \<Rightarrow>
          if (length v_s \<ge> nl) then
            let v_s' = (take nl v_s) in
            let fc' = Frame_context_m (Redex (v_s'@v_ls) [] (b_ecls@b_els)) (drop (Suc k) lcs) nf f_locs1 f_inst2 in
            return (Config_m d s fc' fcs, Step_normal)
          else
            return (Config_m d s fc fcs, crash_invalid)
        else
          return (Config_m d s fc fcs, crash_invalid)

    | (Br_if k) \<Rightarrow>
        let (v_s', es_cont, res) = (app_v_s_br_if k v_s) in
        return (Config_m d s (update_fc_step_m fc v_s' es_cont) fcs, res)

    | (Br_table ks k) \<Rightarrow>
        let (v_s', es_cont, res) = (app_v_s_br_table ks k v_s) in
        return (Config_m d s (update_fc_step_m fc v_s' es_cont) fcs, res)

    | (Call k) \<Rightarrow> do {
        (es_cont, res) \<leftarrow> (app_f_call_m k f_inst2);
        return (Config_m d s (update_fc_step_m fc v_s es_cont) fcs, res) }

    | (Call_indirect k) \<Rightarrow> do {
        (v_s', es_cont, res) \<leftarrow> (app_s_f_v_s_call_indirect_m k (s_m.tabs s) (s_m.funcs s) f_inst2 v_s);
        return (Config_m d s (update_fc_step_m fc v_s' es_cont) fcs, res) }

    | (Return) \<Rightarrow>
        (case fcs of
           [] \<Rightarrow> return (Config_m d s fc fcs, crash_invalid)
         | fc'#fcs' \<Rightarrow> if (length v_s \<ge> nf) then
                         return (Config_m (Suc d) s (update_fc_return_m fc' (take nf v_s)) fcs', Step_normal)
                       else return (Config_m d s fc fcs, crash_invalid))

    | (Get_local k) \<Rightarrow> do {
        (v_s', res) \<leftarrow> (app_f_v_s_get_local_m k f_locs1 v_s);
        return (Config_m d s (update_fc_step_m fc v_s' []) fcs, res) }

    | (Set_local k) \<Rightarrow> do {
        (v_s', res) \<leftarrow> (app_f_v_s_set_local_m k f_locs1 v_s);
        let fc' = Frame_context_m (Redex v_s' es b_es) lcs nf f_locs1 f_inst2 in
        return (Config_m d s fc' fcs, res) }

    | (Tee_local k) \<Rightarrow>
        let (v_s', es_cont, res) = (app_v_s_tee_local k v_s) in
        return (Config_m d s (update_fc_step_m fc v_s' es_cont) fcs, res)

    | (Get_global k) \<Rightarrow> do {
        (v_s', res) \<leftarrow> (app_s_f_v_s_get_global_m k (s_m.globs s) f_inst2 v_s);
        return (Config_m d s (update_fc_step_m fc v_s' []) fcs, res) }

    | (Set_global k) \<Rightarrow> do {
        (v_s', res) \<leftarrow> (app_s_f_v_s_set_global_m k (s_m.globs s) f_inst2 v_s);
        return (Config_m d s (update_fc_step_m fc v_s' []) fcs, res) }

    | (Load t tp_sx a off) \<Rightarrow> do {
        (v_s', res) \<leftarrow> (app_s_f_v_s_load_maybe_packed_m t tp_sx off (s_m.mems s) f_inst2 v_s);
        return (Config_m d s (update_fc_step_m fc v_s' []) fcs, res) }

    | (Store t tp a off) \<Rightarrow> do {
        (v_s', res) \<leftarrow> (app_s_f_v_s_store_maybe_packed_m t tp off (s_m.mems s) f_inst2 v_s);
        return (Config_m d s (update_fc_step_m fc v_s' []) fcs, res) }

    | (Load_vec lv a off) \<Rightarrow> do {
        (v_s', res) \<leftarrow> (app_s_f_v_s_load_vec_m lv off (s_m.mems s) f_inst2 v_s);
        return (Config_m d s (update_fc_step_m fc v_s' []) fcs, res) }

    | (Load_lane_vec svi i a off) \<Rightarrow> do {
        (v_s', res) \<leftarrow> (app_s_f_v_s_load_lane_vec_m svi i off (s_m.mems s) f_inst2 v_s);
        return (Config_m d s (update_fc_step_m fc v_s' []) fcs, res) }

    | (Store_vec sv a off) \<Rightarrow> do {
        (v_s', res) \<leftarrow> (app_s_f_v_s_store_vec_m sv off (s_m.mems s) f_inst2 v_s);
        return (Config_m d s (update_fc_step_m fc v_s' []) fcs, res) }

    | (Current_memory) \<Rightarrow> do {
        (v_s', res) \<leftarrow> (app_s_f_v_s_mem_size_m (s_m.mems s) f_inst2 v_s);
        return (Config_m d s (update_fc_step_m fc v_s' []) fcs, res) }

    | (Grow_memory) \<Rightarrow> do {
        (v_s', res) \<leftarrow> (app_s_f_v_s_mem_grow_m (s_m.mems s) f_inst2 v_s);
        return (Config_m d s (update_fc_step_m fc v_s' []) fcs, res) }

    | _ \<Rightarrow> return (Config_m d s fc fcs, crash_invariant)))"


fun run_step_e_m :: "e \<Rightarrow> config_m \<Rightarrow> res_step_tuple_m Heap" where
  "run_step_e_m e (Config_m d s fc fcs) =
    (case fc of Frame_context_m (Redex v_s es b_es) lcs nf f_locs1 f_inst2 \<Rightarrow>
    (case e of
       Basic b_e \<Rightarrow> run_step_b_e_m b_e (Config_m d s fc fcs)

     | Invoke i_cl \<Rightarrow> do {
       cl \<leftarrow> Array.nth (s_m.funcs s) i_cl;
       (case cl of
             cl_m.Func_native i' (t1s _> t2s) ts es_f \<Rightarrow>
               (case d of
                 Suc d' \<Rightarrow>
                   (let n = length t1s in
                    let m = length t2s in
                    if (length v_s \<ge> n) then
                      let (v_fs, v_s') = split_n v_s n in
                      let fc' = Frame_context_m (Redex v_s' es b_es) lcs nf f_locs1 f_inst2 in
                      let zs = n_zeros ts in do {
                      ff_locs1 \<leftarrow> Array.of_list ((rev v_fs)@zs);
                      let lc = Label_context [] [] m [];
                      let fcf = Frame_context_m (Redex [] [] es_f) [lc] m ff_locs1 i' in
                      return (Config_m d' s fcf (fc'#fcs), Step_normal) }
                    else
                      return (Config_m d s fc fcs, crash_invalid))
               | 0 \<Rightarrow> return (Config_m d s fc fcs, crash_exhaustion))
           | cl_m.Func_host (t1s _> t2s) h \<Rightarrow>
               let n = length t1s in
               let m = length t2s in
               if length v_s \<ge> n
                 then
                   let (v_fs, v_s') = split_n v_s n in do {
                   host_res \<leftarrow> host_apply_impl_m s (t1s _> t2s) h (rev v_fs);
                   case host_res of
                     Some (s',rvs) \<Rightarrow> 
                       if list_all2 (\<lambda>t v. typeof v = t) t2s rvs
                         then
                           let fc' = Frame_context_m (Redex ((rev rvs)@v_s') es b_es) lcs nf f_locs1 f_inst2 in
                           return (Config_m d s' fc' fcs, Step_normal)
                         else
                           return (Config_m d s' fc fcs, crash_invalid)
                   | None \<Rightarrow> return (Config_m d s (Frame_context_m (Redex v_s' es b_es) lcs nf f_locs1 f_inst2) fcs, Res_trap (STR ''host_apply'')) }
                 else
                    return (Config_m d s fc fcs, crash_invalid))}

    | (Init_mem n bs) \<Rightarrow> do {
        res \<leftarrow> (app_s_f_init_mem_m n bs (s_m.mems s) f_inst2);
        return (Config_m d s fc fcs, res) }

    | (Init_tab n icls) \<Rightarrow> do {
        res \<leftarrow> (app_s_f_init_tab_m n icls (s_m.tabs s) f_inst2);
        return (Config_m d s fc fcs, res) }

     | _ \<Rightarrow> return (Config_m d s fc fcs, crash_invariant)))"
(* should never produce Label, Frame, or Trap *)

function(sequential) run_iter_m :: "fuel \<Rightarrow> config_m \<Rightarrow> res_tuple_m Heap" where
  "run_iter_m (Suc n) cfg =
     (case cfg of
        (Config_m d s (Frame_context_m (Redex v_s es b_es) lcs nf f_locs1 f_inst2) fcs) \<Rightarrow>
     (case es of
        [] \<Rightarrow> (case b_es of
                 [] \<Rightarrow> (case lcs of
                          [] \<Rightarrow> (case fcs of
\<comment> \<open> stack values in the outermost frame \<close>
                                   [] \<Rightarrow> return ((Config_m d s (Frame_context_m (Redex v_s [] []) [] nf f_locs1 f_inst2) []), RValue v_s)
\<comment> \<open> stack values returned from an inner frame \<close>
                                 | fc'#fcs' \<Rightarrow> run_iter_m n (Config_m (Suc d) s (update_fc_return_m fc' v_s) fcs'))
\<comment> \<open> stack values returned from an inner label \<close>
                        | (Label_context v_ls b_els nl b_elcs)#lcs' \<Rightarrow> (let f_new = Frame_context_m (Redex (v_s@v_ls) [] b_els) lcs' nf f_locs1 f_inst2 in
                                                             run_iter_m n (Config_m d s f_new fcs)))
\<comment> \<open> run a step of regular code \<close>
               | b_es \<Rightarrow> (case split_v_s_b_s b_es of
                            (v_s',[]) \<Rightarrow> run_iter_m n (Config_m d s (Frame_context_m (Redex (v_s'@v_s) [] []) lcs nf f_locs1 f_inst2) fcs)
                          | (v_s',b_e#b_es') \<Rightarrow> do {
                              (cfg', res) \<leftarrow> run_step_b_e_m b_e (Config_m d s (Frame_context_m (Redex (v_s'@v_s) [] b_es') lcs nf f_locs1 f_inst2) fcs);
                                                (case res of
                                                   Step_normal \<Rightarrow> run_iter_m n cfg'
                                                 | Res_trap str \<Rightarrow> return (cfg', RTrap str)
                                                 | Res_crash str \<Rightarrow> return (cfg', RCrash str)) } ))
\<comment> \<open> run a step of the intermediate reduct \<close>
      | e#es' \<Rightarrow> do {
          (cfg', res) \<leftarrow> run_step_e_m e (Config_m d s (Frame_context_m (Redex v_s es' b_es) lcs nf f_locs1 f_inst2) fcs);
                      (case res of
                         Step_normal \<Rightarrow> run_iter_m n cfg'
                       | Res_trap str \<Rightarrow> return (cfg', RTrap str)
                       | Res_crash str \<Rightarrow> return (cfg', RCrash str)) } ))"

\<comment> \<open> out of fuel \<close>
| "run_iter_m 0 cfg = return (cfg, res_crash_fuel)"

  by pat_completeness auto
termination
  by (relation "measure (\<lambda>p. fst p)") auto

definition "make_empty_inst_m \<equiv> do {
  f_inst2_types \<leftarrow> Array.of_list [];
  f_inst2_funcs \<leftarrow> Array.of_list [];
  f_inst2_tabs \<leftarrow> Array.of_list [];
  f_inst2_mems \<leftarrow> Array.of_list [];
  f_inst2_globs \<leftarrow> Array.of_list [];
  let f_inst2 = \<lparr> types = f_inst2_types, funcs = f_inst2_funcs, tabs = f_inst2_tabs, mems = f_inst2_mems, globs = f_inst2_globs\<rparr> in
  return f_inst2 }"

fun run_instantiate_m :: "fuel \<Rightarrow> depth \<Rightarrow> (s_m \<times> inst_m \<times> e list) \<Rightarrow> (s_m \<times> res) Heap" where
  "run_instantiate_m n d (s, f_inst2, es) = do {
     f_locs1 \<leftarrow> Array.of_list [];
     (cfg',res) \<leftarrow> run_iter_m n (Config_m d s (Frame_context_m (Redex [] es []) [] 0 f_locs1 f_inst2) []);
     case cfg' of (Config_m d' s' fc' fcs') \<Rightarrow> return (s',res) }"

fun run_v_m :: "fuel \<Rightarrow> depth \<Rightarrow> (s_m \<times> v array \<times> inst_m \<times> b_e list) \<Rightarrow> (s_m \<times> res) Heap" where
  "run_v_m n d (s, f_locs1, f_inst2, b_es) = do {
     (cfg',res) \<leftarrow> run_iter_m n (Config_m d s (Frame_context_m (Redex [] [] b_es) [] 0 f_locs1 f_inst2) []);
     case cfg' of (Config_m d' s' fc' fcs') \<Rightarrow> return (s',res) }"

definition "make_empty_store_m \<equiv> do {
  s_funcs \<leftarrow> Array.of_list [];
  s_tabs \<leftarrow> Array.of_list [];
  s_mems \<leftarrow> Array.of_list [];
  s_globs \<leftarrow> Array.of_list [];
  return \<lparr>s_m.funcs=s_funcs, s_m.tabs=s_tabs, s_m.mems=s_mems, s_m.globs=s_globs \<rparr> }"

definition "make_empty_frame_m \<equiv> do {
  f_locs1 \<leftarrow> Array.of_list [];
  f_inst2 \<leftarrow> make_empty_inst_m;
  return (f_locs1, f_inst2) }"

fun run_invoke_v_m :: "fuel \<Rightarrow> depth \<Rightarrow> (s_m \<times> v list \<times> i) \<Rightarrow> (s_m \<times> res) Heap" where
  "run_invoke_v_m n d (s, vs, i) = do {
   (f_locs1, f_inst2) \<leftarrow> make_empty_frame_m;
   (cfg',res) \<leftarrow> run_iter_m n (Config_m d s (Frame_context_m (Redex (rev vs) [Invoke i] []) [] 0 f_locs1 f_inst2) []);
   case cfg' of (Config_m d s fc fcs) \<Rightarrow> return (s,res) }"

end