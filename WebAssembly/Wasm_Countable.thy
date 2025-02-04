theory Wasm_Countable imports Wasm_Base_Defs "HOL-Library.Countable" begin

instance t_num :: countable
  by countable_datatype

instance t_vec :: countable
  by countable_datatype

instance t :: countable
  by countable_datatype

instance tf :: countable
  by countable_datatype

instance tb :: countable
  by countable_datatype

instance inst_ext :: (countable) countable
proof(rule countable_classI[of "\<lambda>i. to_nat (types i, inst.funcs i, inst.tabs i, inst.mems i, inst.globs i, inst.more i)"])
qed auto

instance tp_num :: countable
  by countable_datatype

instance tp_vec :: countable
  by countable_datatype

instance sx :: countable
  by countable_datatype

instance sat :: countable
  by countable_datatype

instance i32 :: countable
proof(rule countable_classI[of "\<lambda>n::i32. nat_of_int n"])
qed (simp add: Rep_i32_inject nat_of_int_i32.rep_eq)

instance i64 :: countable
proof(rule countable_classI[of "\<lambda>n::i64. nat_of_int n"])
qed (simp add: Rep_i64_inject nat_of_int_i64.rep_eq)

instance f32 :: countable
proof(rule countable_classI[of "unat o Rep_f32"])
qed (simp add: Rep_f32_inject)

instance f64 :: countable
proof(rule countable_classI[of "unat o Rep_f64"])
qed (simp add: Rep_f64_inject)

instance v128 :: countable
proof(rule countable_classI[of "unat o Rep_v128"])
qed (simp add: Rep_v128_inject)
  
instance v_num :: countable
  by countable_datatype

instance v_vec :: countable
  by countable_datatype

instance v :: countable
  by countable_datatype

instance unop_i :: countable
  by countable_datatype

instance unop_f :: countable
  by countable_datatype

instance unop :: countable
  by countable_datatype

instance binop_i :: countable
  by countable_datatype

instance binop_f :: countable
  by countable_datatype

instance binop :: countable
  by countable_datatype

instance testop :: countable
  by countable_datatype

instance relop_i :: countable
  by countable_datatype

instance relop_f :: countable
  by countable_datatype

instance relop :: countable
  by countable_datatype

instance cvtop :: countable
  by countable_datatype

instance shape_vec_i :: countable
  by countable_datatype

instance shape_vec_f :: countable
  by countable_datatype

instance shape_vec :: countable
  by countable_datatype

instance unop_vec :: countable ..

instance binop_vec :: countable ..

instance ternop_vec :: countable ..

instance testop_vec :: countable ..

instance shiftop_vec :: countable ..

instance loadop_vec :: countable
  by countable_datatype

instance storeop_vec :: countable
  by countable_datatype

instance b_e :: countable
  by countable_datatype

axiomatization where
  host_countable: "OFCLASS(host, countable_class)"

instance host :: countable
  by (rule host_countable)

instance cl :: countable
  by countable_datatype

instance uint8 :: countable
proof(rule countable_classI[of "\<lambda>n::byte. nat_of_byte n"])
qed (simp add: Rep_uint8_inject nat_of_byte_def nat_of_uint8.rep_eq)

instance mem_rep :: countable
proof(rule countable_classI[of "\<lambda>m::mem_rep. to_nat (Rep_mem_rep m)"])
qed (simp add: Rep_mem_rep_inject)

instance mut :: countable
  by countable_datatype

instance global_ext :: (countable) countable
proof(rule countable_classI[of "\<lambda>g. to_nat (g_mut g, g_val g, global.more g)"])
qed simp

instance s_ext :: (countable) countable
proof (rule countable_classI[of "\<lambda>s. to_nat (funcs s, tabs s, mems s, globs s, s.more s)"])
qed simp

instance limit_t_ext :: (countable) countable
proof (rule countable_classI[of "\<lambda>i. to_nat (l_min i, l_max i, limit_t.more i)"])
qed simp

instance tg_ext :: (countable) countable
proof (rule countable_classI[of "\<lambda>i. to_nat (tg_mut i, tg_t i, tg.more i)"])
qed simp

end