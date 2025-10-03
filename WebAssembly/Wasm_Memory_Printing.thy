theory Wasm_Memory_Printing imports Wasm_Base_Defs Wasm_Type_Printing Wasm_Interpreter begin


definition mem_rep_read_i32 :: "mem_rep \<Rightarrow> nat \<Rightarrow> i32" where
  "mem_rep_read_i32 m n = deserialise_i32 (mem_rep_read_bytes m n (t_num_length T_i32))"

definition mem_rep_read_i64 :: "mem_rep \<Rightarrow> nat \<Rightarrow> i64" where
  "mem_rep_read_i64 m n = deserialise_i64 (mem_rep_read_bytes m n (t_num_length T_i64))"

definition mem_rep_read_f32 :: "mem_rep \<Rightarrow> nat \<Rightarrow> f32" where
  "mem_rep_read_f32 m n = deserialise_f32 (mem_rep_read_bytes m n (t_num_length T_f32))"

definition mem_rep_read_f64 :: "mem_rep \<Rightarrow> nat \<Rightarrow> f64" where
  "mem_rep_read_f64 m n = deserialise_f64 (mem_rep_read_bytes m n (t_num_length T_f64))"

definition load_v_num' :: "mem \<Rightarrow> nat \<Rightarrow> off \<Rightarrow> t_num \<Rightarrow> v_num option" where
  "load_v_num' m n off t = 
  (let l = t_num_length t in
  (if (mem_length m \<ge> (n+off+l)) then
    (case t of
      T_i32 \<Rightarrow> Some (ConstInt32 (mem_rep_read_i32 (snd m) (n+off)))
    | T_i64 \<Rightarrow> Some (ConstInt64 (mem_rep_read_i64 (snd m) (n+off)))
    | T_f32 \<Rightarrow> Some (ConstFloat32 (mem_rep_read_f32 (snd m) (n+off)))
    | T_f64 \<Rightarrow> Some (ConstFloat64 (mem_rep_read_f64 (snd m) (n+off)))
  ) else None))"

definition mem_rep_read_i32_of_i8 :: "mem_rep \<Rightarrow> nat \<Rightarrow> i32" where
  "mem_rep_read_i32_of_i8 m n =  deserialise_i32 ((sign_extend S (t_num_length T_i32)) (mem_rep_read_bytes m n (tp_num_length Tp_i8)))"

definition mem_rep_read_i32_of_u8 :: "mem_rep \<Rightarrow> nat \<Rightarrow> i32" where
  "mem_rep_read_i32_of_u8 m n =  deserialise_i32 ((sign_extend U (t_num_length T_i32)) (mem_rep_read_bytes m n (tp_num_length Tp_i8)))"

definition mem_rep_read_i32_of_i16 :: "mem_rep \<Rightarrow> nat \<Rightarrow> i32" where
  "mem_rep_read_i32_of_i16 m n =  deserialise_i32 ((sign_extend S (t_num_length T_i32)) (mem_rep_read_bytes m n (tp_num_length Tp_i16)))"

definition mem_rep_read_i32_of_u16 :: "mem_rep \<Rightarrow> nat \<Rightarrow> i32" where
  "mem_rep_read_i32_of_u16 m n =  deserialise_i32 ((sign_extend U (t_num_length T_i32)) (mem_rep_read_bytes m n (tp_num_length Tp_i16)))"

definition mem_rep_read_i32_of_i32 :: "mem_rep \<Rightarrow> nat \<Rightarrow> i32" where
  "mem_rep_read_i32_of_i32 =  mem_rep_read_i32"

definition mem_rep_read_i32_of_u32 :: "mem_rep \<Rightarrow> nat \<Rightarrow> i32" where
  "mem_rep_read_i32_of_u32 =  mem_rep_read_i32"

definition mem_rep_read_i64_of_i8 :: "mem_rep \<Rightarrow> nat \<Rightarrow> i64" where
  "mem_rep_read_i64_of_i8 m n =  deserialise_i64 ((sign_extend S (t_num_length T_i64)) (mem_rep_read_bytes m n (tp_num_length Tp_i8)))"

definition mem_rep_read_i64_of_u8 :: "mem_rep \<Rightarrow> nat \<Rightarrow> i64" where
  "mem_rep_read_i64_of_u8 m n =  deserialise_i64 ((sign_extend U (t_num_length T_i64)) (mem_rep_read_bytes m n (tp_num_length Tp_i8)))"

definition mem_rep_read_i64_of_i16 :: "mem_rep \<Rightarrow> nat \<Rightarrow> i64" where
  "mem_rep_read_i64_of_i16 m n =  deserialise_i64 ((sign_extend S (t_num_length T_i64)) (mem_rep_read_bytes m n (tp_num_length Tp_i16)))"

definition mem_rep_read_i64_of_u16 :: "mem_rep \<Rightarrow> nat \<Rightarrow> i64" where
  "mem_rep_read_i64_of_u16 m n =  deserialise_i64 ((sign_extend U (t_num_length T_i64)) (mem_rep_read_bytes m n (tp_num_length Tp_i16)))"

definition mem_rep_read_i64_of_i32 :: "mem_rep \<Rightarrow> nat \<Rightarrow> i64" where
  "mem_rep_read_i64_of_i32 m n =  deserialise_i64 ((sign_extend S (t_num_length T_i64)) (mem_rep_read_bytes m n (tp_num_length Tp_i32)))"

definition mem_rep_read_i64_of_u32 :: "mem_rep \<Rightarrow> nat \<Rightarrow> i64" where
  "mem_rep_read_i64_of_u32 m n=  deserialise_i64 ((sign_extend U (t_num_length T_i64)) (mem_rep_read_bytes m n (tp_num_length Tp_i32)))"

definition mem_rep_read_i64_of_i64 :: "mem_rep \<Rightarrow> nat \<Rightarrow> i64" where
  "mem_rep_read_i64_of_i64 =  mem_rep_read_i64"

definition mem_rep_read_i64_of_u64 :: "mem_rep \<Rightarrow> nat \<Rightarrow> i64" where
  "mem_rep_read_i64_of_u64 =  mem_rep_read_i64"

definition mem_rep_read_i32_packed :: "mem_rep \<Rightarrow> nat \<Rightarrow> sx \<Rightarrow> tp_num \<Rightarrow> i32" where
  "mem_rep_read_i32_packed m n sx tp = (case (sx, tp) of
    (S,Tp_i8) \<Rightarrow> mem_rep_read_i32_of_i8 m n
  | (U,Tp_i8) \<Rightarrow> mem_rep_read_i32_of_u8 m n
  | (S,Tp_i16) \<Rightarrow> mem_rep_read_i32_of_i16 m n
  | (U,Tp_i16) \<Rightarrow> mem_rep_read_i32_of_u16 m n
  | (S,Tp_i32) \<Rightarrow> mem_rep_read_i32_of_i32 m n
  | (U,Tp_i32) \<Rightarrow> mem_rep_read_i32_of_u32 m n)"

definition mem_rep_read_i64_packed :: "mem_rep \<Rightarrow> nat \<Rightarrow> sx \<Rightarrow> tp_num \<Rightarrow> i64" where
  "mem_rep_read_i64_packed m n sx tp = (case (sx, tp) of
    (S,Tp_i8) \<Rightarrow> mem_rep_read_i64_of_i8 m n
  | (U,Tp_i8) \<Rightarrow> mem_rep_read_i64_of_u8 m n
  | (S,Tp_i16) \<Rightarrow> mem_rep_read_i64_of_i16 m n
  | (U,Tp_i16) \<Rightarrow> mem_rep_read_i64_of_u16 m n
  | (S,Tp_i32) \<Rightarrow> mem_rep_read_i64_of_i32 m n
  | (U,Tp_i32) \<Rightarrow> mem_rep_read_i64_of_u32 m n)"

definition load_packed_v_num' :: "sx \<Rightarrow> mem \<Rightarrow> nat \<Rightarrow> off \<Rightarrow> t_num \<Rightarrow> tp_num \<Rightarrow> v_num option" where
  "load_packed_v_num' sx m n off t tp = (
    (if (mem_length m) \<ge> (n+off+(tp_num_length tp)) then
      (case t of
        T_i32 \<Rightarrow> Some (ConstInt32 (mem_rep_read_i32_packed (snd m) (n+off) sx tp))
      | T_i64 \<Rightarrow> Some (ConstInt64 (mem_rep_read_i64_packed (snd m) (n+off) sx tp))
      | T_f32 \<Rightarrow> Some (ConstFloat32 (deserialise_f32 ((sign_extend sx (t_num_length T_i32)) (mem_rep_read_bytes (snd m) (n+off) (tp_num_length tp))) ))
      | T_f64 \<Rightarrow> Some (ConstFloat64 (deserialise_f64 ((sign_extend sx (t_num_length T_i64)) (mem_rep_read_bytes (snd m) (n+off) (tp_num_length tp))) ))
    )
   else None))"

lemma load_packed_v_num_is[code]: "load_packed_v_num sx m n off t tp = load_packed_v_num' sx m n off t tp"
proof -
  have 1: "\<And> n m k sx. n+k \<le> mem_rep_length m \<Longrightarrow> (mem_rep_read_bytes m n k) = (sign_extend sx k (mem_rep_read_bytes m n k))"
    unfolding mem_rep_read_bytes_def  unfolding mem_rep_length_def
    sign_extend_def bytes_takefill_def by (auto simp add: takefill_same')
  show ?thesis
  apply (cases "load m n off (tp_num_length tp)")
  unfolding mem_rep_read_i32_packed_def mem_rep_read_i64_packed_def load_packed_v_num_def load_packed_v_num'_def
    mem_rep_read_i32_of_i8_def
    mem_rep_read_i32_of_u8_def
    mem_rep_read_i32_of_i16_def
    mem_rep_read_i32_of_u16_def
    mem_rep_read_i32_of_i32_def
    mem_rep_read_i32_of_u32_def
    mem_rep_read_i64_of_i8_def
    mem_rep_read_i64_of_u8_def
    mem_rep_read_i64_of_i16_def
    mem_rep_read_i64_of_u16_def
    mem_rep_read_i64_of_i32_def
    mem_rep_read_i64_of_u32_def
    mem_rep_read_i32_def
    using t_num_length_def tp_num_length_def
    apply (auto simp add: read_bytes_def wasm_deserialise_num_def load_def split: if_splits t_num.splits tp_num.splits sx.splits option.splits)
    using mem_length_def 1[of "n+off" "4" "snd m"] 1[of "n+off" "8" "snd m"]
    by auto  
qed

lemma load_v_num_is[code]: "load_v_num m n off t = load_v_num' m n off t"
  unfolding load_v_num_def load_v_num'_def load_def
            write_bytes_def
            mem_rep_read_i32_def 
            mem_rep_read_i64_def
            mem_rep_read_f32_def 
            mem_rep_read_f64_def
            wasm_deserialise_num_def
            read_bytes_def
            mem_rep_read_bytes_def
  by (auto split: t_num.splits v_num.splits)

definition mem_rep_write_i32 :: "mem_rep \<Rightarrow> nat \<Rightarrow> i32 \<Rightarrow> mem_rep" where
  "mem_rep_write_i32 m n val = mem_rep_write_bytes m n (serialise_i32 val)"

definition mem_rep_write_i64 :: "mem_rep \<Rightarrow> nat \<Rightarrow> i64 \<Rightarrow> mem_rep" where
  "mem_rep_write_i64 m n val = mem_rep_write_bytes m n (serialise_i64 val)"

definition mem_rep_write_f32 :: "mem_rep \<Rightarrow> nat \<Rightarrow> f32 \<Rightarrow> mem_rep" where
  "mem_rep_write_f32 m n val = (mem_rep_write_bytes m n (serialise_f32 val))"

definition mem_rep_write_f64 :: "mem_rep \<Rightarrow> nat \<Rightarrow> f64 \<Rightarrow> mem_rep" where
  "mem_rep_write_f64 m n val = mem_rep_write_bytes m n (serialise_f64 val)"


definition mem_rep_write_i8_of_i32 :: "mem_rep \<Rightarrow> nat \<Rightarrow> i32 \<Rightarrow> mem_rep" where
  "mem_rep_write_i8_of_i32 m n val = mem_rep_write_bytes m n (bytes_takefill zero_byte (tp_num_length Tp_i8) (serialise_i32 val))"

definition mem_rep_write_i16_of_i32 :: "mem_rep \<Rightarrow> nat \<Rightarrow> i32 \<Rightarrow> mem_rep" where
  "mem_rep_write_i16_of_i32 m n val = mem_rep_write_bytes m n (bytes_takefill zero_byte (tp_num_length Tp_i16) (serialise_i32 val))"

definition mem_rep_write_i32_of_i32 :: "mem_rep \<Rightarrow> nat \<Rightarrow> i32 \<Rightarrow> mem_rep" where
  "mem_rep_write_i32_of_i32 m n val = mem_rep_write_bytes m n (bytes_takefill zero_byte (tp_num_length Tp_i32) (serialise_i32 val))"

definition mem_rep_write_i8_of_i64 :: "mem_rep \<Rightarrow> nat \<Rightarrow> i64 \<Rightarrow> mem_rep" where
  "mem_rep_write_i8_of_i64 m n val = mem_rep_write_bytes m n (bytes_takefill zero_byte (tp_num_length Tp_i8) (serialise_i64 val))"

definition mem_rep_write_i16_of_i64 :: "mem_rep \<Rightarrow> nat \<Rightarrow> i64 \<Rightarrow> mem_rep" where
  "mem_rep_write_i16_of_i64 m n val = mem_rep_write_bytes m n (bytes_takefill zero_byte (tp_num_length Tp_i16) (serialise_i64 val))"

definition mem_rep_write_i32_of_i64 :: "mem_rep \<Rightarrow> nat \<Rightarrow> i64 \<Rightarrow> mem_rep" where
  "mem_rep_write_i32_of_i64 m n val = mem_rep_write_bytes m n (bytes_takefill zero_byte (tp_num_length Tp_i32) (serialise_i64 val))"

definition store_packed_v_num' :: "mem \<Rightarrow> nat \<Rightarrow> off \<Rightarrow> v_num \<Rightarrow> tp_num \<Rightarrow> mem option" where
  "store_packed_v_num' m n off v tp =
    (if mem_length m \<ge> n + off + (tp_num_length tp) then 
      Some (fst m, (case v of
        ConstInt32 val \<Rightarrow>
          (case tp of
            Tp_i8 \<Rightarrow> mem_rep_write_i8_of_i32 (snd m) (n+off) val
          | Tp_i16 \<Rightarrow> mem_rep_write_i16_of_i32 (snd m) (n+off) val
          | Tp_i32 \<Rightarrow> mem_rep_write_i32_of_i32 (snd m) (n+off) val)
      | ConstInt64 val \<Rightarrow>
          (case tp of
            Tp_i8 \<Rightarrow> mem_rep_write_i8_of_i64 (snd m) (n+off) val
          | Tp_i16 \<Rightarrow> mem_rep_write_i16_of_i64 (snd m) (n+off) val
          | Tp_i32 \<Rightarrow> mem_rep_write_i32_of_i64 (snd m) (n+off) val)
      | ConstFloat32 val \<Rightarrow> mem_rep_write_bytes (snd m) (n + off)
           (bytes_takefill zero_byte (tp_num_length tp) (serialise_f32 val))
      | ConstFloat64 val \<Rightarrow> mem_rep_write_bytes (snd m) (n + off)
           (bytes_takefill zero_byte (tp_num_length tp) (serialise_f64 val))))
   else None)"

lemma store_packed_v_num_is[code]: "store_packed_v_num m n off v tp = store_packed_v_num' m n off v tp"
  unfolding store_packed_v_num_def store_packed_v_num'_def store_def write_bytes_def
  mem_rep_write_i8_of_i32_def
  mem_rep_write_i16_of_i32_def
  mem_rep_write_i32_of_i32_def
  mem_rep_write_i8_of_i64_def
  mem_rep_write_i16_of_i64_def
  mem_rep_write_i32_of_i64_def
  bits_num_def
  by (auto split: if_splits tp_num.splits v_num.splits)

definition store_v_num' :: "mem \<Rightarrow> nat \<Rightarrow> off \<Rightarrow> v_num \<Rightarrow> mem option" where
  "store_v_num' m n off vn = (let l = (t_num_length (typeof_num vn)) in
    (if (mem_length m \<ge> (n+off+l)) then
      (case vn of 
        ConstInt32 val \<Rightarrow> Some (fst m, mem_rep_write_i32 (snd m) (n+off) val)
      | ConstInt64 val \<Rightarrow> Some (fst m, mem_rep_write_i64 (snd m) (n+off) val)
      | ConstFloat32 val \<Rightarrow> Some (fst m, mem_rep_write_f32 (snd m) (n+off) val)
      | ConstFloat64 val \<Rightarrow> Some (fst m, mem_rep_write_f64 (snd m) (n+off) val))
    else None))"

lemma store_v_num_is[code]: "store_v_num m n off v = store_v_num' m n off v"
  unfolding store_v_num_def store_v_num'_def store_def
            write_bytes_def
            mem_rep_write_i32_def 
            mem_rep_write_i64_def
            mem_rep_write_f32_def 
            mem_rep_write_f64_def
  apply (auto split: v_num.splits)
  unfolding word_rsplit_rev_def bits_num_def bytes_takefill_def
            serialise_i32_def
            serialise_i64_def
  using typeof_num_def t_num_length_def takefill_same serialise_f32_len serialise_f64_len
  by (auto simp add: takefill_same' split: t_num.splits)

(* Perhaps a more appropriate place for ocaml_int and related conversions is in Wasm_Type_Printing *)
(* But right now it is only used for Parray memory representation *)
typedecl ocaml_int

consts
  ocaml_int_to_integer :: "ocaml_int \<Rightarrow> integer"
  integer_to_ocaml_int :: "integer \<Rightarrow> ocaml_int"
  ocaml_int_to_ocaml_i32_s :: "ocaml_int \<Rightarrow> ocaml_i32"
  ocaml_int_to_ocaml_i64_s :: "ocaml_int \<Rightarrow> ocaml_i64"

code_printing
  type_constructor ocaml_int \<rightharpoonup> (OCaml) "Int.t"
| constant ocaml_int_to_integer \<rightharpoonup> (OCaml) "Z.of'_int"
| constant integer_to_ocaml_int \<rightharpoonup> (OCaml) "Z.to'_int"
| constant ocaml_int_to_ocaml_i32_s \<rightharpoonup> (OCaml) "I32Wrapper'_convert.of'_int'_s"
| constant ocaml_int_to_ocaml_i64_s \<rightharpoonup> (OCaml) "I64Wrapper'_convert.of'_int'_s"

definition ocaml_int_to_nat :: "ocaml_int \<Rightarrow> nat" where
  "ocaml_int_to_nat x = nat_of_integer (ocaml_int_to_integer x)"

definition nat_to_ocaml_int :: "nat \<Rightarrow> ocaml_int" where
  "nat_to_ocaml_int x = integer_to_ocaml_int (integer_of_nat x)"

consts
  ocaml_mem_rep_pbytes_length :: "mem_rep \<Rightarrow> ocaml_int"
  ocaml_mem_rep_pbytes_mk :: "ocaml_int \<Rightarrow> ocaml_char \<Rightarrow> mem_rep"
  ocaml_mem_rep_pbytes_byte_at :: "mem_rep \<Rightarrow> ocaml_int \<Rightarrow> ocaml_char"
  ocaml_mem_rep_pbytes_read_bytes :: "mem_rep \<Rightarrow> ocaml_int \<Rightarrow> ocaml_int \<Rightarrow> ocaml_char list"
  ocaml_mem_rep_pbytes_write_bytes :: "mem_rep \<Rightarrow> ocaml_int \<Rightarrow> ocaml_char list \<Rightarrow> mem_rep"
  ocaml_mem_rep_pbytes_append :: "mem_rep \<Rightarrow> ocaml_int \<Rightarrow> ocaml_char \<Rightarrow> mem_rep"
  ocaml_mem_rep_pbytes_set_int8 :: "mem_rep \<Rightarrow> ocaml_int \<Rightarrow> ocaml_int \<Rightarrow> mem_rep"
  ocaml_mem_rep_pbytes_get_int8 :: "mem_rep \<Rightarrow> ocaml_int \<Rightarrow> ocaml_int"
  ocaml_mem_rep_pbytes_set_uint8 :: "mem_rep \<Rightarrow> ocaml_int \<Rightarrow> ocaml_int \<Rightarrow> mem_rep"
  ocaml_mem_rep_pbytes_get_uint8 :: "mem_rep \<Rightarrow> ocaml_int \<Rightarrow> ocaml_int"
  ocaml_mem_rep_pbytes_set_int16 :: "mem_rep \<Rightarrow> ocaml_int \<Rightarrow> ocaml_int \<Rightarrow> mem_rep"
  ocaml_mem_rep_pbytes_get_int16 :: "mem_rep \<Rightarrow> ocaml_int \<Rightarrow> ocaml_int"
  ocaml_mem_rep_pbytes_set_uint16 :: "mem_rep \<Rightarrow> ocaml_int \<Rightarrow> ocaml_int \<Rightarrow> mem_rep"
  ocaml_mem_rep_pbytes_get_uint16 :: "mem_rep \<Rightarrow> ocaml_int \<Rightarrow> ocaml_int"
  ocaml_mem_rep_pbytes_set_int32 :: "mem_rep \<Rightarrow> ocaml_int \<Rightarrow> ocaml_i32 \<Rightarrow> mem_rep"
  ocaml_mem_rep_pbytes_get_int32 :: "mem_rep \<Rightarrow> ocaml_int \<Rightarrow> ocaml_i32"
  ocaml_mem_rep_pbytes_set_int64 :: "mem_rep \<Rightarrow> ocaml_int \<Rightarrow> ocaml_i64 \<Rightarrow> mem_rep"
  ocaml_mem_rep_pbytes_get_int64 :: "mem_rep \<Rightarrow> ocaml_int \<Rightarrow> ocaml_i64"

code_printing
  type_constructor mem_rep \<rightharpoonup> (OCaml) "Pbytes.pbt"
| constant ocaml_mem_rep_pbytes_mk \<rightharpoonup> (OCaml) "Pbytes.make "
| constant ocaml_mem_rep_pbytes_length  \<rightharpoonup> (OCaml) "Pbytes.length"
| constant ocaml_mem_rep_pbytes_byte_at \<rightharpoonup> (OCaml) "MemRepWrapper.memRepByteAt"
| constant ocaml_mem_rep_pbytes_read_bytes \<rightharpoonup> (OCaml) "MemRepWrapper.memRepReadBytes"
| constant ocaml_mem_rep_pbytes_write_bytes \<rightharpoonup> (OCaml) "MemRepWrapper.memRepWriteBytes"
| constant ocaml_mem_rep_pbytes_append \<rightharpoonup> (OCaml) "MemRepWrapper.memRepAppend"
| constant ocaml_mem_rep_pbytes_set_int8 \<rightharpoonup> (OCaml) "Pbytes.set'_int8"
| constant ocaml_mem_rep_pbytes_get_int8 \<rightharpoonup> (OCaml) "Pbytes.get'_int8"
| constant ocaml_mem_rep_pbytes_set_uint8 \<rightharpoonup> (OCaml) "Pbytes.set'_uint8"
| constant ocaml_mem_rep_pbytes_get_uint8 \<rightharpoonup> (OCaml) "Pbytes.get'_uint8"
| constant ocaml_mem_rep_pbytes_set_int16 \<rightharpoonup> (OCaml) "Pbytes.set'_int16"
| constant ocaml_mem_rep_pbytes_get_int16 \<rightharpoonup> (OCaml) "Pbytes.get'_int16"
| constant ocaml_mem_rep_pbytes_set_uint16 \<rightharpoonup> (OCaml) "Pbytes.set'_uint16"
| constant ocaml_mem_rep_pbytes_get_uint16 \<rightharpoonup> (OCaml) "Pbytes.get'_uint16"
| constant ocaml_mem_rep_pbytes_set_int32 \<rightharpoonup> (OCaml) "Pbytes.set'_int32"
| constant ocaml_mem_rep_pbytes_get_int32 \<rightharpoonup> (OCaml) "Pbytes.get'_int32"
| constant ocaml_mem_rep_pbytes_set_int64 \<rightharpoonup> (OCaml) "Pbytes.set'_int64"
| constant ocaml_mem_rep_pbytes_get_int64 \<rightharpoonup> (OCaml) "Pbytes.get'_int64"

axiomatization where
  mem_rep_length_is[code]: "mem_rep_length m \<equiv> ocaml_int_to_nat (ocaml_mem_rep_pbytes_length m)" and
  mem_rep_byte_at_is[code]: "mem_rep_byte_at m x \<equiv> ocaml_char_to_isabelle_byte (ocaml_mem_rep_pbytes_byte_at m (nat_to_ocaml_int x))" and
  mem_rep_read_bytes_is[code]: "mem_rep_read_bytes m x y \<equiv> map ocaml_char_to_isabelle_byte (ocaml_mem_rep_pbytes_read_bytes m (nat_to_ocaml_int x) (nat_to_ocaml_int y))" and
  mem_rep_write_bytes_is[code]: "mem_rep_write_bytes m x bs \<equiv> ocaml_mem_rep_pbytes_write_bytes m (nat_to_ocaml_int x) (map isabelle_byte_to_ocaml_char bs)" and
  mem_rep_append_is[code]: "mem_rep_append m x b \<equiv> ocaml_mem_rep_pbytes_append m (nat_to_ocaml_int x) (isabelle_byte_to_ocaml_char b)" and
  mem_rep_mk_is[code]: "mem_rep_mk x = ocaml_mem_rep_pbytes_mk (nat_to_ocaml_int (x * Ki64)) (isabelle_byte_to_ocaml_char zero_byte)" and
  
  mem_rep_write_i32_is[code]: "mem_rep_write_i32 m n val = ocaml_mem_rep_pbytes_set_int32 m (nat_to_ocaml_int n) (isabelle_int32_to_ocaml_int32 val)" and
  mem_rep_read_i32_is[code]: "mem_rep_read_i32 m n = ocaml_int32_to_isabelle_int32 (ocaml_mem_rep_pbytes_get_int32 m (nat_to_ocaml_int n))" and
  mem_rep_write_i64_is[code]: "mem_rep_write_i64 m n vi64 = ocaml_mem_rep_pbytes_set_int64 m (nat_to_ocaml_int n) (isabelle_int64_to_ocaml_int64 vi64)" and
  mem_rep_read_i64_is[code]: "mem_rep_read_i64 m n = ocaml_int64_to_isabelle_int64 (ocaml_mem_rep_pbytes_get_int64 m (nat_to_ocaml_int n))" and
  mem_rep_write_f32_is[code]: "mem_rep_write_f32 m n vf32 = ocaml_mem_rep_pbytes_set_int32 m (nat_to_ocaml_int n) (ocaml_i32_reinterpret_f32 vf32)" and
  mem_rep_read_f32_is[code]: "mem_rep_read_f32 m n = ocaml_f32_reinterpret_i32 (ocaml_mem_rep_pbytes_get_int32 m (nat_to_ocaml_int n))" and
  mem_rep_write_f64_is[code]: "mem_rep_write_f64 m n vf64 = ocaml_mem_rep_pbytes_set_int64 m (nat_to_ocaml_int n) (ocaml_i64_reinterpret_f64 vf64)" and
  mem_rep_read_f64_is[code]: "mem_rep_read_f64 m n = ocaml_f64_reinterpret_i64 (ocaml_mem_rep_pbytes_get_int64 m (nat_to_ocaml_int n))" and
  
  mem_rep_write_i8_of_i32_is[code]: "mem_rep_read_i32_of_i8 m n = ocaml_int32_to_isabelle_int32 (ocaml_int_to_ocaml_i32_s (ocaml_mem_rep_pbytes_get_int8 m (nat_to_ocaml_int n)))" and
  mem_rep_write_u8_of_i32_is[code]: "mem_rep_read_i32_of_u8 m n = ocaml_int32_to_isabelle_int32 (ocaml_int_to_ocaml_i32_s (ocaml_mem_rep_pbytes_get_uint8 m (nat_to_ocaml_int n)))" and  
  mem_rep_write_i16_of_i32_is[code]: "mem_rep_read_i32_of_i16 m n = ocaml_int32_to_isabelle_int32 (ocaml_int_to_ocaml_i32_s (ocaml_mem_rep_pbytes_get_int16 m (nat_to_ocaml_int n)))" and  
  mem_rep_write_u16_of_i32_is[code]: "mem_rep_read_i32_of_u16 m n = ocaml_int32_to_isabelle_int32 (ocaml_int_to_ocaml_i32_s (ocaml_mem_rep_pbytes_get_uint16 m (nat_to_ocaml_int n)))" and  
  mem_rep_write_i32_of_i32_is[code]: "mem_rep_read_i32_of_i32 m n = ocaml_int32_to_isabelle_int32 (ocaml_mem_rep_pbytes_get_int32 m (nat_to_ocaml_int n))" and  
  mem_rep_write_u32_of_i32_is[code]: "mem_rep_read_i32_of_u32 m n = ocaml_int32_to_isabelle_int32 (ocaml_mem_rep_pbytes_get_int32 m (nat_to_ocaml_int n))" and
  
  mem_rep_write_i8_of_i64_is[code]: "mem_rep_read_i64_of_i8 m n = ocaml_int64_to_isabelle_int64 (ocaml_int_to_ocaml_i64_s (ocaml_mem_rep_pbytes_get_int8 m (nat_to_ocaml_int n)))" and
  mem_rep_write_u8_of_i64_is[code]: "mem_rep_read_i64_of_u8 m n = ocaml_int64_to_isabelle_int64 (ocaml_int_to_ocaml_i64_s (ocaml_mem_rep_pbytes_get_uint8 m (nat_to_ocaml_int n)))" and  
  mem_rep_write_i16_of_i64_is[code]: "mem_rep_read_i64_of_i16 m n = ocaml_int64_to_isabelle_int64 (ocaml_int_to_ocaml_i64_s (ocaml_mem_rep_pbytes_get_int16 m (nat_to_ocaml_int n)))" and  
  mem_rep_write_u16_of_i64_is[code]: "mem_rep_read_i64_of_u16 m n = ocaml_int64_to_isabelle_int64 (ocaml_int_to_ocaml_i64_s (ocaml_mem_rep_pbytes_get_uint16 m (nat_to_ocaml_int n)))" and  

  mem_rep_write_i32_of_i64_is[code]: "mem_rep_read_i64_of_i32 m n = wasm_extend_s (ocaml_int32_to_isabelle_int32 (ocaml_mem_rep_pbytes_get_int32 m (nat_to_ocaml_int n)))" and  
  mem_rep_write_u32_of_i64_is[code]: "mem_rep_read_i64_of_u32 m n = wasm_extend_u (ocaml_int32_to_isabelle_int32 (ocaml_mem_rep_pbytes_get_int32 m (nat_to_ocaml_int n)))"
end