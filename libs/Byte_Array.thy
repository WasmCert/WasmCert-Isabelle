theory Byte_Array
  imports
    Main
    "Native_Word.Uint8"
    "Native_Word.Uint32"
    "Native_Word.Uint64"
    "HOL-Imperative_HOL.Array"
    "Array_Blit"
    "More_More_Word"
begin

chapter \<open>Monadic byte arrays, geared towards OCaml's "bytes" type\<close>

typedef byte_array = "UNIV :: (uint8 array) set" ..
setup_lifting type_definition_byte_array
declare Quotient_byte_array[transfer_rule]

instance uint8 :: heap
  apply standard
  apply transfer
  apply auto
  done

instance byte_array :: heap
  apply standard
  apply transfer
  apply auto
  done

lift_definition
  bl_assn :: "byte_array \<Rightarrow> uint8 list \<Rightarrow> assn" (infix "\<mapsto>\<^sub>b\<^sub>a" 82)
  is "\<lambda>(r::uint8 array) (a::uint8 list). r\<mapsto>\<^sub>aa" .

(* basic operations *)

lift_definition new_zeroed_byte_array :: "nat \<Rightarrow> byte_array Heap" is
  "\<lambda>n. Array.new n (0::uint8)" .

lift_definition len_byte_array :: "byte_array \<Rightarrow> nat Heap" is
  "Array.len :: uint8 array \<Rightarrow> nat Heap" .

lift_definition blit_byte_array :: "byte_array \<Rightarrow> nat \<Rightarrow> byte_array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> unit Heap" is
  "blit :: uint8 array \<Rightarrow> nat \<Rightarrow> uint8 array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> unit Heap" .

definition grow_zeroed_byte_array :: "byte_array \<Rightarrow> nat \<Rightarrow> byte_array Heap" where
  "grow_zeroed_byte_array a n \<equiv> do {
    if n=0 then 
      return a
    else do {
      l\<leftarrow>len_byte_array a;
      a'\<leftarrow>new_zeroed_byte_array (l+n);
      blit_byte_array a 0 a' 0 l;
      return a'
    }
  }"

lemma map_Heap_assn:
  assumes
    "inj f"
    "
    < P > 
      c
    <\<lambda>x. Q x>"
  shows "
    < P > 
      map_Heap f c
    <\<lambda>x. Q ((inv f) x)>"
  using assms
  unfolding hoare_triple_def
  apply (cases c)
  apply (simp add: Let_def run.simps)
  apply (metis (no_types, lifting) inv_f_f)
  done

lemma map_Heap_byte_array:
  assumes "
    < P > 
      c
    <\<lambda>(x::uint8 array). Q x>"
  shows "
    < P > 
      map_Heap Abs_byte_array c
    <\<lambda>x. Q (Rep_byte_array x)>"
proof -
  have "inj Abs_byte_array"
    by (metis Abs_byte_array_inverse UNIV_I inj_def)
  moreover hence "inv Abs_byte_array = Rep_byte_array"
    by (simp add: Rep_byte_array_inverse inj_imp_inv_eq)
  ultimately show ?thesis
    using map_Heap_assn assms
    by metis
qed

lemma new_zeroed_byte_array_rule[sep_heap_rules]:
  shows "
    < emp > 
      new_zeroed_byte_array n
    <\<lambda>a'. a'\<mapsto>\<^sub>b\<^sub>a (replicate n 0)>"
  using map_Heap_byte_array[OF new_rule]
  unfolding new_zeroed_byte_array_def bl_assn_def
  by sep_auto

lemma len_byte_array_rule[sep_heap_rules]:
  "<a \<mapsto>\<^sub>b\<^sub>a la>
     len_byte_array a
   <\<lambda>r. a \<mapsto>\<^sub>b\<^sub>a la * \<up>(r = length la)>"
  using map_Heap_byte_array
  unfolding len_byte_array_def bl_assn_def
  by sep_auto

lemma blit_byte_array_rule[sep_heap_rules]:
  assumes LEN: "si+len \<le> length lsrc" "di+len \<le> length ldst"
  shows
  "< src \<mapsto>\<^sub>b\<^sub>a lsrc 
    * dst \<mapsto>\<^sub>b\<^sub>a ldst >
  blit_byte_array src si dst di len
  <\<lambda>_. src \<mapsto>\<^sub>b\<^sub>a lsrc 
    * dst \<mapsto>\<^sub>b\<^sub>a (take di ldst @ take len (drop si lsrc) @ drop (di+len) ldst)
  >"
  using map_Heap_byte_array assms
  unfolding blit_byte_array_def bl_assn_def
  by sep_auto

lemma grow_zeroed_byte_array_rule[sep_heap_rules]:
  shows "
    < a\<mapsto>\<^sub>b\<^sub>ala > 
      grow_zeroed_byte_array a n 
    <\<lambda>a'. a'\<mapsto>\<^sub>b\<^sub>a (la @ replicate n 0)>\<^sub>t"
  using map_Heap_byte_array
  unfolding grow_zeroed_byte_array_def
  by (sep_auto heap:len_byte_array_rule new_zeroed_byte_array_rule blit_byte_array_rule)

(* loading and storing bytes *)

lift_definition load_uint8 :: "byte_array \<Rightarrow> nat \<Rightarrow> uint8 Heap" is
   "\<lambda>(a::uint8 array) n. Array.nth a n" .

fun load_uint8_list :: "byte_array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> uint8 list Heap" where
  "load_uint8_list a n 0 = return []"
| "load_uint8_list a n (Suc l) = do {
     b\<leftarrow>load_uint8 a n;
     bs\<leftarrow>load_uint8_list a (Suc n) l;
     return (b#bs)
   }"

lift_definition store_uint8 :: "byte_array \<Rightarrow> nat \<Rightarrow> uint8 \<Rightarrow> unit Heap" is
   "\<lambda>(a::uint8 array) n b. (do { Array.upd n b a; return () })" .

fun store_uint8_list :: "byte_array \<Rightarrow> nat \<Rightarrow> uint8 list \<Rightarrow> unit Heap" where
  "store_uint8_list a n [] = return ()"
| "store_uint8_list a n (b#bs) = do {
     store_uint8 a n b;
     store_uint8_list a (Suc n) bs
   }"

(* loading and storing uint32 *)

definition load_uint32_of_uintX :: "byte_array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> uint32 Heap" where
  "load_uint32_of_uintX a n x \<equiv> do {
     bs\<leftarrow>load_uint8_list a n x;
     return (Abs_uint32' (word_rcat_rev (map Rep_uint8' bs)))
  }"

definition load_uint32_of_sintX :: "byte_array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> uint32 Heap" where
  "load_uint32_of_sintX a n x \<equiv> do {
     bs\<leftarrow>load_uint8_list a n x;
     return (Abs_uint32' (word_rcat_rev (word_list_sign_extend 4 (map Rep_uint8' bs))))
  }"

definition store_uintX_of_uint32 :: "byte_array \<Rightarrow> nat \<Rightarrow> uint32 \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "store_uintX_of_uint32 a n v x \<equiv> do {
     store_uint8_list a n (map Abs_uint8' (takefill (0::8 word) x (word_rsplit_rev (Rep_uint32' v))))
  }"

definition load_uint32_of_uint8 :: "byte_array \<Rightarrow> nat \<Rightarrow> uint32 Heap" where
  "load_uint32_of_uint8 a n \<equiv> load_uint32_of_uintX a n 1"

definition load_uint32_of_sint8 :: "byte_array \<Rightarrow> nat \<Rightarrow> uint32 Heap" where
  "load_uint32_of_sint8 a n \<equiv> load_uint32_of_sintX a n 1"

definition load_uint32_of_uint16 :: "byte_array \<Rightarrow> nat \<Rightarrow> uint32 Heap" where
  "load_uint32_of_uint16 a n \<equiv>  load_uint32_of_uintX a n 2"

definition load_uint32_of_sint16 :: "byte_array \<Rightarrow> nat \<Rightarrow> uint32 Heap" where
  "load_uint32_of_sint16 a n \<equiv> load_uint32_of_sintX a n 2"

definition load_uint32 :: "byte_array \<Rightarrow> nat \<Rightarrow> uint32 Heap" where
  "load_uint32 a n \<equiv>  load_uint32_of_uintX a n 4"

definition store_uint8_of_uint32 :: "byte_array \<Rightarrow> nat \<Rightarrow> uint32 \<Rightarrow> unit Heap" where
  "store_uint8_of_uint32 a n v \<equiv> store_uintX_of_uint32 a n v 1"

definition store_uint16_of_uint32 :: "byte_array \<Rightarrow> nat \<Rightarrow> uint32 \<Rightarrow> unit Heap" where
  "store_uint16_of_uint32 a n v \<equiv> store_uintX_of_uint32 a n v 2"

definition store_uint32 :: "byte_array \<Rightarrow> nat \<Rightarrow> uint32 \<Rightarrow> unit Heap" where
  "store_uint32 a n v \<equiv> store_uintX_of_uint32 a n v 4"

(* loading and storing uint64 *)

definition load_uint64_of_uintX :: "byte_array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> uint64 Heap" where
  "load_uint64_of_uintX a n x \<equiv> do {
     bs\<leftarrow>load_uint8_list a n x;
     return (Abs_uint64' (word_rcat_rev (map Rep_uint8' bs)))
  }"

definition load_uint64_of_sintX :: "byte_array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> uint64 Heap" where
  "load_uint64_of_sintX a n x \<equiv> do {
     bs\<leftarrow>load_uint8_list a n x;
     return (Abs_uint64' (word_rcat_rev (word_list_sign_extend 8 (map Rep_uint8' bs))))
  }"

definition store_uintX_of_uint64 :: "byte_array \<Rightarrow> nat \<Rightarrow> uint64 \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "store_uintX_of_uint64 a n v x \<equiv> do {
     store_uint8_list a n (map Abs_uint8' (takefill (0::8 word) x (word_rsplit_rev (Rep_uint64' v))))
  }"

definition load_uint64_of_uint8 :: "byte_array \<Rightarrow> nat \<Rightarrow> uint64 Heap" where
  "load_uint64_of_uint8 a n \<equiv> load_uint64_of_uintX a n 1"

definition load_uint64_of_sint8 :: "byte_array \<Rightarrow> nat \<Rightarrow> uint64 Heap" where
  "load_uint64_of_sint8 a n \<equiv> load_uint64_of_sintX a n 1"

definition load_uint64_of_uint16 :: "byte_array \<Rightarrow> nat \<Rightarrow> uint64 Heap" where
  "load_uint64_of_uint16 a n \<equiv> load_uint64_of_uintX a n 2"

definition load_uint64_of_sint16 :: "byte_array \<Rightarrow> nat \<Rightarrow> uint64 Heap" where
  "load_uint64_of_sint16 a n \<equiv> load_uint64_of_sintX a n 2"

definition load_uint64_of_uint32 :: "byte_array \<Rightarrow> nat \<Rightarrow> uint64 Heap" where
  "load_uint64_of_uint32 a n \<equiv> load_uint64_of_uintX a n 4"

definition load_uint64_of_sint32 :: "byte_array \<Rightarrow> nat \<Rightarrow> uint64 Heap" where
  "load_uint64_of_sint32 a n \<equiv> load_uint64_of_sintX a n 4"

definition load_uint64 :: "byte_array \<Rightarrow> nat \<Rightarrow> uint64 Heap" where
  "load_uint64 a n \<equiv> load_uint64_of_uintX a n 8"

definition store_uint8_of_uint64 :: "byte_array \<Rightarrow> nat \<Rightarrow> uint64 \<Rightarrow> unit Heap" where
  "store_uint8_of_uint64 a n v \<equiv> store_uintX_of_uint64 a n v 1"

definition store_uint16_of_uint64 :: "byte_array \<Rightarrow> nat \<Rightarrow> uint64 \<Rightarrow> unit Heap" where
  "store_uint16_of_uint64 a n v \<equiv> store_uintX_of_uint64 a n v 2"

definition store_uint32_of_uint64 :: "byte_array \<Rightarrow> nat \<Rightarrow> uint64 \<Rightarrow> unit Heap" where
  "store_uint32_of_uint64 a n v \<equiv> store_uintX_of_uint64 a n v 4"

definition store_uint64 :: "byte_array \<Rightarrow> nat \<Rightarrow> uint64 \<Rightarrow> unit Heap" where
  "store_uint64 a n v \<equiv> store_uintX_of_uint64 a n v 8"

(* load/store heap rules *) 

lemma [sep_heap_rules]: "<a \<mapsto>\<^sub>b\<^sub>a la> 
  load_uint8 a n
   <\<lambda>r. \<up>(n < length la \<and> r = la!n) * a \<mapsto>\<^sub>b\<^sub>a la >"
  unfolding load_uint8_def bl_assn_def 
  by sep_auto


lemma [sep_heap_rules]: "<a \<mapsto>\<^sub>b\<^sub>a la> 
  load_uint8_list a n x
   <\<lambda>r. \<up>((if x > 0 then n+x \<le> length la else True) \<and> r = take x (drop n la) ) * a \<mapsto>\<^sub>b\<^sub>a la >"
proof(induct x arbitrary:la a n)
case 0
  then show ?case by(sep_auto)
next
  case (Suc x)
  show ?case 
    apply(sep_auto heap:Suc)
    using less_imp_Suc_add apply force
    by (metis Cons_nth_drop_Suc take_Suc_Cons)
qed

lemma [sep_heap_rules]: "<a \<mapsto>\<^sub>b\<^sub>a la> 
  load_uint32_of_uintX a n x
   <\<lambda>r. \<up>(r = (Abs_uint32' \<circ> word_rcat_rev \<circ> map Rep_uint8') (take x (drop n la)) 
 \<and> (if x > 0 then n+x \<le> length la else True)) * a \<mapsto>\<^sub>b\<^sub>a la >"
  unfolding load_uint32_of_uintX_def by sep_auto

lemma [sep_heap_rules]: "<a \<mapsto>\<^sub>b\<^sub>a la> 
  load_uint32_of_sintX a n x
   <\<lambda>r. \<up>(r = (Abs_uint32' \<circ> word_rcat_rev \<circ> word_list_sign_extend 4 \<circ> map Rep_uint8') 
  (take x (drop n la)) 
  \<and> (if x > 0 then n+x \<le> length la else True)) * a \<mapsto>\<^sub>b\<^sub>a la >"
  unfolding load_uint32_of_sintX_def by sep_auto

lemma [sep_heap_rules]: "<a \<mapsto>\<^sub>b\<^sub>a la> 
  load_uint32_of_uint8 a n
   <\<lambda>r. \<up>(r = (Abs_uint32' \<circ> word_rcat_rev \<circ> map Rep_uint8') (take 1 (drop n la))
  \<and> n+1 \<le> length la) * a \<mapsto>\<^sub>b\<^sub>a la >"
  unfolding load_uint32_of_uint8_def by sep_auto

lemma [sep_heap_rules]: "<a \<mapsto>\<^sub>b\<^sub>a la> 
  load_uint32_of_sint8 a n
   <\<lambda>r. \<up>(r = (Abs_uint32' \<circ> word_rcat_rev \<circ> word_list_sign_extend 4 \<circ> map Rep_uint8') 
  (take 1 (drop n la))
  \<and> n+1 \<le> length la ) * a \<mapsto>\<^sub>b\<^sub>a la >"
  unfolding load_uint32_of_sint8_def by sep_auto

lemma [sep_heap_rules]: "<a \<mapsto>\<^sub>b\<^sub>a la> 
  load_uint32_of_uint16 a n
   <\<lambda>r. \<up>(r = (Abs_uint32' \<circ> word_rcat_rev \<circ> map Rep_uint8') (take 2 (drop n la))
  \<and> n+2 \<le> length la )  * a \<mapsto>\<^sub>b\<^sub>a la >"
  unfolding load_uint32_of_uint16_def by sep_auto

lemma [sep_heap_rules]: "<a \<mapsto>\<^sub>b\<^sub>a la> 
  load_uint32_of_sint16 a n
   <\<lambda>r. \<up>(r = (Abs_uint32' \<circ> word_rcat_rev \<circ> word_list_sign_extend 4 \<circ> map Rep_uint8') 
  (take 2 (drop n la))
   \<and> n+2 \<le> length la ) * a \<mapsto>\<^sub>b\<^sub>a la >"
  unfolding load_uint32_of_sint16_def by sep_auto

lemma [sep_heap_rules]: "<a \<mapsto>\<^sub>b\<^sub>a la> 
  load_uint32 a n
   <\<lambda>r. \<up>(r = (Abs_uint32' \<circ> word_rcat_rev \<circ> (map Rep_uint8')) (take 4 (drop n la)) 
  \<and> n+4 \<le> length la) * a \<mapsto>\<^sub>b\<^sub>a la >"
  unfolding load_uint32_def by sep_auto




lemma [sep_heap_rules]: "<a \<mapsto>\<^sub>b\<^sub>a la> 
  load_uint64_of_uintX a n x
   <\<lambda>r. \<up>(r = (Abs_uint64' \<circ> word_rcat_rev \<circ> (map Rep_uint8')) (take x (drop n la)) 
  \<and> (if x > 0 then n+x \<le> length la else True)) * a \<mapsto>\<^sub>b\<^sub>a la >"
  unfolding load_uint64_of_uintX_def by sep_auto

lemma [sep_heap_rules]: "<a \<mapsto>\<^sub>b\<^sub>a la> 
  load_uint64_of_sintX a n x
   <\<lambda>r. \<up>(r = (Abs_uint64' \<circ> word_rcat_rev \<circ> word_list_sign_extend 8 \<circ> map Rep_uint8') 
  (take x (drop n la)) 
  \<and> (if x > 0 then n+x \<le> length la else True)) * a \<mapsto>\<^sub>b\<^sub>a la >"
  unfolding load_uint64_of_sintX_def by sep_auto

lemma [sep_heap_rules]: "<a \<mapsto>\<^sub>b\<^sub>a la> 
  load_uint64_of_uint8 a n
   <\<lambda>r. \<up>(r = (Abs_uint64' \<circ> word_rcat_rev \<circ> map Rep_uint8') (take 1 (drop n la)) 
  \<and> n+1 \<le> length la) * a \<mapsto>\<^sub>b\<^sub>a la >"
  unfolding load_uint64_of_uint8_def by sep_auto

lemma [sep_heap_rules]: "<a \<mapsto>\<^sub>b\<^sub>a la> 
  load_uint64_of_sint8 a n
   <\<lambda>r. \<up>(r = (Abs_uint64' \<circ> word_rcat_rev \<circ> word_list_sign_extend 8 \<circ> map Rep_uint8') 
  (take 1 (drop n la))
  \<and> n+1 \<le> length la) * a \<mapsto>\<^sub>b\<^sub>a la >"
  unfolding load_uint64_of_sint8_def by sep_auto

lemma [sep_heap_rules]: "<a \<mapsto>\<^sub>b\<^sub>a la> 
  load_uint64_of_uint16 a n
   <\<lambda>r. \<up>(r = (Abs_uint64' \<circ> word_rcat_rev \<circ> map Rep_uint8') (take 2 (drop n la)) 
  \<and> n+2 \<le> length la ) * a \<mapsto>\<^sub>b\<^sub>a la >"
  unfolding load_uint64_of_uint16_def by sep_auto

lemma [sep_heap_rules]: "<a \<mapsto>\<^sub>b\<^sub>a la> 
  load_uint64_of_sint16 a n
   <\<lambda>r. \<up>(r = (Abs_uint64' \<circ> word_rcat_rev \<circ> word_list_sign_extend 8 \<circ> map Rep_uint8') 
  (take 2 (drop n la)) 
  \<and> n+2 \<le> length la) * a \<mapsto>\<^sub>b\<^sub>a la >"
  unfolding load_uint64_of_sint16_def by sep_auto

lemma [sep_heap_rules]: "<a \<mapsto>\<^sub>b\<^sub>a la> 
  load_uint64_of_uint32 a n
   <\<lambda>r. \<up>(r = (Abs_uint64' \<circ> word_rcat_rev \<circ> map Rep_uint8') (take 4 (drop n la)) 
  \<and> n+4 \<le> length la ) * a \<mapsto>\<^sub>b\<^sub>a la >"
  unfolding load_uint64_of_uint32_def by sep_auto

lemma [sep_heap_rules]: "<a \<mapsto>\<^sub>b\<^sub>a la> 
  load_uint64_of_sint32 a n
   <\<lambda>r. \<up>(r = (Abs_uint64' \<circ> word_rcat_rev \<circ> word_list_sign_extend 8 \<circ> map Rep_uint8') 
  (take 4 (drop n la)) 
  \<and> n+4 \<le> length la) * a \<mapsto>\<^sub>b\<^sub>a la >"
  unfolding load_uint64_of_sint32_def by sep_auto

lemma [sep_heap_rules]: "<a \<mapsto>\<^sub>b\<^sub>a la> 
  load_uint64 a n
   <\<lambda>r. \<up>(r = (Abs_uint64' \<circ> word_rcat_rev \<circ> (map Rep_uint8')) (take 8 (drop n la)) 
  \<and> n+8 \<le> length la) 
  * a \<mapsto>\<^sub>b\<^sub>a la >"
  unfolding load_uint64_def by sep_auto
end