section {* WebAssembly Core AST *}

theory Wasm_Ast imports Main "HOL-Word.Word" begin

type_synonym \<comment> \<open>immediate\<close>
  i = nat
type_synonym \<comment> \<open>static offset\<close>
  off = nat
type_synonym \<comment> \<open>alignment exponent\<close>
  a = nat

\<comment> \<open>primitive types\<close>
typedef i32 = "UNIV :: (32 word) set" ..
typedecl i64
typedecl f32
typedecl f64

setup_lifting type_definition_i32
declare Quotient_i32[transfer_rule]

\<comment> \<open>memory\<close>
type_synonym byte = "8 word"

type_synonym bytes = "byte list"

definition bytes_takefill :: "byte \<Rightarrow> nat \<Rightarrow> bytes \<Rightarrow> bytes" where
  "bytes_takefill = (\<lambda>(a::8 word) n as. takefill a n as)"

definition bytes_replicate :: "nat \<Rightarrow> byte \<Rightarrow> bytes" where
  "bytes_replicate = (\<lambda>n (b::8 word). replicate n b)"

definition msbyte :: "bytes \<Rightarrow> byte" where
  "msbyte bs = last (bs)"

record limit_t =
  l_min :: nat
  l_max :: "nat option"

free_constructors case_limit_t_ext for limit_t_ext
  using limit_t.cases_scheme
  by blast+

type_synonym tab_t = \<comment> \<open>table type\<close>
  "limit_t"

type_synonym mem_t = \<comment> \<open>memory type\<close>
  "limit_t"

definition Ki64 :: "nat" where
  "Ki64 = 65536"

(* data, max? *)
typedef mem = "UNIV :: ((byte list) \<times> nat option) set" ..
setup_lifting type_definition_mem
declare Quotient_mem[transfer_rule]

lift_definition mem_mk :: "limit_t \<Rightarrow> mem" is "(\<lambda>lim. ((bytes_replicate ((l_min lim) * Ki64) 0), l_max lim))" .

lift_definition byte_at :: "mem \<Rightarrow> nat \<Rightarrow> byte" is "(\<lambda>(m,max) n. m!n)::((byte list) \<times> nat option) \<Rightarrow> nat \<Rightarrow> byte" .
lift_definition mem_length :: "mem \<Rightarrow> nat" is "(\<lambda>(m,max). length m)" .
lift_definition mem_max :: "mem \<Rightarrow> nat option" is "(\<lambda>(m,max). max)" .

lift_definition read_bytes :: "mem \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bytes" is "(\<lambda>(m,max) n l. (take l (drop n m))::(byte list))" .
lift_definition write_bytes :: "mem \<Rightarrow> nat \<Rightarrow> bytes \<Rightarrow> mem" is "(\<lambda>(m,max) n bs. (((take n m) @ bs @ (drop (n + length bs) m)),max)::(byte list \<times> nat option))" .
lift_definition mem_append :: "mem \<Rightarrow> bytes \<Rightarrow> mem" is "(\<lambda>(m,max) bs. (append m bs, max)::(byte list \<times> nat option))" .

lemma take_drop_map:
  assumes "ind+n \<le> length bs"
  shows "(take n (drop ind bs)) = (map ((!) bs) [ind..<ind + n])"
proof -
  have "(drop ind bs) = (map ((!) bs) [ind..<length bs])"
    using drop_map map_nth
    by (metis add.commute add.right_neutral drop_upt)
  thus ?thesis
    by (simp add: assms(1) take_map)
qed

lemma read_bytes_map:
  assumes "ind+n \<le> mem_length m"
  shows "read_bytes m ind n = (map (\<lambda>k. byte_at m k) [ind..<ind+n])"
  using assms
  unfolding read_bytes_def byte_at_def mem_length_def
  by (simp add: take_drop_map split: prod.splits)

\<comment> \<open>host\<close>
typedecl host
typedecl host_state

datatype \<comment> \<open>value types\<close>
  t = T_i32 | T_i64 | T_f32 | T_f64

datatype \<comment> \<open>packed types\<close>
  tp = Tp_i8 | Tp_i16 | Tp_i32

datatype \<comment> \<open>mutability\<close>
  mut = T_immut | T_mut

record tg = \<comment> \<open>global types\<close>
  tg_mut :: mut
  tg_t :: t

free_constructors case_tg_ext for tg_ext
  using tg.cases_scheme
  by blast+

datatype \<comment> \<open>function types\<close>
  tf = Tf "t list" "t list" ("_ '_> _" 60)

(* TYPING *)
record t_context =
  types_t :: "tf list"
  func_t :: "tf list"
  global :: "tg list"
  table :: "tab_t list"
  memory :: "mem_t list"
  local :: "t list"
  label :: "(t list) list"
  return :: "(t list) option"

datatype
  sx = S | U

datatype
  unop_i = Clz | Ctz | Popcnt

datatype
  unop_f = Neg | Abs | Ceil | Floor | Trunc | Nearest | Sqrt

datatype
  unop = Unop_i unop_i | Unop_f unop_f

datatype
  binop_i = Add | Sub | Mul | Div sx | Rem sx | And | Or | Xor | Shl | Shr sx | Rotl | Rotr

datatype
  binop_f = Addf | Subf | Mulf | Divf | Min | Max | Copysign

datatype
  binop = Binop_i binop_i | Binop_f binop_f
  
datatype
  testop = Eqz
  
datatype
  relop_i = Eq | Ne | Lt sx | Gt sx | Le sx | Ge sx
  
datatype
  relop_f = Eqf | Nef | Ltf | Gtf | Lef | Gef

datatype
  relop = Relop_i relop_i | Relop_f relop_f

  
datatype
  cvtop = Convert | Reinterpret

datatype \<comment> \<open>values\<close>
  v =
    ConstInt32 i32
    | ConstInt64 i64
    | ConstFloat32 f32
    | ConstFloat64 f64

datatype \<comment> \<open>basic instructions\<close>
  b_e =
    Unreachable
    | Nop
    | Drop
    | Select
    | Block tf "b_e list"
    | Loop tf "b_e list"
    | If tf "b_e list" "b_e list"
    | Br i
    | Br_if i
    | Br_table "i list" i
    | Return
    | Call i
    | Call_indirect i
    | Get_local i
    | Set_local i
    | Tee_local i
    | Get_global i
    | Set_global i
    | Load t "(tp \<times> sx) option" a off
    | Store t "tp option" a off
    | Current_memory
    | Grow_memory
    | EConst v ("C _" 60)
    | Unop t unop
    | Binop t binop
    | Testop t testop
    | Relop t relop
    | Cvtop t cvtop t "sx option"

record inst = \<comment> \<open>instances\<close>
  types :: "tf list"
  funcs :: "i list"
  tabs :: "i list"
  mems :: "i list"
  globs :: "i list"

datatype cl = \<comment> \<open>function closures\<close>
  Func_native inst tf "t list" "b_e list"
| Func_host tf host

type_synonym tabinst = "(i option) list \<times> nat option"

abbreviation "tab_size (t::tabinst) \<equiv> length (fst t)"
abbreviation "tab_max (t::tabinst) \<equiv> snd t"

record global =
  g_mut :: mut
  g_val :: v

record s = \<comment> \<open>store\<close>
  funcs :: "cl list"
  tabs :: "tabinst list"
  mems :: "mem list"
  globs :: "global list"

record f = \<comment> \<open>frame\<close>
  f_locs :: "v list"
  f_inst :: inst

datatype e = \<comment> \<open>administrative instruction\<close>
  Basic b_e ("$_" 60)
  | Trap
  | Invoke cl
  | Label nat "e list" "e list"
  | Local nat f "e list"

datatype Lholed =
    \<comment> \<open>L0 = v* [<hole>] e*\<close>
    LBase "e list" "e list"
    \<comment> \<open>L(i+1) = v* (label n {e* } Li) e*\<close>
    | LRec "e list" nat "e list" Lholed "e list"

end
