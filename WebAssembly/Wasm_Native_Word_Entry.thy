theory Wasm_Native_Word_Entry imports Wasm_Base_Defs "Native_Word.Uint32" "Native_Word.Uint64" begin

lift_definition i32_impl_abs :: "uint32 \<Rightarrow>i32" is "(\<lambda>x. x)" .
lift_definition i64_impl_abs :: "uint64 \<Rightarrow>i64" is "(\<lambda>x. x)" .

lift_definition i32_impl_rep :: "i32 \<Rightarrow>uint32" is "(\<lambda>x. x)" .
lift_definition i64_impl_rep :: "i64 \<Rightarrow>uint64" is "(\<lambda>x. x)" .

end