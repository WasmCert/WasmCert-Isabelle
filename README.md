# WasmCert-Isabelle

A mechanisation of Wasm in Isabelle. BSD-2 licensed - see LICENSE for details and copyright.

An updated version of the mechanisation from "Mechanising and Verifying the WebAssembly Specification" (C. Watt, CPP 2018).

The type soundness statement and proof can be found in WebAssembly/Wasm_Soundness.thy.

## Building

Currently this repository contains only free-standing Isabelle/HOL files, which have been updated for use with Isabelle2024. The extracted OCaml executable definitions can be found in the code subdirectory, but are currently not fully functional. For a working interpreter build, see one of the interpreter branches.
