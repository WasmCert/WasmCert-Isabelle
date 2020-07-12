# WasmCert-Isabelle
A mechanisation of Wasm in Isabelle.

(C) C. Watt 2020 - see LICENSE

An updated version of the mechanisation from "Mechanising and Verifying the WebAssembly Specification" (C. Watt, CPP 2018).

The type soundness statement and proof can be found in WebAssembly/Wasm_Soundness.thy.

TODO: update the executable type checker and interpreter for extraction to OCaml.

# Building

Currently this repository contains only free-standing Isabelle/HOL files, which have been updated for use with Isabelle2020. A build process for the interpreter will be provided once OCaml extraction is re-implemented.
