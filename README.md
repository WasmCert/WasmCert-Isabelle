# WasmCert-Isabelle

A mechanisation of Wasm in Isabelle. BSD-2 licensed - see LICENSE for details and copyright.

An updated version of the mechanisation from "Mechanising and Verifying the WebAssembly Specification" (C. Watt, CPP 2018).

The type soundness statement and proof can be found in [WebAssembly/Wasm_Soundness.thy](./WebAssembly/Wasm_Soundness.thy).

## Building

To build, you first need Isabelle2025-2 which, as of February 2026, together with instalation instructions you can find [here](https://isabelle.in.tum.de/installation.html). If a newer version has been released since, past versions of Isabelle can be found [here](https://isabelle.in.tum.de/download_past.html).

You also need to link a version of Archive of Formal Proofs (AFP) with Isabelle. You may download it the most recent version of AFP [here](https://www.isa-afp.org/download/) but the past versions of AFP (including the ones that should work with Isabelle 2025-2) can be found [here](https://foss.heptapod.net/isa-afp). To link the AFP version with Isabelle, follow the instructions [here](https://www.isa-afp.org/help/).

Once you have Isabelle2025-2 linked with AFP, you may open the theory files in the project using Isabelle, such as the [WebAssembly/Wasm_Soundness.thy](./WebAssembly/Wasm_Soundness.thy) file which will initiate the checking of the WebAssembly type soundness proof.

The extracted OCaml executable definitions can be found in the [WebAssembly/code](./WebAssembly/code) subdirectory. The top-level printing directives for the extracted code are in [WebAssembly/Wasm_Printing.thy](./WebAssembly/Wasm_Printing.thy). A version of the Wasm OCaml reference interpreter, modified to work with our verified extracted definitions, can be found [here](https://github.com/conrad-watt/spec/tree/ac31ea1426925ce7ed8f72eb380542b8a248a6d3/interpreter).
