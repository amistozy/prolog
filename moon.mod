// Learn more about moon.mod configuration:
// https://docs.moonbitlang.com/en/latest/toolchain/moon/module.html
//
// To add a dependency, run this command in your terminal:
//   moon add moonbitlang/x
//
// Or manually declare it in `import`, for example:
// import {
//   "moonbitlang/x@0.4.6",
// }

name = "amistozy/prolog"

version = "0.1.6"

readme = "README.mbt.md"

repository = "https://github.com/amistozy/prolog"

license = "Apache-2.0"

keywords = [ "prolog", "edsl", "logic-programming", "logic", "moonbit" ]

preferred_target = "wasm"

description = "A Prolog EDSL in MoonBit: build terms, clauses and programs as ordinary MoonBit values and run SLD resolution with backtracking. Includes a Prolog syntax parser, DCG rules, dif/2 constraints and a relational standard library, modeled after Scryer Prolog."
