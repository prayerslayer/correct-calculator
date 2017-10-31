# Correct Calculator

* JS-based calculator (`react`, `styled-components`)
* Math functions written and proven correct in Coq, meaning all the laws of basic calculus hold true (transitivity of addition, neutral/inverse elements etc.)
* Transpiled to JS module via OCaml/Bucklescript

## Why

Because.

## Is this infallible code?

No.

* Coq -> OCaml -> JS, every transpiler would need to be provably correct, which I doubt they are.
* There might be errors in the logic I wrote, even though it's consistent
* Every operation is defined recursively, because the Set of elements is defined by Zero and a Successor function, and backed by recursive code. Maybe there's a flag in a compiler along the way to convert recursions to imperative code, but right now the biggest number I can enter in Chrome is 15549. (But to be fair, you wouldn't write functions of basic calculus on your own in a real project :) It's already in the Coq Stdlib.)
