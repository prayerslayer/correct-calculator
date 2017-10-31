# Correct Calculator

* JS-based calculator (`react`, `styled-components`)
* Math functions written and proven correct in Coq, meaning all the laws of basic calculus hold true (transitivity of addition, neutral/inverse elements etc.)
* Transpiled to CommonJS via OCaml/Bucklescript

## Why

Because.

## Is this infallible code?

No.

* Coq -> OCaml -> JS, every transpiler would need to be provably correct, which I doubt they are.
* There might be errors in the logic I wrote, even though it's consistent
* Every number has a unary representation, because I extracted Coq's inductive `nat` to OCaml's `0` and `Pervasives.succ`. Right now the biggest number I can enter in Chrome is 15549, with `S(15549)` I get a stack overflow :upside_down_face:

## Todo, possibly, if ever

* Use more efficient number type
* Negative numbers
* Advanced operators like square root, power...
