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
* Some Lemmas I know to be true, but couldn't yet convince Coq (like `∀ x : nat, x > 0 -> x / x = 1`). So yeah, that happens too.
* Every number has a unary representation (ie. 2 = `S(S(0))`), because I extracted Coq's inductive `nat` to OCaml's `0` and `Pervasives.succ`. Right now the biggest number I can enter in Chrome is 15549, with 15550 I get a stack overflow :upside_down_face:

## Todo, possibly, if ever

* Use more efficient number type
* Negative numbers
* Advanced operators like square root, power...
