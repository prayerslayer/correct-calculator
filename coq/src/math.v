Section Addition.

Fixpoint add (a b : nat) : nat :=
  match a with
  | O => b
  | (S n) => (S (add n b))
  end.


Lemma addition_of_identity_element : forall (x : nat), (add x O) = x.
Proof.
induction x.

trivial.

simpl. rewrite -> IHx.
trivial.
Qed.

Lemma inc: forall (x: nat), (add x 1) = (S x).
Proof.
induction x.

trivial.

simpl.
rewrite IHx.
reflexivity.
Qed.

Lemma add_is_invertible : forall (x y : nat), (S (add x y)) = (add x (S y)).
Proof.
induction y.

rewrite addition_of_identity_element.
rewrite inc.
reflexivity.

trivial.
Qed.


Theorem addition_transitivity : forall (x y z : nat), (add x (add y z)) = (add (add x y) z).
Proof.
intros x y z.
induction x.

simpl.
reflexivity.

simpl.
rewrite IHx.
reflexivity.
Qed.

Theorem addition_commutativity : forall (x y : nat), (add x y) = (add y x).
Proof.
induction x.

simpl.
symmetry.
apply addition_of_identity_element.

induction y.

simpl.
rewrite addition_of_identity_element.
trivial.

simpl.
rewrite <- IHy.
rewrite (add_is_invertible (S x)).
simpl.
reflexivity.

Qed.

End Addition.


Section Multiplication.

Fixpoint mult (a b : nat) : nat :=
  match a with
  | O => O
  | (S n) => (add (mult n b) b)
  end.

Lemma mult_of_inverse_element : forall (x : nat), (mult x O) = O.
Proof.
induction x.

trivial.

simpl.
rewrite IHx.
trivial.
Qed.

Lemma mult_of_neutral_element : forall (x : nat), (mult x 1) = x.
Proof.
induction x.

trivial.

simpl.
rewrite IHx.
rewrite -> inc.
trivial.
Qed.

Theorem mult_commutativity: forall (x y : nat), (mult x y) = (mult y x).
Proof.
induction x.

(* Zero x *)
induction y.
  (* Zero y *)
  reflexivity.

  (* S y *)
  simpl.
  rewrite mult_of_inverse_element.
  trivial.

(* S x *)
induction y.
  (* Zero y *)
  simpl.
  rewrite mult_of_inverse_element.
  trivial.

  (* S y *)
  simpl.
  rewrite <- IHy.
  rewrite IHx.
  simpl.
  rewrite (IHx y).
  (* bring successors to front *)
  rewrite (addition_commutativity (add (mult y x) x)).
  rewrite (addition_commutativity (add (mult y x) y)).
  simpl.
  (* i choose you, transitivity! *)
  rewrite (addition_transitivity y).
  rewrite (addition_commutativity x).
  rewrite (addition_commutativity y).
  reflexivity.
Qed.

End Multiplication.


Section Subtraction.

Fixpoint sub (a b : nat) : nat :=
  match a with
  | O => O
  | (S n) => match b with
             | O => a
             | (S m) => (sub n m)
             end
  end.

Lemma sub_of_neutral_element: forall (x: nat), (sub x O) = x.
Proof.

induction x.

trivial.
trivial.
Qed.

Lemma sub_of_inverse_element: forall (x: nat), (sub x x) = O.
Proof.

induction x.

trivial.

simpl.
rewrite -> IHx.
reflexivity.
Qed.

End Subtraction.

Section Division.

Fixpoint div_remainder (a b i j: nat) : (prod nat nat) :=
   match a with
   | O => (i, j)
   | (S n) => match j with
              | O => (div_remainder n b (S i) b)
              | (S m) => (div_remainder n b i m)
              end
   end.

Definition div (a b : nat) :=
  match b with
  | O => O
  | (S n) => fst (div_remainder a n 0 n)
  end.

Definition mod (a b : nat) :=
  match b with
  | O => O
  | (S n) => (sub n (snd (div_remainder a n 0 n)))
  end.

Lemma div_of_inverse_element: forall (x : nat), (div x 0) = 0.
Proof.
intros.
simpl.
reflexivity.
Qed.

(* TODO division by neutral element 1 *)
End Division.


Extraction Language Ocaml.
Extract Inductive nat => int [ "0" "Pervasives.succ" ]
 "(fun fO fS n -> if n=0 then fO () else fS (n-1))".
Extraction "/Users/npiccolotto/Projects/prayerslayer/calc/coq/dist/math" div mod add mult sub.
