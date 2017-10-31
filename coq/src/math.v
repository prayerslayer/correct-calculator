(* ADDITION *)

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



(* MULTIPLICATION *)

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


(* SUBTRACTION *)

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

(* DIVISION *)

Fixpoint equal (a b : nat) : bool :=
  match a, b with
  | O, O => true
  | (S n), (S m) => (equal n m)
  | _, _ => false
  end.

Lemma equal_reflexivity (x : nat) : (equal x x) = true.
Proof.
induction x.

simpl.
reflexivity.

simpl.
rewrite -> IHx.
reflexivity.
Qed.

Proposition equal_correct_true (x y : nat) : x = y -> (equal x y) = true.
Proof.
intros.
induction x, y.


simpl.
trivial.


simpl.
discriminate.

simpl.
discriminate.


rewrite -> H.
simpl.
apply equal_reflexivity.
Qed.


(* TODO this swallows the remainder which could be used for modulo *)
Fixpoint div (a b : nat) : nat :=
  let fix _div (x y i j : nat) : nat :=
     match x with
     | O => i
     | (S n) => match y with
                | O => x
                | _ => if (equal j y) then (_div n b (S i) 1) else (_div n b i (S j))
                end
     end
   in _div a b 0 1.


Extraction Language Ocaml.
Extract Inductive nat => int [ "0" "Pervasives.succ" ]
 "(fun fO fS n -> if n=0 then fO () else fS (n-1))".
Extraction "/Users/npiccolotto/Projects/prayerslayer/calc/coq/dist/math" div add mult sub.
