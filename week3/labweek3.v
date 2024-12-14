Inductive Nat := O : Nat | S : Nat -> Nat.

Definition one := S O.
Definition two := S one.
Definition three := S two.
Definition four := S three.
Definition five := S four.

Fixpoint eq_Nat (n m : Nat) :=
  match n, m with
  | O, O       => true
  | O, S _     => false
  | S _, O     => false 
  | S n', S m' => eq_Nat n' m'
  end.

Compute eq_Nat O O.
Compute eq_Nat one O.
Compute eq_Nat one one.
Compute eq_Nat one four.
Compute eq_Nat five four.
Compute eq_Nat five five.

Fixpoint add (m n : Nat) : Nat :=
  match m with
  | O => n
  | S m' => S (add m' n)
  end.

Compute add one one.
Compute add one five.
Compute add five one.
Compute add five O.
Compute add O five.

Fixpoint max (m n : Nat) : Nat :=
  match m with
  | O => n
  | S m' => match n with
            | O => m
            | S n' => S (max m' n')
            end
  end.

Compute max one two.
Compute max O one.
Compute max one O.
Compute max four five.
Compute max five four.

(*Exercitiul 1*)
Fixpoint le_Nat (m n : Nat) : bool :=
match m,n with
| O, _ => true
| S _, O =>false
| S m', S n' => le_Nat m' n'
end.

Compute le_Nat O O. (* true *)
Compute le_Nat O one. (* true *)
Compute le_Nat one O. (* false *)
Compute le_Nat one one. (* true *)
Compute le_Nat one five. (* true *)
Compute le_Nat five one. (* false *)
Compute le_Nat five four. (* false *)
Compute le_Nat five five. (* true *)

(*Exercitiul 2*)
Lemma le_then_O :
  forall m,
    le_Nat m O = true -> m = O.
Proof.
intros n.
intros H0.
destruct n as [|n'].
-trivial.
-simpl in H0. inversion H0.
Qed.
(*SAU*)
(*intros n H.
induction n.
-trivial.
-simpl in H.
inversion H.
Qed.
*)

(*Exercitiul 3*)
(*A*)
Lemma le_refl:
  forall x,
    le_Nat x x = true.
Proof.
intros n.
induction n.
-simpl. trivial.
-simpl. rewrite IHn. trivial.
Qed.
 
(*B*)

Lemma le_Trans :
  forall m n p,
    le_Nat m n = true ->
    le_Nat n p = true ->
    le_Nat m p = true.
Proof.
induction m. 
intros.
-simpl. trivial.
- induction n.
-- intros. inversion H.
-- induction p.
---intros. inversion H0.
--- simpl . apply IHm.
Qed. 
(*
induction m.
intros n p.
- simpl. intros H0 H1. trivial.
- induction n. intros p.
-- intros H0 H1. simpl in H0. inversion H0.
-- induction p.
--- simpl. intros H0 H1. inversion H1.
--- simpl. apply IHm.
Qed.
*)

(*Exercitiul 4*)
Lemma le_add :
  forall x y,
    le_Nat x (add x y) = true.
Proof.
intros x y.
induction x .
-simpl. trivial.
-simpl. rewrite IHx. trivial.
Qed.



Lemma add_n_O_is_n_1:
  forall m n, le_Nat m (add n O) = le_Nat m ( add O n).
Proof.
  induction m.
  - simpl. trivial.
  -induction n. 
--simpl. trivial.
-- simpl. apply IHm.
Qed.

(*Exercitiul 5*)
 Lemma le_add_consistent :
  forall m n k,
    le_Nat m n = true ->
    le_Nat m (add n k) = true.
Proof.
induction m.
- intros n k H0. simpl. trivial.
- induction n.
-- intros k H0. inversion H0.
-- induction k.
--- intros H0. simpl. rewrite add_n_O_is_n_1. simpl. simpl in H0. rewrite H0. trivial.
--- simpl. apply IHm.
Qed.
(*lemma 1 2 3 si 4 sunt helper pentru rezolvarea ex 6 si 7*)
Lemma lemma_2 :
forall m n ,
  S m = n -> S ( S m ) = S ( n ) .
Proof.
intros m n H0.
rewrite H0. trivial.
Qed.

Lemma lemma_3 :
forall m n ,
  S ( S m ) = S ( n ) -> S m = n .
Proof.
intros m n H0.
inversion H0.
rewrite H1. trivial.
Qed.
 Lemma lemma_1 :
forall m n,
le_Nat m n = true -> S (max m n) = S n.
Proof.
induction m.
induction n.
- simpl. trivial.
- simpl. trivial.
- induction n.
  --simpl. intros H0. inversion H0.
  --simpl. intros H1. apply lemma_2. apply  IHm. rewrite H1. trivial.
Qed. 
 Lemma lemma_5 :
forall m n,
le_Nat m n = false -> S (max m n) = S m.
Proof.
induction m.
induction n.
- simpl. trivial.
- simpl. intros H0. inversion H0.
- induction n.
  --simpl. trivial.
  --simpl. intros H1. apply lemma_2. apply  IHm. rewrite H1. trivial.
Qed. 


(*Exercitiul 6*)
Lemma le_max_true :
  forall m n,
    le_Nat m n = true ->
    max m n = n.
Proof.
induction m.
-simpl. trivial.
-induction n.
  -- simpl. intros H0. inversion H0.
  -- simpl. apply lemma_1.
Qed.

(*Exercitiul 7*)
Lemma le_max_false :
  forall m n,
    le_Nat m n = false ->
    max m n = m.
Proof.
induction m.
- simpl. intros n H1. inversion H1.
- induction n.
  -- simpl. trivial.
  -- simpl.  apply lemma_5.
Qed.
 


