Inductive nat := O : nat | S : nat -> nat.

Definition one := S O.
Definition two := S one.
Definition three := S two.
Definition four := S three.
Definition five := S four.

Fixpoint eq_Nat (n m : nat) :=
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
Fixpoint add (m n : nat) : nat :=
  match m with
  | O => n
  | S m' => S (add m' n)
  end.
Compute add one one.
Compute add one five.
Compute add five one.
Compute add five O.
Compute add O five.

Fixpoint max (m n : nat) : nat :=
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


(*Ex 1*)
Fixpoint le_Nat(m n :nat) : bool :=
match m with
|O => true
|S m' => match n with
        | O => false
        | S n' => le_Nat m' n'
        end
end.


Compute le_Nat O O. (* true *)
Compute le_Nat O one. (* true *)
Compute le_Nat one O. (* false *)
Compute le_Nat one one. (* true *)
Compute le_Nat one five. (* true *)
Compute le_Nat five one. (* false *)
Compute le_Nat five four. (* false *)
Compute le_Nat five five. (* true *)

(*Ex 2*)
Lemma le_then_O :
  forall m,
    le_Nat m O = true -> m = O.
Proof.
intros n.
intros H0.
induction n.
-trivial.
-simpl in H0. inversion H0.
Qed.


(*Ex 3*)

Lemma le_refl:
  forall x,
    le_Nat x x = true.
Proof.
intros n.
induction n.
-simpl. trivial.
-simpl. rewrite IHn. trivial.
Qed.

Lemma le_Trans:
forall (m n p : nat),
le_Nat m n=true ->
le_Nat n p= true ->
le_Nat m p=true.
Proof.

induction m.
-simpl. reflexivity.
-intros n p H1 H2.
 simpl.
 destruct p.
 + simpl in *.
   destruct n.
   assumption.
   simpl in H2.
   assumption.
 + simpl in H1.
   destruct n.
   ++ inversion H1.
   ++ simpl in H2.
     apply IHm with (n:=n).
     exact H1.
     exact H2.
Qed.

(*Ex 4*)

Lemma le_x_add_y:
forall (x y : nat),
le_Nat x (add x y)=true.
induction x.
-simpl. reflexivity.
-simpl. trivial.
Qed.

(*Ex 5*)

Lemma add_n_O_is_n:
  forall n,
    add n O = n.
Proof.
  induction n.
  - simpl.
    reflexivity.
  - simpl.
    rewrite IHn.
    reflexivity.
Qed.

Lemma le_x_y_z:
forall (x y z :nat),
le_Nat x y = true -> le_Nat x (add y z)=true.
induction x.
- intros y z H0. simpl. trivial.
- induction y.
  +intros z H0. inversion H0.
  + induction z.
    -- intros H0. simpl. rewrite add_n_O_is_n. simpl. simpl in H0. rewrite H0. trivial.
    -- simpl. apply IHx.
Qed.



