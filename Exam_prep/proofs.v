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
Fixpoint le_Nat(m n :nat) : bool :=
match m with
|O => true
|S m' => match n with
        | O => false
        | S n' => le_Nat m' n'
        end
end.

Lemma le_then_O :
  forall m,
    le_Nat m O = true -> m = O.
Proof.
intros m H.
destruct m as [|m'].
-reflexivity.
-inversion H.
Qed.

Lemma le_then_O' :
  forall m,
    le_Nat m O = true -> m = O.
Proof.
induction m.
- intro H. reflexivity.
- intro H. inversion H.
Qed.

Lemma le_refl:
  forall x,
    le_Nat x x = true.
induction x.
- simpl. reflexivity.
- simpl. apply IHx.
Qed.



Lemma le_Trans :
  forall m n p,
    le_Nat m n = true ->
    le_Nat n p = true ->
    le_Nat m p = true.
Proof.
induction m.
- induction n.
--- intro p. intros H1 H2. apply H2.
--- induction p.
+ intros H2 H3. inversion H3.
+ simpl. intros H4 H5. reflexivity.
- induction n.
-- intro p. intro H6. inversion H6.
-- induction p.
+ intros H7 H8. inversion H8.
+ simpl. apply IHm.
Qed.

Lemma le_x_add_y:
forall (x y : nat),
le_Nat x (add x y)=true.
induction x.
-simpl. reflexivity.
-simpl. apply IHx.
Qed.

Lemma le_x_y_z:
forall (x y z :nat),
le_Nat x y = true -> le_Nat x (add y z)=true.
induction x.
-intros y z H. simpl. reflexivity.
-induction y.
--intros z H1. inversion H1.
--simpl. apply IHx.
Qed.


Lemma le_x_y_z':
forall (x y  :nat),
le_Nat x y = true -> max x y=y.
Proof.
induction x.
-intros y H. simpl. reflexivity.
-induction y. 
--intro H. inversion H.
--simpl. intro H. rewrite IHx.
+reflexivity.
+apply  H.
Qed.

Qed.

Lemma le_x_y_z'':
forall (x y  :nat),
le_Nat x y = false -> max x y=x.
induction x.
- induction y.
--intro H. simpl. reflexivity.
--intro H1. inversion H1.
-induction y.
-- simpl. intro H2. reflexivity.
--simpl.  intro H5. rewrite IHx.
+reflexivity.
+apply H5.
Qed. 
