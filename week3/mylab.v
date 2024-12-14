Fixpoint le_Nat (m n : nat) : bool :=
match m, n with
| O, n => true
| S m', O => false
| S m', S n' => le_Nat m' n'
end.

Definition one := S O.
Definition two := S one.
Definition three := S two.
Definition four := S three.
Definition five := S four.

Compute le_Nat O O. (* true *)
Compute le_Nat O one. (* true *)
Compute le_Nat one O. (* false *)
Compute le_Nat one one. (* true *)
Compute le_Nat one five. (* true *)
Compute le_Nat five one. (* false *)
Compute le_Nat five four. (* false *)
Compute le_Nat five five. (* true *)


Lemma le_then_O :
  forall m,
    le_Nat m O = true -> m = O.
Proof.
intros n.
intros H.
destruct n as [|k'].
-reflexivity.
-simpl; inversion H.
Qed.

Lemma le_refl:
  forall x,
    le_Nat x x = true.
Proof.
intro x.
induction x.
-simpl. reflexivity.
-simpl. rewrite IHx. reflexivity.
Qed.

Lemma le_Trans :
  forall m n p,
    le_Nat m n = true ->
    le_Nat n p = true ->
    le_Nat m p = true.
Proof.
induction m.
intros n p.
intro H0.
-simpl in H0. reflexivity.
-induction n. 
+intro p. intro IHn. inversion IHn.
+intro p. intro H1.  induction p.
--intro H2.  inversion H2.
--intro H2. simpl. simpl in H1. simpl in H2. apply IHm with (n:=n).
---exact H1.
---exact H2.
Qed.
