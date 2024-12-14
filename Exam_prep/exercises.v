

Inductive Tree :=
| root : Tree
| left : Tree -> Tree
| right : Tree -> Tree.



Fixpoint CountNodes (t: Tree) : nat :=
match t with
| root => S O
| left r => 1 +  CountNodes r
| right r => 1 + CountNodes r
end.

Print nat.

Fixpoint isEven (n: nat) : bool :=
match n with
| O => true
| S n' => negb( isEven n')
end.

Fixpoint Factorial (n: nat) : nat :=
match n with
|O => 1
| S n' => n*(Factorial n')
end.

Fixpoint LessThan (n1 n2 : nat ) :=
match (n1, n2) with
|(O, O) => false
|(O, S n') => true
|(S n', O) => false
|(S m', S n') => LessThan m' n'
end.


Fixpoint plus (n m : nat) : nat :=
match n with
| O => m
| (S n') => S (plus n' m)
end.



Theorem plus_0_0 : plus O O = O.
Proof.
simpl.
reflexivity.
Qed.

Theorem plus_m_n_is_plus_n_n : forall m n, m=n ->
plus m n= plus n n.
Proof.
intros.
rewrite H. reflexivity.
Qed.


Theorem plus_c_a : forall k, plus k (S O) <> O.
Proof.
intros.
destruct k as [|k'].
- simpl. unfold not. intro H. inversion H.
-unfold not. intro H'. inversion H'.
Qed.

Theorem plus_c_a' : forall k, plus k (S O) <> O.
Proof.
intros.
unfold not.
intro H.
destruct k as [|k'].
- simpl. inversion H.
-inversion H.
Qed.

Theorem n_plus_0_is_0 : forall n, plus n O=n.
induction n.
-simpl. reflexivity.
-simpl. rewrite IHn. reflexivity.
Qed.

Theorem plus_n_Sm_is_S_n_m:
forall n m, plus n (S m)=S(plus n m).
induction n.
-simpl. reflexivity.
-simpl. intro m. rewrite IHn. reflexivity.
Qed.

Theorem plus_exercise_1:
forall n, plus n (plus n O)=plus n n.
Proof.
induction n.
-simpl. trivial.
-simpl. rewrite plus_n_Sm_is_S_n_m. rewrite plus_n_Sm_is_S_n_m.
rewrite IHn. reflexivity.
Qed.
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
Compute le_Nat five five. 

Lemma le_then_0: forall n, le_Nat n O = true -> n=O.
Proof.
destruct n as [|n'].
-intro H. reflexivity.
-intro H'. inversion H'.
Qed.


Lemma le_refl:
  forall x,
    le_Nat x x = true.
Proof.
induction x.
-simpl. reflexivity.
-simpl. apply IHx.
Qed.

Lemma le_Trans :
  forall m n p,
    le_Nat m n = true ->
    le_Nat n p = true ->
    le_Nat m p = true.
Proof.
induction m.
-simpl. trivial.
-induction n.
-- simpl. intro p. intro H'. inversion H'.
--induction p.
---intro H''. intro H1. inversion H1.
---simpl. apply IHm.
Qed.


Lemma le_add :
  forall x y,
    le_Nat x (add x y) = true.
Proof.
induction x.
-simpl. reflexivity.
-simpl. apply IHx.
Qed.

Lemma add_n_O_is_n_1:
  forall m n, le_Nat m (add n O) = le_Nat m ( add O n).
Proof.
induction m.
-simpl. trivial.
-destruct n as [|n'].
--simpl. trivial.
--simpl. apply IHm.
Qed.

Lemma add_n_O_is_n:
  forall n,
    add n O = n.
Proof.
induction n.
-simpl. trivial.
-simpl. rewrite IHn. trivial.
Qed.

Lemma le_x_y_z:
forall (x y z :Nat),
le_Nat x y = true -> le_Nat x (add y z)=true.
Proof.
induction x.
- simpl. trivial.
-induction y.
-- induction z.
---simpl. trivial.
---simpl. intro H'. inversion H'.
--induction z.
---simpl. rewrite add_n_O_is_n_1. simpl. intro H1. apply H1.
---

Inductive List :=
|Nil : List
|Cons : nat->List->List.

Fixpoint Last_Element (list : List) : nat :=
match list with
| Nil => 0
| Cons n Nil => n
| Cons n l' => Last_Element l'
end.

Compute Last_Element ( Cons (S(S(S(O)))) (Cons (S(S(O))) Nil)).

