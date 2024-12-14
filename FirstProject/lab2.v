
Fixpoint plus (k m : nat) : nat :=
match k with
| O => m
| S n => S (plus n m)
end.
Eval compute in (plus (S (S O)) (S (S O))).

Inductive Nat := O : Nat | S : Nat -> Nat.

Definition one := S O.
Definition two := S one.
Definition three := S two.
Definition four := S three.
Definition five := S four.

Fixpoint eq_Nat (n m : Nat) :=
match (n, m) with
| (O, O) => true
| (O, S a) => false
| (S a, O) => false
| (S a, S b) => eq_Nat a b
end. 

Compute eq_Nat O O.
Compute eq_Nat one O.
Compute eq_Nat one one.
Compute eq_Nat one four.
Compute eq_Nat five four.
Compute eq_Nat five five.

Fixpoint add (m n : Nat) : Nat := 
match (m, n) with
|(O, n) => n
|(m, O) => m
|(S a, S b) => S(S(add a b))
end.

Compute add one one.
Compute add one five.
Compute add five one.
Compute add five O.
Compute add O five.

Fixpoint max (m n : Nat) : Nat := 
match (m, n) with
|(O, n) => n
|(m, O) => m
|(S a, S b) => S(max a b)
end.

Compute max one two.
Compute max O one.
Compute max one O.
Compute max four five.
Compute max five four.



