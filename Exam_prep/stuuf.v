Inductive List (T : Type) : Type :=
| Nil: List T 
| Cons : T->List T -> List T.


 Check Nil bool.


Fixpoint repeat (T: Type) (e: T) (n: nat) : List T :=
match n with
| O => Nil _
| S n' => Cons _ e (repeat T e n')
end.

Compute repeat bool true 7.

Arguments Nil {T}.
Arguments Cons {T}.


Fixpoint length {T : Type} (l : List T) :=
match l with
| Nil => O
| Cons _ l' => S(length l')
end.

Fixpoint concat {T : Type} (l1 l2 : List T) : List T :=
match l1 with
| Nil => l2
| Cons e l' => Cons e (concat l' l2)
end.

Fixpoint filter {T:Type} (f: T-> bool) (l: List T) : List T :=
match l with
|Nil => Nil
|Cons x xs => if (f x)
              then Cons x (filter f xs)
              else filter f xs
end.

Check filter.


Require Import Nat.

Definition num_list := Cons 2 ( Cons 15 ( Cons 7 ( Cons 18 Nil))).

Definition has_one_digit (n: nat) := leb n 9.


Compute has_one_digit 10.

Compute has_one_digit 7.
Compute has_one_digit 89.


Definition mult (n: nat) := n*2.
Fixpoint filter' {T : Type} (f:T -> nat) (l: List T) :=
match l with
|Nil => Nil
|Cons e l' => Cons (f e) (filter' f l')
end.


Compute filter' (fun x=> 2*x) num_list.

Definition id {A : Type} { B: Type} ( f: A -> B ) := f.
Check id.


Compute has_one_digit 1.
Compute id has_one_digit 1.

Check filter.
Check (id filter).

Definition compose {A : Type} {B:Type}{C:Type} (f:B->C)(g:A->B) :=
fun x => f (g x).

Check compose (fun x : bool => if x then Nil else (Cons 1 Nil)) (fun x : nat => leb x 0). 
