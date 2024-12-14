Inductive List :=
|Nil : List
|Cons : nat->List->List.

Fixpoint Last_Element (list : List) : nat :=
match list with
| Nil => O
| Cons n Nil => n
| Cons n l' => Last_Element l'
end.

Compute Last_Element ( Cons (S(S(S(O)))) (Cons (S(S(O))) Nil)).

Fixpoint length(l : List) :=
match l with
| Nil => O
| Cons _ l' => S (length l')
end.

Fixpoint append(l1 l2 : List) :=
match l1 with
| Nil => l2
| Cons x l1' => Cons x (append l1' l2)
end.

Lemma append_len:
forall l1 l2,
plus (length l1) (length l2) = length (append l1 l2).
induction l1.
-simpl. trivial.
-simpl. intro l2. rewrite IHl1. reflexivity.
Qed.

Inductive ListT (T: Type) : Type :=
| NilT: ListT T
| ConsT: T -> ListT T-> ListT T.

Definition ListNat:= ListT nat.
Definition ListBool:= ListT bool.

Check NilT nat.
Check NilT bool.

Fixpoint CheckLength (T: Type) ( l : ListT Type) : nat :=
match l with
|NilT _ => O
|ConsT _ _ l' => (S O) + CheckLength T l'
end.

Lemma not_so_simple_impl :
forall m n, m = 0 -> n = 0 -> n + m = 0.
Proof.
intros m n Hm Hn.
rewrite Hn.
rewrite Hm.
simpl.
reflexivity.
Qed.
