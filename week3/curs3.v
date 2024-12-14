Inductive nat :=
|O:nat
|S:nat->nat.

Fixpoint le_Nat(m n :nat) : bool :=
match m with
|O => true
|S m' => match n with
        | O => false
        | S n' => le_Nat m' n'
        end
end.

Compute le_Nat O (S O).

Lemma le_Trans:
forall (m n p : nat),
le_Nat m n=true ->
le_Nat n p= true ->
le_Nat m p=true.
Proof.
(*intros m n p H1 H2*)
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






(*Inductive ListNat :=
| Nil : ListNat
| Cons : nat -> ListNat -> ListNat.

Compute Nil.
Compute (Cons(S O) Nil).
Compute(Cons O (Cons (S O) Nil)).
*)
(*Inductive ListBool :=
| Nil' : ListNat
| Cons : nat -> ListNat -> ListNat.
*)
(*Polymorphism*)
Inductive List (T: Type) :=
|Nil : List T
|Cons : T -> List T -> List T.


Check Nil.
Check Cons.
Definition ListNat := List nat.
Compute (Cons nat O
          (Cons nat (S O) (Nil nat))).

Arguments Nil {T}.
Arguments Cons {T}.

Compute (Cons O 
          (Cons (S O) Nil)).



Fixpoint length {T: Type} (l : List T) : nat :=
match l with 
| Nil => O
| Cons e l' => S (length l')
end.


(*Higher-order functions=functii care pot primi ca argumente alte functii *)
Fixpoint filter
{T: Type}
(l : List T)
(f : T -> bool) :=
match l with
|Nil => Nil
|Cons x l' => if (f x)
              then Cons x (filter l' f)
              else (filter l' f)
end.


Definition myList :=
(Cons 2 (Cons 7 ( Cons 20 ( Cons 14 ( Cons 12 Nil))))).
Check myList.

Check nat.



(*Definition is_digit (n: nat) : bool :=
if nat. leb n 9
then true
else false.*)

Definition compose (A B C : Type)
(f: B -> C)
(g: A -> B) : A -> C :=
fun x => f (g x).

(*Compute (compose (fun x => x+5)( fun x => x*2) (fun x => x+5)) 10.*)

Lemma conj_vs_impl:
forall P Q R,
(P -> Q -> R) <->
(P /\ Q -> R).
Proof.
split.
- intros H ( H1 & H2).
  apply H; assumption.
- intros H H1 H2.
  apply H.
  split; assumption.
Qed.


Check 10=10.

Compute 10=10.

Goal 10=10.
reflexivity.
Qed.

Goal 10=11.
Abort.


(*Lema simple_disj:
2+5 = 7 \/ 2+5=8.
Proof
left.
simpl.
trivial.
Qed.*)


Lemma disj_as_hyp:
forall n,
n=0 \/ 5+5=11 ->
n+3=3.
Proof.
intros. 
destruct H as [H | H].
-subst n. trivial.
-simpl in H. inversion H.
Qed.


Lemma interesting_neg:
forall (x:nat),
~(x<>x).
Proof.
intros x.
unfold not.
intros.
apply H.
reflexivity.
Qed.

Lemma exists_:
exists n, n=0.
Proof.
exists 0. (*witness*)
reflexivity.
Qed.

Lemma exists_ip:
forall m,
(exists n, m=2+n) ->
(exists n', m=1+n').
Proof.
intros m [n0 P].
(*destruct H as [n0 P]*)
exists (1+n0).
subst m.
simpl.
trivial.
Qed.


