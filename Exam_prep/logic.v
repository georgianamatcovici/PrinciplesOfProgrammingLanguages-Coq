Lemma not_so_simple_impl :
forall m n, m = 0 -> n = 0 -> n + m = 0.
Proof.
intros m n Hm Hn.
rewrite Hn.
rewrite Hm.
simpl.
reflexivity.
Qed.

Lemma simple_conjunction :
2 + 3 = 5 /\ 5 + 5 = 10.
Proof.
split.
- simpl. reflexivity.
- simpl. reflexivity.
Qed.

Lemma implication_and_conjunction:
forall n, n = 0 -> n + 3 = 3 /\ n + 5 = 5.
Proof.
intros n Hn.
split; rewrite Hn; simpl; reflexivity.
Qed.

Lemma conjunction_as_hypothesis:
forall m n, n = 0 /\ m = 0 -> n + 3 = 3.
intros m n.
intros [H2 H1].
rewrite H2.
simpl. reflexivity.
Qed.

Lemma simple_disjunction:
2 + 3 = 5 \/ 5 + 5 = 10.
Proof.
right.
simpl.
reflexivity.
Qed.

Lemma disjunction_as_hypothesis:
forall n, n = 0 \/ 5 + 5 = 11 -> n + 3 = 3.
Proof.
intros n Hn.
destruct Hn as [Hn|Hn].
-rewrite Hn. simpl. reflexivity.
-inversion Hn.
Qed.

Lemma simple_negation:
forall (x : nat), ~( x <> x) .
intro x.
unfold not.
intro H. apply H.
reflexivity.
Qed.

Lemma exists_zero:
exists (n : nat), n = 0.
Proof.
exists 0.
reflexivity.
Qed.

Lemma exists_as_hypothesis:
forall m, (exists n, m = 2 + n) -> (exists n', m = 1 + n').
Proof.
intros m [n Hmn].

exists (1+n).
rewrite Hmn.
simpl. reflexivity.
Qed.

Theorem ex_falso:
forall P, False->P.
intros P H. inversion H.
Qed.

Theorem and_elim_1:
forall (A B : Prop), A /\ B ->A.
Proof.
intros A B H.
destruct H as [H1 H2].
apply H1.
Qed.


Theorem and_elim_2:
forall (A B : Prop), A /\ B ->B.
Proof.
intros A B H.
destruct H as [H1 H2].
apply H2.
Qed.

Theorem and_intro:
forall (A B : Prop), A -> B -> (A /\ B).
Proof.
intros A B H1 H2.
split.
- apply H1.
- apply H2.

Qed.


Theorem or_elim:
forall (A B C : Prop), (A -> C) -> (B -> C) -> (A \/ B) -> C.
Proof.
intros A B C.
intros H1 H2.
intros [H | H].
- apply H1. apply H.
- apply H2. apply H.

Qed.

Theorem or_intro_1:
forall (A B : Prop), A -> (A \/ B). 
Proof.
left.
apply H.
Qed.

Theorem not_not :
forall (P : Prop), P -> ~~P.
Proof.
intro P.
unfold not. intros H1 H2.
 apply H2. apply H1.
Qed.

Lemma exists_positive:
exists (n : nat), n+1=2.
Proof.
exists 1.
simpl. reflexivity.
Qed.


Lemma exists_correct :
  forall m, (exists n, m = 4 + n) -> (exists n', m = 2 + n').
Proof.
intros m [n Hn].
exists (2+n).
rewrite Hn.
simpl. trivial.
Qed.



