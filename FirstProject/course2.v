Fixpoint plus (k m : nat) : nat :=
match k with
| O => m
| S n => S (plus n m)
end.
Eval compute in (plus (S (S O)) (S (S O))).


(*Proof by simplification*)
Lemma plus_O_m_is_m :
forall m, plus O m = m.
Proof.
(* first, we move m from the quantifier
in the goal to a context of current
assumptions using the 'intro' tactic *)
intros m.
(* the current goal is now provable
using the definition of plus: we
apply the 'simpl' tactic for that*)
simpl.
(* the current goal is just reflexivity *)
reflexivity.
(* Qed checks if the proof is correct *)
Qed.


(*Proof by rewriting*)
Theorem plus_eq:
forall m n, m = n -> plus O m = plus O n.
Proof.
intros.
rewrite <- H.
reflexivity.
Qed.



Theorem plus_c_a:
  forall k,
    plus k (S O) <> O.
Proof.
  intros k.
  unfold not.
  intro H.
  destruct k as [ |k'].
- simpl in H; inversion H.
- simpl in H; inversion H.
Qed.


Check nat_ind.


Lemma plus_n_O_is_n:
  forall n,
    plus n O = n.
Proof.
  induction n.
  - simpl.
    reflexivity.
  - simpl.
    rewrite IHn.
    reflexivity.
Qed.

Theorem plus_comm:
  forall m n,
    plus m n = plus n m.
Proof.
  induction m.
  - intro n.
    rewrite plus_n_O_is_n.
    rewrite plus_O_m_is_m.
    reflexivity.
  - induction n.
    + rewrite plus_n_O_is_n.
      simpl.
      reflexivity.
    + simpl.
      rewrite <- IHn.
      simpl.
      rewrite IHm.
      simpl.
      rewrite IHm.
      reflexivity.
Qed.

