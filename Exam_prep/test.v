Print nat.
Require Import String.
Require Import Nat.
(* Check "a". throws 'Error: No interpretation for string "a".' *)
Open Scope string_scope.
Check "a".
Check  "".
Check "abcb".

Inductive LP :=
|prop : string -> LP
|not : LP -> LP
|and : LP -> LP -> LP
|or : LP -> LP -> LP.


Definition p := prop "p".
Definition q := prop "q".
Definition r := prop "r".

Definition example1 := not p.            (* not p *)
Definition example2 := and p q.          (* p /\ q *)
Definition example3 := or p (not r).     (* p \/ not r *)
Definition example4 := and (not p) (or q r).

Check LP_ind.

Definition Env := string ->bool.
Coercion prop : string >-> LP.
Fixpoint eval (form : LP) (tau : Env) : bool :=
match form with 
| prop x => tau x
| not x => negb (eval x tau)
| and x y => andb (eval x tau) (eval y tau)
| or x y => orb (eval x tau) (eval y tau)
end.

Definition tau : Env :=
  fun x =>
    match x with
    | "p" => true
    | "q" => false
    | "r" => true
    | _ => false
    end.

Lemma lema : forall f tau,
eval f tau = eval (not (not f)) tau.
Proof.
induction f.
-intro tau. simpl. destruct (tau s).
-- simpl. reflexivity.
-- simpl. reflexivity.
- intro tau. simpl. destruct (eval f tau); simpl; reflexivity.
- intro tau. simpl. rewrite IHf1. rewrite IHf2. simpl. destruct (eval f1 tau); destruct (eval f2 tau); 
simpl; reflexivity.
-intro tau. simpl. rewrite IHf1. rewrite IHf2. simpl. destruct (eval f1 tau); destruct (eval f2 tau); 
simpl; reflexivity.
Qed.

