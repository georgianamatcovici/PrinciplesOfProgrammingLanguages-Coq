Require Import String.
Open Scope string_scope.

Check "asdasf".

Inductive AExp :=
| num : nat -> AExp
| var : string -> AExp
| add : AExp -> AExp -> AExp
| mul : AExp -> AExp -> AExp.


(* Coercions *)
Coercion num : nat >-> AExp.
Coercion var : string >-> AExp.
Notation "A +' B" :=
  (add A B)
    (left associativity, at level 50).
Notation "A *' B" :=
  (mul A B)
    (left associativity, at level 40).


(* Environment *)
Definition Env := string -> nat.
Definition env0 :=
  fun (x : string) => 0.
Definition update
  (env : Env)
  (x : string)
  (v : nat) : Env :=
  fun y => if x =? y
           then v
           else env y.



(* <AExp, Env> => <nat> *)

Reserved Notation "A -[ S ]-> V"  (at level 60).
Inductive aeval : AExp -> Env -> nat -> Type :=
| lookup : forall x sigma, (var x) -[ sigma ]-> (sigma x)
| ss_add1:
a1-[sigma]-> a1' ->
(a1 +' a2) - [sigma]-> a1'+a2
| ss_add2:
a2-[sigma]-> a2' ->
(a1 +' a2) - [sigma]-> a1 + a2'
| ss_add forall (i1 i2 :nat) sigma, n
n=i1+i2 ->
(i1 +' i2) -[sigma] -> i1+i2
| ss_mul1:
a1-[sigma]-> a1' ->
(a1 *' a2) - [sigma]-> a1'*a2
| ss_mul2:
a2-[sigma]-> a2' ->
(a1 *' a2) - [sigma]-> a1 * a2'
| ss_add forall (i1 i2 :nat) sigma,
(i1 +' i2) -[sigma] -> i1+i2



where "A =[ S ]=> V" := (aeval A S V).


Example e1: "x" +' 2 -[update env0 "x" 10] -> 10 +' 2.
Proof.
apply ss_add1.
apply lookup.
Qed.


Reserved Notation "A -< S >* V"  (at level 60).
Inductive a_clos: AExp -> Env ->AExp ->Type :=
|a_refl : forall a sigma, a- <sigma>* a
| a_tran : forall a1 a2 a3 sigma, 
a1-[ si

Example e1' : "x"+2
-<update env0 "x" 10>*
12.
Proof.
eapply a_tran.
-apply e1.
-eapply a_tran.
+ apply ss_add.
reflexivity.
+ simpl.
apply a_refl.
Qed.

Definition envXY :=
update(update env0 x "10") "y" 11.


Example e2:
"x"+"y" -<envXY>*21.
Proof.
eapply a_tran.
-apply ss_add1.
apply lookup.
-unfold envXY, update.
simpl.
eapply a_tran.
+apply ss_add2.
apply lookup.
+ apply a_tran.
apply ss_add.
reflexivity.
simpl. apply a_refl.

Create 
Hint Constructors 

