Require Import String.
(* Check "a". throws 'Error: No interpretation for string "a".' *)
Open Scope string_scope.
Check "a".
Check  "".
Check "abcb".


Inductive AExp :=
| num : nat -> AExp
| var : string -> AExp
| add : AExp -> AExp -> AExp
| mul : AExp -> AExp -> AExp.
Coercion num : nat >-> AExp.
Coercion var : string >-> AExp.

Reserved Notation "A =[ S ]=> N" (at level 60).
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
Notation "A +' B" :=
  (add A B)
    (left associativity, at level 50).
Notation "A *' B" :=
  (mul A B)
    (left associativity, at level 40).

Reserved Notation "A =[ S ]=> N" (at level 60).

Reserved Notation "A =[ S ]=> N" (at level 60).

Reserved Notation "A =[ S ]=> N" (at level 60).


Inductive aeval : AExp -> Env -> nat -> Type :=
| const : forall n sigma, num n =[ sigma ]=> n
| lookup : forall x sigma, var x =[ sigma ]=> sigma x
| bs_add : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n=(i1+i2) ->
    add a1 a2 =[ sigma ]=> n
| bs_mul : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n=i1*i2 ->
    mul a1 a2 =[ sigma ]=> n
where "A =[ S ]=> N" := (aeval A S N).

Definition env3 (x: string) : nat:=
if( string_dec x "x")
   then 10
   else 0.


Example ex1: 2 +' "x" =[ env3 ]=> 12.
Proof.
apply bs_add with (i1 :=2 ) (i2 := 10).
-apply const.
-apply lookup.
-simpl. reflexivity.
Qed.

Example ex2: 2 +' "x" =[ env3 ]=> 12.
Proof.
eapply bs_add.
-apply const.
-apply lookup.
-eauto.
Qed.

Definition env4 (x: string) : nat :=
  if string_dec x "x" then 3
  else if string_dec x "y" then 4
  else 0.
Example ex3: (2 +' "x") *' ("y" +' 5) =[ env4 ]=> 45.
Proof.
eapply bs_mul.
-eapply bs_add.
--apply const.
--apply lookup.
--unfold env4. simpl. trivial.
-eapply bs_add.
--apply lookup.
--apply const.
--unfold env4. simpl. trivial.
-simpl. trivial. 
Qed.

Inductive BExp :=
| btrue : BExp
| bfalse : BExp
| band : BExp -> BExp -> BExp
| bnot : BExp -> BExp
| blt : AExp -> AExp -> BExp.

Notation "B1 &&' B2" :=
  (band B1 B2) (left associativity,
      at level 65).
Notation "!' B" :=
  (bnot B) (at level 62).
Notation "A1 <' A2" :=
  (blt A1 A2)
    (at level 60).
Reserved Notation "B -[ S ]-> B'"  (at level 80).


Inductive beval : BExp -> Env -> bool -> Type :=
| tt : forall sigma, btrue -[ sigma ]-> true
| ff : forall sigma, bfalse -[ sigma ]-> false
| andFalse : forall b1 b2 sigma,
    b1 -[ sigma ]-> false ->
    (b1 &&' b2) -[ sigma ]-> false
| andTrue : forall b1 b2 sigma b,
    b1 -[ sigma ]-> true ->
    b2 -[ sigma ]-> b ->
    (b1 &&' b2) -[ sigma ]-> b
| notFalse : forall b sigma,
    b -[ sigma ]-> false ->
    !' b -[ sigma ]-> true
| notTrue : forall b sigma,
    b -[ sigma ]-> true ->
    !' b -[ sigma ]-> false
| blt1 : forall a1 a2 i1 i2 sigma b,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    b=Nat.ltb i1 i2 ->
    a1 <' a2 -[ sigma ]-> b
where "B -[ S ]-> B'" := (beval B S B').

Inductive Stmt :=
| assign : string -> AExp -> Stmt
| ite : BExp -> Stmt -> Stmt -> Stmt
| while : BExp -> Stmt -> Stmt
| skip : Stmt
| seq : Stmt -> Stmt -> Stmt.

Notation "X ::= A" := (assign X A)
                        (at level 90).
Notation "S1 ; S2" := (seq S1 S2)
                        (at level 98).

Reserved Notation "S ~[ E ]~> E'" (at level 99).


Inductive eval : Stmt -> Env -> Env -> Type :=
| bs_skip : forall sigma, 
    skip ~[ sigma ]~> sigma
| bs_assign : forall var a sigma i sigma',
    a =[ sigma ]=> i ->
   sigma' = update sigma var i ->
    (assign var a) ~[ sigma ]~> sigma'
|bs_seq : forall s1 s2  sigma sigma1 sigma2,
s1 ~[sigma]~> sigma1 ->
s2 ~[sigma1]~> sigma2 ->
(s1 ; s2) ~[sigma]~> sigma2
|bs_ite_f : forall b s1 s2 sigma2 sigma,
s2 ~[sigma2]~> sigma ->
b -[sigma2]-> false ->
ite b s1 s2 ~[sigma2]~> sigma
| bs_ite_t : forall b s1 s2 sigma sigma',
b -[sigma]-> true ->
s1 ~[sigma]~> sigma' ->
(ite b s1 s2) ~[sigma]~> sigma'
|bs_while_f : forall b s sigma,
b -[sigma]-> false ->
while b s ~[sigma]~> sigma
|bs_while_t : forall b s sigma sigma',
b -[sigma]-> true ->
(s ; while b s) ~[sigma]~> sigma' ->
(while b s) ~[ sigma ]~> sigma'
where "S ~[ E ]~> E'" := (eval S E E').


Create HintDb mydb.
Hint Constructors aeval : mydb.
Hint Constructors beval : mydb.
Hint Constructors eval : mydb.
Hint Unfold update : mydb.
Example ex3':
  ("i" ::= 0 ; 
   while ("i" <' 1) ("i" ::= "i" +' 1))
  ~[ env0 ]~>
  update (update env0 "i" 0) "i" 1.
Proof.
eauto 10 with mydb.
Qed.


Fixpoint aeval_fun (a : AExp) (sigma : Env) : nat :=
match a with
|var x => (sigma x)
|num n => n
|add a1 a2 => (aeval_fun a1 sigma) + (aeval_fun a2 sigma)
|mul a1 a2 => (aeval_fun a1 sigma) * (aeval_fun a2 sigma)
end.


Lemma equiv :
forall aexp sigma n, 
n= aeval_fun aexp sigma -> aexp =[sigma]=> n.
Proof.
induction aexp.
-intros sigma n0. simpl. intro H1. rewrite H1. apply const.
-intros sigma n0. simpl. intro H2. rewrite H2. apply lookup.
-simpl. intros sigma n H. eapply bs_add. 
-- apply IHaexp1. trivial.
-- apply IHaexp2. trivial.
--apply H.
-simpl. intros sigma n H1. eapply bs_mul.
-- apply IHaexp1. trivial.
-- apply IHaexp2. trivial.
--apply H1.
Qed.

Lemma equiv' :
forall aexp sigma n,
aexp =[sigma]=> n ->
n= aeval_fun aexp sigma.
Proof.
induction aexp.
-intros sigma n0. simpl. intro H1. inversion H1. reflexivity.
-intros sigma n. simpl. intro H2. inversion H2. reflexivity.
-intros sigma m. intro H. simpl. eapply bs_add in H.


