Require Import String.
Open Scope string_scope.



Inductive Exp :=
| num : nat -> Exp
| var : string -> Exp
| add : Exp -> Exp -> Exp
| sub : Exp -> Exp -> Exp
| div : Exp -> Exp -> Exp.


Coercion num : nat >-> Exp.
Coercion var : string >-> Exp.
Notation "A +' B" :=
  (add A B)
    (left associativity, at level 50).
Notation "A -' B" :=
  (sub A B)
    (left associativity, at level 50).
Notation "A /' B" :=
  (div A B)
    (left associativity, at level 40).

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

(*ex1*)
Reserved Notation "A -[ S ]-> V"  (at level 60).
Inductive aeval_ss : Exp -> Env -> Exp
                     -> Type :=
| lookup : forall x sigma,
    (var x) -[ sigma ]-> (sigma x)
| ss_add1 : forall a1 a1' a2 sigma,
  a1 -[ sigma ]-> a1' ->
  (a1 +' a2) -[ sigma ]-> a1' +' a2
| ss_add2 : forall a1 a2 a2' sigma,
  a2 -[ sigma ]-> a2' ->
  (a1 +' a2) -[ sigma ]-> a1 +' a2'
| ss_add : forall (i1 i2 : nat) sigma n,
    n = i1 + i2 -> 
    (i1 +' i2) -[ sigma ]-> n 
| ss_sub1 : forall a1 a1' a2 sigma,
  a1 -[ sigma ]-> a1' ->
  (a1 -' a2) -[ sigma ]-> a1' -' a2
| ss_sub2 : forall a1 a2 a2' sigma,
  a2 -[ sigma ]-> a2' ->
  (a1 -' a2) -[ sigma ]-> a1 -' a2'
| ss_sub : forall (i1 i2 : nat) sigma n,
  i1>=i2->
  n=i1-i2 ->
  (i1 -' i2) -[ sigma ]-> n
| ss_div1 : forall a1 a1' a2 sigma,
  a1 -[ sigma ]-> a1' ->
  (a1 /' a2) -[ sigma ]-> a1' /' a2
| ss_div2 : forall a1 a2 a2' sigma,
  a2 -[ sigma ]-> a2' ->
  (a1 /' a2) -[ sigma ]-> a1 /' a2'
| ss_div : forall (i1 i2 : nat) sigma n,
  i2 <> 0 ->
  n= Nat.div i1  i2 ->
  (i1 -' i2) -[ sigma ]-> n

where "A -[ S ]-> V" := (aeval_ss A S V).

Definition env2 :=
  fun (x : string) => 10.

Reserved Notation "A -< S >* V"  (at level 61).
Inductive a_clos : Exp -> Env -> Exp
                   -> Type :=
| a_refl : forall a sigma, a -< sigma >* a
| a_tran : forall a1 a2 a3 sigma,
  a1 -[ sigma ]-> a2 ->
  a2 -< sigma >* a3 -> 
  a1 -< sigma >* a3
where "A -< S >* V" := (a_clos A S V).


Create HintDb mydb.
Hint Constructors aeval_ss : mydb.
Hint Constructors a_clos : mydb.
Hint Unfold env2 : mydb.
Hint Unfold update : mydb.



Example e1 : "x" -' 2 -[ env2]->
             10 -' 2.
Proof.
eapply ss_sub1.
apply lookup.
Qed.

Definition env3 :=
  fun (x : string) => 5.

Example e2 : 15 -' "x" -[ env3]->
             15 -' 5.
Proof.
  eapply ss_sub2.
apply lookup.
Qed.


Example e3 : "x"/'2 -[ env2]->
             10 /' 2.
Proof.
  eapply ss_div1.
apply lookup.
Qed.

Example e4 : 15/' "x" -[ env3]->
             15 /' 5.
Proof.
  eapply ss_div2.
apply lookup.
Qed.

Inductive Cond :=
| base : bool -> Cond
| bnot : Cond -> Cond
| beq  : Exp -> Exp -> Cond 
| less : Exp -> Exp -> Cond
| bor : Cond -> Cond -> Cond.

Notation " x <' y" := (less x y) (at level 80).
Notation " x =' y" := (beq x y) (at level 80).
Notation "! x " := (bnot x) (at level 81).
Notation " x |' y" := (bor x y) (at level 82).

Coercion base: bool >->Cond.

Reserved Notation "B -{ S }-> B'"  (at level 80).


Inductive beval : Cond -> Env -> Cond -> Type :=
| s_base : forall sigma b, base b -{ sigma }-> b
| not' : forall b b' sigma,
    b -{ sigma }-> b' ->
    (! b) -{ sigma }-> ! b'
| notTrue : forall sigma,
    (! true )-{ sigma }-> false 
| notFalse : forall sigma,
    (! false) -{ sigma }-> true 
| or' : forall b1 b1' b2 sigma,
    b1 -{ sigma }-> b1' ->
    (b1 |' b2)-{ sigma }-> (b1' |' b2)
| orFalse: forall b2 sigma,
    (false |' b2) -{ sigma }-> b2
| orTrue: forall b2 sigma,
    (true |' b2) -{ sigma }-> true 
| blt1: forall a1 a1' a2 sigma,
  a1 -[ sigma ]-> a1' -> 
  a1 <' a2 -{ sigma }-> (a1' <' a2)
| blt2: forall a2 a2' (i1 : nat) sigma,
  a2 -[ sigma ]-> a2' -> 
  i1 <' a2 -{ sigma }-> (i1 <' a2')
| blt': forall i1 i2 sigma,
    num i1 <' num i2 -{ sigma }->
    if (Nat.ltb i1 i2) then true else false
| eq1: forall a1 a1' a2 sigma,
  a1 -[ sigma ]-> a1' -> 
  a1 =' a2 -{ sigma }-> (a1' =' a2)
| eq2: forall a2 a2' (i1 : nat) sigma,
  a2 -[ sigma ]-> a2' -> 
  i1 =' a2 -{ sigma }-> (i1 =' a2')
| eq: forall i1 i2 sigma,
    num i1 =' num i2 -{ sigma }->
    if (Nat.eqb i1 i2) then true else false
where "B -{ S }-> B'" := (beval B S B').


Example e5 : 15 <' "x" -{ update env0 "x" 3 }-> (15 <' 3).
Proof.
eapply blt2.
apply lookup.
Qed.

Example e6 : (true |' false) -{ env0 }-> true.
Proof.
apply orTrue.
Qed.

Example e7 : (false |' false) -{ env0 }-> false.
Proof.
apply orFalse.
Qed.

Example e8 : "x" =' 15 -{ update env0 "x" 3 }-> (3 =' 15).
Proof.
apply eq1.
apply lookup.
Qed.

(*ex2*)
Inductive Stmt :=
| skip : Stmt 
| assign : string -> Exp -> Stmt
| seq : Stmt -> Stmt -> Stmt
| ite : Cond -> Stmt -> Stmt -> Stmt (* if-then-else *)
| it  : Cond -> Stmt -> Stmt (* if-then *)
| dowhile : Stmt -> Cond -> Stmt.


Notation "S1 ; S2" := (seq S1 S2) (right associativity, at level 99).
Notation "X ::= A" := (assign X A) (at level 95).

Reserved Notation "[ S , E ]~>[ S' , E' ]" (at level 99).
Inductive eval : Stmt -> Env -> Stmt -> Env -> Type :=

| ss_assign1 : forall x a a' sigma,
    a -[ sigma ]-> a' ->
    (eval (assign x a) sigma (assign x a') sigma)
| ss_assign: forall sigma x (v: nat),
    (eval (assign x v) sigma skip (update sigma x v))
| seq1: forall s1 s1' s2 sigma,
  (eval s1 sigma s1' sigma) ->
  (eval (seq s1 s2) sigma (seq s1' s2) sigma)
| ss_seq: forall s2 sigma,
  (eval (seq skip s2) sigma s2 sigma)
| ss_ite: forall s1 s2 b b' sigma,
    (b -{ sigma }-> b') ->
  (eval (ite b s1 s2) sigma (ite  b' s1 s2) sigma)
| ss_ite_true: forall s1 s2  sigma,
  (eval (ite true s1 s2) sigma s1 sigma)
| ss_ite_false: forall s1 s2  sigma,
  (eval (ite false s1 s2) sigma s2 sigma)
| ss_it: forall s1 b b' sigma,
    (b -{ sigma }-> b') ->
  (eval (it b s1) sigma (it  b' s1) sigma)
| ss_it_true: forall s1  sigma,
  (eval (it true s1 ) sigma s1 sigma)
| ss_it_false: forall s1  s2 sigma,
  (eval (it false s1 ; s2) sigma s2 sigma)
| do_While : forall s b sigma,
    eval (dowhile s b) sigma (s; (ite b (dowhile s b) skip)) sigma
.

Example e9 :
  eval (assign "n" 10) env0 skip (update env0 "n" 10).
Proof.
  apply ss_assign.
Qed.

Definition env4 :=
  fun (n : string) => 2.


Example e11 :
  eval (ite (false) ("x" ::= 17) ("x" ::=2) ; "y" ::= 4) env0
       ("x" ::=2 ; "y" ::= 4) env0.
Proof.
eapply seq1.
apply ss_ite_false.
Qed.

Example e12 :
  eval (it (true ) ("x" ::= 17); "y" ::= 4) env0
       ("x" ::=17 ; "y" ::= 4) env0.
Proof.
eapply seq1.
apply ss_it_true.
Qed.


Example e13 :
  eval (it (true ) ("x" ::= 17); "y" ::= 4) env0
       ("x" ::=17 ; "y" ::= 4) env0.
Proof.
eapply seq1.
apply ss_it_true.
Qed.


Example e14 :
  eval (dowhile ("n" ::= 2) false) env0
       ("n" ::= 2 ; ite false (dowhile ("n" ::= 2) false) skip) env0.
Proof.
  apply do_While.
Qed.