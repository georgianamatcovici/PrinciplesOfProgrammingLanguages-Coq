Require Import String.
Open Scope string_scope.
Require Import Lia.

Check "asdasf".

Inductive Exp :=
| num : nat -> Exp
| var : string -> Exp
| add : Exp -> Exp -> Exp
| sub : Exp -> Exp -> Exp
| div : Exp -> Exp -> Exp.

Coercion num : nat >-> Exp.
Coercion var : string >-> Exp.

Notation "x +' y" := (add x y) (at level 50, left associativity).
Notation "x -' y" := (sub x y) (at level 50, left associativity).
Notation "x /' y" := (div x y) (at level 40, left associativity).



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
Reserved Notation "A =[ S ] => N" (at level 60).
Inductive ExprEval : Exp -> Env -> nat -> Prop :=
| const : forall i sigma, num i =[sigma] => i
| lookup : forall x sigma, var x =[sigma] => sigma x
| bs_add: forall a1 a2 i1 i2 sigma n,
  a1 =[sigma] => i1 ->
  a2 =[sigma] => i2 ->
  n  = i1 + i2 ->
  a1 +' a2 =[sigma] => n
| bs_sub: forall a1 a2 i1 i2 sigma n,
  a1 =[sigma] => i1 ->
  a2 =[sigma] => i2 ->
  i1 >= i2 ->
  n  = i1 - i2 ->
  a1 -' a2 =[sigma] => n
| bs_div: forall a1 a2 i1 i2 sigma n,
  a1 =[sigma] => i1 ->
  a2 =[sigma] => i2 ->
  i2 <> 0 ->
  n  = (Nat.div i1 i2) ->
  a1 /' a2 =[sigma]=> n
where "A =[ S ] => N" := (ExprEval A S N).

Example e1 : "x" -' 2 =[ update env0 "x" 10 ]=> 8.
Proof.
  apply bs_sub with (i1 := 10) (i2 := 2).
  - apply lookup.
  - apply const.
  -simpl.
  lia.
-reflexivity.
Qed.


Example e2 : 12 -' "x" =[ update env0 "x" 7 ]=> 5.
Proof.
  apply bs_sub with (i1 := 12) (i2 := 7).
 - apply const.
  - apply lookup.
  -simpl.
  lia.
-reflexivity.
Qed.


Example e3 : "x" /' 2 =[ update env0 "x" 10 ]=> 5.
Proof.
  apply bs_div with (i1 := 10) (i2 := 2).
  - apply lookup.
  - apply const.
  -simpl.
  lia.
-reflexivity.
Qed.


Example e4 : 15 /' "x" =[ update env0 "x" 3 ]=> 5.
Proof.
  apply bs_div with (i1 := 15) (i2 := 3).
  - apply const.
  - apply lookup.
  -simpl.
  lia.
-reflexivity.
Qed.


(*ex2*)
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

Reserved Notation "B ={ Sigma }=> B'"
         (at level 90). 



Inductive CondEval :
  Cond -> Env -> Cond -> Type :=
| bbase : forall sigma b, base b ={ sigma }=> base b
| not_t : forall b sigma,
    b ={sigma}=> base true ->
    bnot b ={sigma}=> base false 
| not_f : forall b sigma,
    b ={sigma}=> base false ->
    bnot b ={sigma}=> base true
| or_f : forall b1 b2 sigma b,
   b1 ={sigma}=> base false ->
   b2 ={sigma}=> b ->
   b1 |' b2 ={sigma}=> b
| or_t : forall b1 b2 sigma,
   b1 ={sigma}=> base true ->
   b1 |' b2 ={sigma}=> base true
| bbeq : forall a1 a2 sigma i1 i2 b,
   a1 =[sigma]=> i1 ->
   a2 =[sigma]=> i2 ->
   b = Nat.eqb i1 i2 ->
   a1 =' a2 ={sigma}=> base b
| less_than_1 : forall a1 a2 i1 sigma, 
  a1 =[sigma]=> i1 ->
  a1 <' a2 ={sigma}=> i1 <' a2
| less_than_2 : forall  a2 i1 i2 b sigma,
   a2 =[sigma] => i2->
   b=Nat.ltb i1 i2 ->
  i1 <' a2 ={sigma}=>  base b
where "B ={ Sigma }=> B'" := (CondEval B Sigma B').



Example e5 : 15 <' "x" ={ update env0 "x" 3 }=>  base false.
Proof.
eapply less_than_2.
eapply lookup.
reflexivity.
Qed.





Definition env1 :=
  update
    (update
       (update env0 "i" 10)
       "j" 11)
    "n" 12.

Create HintDb mydb.
Hint Constructors CondEval : mydb.
Hint Constructors ExprEval : mydb.
Hint Unfold Nat.ltb : mydb.
Hint Unfold env1 : mydb.




(* ex3 *)
Inductive Stmt :=
| skip : Stmt 
| assign : string -> Exp -> Stmt
| seq : Stmt -> Stmt -> Stmt
| ite : Cond -> Stmt -> Stmt -> Stmt (* if-then-else *)
| it  : Cond -> Stmt -> Stmt (* if-then *)
| dowhile : Stmt -> Cond -> Stmt.

Notation "S1 ; S2" := (seq S1 S2) (right associativity, at level 99).
Notation "X ::= A" := (assign X A) (at level 95).


Reserved Notation "S ~[ E ]~> E'" (at level 99).
Inductive eval : Stmt -> Env -> Env -> Type :=
| b_skip    :  forall sigma,
               ( skip ) ~[ sigma ]~> sigma
| b_assign : forall x a v sigma sigma',
  a =[ sigma ]=> v ->
  sigma' = update sigma x v -> 
  (x ::= a) ~[ sigma ]~> sigma'
| b_seq : forall s1 s2 sigma1 sigma2 sigma3,
  s1 ~[ sigma1 ]~> sigma2 ->
  s2 ~[ sigma2 ]~> sigma3 -> 
  (s1 ; s2) ~[ sigma1 ]~> sigma3
| b_doWhile_f :  forall s1 cond1 sigma sigma1,
              s1 ~[ sigma ]~> sigma1
            -> cond1 ={ sigma1 }=> base false
            -> (dowhile s1 cond1) ~[ sigma ]~> sigma1
| b_doWhile_t :  forall s1 cond1 sigma sigma1 sigma2,
              s1 ~[ sigma ]~> sigma1
            -> cond1 ={ sigma1 }=> base true
            -> (dowhile s1 cond1) ~[ sigma1]~> sigma2
            -> (dowhile s1 cond1) ~[ sigma ]~> sigma2
| it_t      :   forall cond1 s1 sigma sigma1,
               cond1 ={ sigma }=> base true
            -> s1 ~[ sigma ]~> sigma1
            -> (it cond1 s1) ~[ sigma ]~> sigma1
| it_f      :  forall cond1 s1 sigma,
              cond1 ={ sigma }=> base false
            -> (it cond1 s1) ~[ sigma ]~> sigma
| ite_t : forall b sigma sigma' s1 s2,
  b ={ sigma }=> base true ->
  s1 ~[ sigma ]~> sigma' ->
  (ite b s1 s2) ~[ sigma ]~> sigma'
| ite_f : forall b sigma sigma' s1 s2,
  b ={ sigma }=> base false ->
  s2 ~[ sigma ]~> sigma' ->
  (ite b s1 s2) ~[ sigma ]~> sigma'
where "S ~[ E ]~> E'" := (eval S E E').

Hint Constructors eval : mydb.
Hint Unfold env0 : mydb.


Example e6:
  (assign "n" 10) ~[ env0 ]~> update env0 "n" 10.
Proof.
  eauto with mydb.
Qed.
Definition env2 :=
  fun (x1 : string) => 20.
Definition env3 := update (update ( fun x => 0) "x1" 10) "x2" 20.

Definition env4 := update (update env3 "x1" 20) "x2" 10.
Example e7:
  (skip) ~[ env0 ]~> env0.
Proof.
  eauto with mydb.
Qed.
Example e8 : 
("x1" ::=20;
"x2" ::=10) ~[ env3 ]~> env4.
Proof.
eapply b_seq.
  -eapply b_assign.
    -- eapply const.
    -- trivial.
  -eapply b_assign.
    -- eapply const.
    -- trivial.
Qed.

Example e9 : 
(ite ( 3=' 4)
   ( "i" ::= 20 )
    ( skip );
 it ( ! "i" <' 20-10 )
    ("i" ::= "i"-'10)
) ~[ env3 ]~> env3.
Proof.

  eapply b_seq.
  - eapply ite_f.
    -- eapply bbeq.
        --- eapply const.
        --- eapply const.
        --- simpl. trivial.
    -- eapply b_skip.
  - eapply it_f. eapply not_t. eapply less_than_1. eapply less_than_2.
    -- eapply lookup.
    -- simpl. eapply const.
    -- unfold env3. unfold update. simpl. trivial.
Qed.  

Example e9 : 
(
  "i" ::= 1;
  "n" ::= 2;
  dowhile (
    "i" ::= "i" +' 1
  )
  ("i" <' "n")
) ~[ env3 ]~> (update (update ( update env3 "i" 1) "n" 2) "i" 2).
Proof.

  eapply b_seq.
  - eapply b_assign.
      -- eapply const.
      -- trivial.
  - eapply b_seq.
    -- eapply b_assign.
        --- eapply const.
        --- trivial.
    -- eapply b_doWhile_f.
        --- eapply b_assign.
                ---- eapply bs_add.
                  ----- eapply lookup.
                  ----- eapply const.
                  ----- simpl. trivial.
                ---- trivial.
        --- eapply less_than_1. eapply less_than_2.
                ---- eapply lookup.
                ---- eapply lookup.
                ---- unfold update. simpl. trivial.
Qed.
