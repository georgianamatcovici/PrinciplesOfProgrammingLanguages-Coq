Require Import String.
Open Scope string_scope.
Import Nat.
Require Import Lia.

Check "asdasf".
Definition Env := string -> nat.
Definition env0 :=
  fun (x : string) => 0.
Definition env1 : Env := fun (x : string) => 0.
Definition env2 :=
fun y =>
if (string_dec y "n")
then 10
else 0.

Definition update
  (env : Env)
  (x : string)
  (v : nat) : Env :=
  fun y => if x =? y
           then v
           else env y.

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



Inductive Cond :=
| base : bool -> Cond
| bnot : Cond -> Cond
| beq  : Exp -> Exp -> Cond 
| less : Exp -> Exp -> Cond
| bor : Cond -> Cond -> Cond.





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

Example e2 : ~ exists n, 3 -' 5 =[env0] => n.
Proof.
  intros [n H].           
  inversion H; subst.      
  inversion H2; subst.     
  inversion H3; subst.     
  lia.                     
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

Example e4 : ~ exists n, 3 -' 5 =[env0] => n.
Proof.
  intros [n H].           
  inversion H; subst.      
  inversion H2; subst.     
  inversion H3; subst.     
  lia.  
Qed.

Notation " x <' y" := (less x y) (at level 80).
Notation " x =' y" := (beq x y) (at level 80).
Notation "! x " := (bnot x) (at level 81).
Notation " x |' y" := (bor x y) (at level 82).

Reserved Notation "B ={ Sigma }=> B'"
         (at level 90). 

(*ex2*)
Inductive bool_evaluations :
  Cond -> Env -> bool -> Type :=
| Base : forall sigma b, base b ={ sigma }=> b
| NotT : forall b sigma,
    b ={sigma}=> true ->
    bnot b ={sigma}=> false 
| NotF : forall b sigma,
    b ={sigma}=> false ->
    bnot b ={sigma}=> true
| OrT : forall b1 b2 sigma b,
   b1 ={sigma}=> true ->
   b2 ={sigma}=> b ->
   b1 |' b2 ={sigma}=> b
| OrF : forall b1 b2 sigma,
   b1 ={sigma}=> false ->
   b1 |' b2 ={sigma}=> false
| Beq : forall exp1 exp2 sigma i1 i2 b,
   exp1 =[sigma]=> i1 ->
   exp2 =[sigma]=> i2 ->
   b = Nat.eqb i1 i2 ->
   exp1 =' exp2 ={sigma}=>b
| lessThan : forall exp1 exp2 i1 i2 b sigma, 
  exp1 =[sigma]=> i1 ->
  exp2 =[sigma]=> i2 ->
  b  = (Nat.ltb i1 i2) ->
  exp1 <' exp2 ={sigma}=> b 
where "B ={ Sigma }=> B'" := (bool_evaluations B Sigma B').


(*ex3*)

Inductive Stmt :=
| assign : string -> Exp -> Stmt
| ite : Cond -> Stmt -> Stmt -> Stmt
| while : Cond -> Stmt -> Stmt
| skip : Stmt
| seq : Stmt -> Stmt -> Stmt.

Notation "S1 ; S2" := (seq S1 S2) (right associativity, at level 99).
Notation "X ::= A" := (assign X A) (at level 95).


Reserved Notation "S ~[ E ]~> E'" (at level 99).
Inductive eval : Stmt -> Env -> Env -> Type :=
| b_assign : forall x a v sigma sigma',
  a =[ sigma ]=> v ->
  sigma' = update sigma x v -> 
  (x ::= a) ~[ sigma ]~> sigma'
| b_seq : forall s1 s2 sigma1 sigma2 sigma3,
  s1 ~[ sigma1 ]~> sigma2 ->
  s2 ~[ sigma2 ]~> sigma3 -> 
  (s1 ; s2) ~[ sigma1 ]~> sigma3
| while_t : forall b s sigma sigma',
  b -[ sigma ]-> true ->
  (s ; while b s) ~[ sigma ]~> sigma' ->
  (while b s) ~[ sigma ]~> sigma'
| while_f : forall b s sigma,
  b -[ sigma ]-> false ->
  (while b s) ~[ sigma ]~> sigma 
| ite_t : forall b sigma sigma' s1 s2,
  b -[ sigma ]-> true ->
  s1 ~[ sigma ]~> sigma' ->
  (ite b s1 s2) ~[ sigma ]~> sigma'
| ite_f : forall b sigma sigma' s1 s2,
  b -[ sigma ]-> false ->
  s2 ~[ sigma ]~> sigma' ->
  (ite b s1 s2) ~[ sigma ]~> sigma'
where "S ~[ E ]~> E'" := (eval S E E').






