(*
Un limbaj format din:
1. expresii aritmetice
2. expresii boolene
3. instructiuni: assignment, if-then-else, while, skip, sequences
 *)

Require Import String.
Open Scope string_scope.

Check "asdasf".

Inductive AExp :=
| num : nat -> AExp
| var : string -> AExp
| add : AExp -> AExp -> AExp
| mul : AExp -> AExp -> AExp.


Check add (num 3) (var "x").

(* Coercions *)
Coercion num : nat >-> AExp.
Coercion var : string >-> AExp.

Check add 3 "x".
Set Printing Coercions.
Check add 3 "x".
Unset Printing Coercions.
Check add 3 "x".

Notation "A +' B" :=
  (add A B)
    (left associativity, at level 50).
Notation "A *' B" :=
  (mul A B)
    (left associativity, at level 40).

Definition Env := string -> nat.
(*<AExp, Env> => <nat> *)

Reserved Notation "A =[ S ] => V" (at level 60).

Reserved notation "B =[  S ] -> B" (at level 80).
Inductive beval : BExp ->Env ->bool -> Type :=
|tt : forall sigma, btrue- [sigma] ->true
|ff : forall sigma, bfalse - [sigma] ->false
|notTrue : forall b sigma
b - [sigma ] -> b'
bnot b - [sigma ] -> b'
|notFalse : forall b sigma
b - [sigma ] -> false
bnot b - [sigma ] -> true
|andTrue : 
b1 - [sigma ] -> true ->
| blt1: a1 <' a2 -[ sigma ] -> false
|blt1 :
a1=[sigma ] =>i1
 

Inductive aeval : AExp -> Env ->nat -> Type :=
|const : forall n sigma, (num n) =[ sigma ] => n
|lookup : forall x sigma, (var x) =[ sigma ] => (sigma x)
|bs_add : 
a1= [sigma ] => i1
a2=[sigma] => i2
n=i1+i2 ->
a1+' a2=[sigma] => n
|bs_mull : 
a1= [sigma ] => i1
a2=[sigma] => i2
a1 *' a2=[sigma] => i1+i2
where "A = [ S ] |=>V" := (aeval A S V).


Exmple e1:"x" +' 2=[update env0 "x" 10] =>12.
Proof.
apply bs_add with (i1:=10) (i2:= 2).
-apply lookup.
-apply const.
-simpl.
reflexivity.
Qed.

Exmple e1':"x" +' 2=[update env0 "x" 10] =>12.
Proof.
eapply bs_add. (*existential apply*)
-apply lookup.
-apply const.
-simpl.
reflexivity.
Qed.

Definition env0 :=
  fun (x : string) => 0.
Definition env1 := update (update env0 "i" 10) "j" 11 )
Example e2 : 
"i" +' 1 <' 
Proof.
apply andTrue.
- eapply blt1.
  + apply lookup.
  + eapply bs_add.
     * apply lookup.
     * apply const.
     * apply const.
     * simpl.
         reflexivity
   + unfold env1.
     unfold update.
     simpl.
     unfold Nat.ltb.
     simpl.
    reflexivity.
  -apply tt.
Qed.

Create HintDb mydb.
Hint Constructors beval : mydb.
Hint Constructors aeval : mydb.
Hint Unfold Nat.ltb : mydb 
Hint Unfold env1 : mydb 



Check const.
Check (const(num 10) env0 10).


Check 2 +' 5.
Check "x" +' 5 +' "y".
Set Printing Parentheses.
Check "x" +' 5 +' "y".

Check "x" +' 5 *' "y".
Check "x" *' 5 +' "y".

Print bool.
(* boolean *)
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

Check "i" <' "n".
Check "i" +' 1 <' 5 *' "j" +' 4 &&' btrue.


Check 2 *' (3 +' 5).


Inductive Stmt :=
| assign : string -> AExp -> Stmt
| ite : BExp -> Stmt -> Stmt -> Stmt
| while : BExp -> Stmt -> Stmt
| skip : Stmt
| seq : Stmt -> Stmt -> Stmt.

Check (assign "n" 10).
Check (assign "i" 0).
Check (assign "s" ("s" +' "i")).

Notation "X ::= A" := (assign X A)
                        (at level 90).
Check "n" ::= 10.
Check "i" ::= 0.
Check "s" ::= "s" +' "i".

Check ite ("i" <' "n")
          ( "i" ::= "i" +' 1)
          ( "i" ::= "i" *' 1).

Check while ("i" <' "n")
  ("s" ::= "s" +' "i").

Check skip.
Check seq ("s" ::= "s" +' "i")
  ("i" ::= "i" +' 1).

Notation "S1 ; S2" := (seq S1 S2)
                        (at level 99).
Check
  "s" ::= "s" +' "i" ;
"i" ::= "i" +' 1.


Definition sum :=
"n" ::= 10 ;
"i" ::= 0 ;
"s" ::= 0 ;
while ("i" <' "n" +' 1) (
    "s" ::= "s" +' "i" ;
    "i" ::= "i" +' 1
  ).
Check sum.

Unset Printing All.


(* Environment *)
Definition Env := string -> nat.

Definition env1 :=
  fun (x : string) => 0.
  
Compute env1 "x".
Compute env1 "y".

Definition env2 :=
  fun y => if y =? "n"
           then 10
           else 0.

Compute env2 "n".
Compute env2 "x".

Definition update
  (env : Env)
  (x : string)
  (v : nat) : Env :=
  fun y => if x =? y
           then v
           else env y.

Compute (update env1 "n" 100) "n".

Compute (update env1 "n" 100) "x".


Print AExp.

Fixpoint aeval
  (a : AExp) (e : Env) : nat :=
  match a with
  | num n => n
  | var x => e x
  | add a1 a2 => (aeval a1 e) +
                   (aeval a2 e)
  | mul a1 a2 => (aeval a1 e) *
                   (aeval a2 e)
  end.


Compute aeval (2 +' "n") env2.

Compute aeval
  (2 +' "n")
  (update env1 "n" 100).

    
Compute aeval
  (2 *' "n")
  (update env1 "n" 100).

Compute aeval
  ((2 +' "n") *' (2 +' "x"))
  (update env1 "n" 100).

Check true.
Check andb.
Compute andb false true.
Print BExp.
Check negb.

Import Nat.

Print leb.
Check leb 1 2.
Check ltb.
Compute ltb 1 2.
Compute ltb 2 1.

Fixpoint beval
  (b : BExp)
  (e : Env) : bool :=
  match b with
  | btrue => true
  | bfalse => false
  | band b1 b2 => andb
                    (beval b1 e)
                    (beval b2 e)
  | bnot b => negb (beval b e)
  | blt a1 a2 => ltb
                   (aeval a1 e)
                   (aeval a2 e)
  end.


Compute beval ("i" <' "n") env2.
Compute beval ("n" <' "i") env2.


Print Stmt.

Fixpoint eval
  (s : Stmt)
  (e : Env)
  (fuel : nat)
  : Env :=
  match fuel with
  | O => e
  | S n' => 
      match s with
      | assign x a => update e x
                        (aeval a e)
      | ite b s1 s2 =>
          if (beval b e)
          then (eval s1 e n')
          else (eval s2 e n')
      | skip => e
  | seq s1 s2 => eval s2 (eval s1 e n') n'
      | while b s =>
          if negb (beval b e)
          then e
          else eval (seq s (while b s)) e n'
      end
  end.


Check sum.

Compute (eval sum env1 10) "s".

Print list.

Inductive Error (T: Type) : Type :=
| Err : Error T
| Value : T -> Error T.


Fixpoint eval'
  (s : Stmt)
  (e : Env)
  (fuel : nat)
  : Error Env :=
  match fuel with
  | O => Err Env
  | S n' => 
      match s with
      | assign x a => Value _ (update e x (aeval a e))
      | ite b s1 s2 =>
          if (beval b e)
          then (eval' s1 e n')
          else (eval' s2 e n')
      | skip => Value _ e
      | seq s1 s2 => match (eval' s1 e n') with
                     | Err _ => Err Env
                     | Value _ e' => eval' s2 e' n'
                     end
      | while b s =>
          if negb (beval b e)
          then Value _ e
          else eval' (seq s (while b s)) e n'
      end
  end.

Compute match (eval' sum env1 1000) with
        | Err _ => "err"
        | Value _ e => "success"
        end.

Inductive Result (S T : Type) : Type :=
| Er : S -> Result S T
| Val : T -> Result S T.
Check Val.
Definition extract (r : Error Env) (x : string)
  : Result string nat :=
  match r with
  | Err _ => Er _ _ "error"
  | Value _ e => Val _ _ (e x)
  end.

Compute extract (eval' sum env1 10) "s".


Definition sum' (n : nat) :=
"i" ::= 0 ;
"s" ::= 0 ;
while ("i" <' n +' 1) (
    "s" ::= "s" +' "i" ;
    "i" ::= "i" +' 1
  ).


Theorem sum_is_correct:
  forall n k N,
    extract (eval' (sum' n) env1 k) "s" =
      Val string nat N ->
    2 * N = n * (n + 1).
Proof.
Abort.
