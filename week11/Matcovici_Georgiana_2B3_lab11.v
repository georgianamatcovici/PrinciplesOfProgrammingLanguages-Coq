Require Import String.
(* Check "a". throws 'Error: No interpretation for string "a".' *)
Open Scope string_scope.
Check "a".
Check  "".
Check "abcb".
Require Import List.
Import ListNotations.

Inductive AExp : Type :=
| num : nat -> AExp
| var : string -> AExp
| add : AExp -> AExp -> AExp
| sub : AExp -> AExp -> AExp
| div : AExp -> AExp -> AExp.

Coercion num : nat >-> AExp.
Coercion var : string >-> AExp.

Notation "x +' y" := (add x y) (at level 50, left associativity).
Notation "x -' y" := (sub x y) (at level 50, left associativity).
Notation "x /' y" := (div x y) (at level 40, left associativity).

Check (add (num 2) (add (var "x") (div (num 2) (var "y")))).
Check (add 2 (add "x" (div 2 "y"))).
Set Printing Coercions.
Check (add 2 (add "x" (div 2 "y"))).
Unset Printing Coercions.
Check 2 +' ("x" +' 2 /' "y").
Set Printing All.
Check 2 -' ("x" +' 2 /' "y").
Check 2 -' "x" /' "y".
Check "x" /' "y" +' 2.
Check "x" /' "y" /' "z".
Unset Printing All.



Inductive Cond :=
| base : bool -> Cond
| bnot : Cond -> Cond
| beq  : AExp -> AExp -> Cond
| less : AExp -> AExp -> Cond
| band : Cond -> Cond -> Cond.


Notation " x <' y" := (less x y) (at level 80).
Notation " x =' y" := (beq x y) (at level 80).
Notation "! x " := (bnot x) (at level 81).
Notation " x &' y" := (band x y) (at level 82).
Notation " x |' y" := (bnot (band (bnot x) (bnot y))) (at level 82).


Inductive Stmt :=
| skip : Stmt
| assign : string -> AExp -> Stmt
| seq : Stmt -> Stmt -> Stmt
| ite : Cond -> Stmt -> Stmt -> Stmt
| while : Cond -> Stmt -> Stmt
| Return : AExp -> Stmt.



Notation "m ::= y" := (assign m y) (at level 85).

Notation "x ;; y" := (seq x y) (at level 99).
            

Definition param :=
list string.

Inductive method :=
|Method: string ->param->Stmt->method.

Inductive class :=  
| Class : string -> list string -> list method -> class.
 Check list.
Print list.



Definition ClassNumbers :=
Class "Numbers" 
["x"; "y"]
[Method "add" ["x"; "y"] (Return ("x" +' "y"));
 Method "sub" ["x"; "y"] ("z"::=("x" -' "y") ;; Return "z")].

Definition ClassStudent :=
Class "Student" 
["id"; "year"; "average_grade"]
[Method "get_id" [] (Return ("id"));
Method "get_year" [] (Return ("year"));
Method "get_average_grade" [] (Return ("average_grade"));
Method "set_id" ["x"] ("id"::="x");
Method "set_year" ["x"] ("year"::="x");
Method "set_average_grade" ["x"] ("average_grade"::="x")
].

Definition ClassCourse :=
Class "Course" 
["id"; "name"; "credits"; "semester"]
[
  Method "get_id" [] (Return ("id"));
  Method "get_name" [] (Return ("name"));
  Method "get_credits" [] (Return ("credits"));
  Method "get_semester" [] (Return ("semester"));
  Method "set_id" ["x"] ("id"::="x");
  Method "set_name" ["x"] ("name"::="x");
  Method "set_credits" ["x"] ("credits"::="x");
  Method "set_semester" ["x"] ("semester"::="x")
].


