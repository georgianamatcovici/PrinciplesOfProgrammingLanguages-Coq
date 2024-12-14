Require Import String.
(* Check "a". throws 'Error: No interpretation for string "a".' *)
Open Scope string_scope.
Check "a".
Check  "".
Check "abcb".

(*ex1*)
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


(*ex2*)
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
Notation " x >' y" := (band (bnot(less x y)) (bnot( beq x y))) (at level 80).
Notation " x <=' y" := (bnot (band(bnot (less x y))(bnot(beq x y)))) (at level 80).
Notation " x >=' y" := (bnot (less x y)) (at level 80).
Check "x" <' "y".
Check "x" =' "y".
Check ! "x" =' "y".
Check "x" <' "y" &' "x" =' "y".
Check "x" <' "y" |' "x" =' "y".
Check "x" >' "y" |' "x" =' "y".
Check "x" >' "y".
Check 2 >' "y".
Check 3 >' "y".
Check "x" <=' "y".
Check 3 <=' "y".
Check 2 <=' "y".
Check "x" >=' "y".
Check 2 >=' "y".
Check 1 >=' "y".
Check !(! "x" <' "y" &' ! "x" =' "y").
Check ("x" <' "y" |' "x" =' "y") .


(*3*)
Inductive Stmt :=
| skip : Stmt
| assign : string -> AExp -> Stmt
| seq : Stmt -> Stmt -> Stmt
| ite : Cond -> Stmt -> Stmt -> Stmt
| while : Cond -> Stmt -> Stmt.


(*4*)



Notation "m ::= y" := (assign m y) (at level 85).

Notation "x ;; y" := (seq x y) (at level 99).



Definition is_even (x : string) :=
  ite (x /' 2 =' 0) ("is_even" ::= 1) ("is_even" ::= 0).

Definition compute_modulo (x y : string) :=
  "m" ::= 0 ;;
   while (x >' y) (
      x ::= x -' y
   );;
   ite (x =' y) ("m" ::= 0) ("m" ::= x) ;;
   "result" ::= "m".

(*5*)
Definition gcd (x y : string) :=
 while(! x =' y) (
ite (x >' y) (x ::= x -' y) (y ::= y -' x)
);;
"result" ::=x.

(*6*)
Definition Fibonacci (n: string) :=
  "result" ::= 0 ;;                              
  ite (n =' "1" |' n =' "2")                      
      ("result" ::= 1)                             
      (                                         
        "cnt" ::= 2 ;;                            
        "a" ::= 1 ;;                             
        "b" ::= 1 ;;                             
        while ("cnt" <' n) (                    
          "c" ::= "a" +' "b" ;;                  
          "a" ::= "b" ;;                         
          "b" ::= "c" ;;                          
          "cnt" ::= "cnt" +' 1                    
        );;
        "result" ::= "c"
).    

Definition max( x y : string) :=
"max" ::= x;;
ite (x >' y) ("max" ::=x) ("max" ::= y)
.                  



