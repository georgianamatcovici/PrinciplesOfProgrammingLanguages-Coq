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
Notation "x /' y" := (div x y) (at level 55, left associativity).

(*ex2*)
Inductive Cond := 
| base : bool -> Cond
| bnot : Cond -> Cond
| beq  : AExp -> AExp -> Cond
| less : AExp -> AExp -> Cond
| band : Cond -> Cond -> Cond.

Coercion base : bool >-> Cond.

Notation "x <' y" := (less x y) (at level 50, left associativity).
Notation "x =' y" := (beq x y) (at level 50, left associativity).
Notation "! x" := (bnot x) (at level 60, right associativity).
Notation "x &' y" := (band x y) (at level 80, right associativity).
Notation "x |' y" := (bnot (band (bnot x) (bnot y))) (at level 80, right associativity).
Notation "x >' y" := (band (bnot (less x y)) (bnot (beq x y))) (at level 50, left associativity).
Notation "x <=' y" := (bnot (band (bnot (less x y)) (bnot (beq x y)))) (at level 50, left associativity).
Notation "x >=' y" := (bnot (less x y)) (at level 50, left associativity).

(*ex3*)
Inductive Stmt :=
| skip : Stmt
| assign : string -> AExp -> Stmt
| seq : Stmt -> Stmt -> Stmt
| ite : Cond -> Stmt -> Stmt -> Stmt
| while : Cond -> Stmt -> Stmt.

Notation "x ::= y" := (assign x y) (at level 85, right associativity).
Notation "x ;; y" := (seq x y) (at level 85, right associativity).
Notation "if ( c ) ( x ) ( y )" := (ite c x y) (at level 85, right associativity).
Notation "while ( c ) ( x )" := (while c x) (at level 85, right associativity).



Definition compute_modulo (x y : string) :=
  "m" ::= 0 ;; (* Prima instrucțiune este de tip Stmt *)
  while (x >' y) (x ::= x -' y) ;;  (* Secvența are instrucțiuni de tip Stmt *)
  if (x =' y) ("m" ::= 0) ("m" ::= x) ;;  (* La fel aici *)
  "result" ::= "m".

Definition is_even (x : string) :=
  if (x /' 2 =' 0) ("is_even" ::= 1) ("is_even" ::= 0).