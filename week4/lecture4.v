(*Inductive Exp :=
| number : nat -> Exp
| plus : Exp -> Exp -> Exp.

Check number 3.
Check plus (number 2) (number 5).
Coercion number : nat >-> Exp.
Check (plus 2 (plus 4 6)).*)
Require Import String.
(* Check "a". throws 'Error: No interpretation for string "a".' *)
Open Scope string_scope.
Check "a".
Check  "".
Check "abcb".

Inductive Exp : Type :=
| num : nat -> Exp
| plus : Exp -> Exp -> Exp
| mul : Exp -> Exp -> Exp.

Check (plus(num 6) (num 7)).

Inductive AExp :=
| avar : string -> AExp
| anum : nat -> AExp
| aplus : AExp -> AExp -> AExp
| amul : AExp -> AExp -> AExp.
Coercion anum : nat >-> AExp.
Coercion avar : string >-> AExp.
Notation "A +' B" := (aplus A B)
(at level 50, left associativity).
Notation "A *' B" := (amul A B)
(at level 40, left associativity).