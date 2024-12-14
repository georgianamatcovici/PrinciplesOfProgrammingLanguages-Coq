Require Import String.
Require Import Nat.
(* Check "a". throws 'Error: No interpretation for string "a".' *)
Open Scope string_scope.
Check "a".
Check  "".
Check "abcb".

Inductive Exp :=
| avar : string -> Exp
| anum : nat -> Exp
| aplus : Exp -> Exp -> Exp
| amul : Exp -> Exp -> Exp
| btrue : Exp
| bfalse : Exp
| bnot : Exp -> Exp
| band : Exp -> Exp -> Exp
| blessthan : Exp -> Exp -> Exp
| bgreaterthan : Exp -> Exp -> Exp.
Coercion anum : nat >-> Exp.
Coercion avar : string >-> Exp.
Notation "A +' B" := (aplus A B) (at level 50, left associativity).
Notation "A *' B" := (amul A B) (at level 40, left associativity).
Notation "A <' B" := (blessthan A B) (at level 80).
Notation "A >' B" := (bgreaterthan A B) (at level 80).
Infix "and'" := band (at level 82).
Notation "! A" := (bnot A) (at level 81).