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


Inductive Stmt :=
| skip : Stmt
| assign : string -> Exp -> Stmt
| seq : Stmt -> Stmt -> Stmt
| ite : Cond -> Stmt -> Stmt -> Stmt
| it : Cond -> Stmt -> Stmt
| dowhile : Stmt -> Cond -> Stmt
| Return : Exp -> Stmt.


Notation "S1 ; S2" := (seq S1 S2) (right associativity, at level 99).
Notation "X ::= A" := (assign X A) (at level 85).


Inductive Method :=
|method: string -> list(string)->Stmt->Method.

Inductive Class := 
| class : string -> list (string) -> Method -> Class.

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

Definition sum :=
  method "sum" [] skip.


Definition sum :=
  method "sum" ["a"; "b"] (skip).

Definition mul_method :=
  method
    "multiply"
    ["a"; "b"]
    (skip ; Return ("a" * "b")).

(* Declarație clasă cu membru și metode *)
Definition example_class :=
  class
    "Calculator"            (* Numele clasei *)
    ["memory"]              (* Membrii de date *)
    sum_method. 
