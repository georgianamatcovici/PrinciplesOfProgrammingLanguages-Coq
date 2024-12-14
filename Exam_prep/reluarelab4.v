Require Import String.
(* Check "a". throws 'Error: No interpretation for string "a".' *)
Open Scope string_scope.
Check "a".
Check  "".
Check "abcb".
Require Import Nat.

Check nat_ind.


Inductive AExp :=
| num : nat -> AExp
| var : string -> AExp
| add : AExp -> AExp -> AExp
| sub : AExp -> AExp -> AExp
| mul : AExp -> AExp -> AExp
| div : AExp -> AExp -> AExp.

Coercion num : nat >-> AExp.
Coercion var : string >-> AExp.

Notation " x +' y" := (add x y) (at level 50, left associativity).
Notation " x -' y" := (sub x y) (at level 50, left associativity).
Notation " x *' y" := (mul x y) (at level 40, left associativity).
Notation " x /' y" := (div x y) (at level 40, left associativity).

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
| prop : string -> Cond
| base : bool-> Cond
| bnot : Cond -> Cond
| band : Cond -> Cond -> Cond
| beq : AExp -> AExp -> Cond
| less : AExp -> AExp -> Cond.

Coercion base : bool >-> Cond.
Notation " ! x" := (bnot x) (at level 83, left associativity).
Notation " x &' y" := (band x y) (at level 84, left associativity).
Notation " x =' y" := (beq x y) (at level 82, left associativity).
Notation " x <' y" := (less x y) (at level 81, left associativity).
Notation " x |' y" := (bnot (band (bnot x) (bnot y))) (at level 85).
Notation " x >' y" := (band (bnot(less x y)) (bnot( beq x y))) (at level 81).
Notation " x <=' y" := (bnot (band(bnot (less x y))(bnot(beq x y)))) (at level 81).
Notation " x >=' y" := (bnot (less x y)) (at level 81).

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

Inductive Stmt :=
| skip : Stmt
| assign : string -> AExp -> Stmt
| assignb : string ->Cond ->Stmt
| seq : Stmt -> Stmt -> Stmt
| ite : Cond -> Stmt-> Stmt -> Stmt
| it : Cond-> Stmt -> Stmt
| while : Cond -> Stmt -> Stmt
| for_loop : Stmt -> Cond -> Stmt -> Stmt -> Stmt.

Notation " x ::= a" := (assign x a)( at level 90, left associativity).
Notation " s1 ;; s2 " := (seq s1 s2)( at level 93, left associativity).
Definition compute_modulo (x y : string) :=
  "m" ::= 0 ;;
   while (x >' y) (
      x ::= x -' y
   );;
   ite (x =' y) ("m" ::= 0) ("m" ::= x) ;;
   "result" ::= "m".

Definition is_even (x : string) :=
  ite (x /' 2 =' 0) ("is_even" ::= 1) ("is_even" ::= 0).

Definition max (x y : string) :=
"max" ::=0;;
ite (x >' y) ("max" ::=x) ("max" ::=y).


Definition max' (x y : string) :=
"max" ::=x;;
it (y >' x) ("max" ::=y).

Definition sum :=
"n" ::= 10;;
"s" ::= 0;;
for_loop ( "i" ::= 0 )( "i" <' "n" +' 1) ( "i" ::= "i" +' 1)
( "s" ::= "s" +' "i").
Definition sum1 :=
"n" ::= 10;;
"s" ::= 0;;
"i" ::= 0  ;;
while ( "i" <' "n" +' 1) 
( "s" ::= "s" +' "i" ;;
"i" ::= "i" +' 1).

Check sum.


Definition Env := string-> nat.
Definition env1 : Env := 
fun x => 0.
Definition env2 : Env :=
fun x => if (string_dec x "x")
         then 10
         else 0.

Compute env1 "y".
Compute env2 "x".

Definition update (env1 : Env) (y : string) (v: nat) : Env :=
fun x => if (string_dec x y) then v
         else env1 x.

Fixpoint aeval( a: AExp) (sigma : Env) : nat :=
match a with
| num n => n
| var x => sigma x
| add a1 a2 => (aeval a1 sigma) + (aeval a2 sigma)
| sub a1 a2 => (aeval a1 sigma) - (aeval a2 sigma)
| mul a1 a2 => (aeval a1 sigma) * (aeval a2 sigma)
| div a1 a2 => Nat.div (aeval a1 sigma) (aeval a2 sigma)
end.
Definition Tau := string -> bool.
Definition updateT ( : Env) (y : string) (v: nat) : Env :=
fun x => if (string_dec x y) then v
         else env1 x.
Fixpoint beval (b : Cond) (sigma : Env) (tau : Tau) : bool :=
match b with
|prop p => tau p
|base b' => b'
|bnot b' => negb (beval b' sigma tau)
|band b1 b2 => andb (beval b1 sigma tau) (beval b2 sigma tau)
|beq a1 a2 => Nat.eqb (aeval a1 sigma ) (aeval a2 sigma )
|less a1 a2 => Nat.ltb (aeval a1 sigma ) (aeval a2 sigma )
end.


Fixpoint eval( s: Stmt) (sigma : Env) (tau : Tau) (fuel : nat): Env :=
  match fuel with 
| O => sigma
| S n' =>               
        match s with
        | skip => sigma
        | assign x val => update sigma x (aeval val sigma)
        | assignb x val => update tau x (beval val tau)
        | seq s1 s2 => (eval s2 (eval s1 sigma tau n') tau n')
        | ite cond s1 s2 => match (beval cond sigma tau) with
                    |true => (eval s1 sigma tau n')
                    | false => (eval  s2 sigma tau n')
                    end
        | it cond s1 => match (beval cond sigma tau) with
                  |true => (eval s1 sigma tau n')
                  | false => sigma
                  end
        |while cond s =>  match (beval cond sigma tau) with
                  |true => eval (seq s (while cond s)) sigma tau n'
                  | false => sigma
                  end
          | for_loop s1 cond s2 s3 =>
          let sigma' := eval s1 sigma tau n' in (* Inițializare *)
          eval (while cond (seq s2 s3)) sigma' tau n' (* Transformare în while *)
         end
end.

Definition env3 := update env2 "y" 5.
Definition tau1 : Tau := fun  x => true.
Definition max1 := max "x" "y".
Compute (eval max1 env3 tau1 100) "max".

Inductive LP:=
| prop1 : string-> LP
| not : LP -> LP
| and : LP-> LP -> LP
| or : LP -> LP -> LP.



Fixpoint leval (phi : LP) (tau : Tau) : bool :=
match phi with
| prop1 p => tau p
| not phi' => negb (leval phi' tau)
| and phi1 phi2 => andb (leval phi1 tau) (leval phi2 tau)
| or phi1 phi2 => orb (leval phi1 tau) (leval phi2 tau)
end.


