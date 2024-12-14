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

Definition Env := string->nat.
Definition env1 : Env := fun (x : string) => 0.
Definition env2 :=
fun y =>
if (string_dec y "n")
then 10
else 0.

Definition update   (env : string->nat) (v : string) (n : nat)
                  : (string -> nat) :=
fun x => if eqb x v then n else (env x).



Check option.
Check option nat.
Print option.
Check (Some 2).
Check None.

(*ex1*)
Fixpoint aeval ( a: AExp) (e : Env) : option nat :=
match a with
| num n => Some (n)
| var x => Some(e x)
| add a1 a2 => match aeval a1 e with 
               | Some a1' => match aeval a2 e with
                             | Some a2' => Some( a1' + a2' )
                             | None => None
                              end
               | None => None
               end
|sub a1 a2 => match aeval a1 e with 
               | Some a1' => match aeval a2 e with
                             | Some a2' => if Nat.ltb a1' a2' then None else Some(a1'-a2')
                             | None => None
                              end
               | None => None
               end
|div a1 a2  => match aeval a1 e with
               |Some a1' => match aeval a2 e with 
                           | Some 0 => None
                           | Some a2' => Some(Nat.div a1' a2')
                           | None=>None
                           end 
               |None => None
               end
end.
Compute aeval (2 +' "n") env2.
Compute aeval (2 -' "n") env1.
Compute aeval(2/'5 +' (4/'(3+' 1/'0))) env2.
Compute aeval (4 +' "n" /' "n1" +' 4) env2.
Compute aeval (100 /' "n" +' "n" /' 100) env2.

Fixpoint beval
(b: Cond)
(e: Env) : option bool :=
match b with 
|base b' => Some(b')
|bnot b => match beval b e with
           |None=>None
           |Some b' => Some(negb b')
           end
|band b1 b2 => match beval b1 e with 
               | Some b1' => match beval b2 e with
                             | Some b2' => Some(andb b1' b2')
                             | None => None
                              end
               | None => None
               end
|beq b1 b2 =>  match aeval b1 e with 
               | Some b1' => match aeval b2 e with
                             | Some b2' => Some(Nat.eqb b1' b2')
                             | None => None
                              end
               | None => None
               end
              
|less b1 b2 => match aeval b1 e with 
               | Some b1' => match aeval b2 e with
                             | Some b2' => Some(Nat.ltb b1' b2')
                             | None => None
                              end
               | None => None
               end
end.

Compute beval ( 2<'3 |' 4='5-'10) env1. 
Compute beval ( "n">'10 &' 4 =' "n"/'2-'3/'3) env2.
Compute beval ("n" <=' "n" +' "n"-'10) env2.


Fixpoint eval (s : Stmt)
(e : Env) 
(fuel: nat): Env :=
match fuel with
|0 => e
|S n' => match s with
   | assign x a => match aeval a e with
                   |None => e
                   |Some val => update e x val
                   end
   | ite b s1 s2 => match beval b e with
                   |None => e
                   |Some val => if(beval b e) then (eval s1 e n') else (eval s2 e n')
                   end
   | skip => e
   | seq s1 s2 => eval s2 (eval s1 e n') n'
   | while b s => match beval b e with 
                  |None => e
                  |Some val => if (beval b e) then eval (seq s (while b s)) e n' else e
                   end
 end

end.

Compute (eval ("n" ::=10 ;; "i"::=100)env2 10) "i".


Definition env3 :=
fun y =>
if (string_dec y "a")
then 18
else if (string_dec y "b")
then 12
else 0.

Definition env4 :=
fun y =>
if (string_dec y "a")
then 11
else if (string_dec y "b")
then 5
else 0.

Definition gcd (x y : string) :=
 while(! x =' y) (
ite (x >' y) (x ::= x -' y) (y ::= y -' x)
);;
"result" ::=x.

Compute (eval (gcd "a" "b") env3 1000) "result".
Compute (eval (gcd "a" "b") env4 1000) "result".




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
Compute (update env1 "f" 9) "f".                    
Compute (eval (Fibonacci "f") (update env1 "f" 1) 1000)"result".

(*3*)
Inductive LExp : Type :=
| lbase : bool -> LExp
| lvar : string -> LExp
| lnot : LExp->LExp
| land : LExp -> LExp -> LExp
| lor : LExp -> LExp -> LExp.

Definition Assignment := string->bool.
Definition assign1 : Assignment:= fun (x : string) => false.
Definition assign2 :=
fun y =>
if (string_dec y "p")
then true
else false.
Compute assign2 "p".


Fixpoint leval ( a: LExp) (e : Assignment) : bool :=
match a with
| lbase b => b
| lvar x => e x
| lnot x => negb (leval x e)
| land a1 a2 => andb (leval a1 e) (leval a2 e)
|lor a1 a2 => orb (leval a1 e) (leval a2 e)
end.



