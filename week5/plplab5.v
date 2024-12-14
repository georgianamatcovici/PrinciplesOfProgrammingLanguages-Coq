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

Definition Env := string->nat.
Definition env1 : Env := fun (x : string) => 0.
Definition env2 :=
fun y =>
if (string_dec y "n")
then 10
else 0.

Definition update (env : Env) (x: string) (v:nat) : Env :=
fun y =>
if (string_dec x "y")
then v
else env y.

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

(*ex2*)

Inductive Cond :=
| base : bool -> Cond
| bnot : Cond -> Cond
| beq  : AExp -> AExp -> Cond
| less : AExp -> AExp -> Cond
| band : Cond -> Cond -> Cond.

Inductive Stmt :=
| skip : Stmt 
| assign : string -> AExp -> Stmt
| seq : Stmt -> Stmt -> Stmt
| ite : Cond -> Stmt -> Stmt -> Stmt (* if-then-else *)
| while : Cond -> Stmt -> Stmt.



Notation " x <' y" := (less x y) (at level 80).
Notation " x =' y" := (beq x y) (at level 80).
Notation "! x " := (bnot x) (at level 81).
Notation " x &' y" := (band x y) (at level 82).
Notation " x |' y" := (bnot (band (bnot x) (bnot y))) (at level 82).
Notation " x >' y" := (band (bnot(less x y)) (bnot( beq x y))) (at level 80).
Notation " x <=' y" := (bnot (band(bnot (less x y))(bnot(beq x y)))) (at level 80).
Notation " x >=' y" := (bnot (less x y)) (at level 80).

Print Nat.ltb.
Check option.
Check option bool.

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
Compute beval ( 2<'3 |' 4='5-'10).

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

Definition gcd (x y : string) :=
 while(! x =' y) (
ite (x >' y) (x ::= x -' y) (y ::= y -' x)
);;
"result" ::=x.


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

Compute (eval (fibo "f") (update env "f" 1) 1000)"response".
Compute (eval (fibo "f") (update env "f" 2) 1000)"response".



