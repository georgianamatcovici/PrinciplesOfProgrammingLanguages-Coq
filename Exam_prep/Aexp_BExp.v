Require Import String.
Require Import Nat.
(* Check "a". throws 'Error: No interpretation for string "a".' *)
Open Scope string_scope.
Check "a".
Check  "".
Check "abcb".
Definition Env' := string -> option nat.
Definition sigma1 :=
fun x => if( string_dec x "x") 
         then Some 10
         else None.

Definition update(env: Env')(var: string)(val: option nat) :=
fun x => if(string_dec x var)
         then val
         else env x.
Compute update sigma1 "x" (Some 10) "y".
Inductive AExp :=
| avar : string -> AExp
| anum : nat -> AExp
| aplus : AExp -> AExp -> AExp
| asub : AExp -> AExp ->AExp
| amul : AExp -> AExp -> AExp
| adiv : AExp -> AExp ->AExp
| amod : AExp -> AExp ->AExp.

Definition add (n m : option nat) : option nat :=
match (n, m) with
|(None, _) => None
| (_, None) => None
| (Some a, Some b) => (Some (a+b))
end.

Definition sub (n m : option nat) : option nat :=
  match n, m with
  | None, _ => None
  | _, None => None
  | Some a, Some b => if ( Nat.ltb a b)
                      then None
                      else Some (a - b)
  end.

Definition mul (n m : option nat) : option nat :=
match (n, m) with
|(None, _) => None
| (_, None) => None
| (Some a, Some b) => (Some (a*b))
end.

Definition div (n m : option nat) : option nat :=
  match n, m with
  | None, _ => None
  | _, None => None
  | Some a, Some b => if ( Nat.eqb b 0)
                      then None
                      else Some (Nat.div a b)
  end.

Definition mod_option (n m : option nat) : option nat :=
  match n, m with
  | None, _ => None
  | _, None => None
  | Some a, Some b => if Nat.eqb b 0
                      then None
                      else Some (Nat.modulo a b)
  end.

Fixpoint aeval' (a : AExp) (sigma : Env') : option nat :=
match a with 
| avar x => sigma x
| anum n => Some n
| aplus a b => add( aeval' a sigma ) ( aeval' b sigma)
| amul a b => mul( aeval' a sigma ) ( aeval' b sigma)
| asub a b => sub( aeval' a sigma ) ( aeval' b sigma)
| adiv a b => div( aeval' a sigma ) ( aeval' b sigma)
| amod a b => mod_option ( aeval' a sigma ) ( aeval' b sigma)
end.

Compute aeval' (asub (adiv (anum 8) (anum 4)) (amod(anum 9) (anum 8))).

Inductive BExp :=
| btrue : BExp
| bfalse : BExp
| band : BExp->BExp->BExp
| bnot : BExp -> BExp
| blt : AExp->AExp->BExp.

Definition option_and (a b : option bool) : option bool :=
match (a, b) with
| (None, _) => None
|( _, None) => None
| (Some a', Some b') => Some (andb a' b')
end.


Definition option_not (b : option bool) : option bool :=
match b with
| None => None
| Some b' => Some (negb b')
end.

Definition option_lt (a b : option nat) : option bool :=
match (a, b) with
| (None, _) => None
|( _, None) => None
| (Some a', Some b') => Some (Nat.ltb a' b')
end.

Fixpoint beval (b : BExp) (env : Env') : option bool :=
match b with
|bfalse => Some false
|btrue => Some true
|band b1 b2 => option_and (beval b1 env) (beval b2 env)
|bnot b' => option_not (beval b' env)
|blt a1 a2 => option_lt (aeval' a1 env) (aeval' a2 env)
end.




Inductive Stmt :=
| assign : string -> AExp -> Stmt
| ite : BExp -> Stmt -> Stmt -> Stmt
| while : BExp -> Stmt -> Stmt
| skip : Stmt
| seq : Stmt -> Stmt -> Stmt.

Fixpoint eval( s: Stmt) (env : Env')(fuel: nat) : Env' :=
match fuel with 
| O => env
| S fuel'=> match s with
            |skip => env
            |seq s1 s2 => eval s2 ( eval s1 env fuel') fuel'
            |assign var aexp => update env var (aeval' aexp env)
            |ite cond s1 s2 => match (beval cond env) with
                   |None => env
                   |Some true => eval s1 env fuel'
                   | Some false => eval s2 env fuel'
                   end
            |while cond s => match (beval cond env) with
                 |None => env
                 |Some true => eval (seq s (while cond s)) env fuel'
                 |Some false => env
                 end
         end
end.