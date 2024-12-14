Require Import String.
Open Scope string_scope.

Check "asdasf".

Inductive Exp :=
| num : nat -> Exp
| var : string -> Exp
| add : Exp -> Exp -> Exp
| sub : Exp -> Exp -> Exp
| div : Exp -> Exp -> Exp.


Coercion num : nat >-> Exp.
Coercion var : string >-> Exp.
Notation "A +' B" :=
  (add A B)
    (left associativity, at level 50).
Notation "A -' B" :=
  (sub A B)
    (left associativity, at level 50).
Notation "A /' B" :=
  (div A B)
    (left associativity, at level 40).

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


Reserved Notation "<| A , S |> => <| A' , S' |>" (at level 60).


Inductive aeval : Exp -> Env -> Exp -> Env -> Type :=
| lookup : forall v st, <| var v, st |> => <| st v , st |>
| add_1 : forall a1 a2 a1' st,
    <| a1 , st |> => <| a1' , st |> ->
    <| a1 +' a2 , st |> => <| a1' +' a2 , st |>
| add_2 : forall a1 a2 a2' st,
    <| a2 , st |> => <| a2' , st |> ->
    <| a1 +' a2 , st |> => <| a1 +' a2' , st |>
| s_add : forall i1 i2 st n,
    n = i1 + i2  ->
    <| i1 +' i2 , st |> => <| n , st |>
| sub_1 : forall a1 a2 a1' st,
    <| a1 , st |> => <| a1' , st |> ->
    <| a1 -' a2 , st |> => <| a1' -' a2 , st |>
| sub_2 : forall a1 a2 a2' st,
    <| a2 , st |> => <| a2' , st |> ->
    <| a1 -' a2 , st |> => <| a1 -' a2' , st |>
| s_sub : forall i1 i2 st n,
    i1>=i2 ->
    n = i1 - i2  ->
    <| i1 -' i2 , st |> => <| n , st |>
| div_1 : forall a1 a2 a1' st,
    <| a1 , st |> => <| a1' , st |> ->
    <| a1 /' a2 , st |> => <| a1' /' a2 , st |>
| div_2 : forall a1 a2 a2' st,
    <| a2 , st |> => <| a2' , st |> ->
    <| a1 /' a2 , st |> => <| a1 /' a2' , st |>
| s_div : forall i1 i2 st n,
    i2 <> 0 ->
    n = Nat.div i1  i2  ->
    <| i1 /' i2 , st |> => <| n , st |>
where "<| A , S |> => <| A' , S' |>" := (aeval A S A' S').

Definition env2 :=
  fun (x : string) => 10.


Example e1 : <|"x" -' 2, env2|> => <| 10 -' 2, env2 |>.
Proof.
  eapply sub_1.
apply lookup.
Qed.

Definition env3 :=
  fun (x : string) => 5.

Example e2 : <|15 -' "x", env3|> => <| 15 -' 5, env3 |>.
Proof.
  eapply sub_2.
apply lookup.
Qed.




Example e3 : <|"x" /' 2, env2|> => <| 10 /' 2, env2 |>.
Proof.
  eapply div_1.
apply lookup.
Qed.



Example e4 : <|15 /' "5", env3|> => <| 15 /' 5, env3 |>.
Proof.
  eapply div_2.
apply lookup.
Qed.

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

Reserved Notation "B ={ Sigma }=> B'"
         (at level 90). 

Coercion base : bool >-> Cond.


Reserved Notation "<[ B , S ]> -> <[ B' , S' ]>" (at level 90).
Print Cond.
Inductive beval : Cond -> Env -> Cond -> Env -> Type :=
| not : forall b b' s,
    <[ b , s ]> -> <[ b' , s ]> ->
    <[ ! b , s ]> -> <[ ! b' , s ]>
| not_true : forall s,
    <[ ! true , s ]> -> <[ false , s ]>
| not_false : forall s,
    <[ ! false , s ]> -> <[ true , s ]>
| or_1 : forall b1 b1' b2 s,
    <[ b1 , s ]> -> <[ b1' , s ]> ->
    <[ b1 |' b2 , s ]> -> <[ b1' |' b2 , s ]>
| or_true : forall b2 s,
    <[ true |' b2 , s ]> -> <[ true , s ]>
| or_false : forall b2 s,
    <[ false |' b2 , s ]> -> <[ b2 , s ]>
| lt_1 : forall a1 a2 a1' s,
    <|a1 , s |> => <| a1' , s |> ->
    <[ a1 <' a2 , s ]> -> <[ a1' <' a2 , s ]>
| lt_2 : forall (i1 : nat) a2 a2' s,
(<| a2 , s |> => <| a2' , s |>) ->
<[ i1 <' a2 , s ]> -> <[ i1 <' a2' , s ]>
| lt : forall (i1 i2 : nat) s b,
b = (if Nat.ltb i1 i2 then true else false) ->
<[ i1 <' i2 , s ]> -> <[ b , s ]>
| beq_1 : forall a1 a2 a1' s,
    <|a1 , s |> => <| a1' , s |> ->
    <[ a1 =' a2 , s ]> -> <[ a1' =' a2 , s ]>
| beq_2 : forall (i1 : nat) a2 a2' s,
(<| a2 , s |> => <| a2' , s |>) ->
<[ i1 =' a2 , s ]> -> <[ i1 =' a2' , s ]>
| bbeq : forall (i1 i2 : nat) s b,
b = (if Nat.eqb i1 i2 then true else false) ->
<[ i1 <' i2 , s ]> -> <[ b , s ]>

where "<[ B , S ]> -> <[ B' , S' ]>" := (beval B S B' S').


Example e5 : <[15 <' "x", update env0 "x" 3]> -> <[15 <' 3, update env0 "x" 3]>.
Proof.
apply lt_2.
apply lookup.
Qed.

Example e6 : <[ true |' false , env0 ]> -> <[true, env0]>.
apply or_true.
Qed.

Inductive Stmt :=
| skip : Stmt 
| assign : string -> Exp -> Stmt
| seq : Stmt -> Stmt -> Stmt
| ite : Cond -> Stmt -> Stmt -> Stmt (* if-then-else *)
| it  : Cond -> Stmt -> Stmt (* if-then *)
| dowhile : Stmt -> Cond -> Stmt.

Notation "S1 ; S2" := (seq S1 S2) (right associativity, at level 99).
Notation "X ::= A" := (assign X A) (at level 95).

Reserved Notation "<{ S , E }> => <{ S' , E' }>" (at level 90).


Inductive eval : Stmt -> Env -> Stmt -> Env -> Type :=
| eassign_1 : forall var a a' st,
    <| a , st |> => <| a' , st |> ->
    <{ var ::= a , st }> => <{ var ::= a' , st }>
| eassign_2 : forall var st st' n,
    st' = update st var n ->
    <{ var ::= n , st }> => <{ skip , st' }>
| eskip : forall s2 st,
    <{ skip ; s2 , st }> => <{ s2 , st }>
| eseq : forall s1 s1' s2 st st',
    <{ s1 , st }> => <{ s1' , st' }> ->
    <{ s1 ; s2 , st }> => <{ s1' ; s2 , st' }>
| eite_1 : forall b b' st s1 s2,
    <[ b , st ]> -> <[ b' , st ]> ->
    <{ ite b s1 s2 , st }> => <{ ite b' s1 s2 , st }>
| eite_true : forall s1 s2 st,
    <{ ite true s1 s2 , st }> => <{ s1 , st }>
| eite_false : forall s1 s2 st,
    <{ ite false s1 s2 , st }> => <{ s2 , st }>



where "<{ S , E }> => <{ S' , E' }>" := (eval S E S' E').





