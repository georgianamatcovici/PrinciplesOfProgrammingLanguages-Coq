Require Import String.
Open Scope string_scope.

Check "asdasf".

Inductive AExp :=
| num : nat -> AExp
| var : string -> AExp
| add : AExp -> AExp -> AExp
| mul : AExp -> AExp -> AExp.


(* Coercions *)
Coercion num : nat >-> AExp.
Coercion var : string >-> AExp.
Notation "A +' B" :=
  (add A B)
    (left associativity, at level 50).
Notation "A *' B" :=
  (mul A B)
    (left associativity, at level 40).


(* Environment *)
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
Inductive aeval : AExp -> Env -> AExp -> Env -> Type:=
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
| mul_1 : forall a1 a2 a1' st,
<| a1 , st |> => <| a1' , st |> ->
<| a1 *' a2 , st |> => <| a1' *' a2 , st |>
| mul_2 : forall a1 a2 a2' st,
<| a2 , st |> => <| a2' , st |> ->
<| a1 *' a2 , st |> => <| a1 *' a2' , st |>
|s_mul : forall i1 i2 st n,
n = i1 * i2 ->
<| i1 *'  i2 , st |> => <| n , st |>
where "<| A , S |> => <| A' , S' |>" := (aeval A S A' S').

Example e1 :
<| 2 +' "n" , update env0 "n" 10 |> => <| 2 +' 10, update env0 "n" 10 |>.
Proof.
eapply add_2.
eapply lookup.
Qed.

Reserved Notation "<| A , S |> =>* <| A' , S' |>" (at level 60).
Inductive aeval_clos : AExp -> Env -> AExp -> Env -> Type :=
| a_refl : forall a st, <| a , st |> =>* <| a , st |>
| a_trans : forall a1 a2 a3 st,
(<| a1 , st |> => <| a2 , st |>) ->
<| a2 , st |> =>* <| a3 , st |> ->
<| a1 , st |> =>* <| a3 , st |>
where "<| A , S |> =>* <| A' , S' |>" := (aeval_clos A S A' S').


Example e2 :
<| 2 +' "n" , update env0 "n" 10 |> =>* <| 12 , update env0 "n" 10 |> .
Proof.
- eapply a_trans with (a2 := 2 +' 10).
+ eapply add_2.
-- eapply lookup.
+ eapply a_trans.
-- eapply s_add. eauto.
-- simpl. eapply a_refl.
Qed.


Inductive BExp :=
| btrue : BExp
| bfalse : BExp
| band : BExp -> BExp -> BExp
| bnot : BExp -> BExp
| blt : AExp -> AExp -> BExp.


Notation "B1 &&' B2" :=
  (band B1 B2) (left associativity,
      at level 65).
Notation "!' B" :=
  (bnot B) (at level 62).
Notation "A1 <' A2" :=
  (blt A1 A2)
    (at level 60).



Reserved Notation "<| B , S |> -> <| B' , S' |>" (at level 90).
Print BExp.
Inductive beval : BExp -> Env -> BExp -> Env -> Type :=
| not : forall b b' s,
    <| b , s |> -> <| b' , s |> ->
    <| !' b , s |> -> <| !' b' , s |>
| not_true : forall s,
    <| !' btrue , s |> -> <| bfalse , s |>
| not_false : forall s,
    <| !' bfalse , s |> -> <| btrue , s |>
| and_1 : forall b1 b1' b2 s,
    <| b1 , s |> -> <| b1' , s |> ->
    <| b1 &&' b2 , s |> -> <| b1' &&' b2 , s |>
| and_false : forall b2 s,
    <| bfalse &&' b2 , s |> -> <| bfalse , s |>
| and_true : forall b2 s,
    <| btrue &&' b2 , s |> -> <| b2 , s |>
| lt_1 : forall a1 a2 a1' s,
    <| a1 , s |> -> <| a1' , s |> ->
    <| a1 <' a2 , s |> -> <| a1' <' a2 , s |>
where "<| B , S |> -> <| B' , S' |>" := (beval B S B' S').


