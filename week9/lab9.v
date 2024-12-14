Require Import String.
Require Import Nat.
(* Check "a". throws 'Error: No interpretation for string "a".' *)
Open Scope string_scope.
Check "a".
Check  "".
Check "abcb".

Inductive E :=
| O : E
| S : E -> E
| isZero : E -> E
| T : E
| F : E
| ite : E -> E -> E -> E.

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

(*ex1*)
Reserved Notation "A -[ S ]-> V"  (at level 60).
Inductive eval_ss : E -> Env -> E -> Prop :=
| const : forall env, O -[ env ]-> O
| succ : forall env e e',
e -[ env ]-> e' ->
(S e) -[env]-> S e'
| isZero_O : forall env,
    isZero O -[ env ]-> T
| isZero_succ : forall env e,
    isZero (S e) -[ env ]-> F
| isZero_ss : forall env e e',
    e -[ env ]-> e' -> 
    isZero e -[ env ]-> isZero e'
| true_ss : forall env,
    T -[ env ]-> T
| false_ss : forall env,
    F -[ env ]-> F
| ite_true : forall env e1 e2,
    ite T e1 e2 -[ env ]-> e1
| ite_false : forall env e1 e2,
    ite F e1 e2 -[ env ]-> e2
| ite_ss : forall env e e' e1 e2,
    e -[ env ]-> e' ->
    ite e e1 e2 -[ env ]-> ite e' e1 e2
where "A -[ S ]-> V" := (eval_ss A S V).



(*ex2*)
(*        .
TZero ------------
        O : Nat

         e : Nat
TSucc -------------
        S e : Nat


         e : Nat
TisZero -------------
        isZero e : Bool

           .
TTrue -------------
        T : Bool

           .
TFalse -------------
        F : Bool

      c:Bool e1:Nat e2:Nat
TIte ------------------------
        ite c e1 e2 : Nat


*)
(*ex3*)
Inductive Typ: Type :=
| Bool : Typ
| Nat : Typ.

Inductive type_of : E -> Typ -> Prop :=
| t_zero : type_of(O) Nat
| t_succ : forall e,
(type_of e Nat) ->
(type_of (S e) Nat)
| t_isZero : forall e,
(type_of e Nat) ->
(type_of (isZero e) Bool)
| t_true : 
type_of (T) Bool
| t_false : 
type_of (F) Bool
| t_Ite : forall c e1 e2,
(type_of c Bool) ->
(type_of e1 Nat) ->
(type_of e2 Nat) ->
(type_of (ite c e1 e2) Nat)
.

Example e1: 
  type_of (isZero (S (S O))) Bool.
Proof.
eapply t_isZero.
eapply t_succ.
eapply t_succ.
eapply t_zero.
Qed.
(*e2 ...*)

Inductive value : E -> Prop :=
| v_zero : value O
| v_true : value T
| v_false : value F.


Lemma zero_canonical : forall e,
type_of e Nat -> value e -> e = O.
Proof.
intros e Htyp Hval.
inversion Htyp; subst.
- reflexivity.
- inversion Hval.
- inversion Hval.
Qed.

Lemma bool_canonical : forall e,
  type_of e Bool ->
  value e ->
  e = T \/ e = F.
Proof.
intros e Htyp Hval.
inversion Htyp; subst.
- inversion Hval.
- left; reflexivity. 
- right; reflexivity.
Qed.

Create HintDb types.
Hint Constructors type_of : types.

Theorem progress :
forall t T state,
type_of t T ->
value t \/ exists t', t -[ state ]-> t'.
Proof.
intros t T state H .
induction H .
- left. constructor.  

- destruct IHtype_of as [Hval | [t' Hstep]]; eauto with types.
+  right. inversion Hval.
-- exists (S O). apply succ. apply const.
-- exists (S T). apply succ. apply true_ss.
-- exists (S F). apply succ. apply false_ss.
+ right. exists (S t'). apply succ. apply Hstep.
- destruct IHtype_of as [Hval | [t' Hstep]]; eauto with types. inversion Hval.



