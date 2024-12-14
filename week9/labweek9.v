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



(*ex1*)
Reserved Notation "A --> V"  (at level 60).
Inductive eval_ss : E -> E -> Prop :=
| const : O --> O
| succ : forall e e',
e --> e' ->
(S e) --> S e'
| isZero_O :
    isZero O --> T
| isZero_succ : forall e,
    isZero (S e) --> F
| isZero_ss : forall e e',
    e --> e' -> 
    isZero e --> isZero e'
| true_ss :
    T --> T
| false_ss : 
    F --> F
| ite_true : forall e1 e2,
    ite T e1 e2 --> e1
| ite_false : forall e1 e2,
    ite F e1 e2 --> e2
| ite_ss : forall e e' e1 e2,
    e --> e' ->
    ite e e1 e2 --> ite e' e1 e2
where "A --> V" := (eval_ss A V).



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

(*
         



                     .
              ---------------- TZero
                   O : Nat 
           -------------------- TSucc
                  S(O) : Nat
           -------------------- TSucc
                S(S(O)) : Nat
        ---------------------------- TisZero
            isZero(S(S O))  : Bool


*)

Example e2:
type_of ( ite T O (S(O))) Nat.
Proof.
eapply t_Ite.
- apply t_true.
- apply t_zero.
-apply t_succ. apply t_zero.
Qed.

(*                                           .
                                           ----- TZero
       .                  .                O:Nat
      ------ TTrue       ------TZero      --------- TSucc
      T:Bool             O: Nat          S(O) : Nat
      -------------------------------------------------TIte
        ite T O (S(O)) : Nat


*)




(*ex4*)

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

Theorem preservation :
forall e T e',
type_of e T ->
e --> e' ->
type_of e' T.
Proof.
intros e T e' H H0. revert e' H0.
induction H; intros t' H'; inversion H'; subst; eauto with types.
Qed.



Theorem progress :
forall e T ,
type_of e T ->
value e \/ exists e', e --> e'.
Proof.
intros t T  H . induction H; eauto with types.
- left. apply v_zero.
- destruct IHtype_of as [Ha1 | [t' Ha1 ]]; eauto with types. apply zero_canonical in H; auto.
inversion H; eauto with types.
+right. exists (S O). apply succ. apply const.
+right. exists (S t'). apply succ. apply Ha1.
- destruct IHtype_of as [Hb | [t' Hb]]; eauto with types.
apply zero_canonical in H ; auto.
inversion H ; eauto with types.
+right. exists T. apply isZero_O.
+right. exists (isZero t'). apply isZero_ss. exact Hb.
-left. apply v_true.
-left. apply v_false.
- destruct IHtype_of1 as [Hb | [t' Hb]]; eauto with types.
destruct IHtype_of2 as [Hb1 | [t' Hb1]]; eauto with types.
destruct IHtype_of3 as [Hb2 | [t' Hb2]]; eauto with types.
++destruct Hb.
+++inversion H.
+++right. exists e3. apply ite_true.
+++right. exists e4. apply ite_false.
++ destruct Hb.
+++ inversion H.
+++ right. exists e3. apply ite_true.
+++ right. exists e4. apply ite_false.
++destruct Hb.
+++ inversion H.
+++ right. exists e3. apply ite_true.
+++ right. exists e4. apply ite_false.
++ right. exists (ite t' e3 e4). apply ite_ss. exact Hb.
Qed.

Reserved Notation "A -->* A'" (at level 60).
Inductive eval_clos : E -> E -> Prop :=
| refl : forall a, a -->* a
| tran : forall  a1 a2 a3, 
a1 --> a2 ->
a2 -->* a3 ->
a1 -->* a3
where "A -->* A'" := (eval_clos A A').

Corollary soundness :
forall t t' T,
type_of t T ->
t-->* t' ->
value t' \/ exists t'', t'-->t''.
Proof.
intros t t' T H S.
induction S.
--apply progress in H; eauto.
--apply IHS. eapply preservation; eauto.
Qed.


