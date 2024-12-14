Require Import String.
Open Scope string_scope.

(* mapping string |-> nat *)
Definition Env := string -> nat.
Definition update
           (env : string -> nat)
           (x   : string)
           (v   : nat) :
  (string -> nat) :=

  fun y => if eqb y x
           then v
           else (env y).

(* arithmetic expressions *)
Inductive Exp :=
| num : nat -> Exp
| var : string -> Exp
| add : Exp -> Exp -> Exp
| sub : Exp -> Exp -> Exp
| div : Exp -> Exp -> Exp.


Coercion var : string >-> Exp.
Coercion num : nat >-> Exp.
Notation "A +' B" := (add A B)
                      (at level 50,
                        left associativity).
Notation "A -' B" := (sub A B)
                      (at level 50,
                        left associativity).
Notation "A /' B" := (div A B)
                      (at level 40,
                        left associativity).

(* 

                   .
Const --------------------------
       < i , sigma > => < i >

                   .
Var  --------------------------
       < x , sigma > => < sigma(x) >

      <a1, sigma> => i1   <a2, sigma> => i2 
Add ---------------------------------------
        <a1 +' a2, sigma> => <i1 + i2>

      <a1, sigma> => i1   <a2, sigma> => i2    i1>=i2 
Sub ---------------------------------------------------
        <a1 -' a2, sigma> => <i1 - i2>

      <a1, sigma> => i1   <a2, sigma> => i2    i2 != 0
Div ---------------------------------------------------
        <a1 /' a2, sigma> => <i1 / i2>

*)

Reserved Notation "A =[ S ] => N" (at level 60).

Print Exp.

Compute (true = Nat.ltb 1 1).

Inductive eval_expressions : Exp -> Env -> nat -> Prop :=
| Const : forall i sigma, num i =[sigma] => i
| Var : forall x sigma, var x =[sigma] => sigma x
| Add: forall a1 a2 i1 i2 sigma n,
  a1 =[sigma] => i1 ->
  a2 =[sigma] => i2 ->
  n  = i1 + i2 ->
  a1 +' a2 =[sigma] => n
| Sub: forall a1 a2 i1 i2 sigma n,
  a1 =[sigma] => i1 ->
  a2 =[sigma] => i2 ->
  i1 >= i2 ->
  n  = i1 - i2 ->
  a1 -' a2 =[sigma] => n
| Div: forall a1 a2 i1 i2 sigma n,
  a1 =[sigma] => i1 ->
  a2 =[sigma] => i2 ->
  i2 <> 0 ->
  n  = (Nat.div i1 i2) ->
  a1 /' a2 =[sigma]=> n
where "A =[ S ] => N" := (eval_expressions A S N).

Inductive Cond :=
| base : bool -> Cond
| bnot : Cond -> Cond
| beq  : Exp -> Exp -> Cond 
| less : Exp -> Exp -> Cond
| band : Cond -> Cond -> Cond.

Compute (false = ( Nat.eqb 4 5 )).
Compute ( true = (Nat.ltb 12 3)).
Notation "! A" := (bnot A) (at level 70).
Notation "A =' B " := (beq A B)(at level 65).
Notation "A &&' B" := (band A B) (at level 76, left associativity).
Notation "A <' B" := (less A B) (at level 65).
(*
  Notation "A >' B" := (band (bnot(less A B)) (bnot (eq A B)) ) (at level 65).
*)

(*                 .
base --------------------------
       < base b , sigma > => b

      <b, sigma> => <true>
bnotF -----------------------------------------
        <!b, sigma> => <true>


      <b, sigma> => <true> 
bnotT -----------------------------------------
        <!b, sigma> => <false>

      <b1, sigma> => <false> 
bandF -----------------------------------------
        <b1 and b2, sigma> => <false>

      <b1, sigma> => <true> <b2,sigma> => <b'> 
bandT -----------------------------------------
        <b1 and b2, sigma> => <b'>

      <exp1, sigma> => <i1> <exp2,sigma> => <i2> b = (Nat.eqb i1 i2) 
beq -------------------------------------------------------------------
        <exp1 =' exp2, sigma> => <b>


          <a1, sigma> => i1   <a2, sigma> => i2   b = (Nat.ltb i1 i2) 
lessThan --------------------------------------------------------------
          <a1 <' a2, sigma> => <b>

*)

Reserved Notation "B ={ Sigma }=> B'"
         (at level 90). 


Inductive bool_evaluations :
  Cond -> Env -> bool -> Prop :=
| Base : forall sigma b, base b ={ sigma }=> b
| NotT : forall b sigma,
    b ={sigma}=> true ->
    bnot b ={sigma}=> false 
| NotF : forall b sigma,
    b ={sigma}=> false ->
    bnot b ={sigma}=> true
| AndT : forall b1 b2 sigma b,
   b1 ={sigma}=> true ->
   b2 ={sigma}=> b ->
   b1 &&' b2 ={sigma}=> b
| AndF : forall b1 b2 sigma,
   b1 ={sigma}=> false ->
   b1 &&' b2 ={sigma}=> false
| Beq : forall exp1 exp2 sigma i1 i2 b,
   exp1 =[sigma]=> i1 ->
   exp2 =[sigma]=> i2 ->
   b = Nat.eqb i1 i2 ->
   exp1 =' exp2 ={sigma}=>b
| lessThan : forall exp1 exp2 i1 i2 b sigma, 
  exp1 =[sigma]=> i1 ->
  exp2 =[sigma]=> i2 ->
  b  = (Nat.ltb i1 i2) ->
  exp1 <' exp2 ={sigma}=> b 
where "B ={ Sigma }=> B'" := (bool_evaluations B Sigma B').

Definition Env1 := update (fun x => 0) "n" 10.
Compute Env1 "n1".


Create HintDb mydb_of_tactics.
#[local] Hint Constructors eval_expressions : mydb_of_tactics.
#[local] Hint Unfold Env1 : mydb_of_tactics.
#[local] Hint Unfold update : mydb_of_tactics.
#[local] Hint Unfold not : mydb_of_tactics.

(* EXEMPLE EVALUARE EXPRESII *)

Example eval_1: (* Derivare num*)
123 =[ Env1 ] => 123.
Proof.
  - eapply Const.
Qed.

Definition Env2 := update (update ( fun x => 100) "x2" 20) "x12" 120. (* In Env2 x2 = 20; x12 = 120 *)
Compute Env2 "n1".
Compute Env2 "x2".

#[local] Hint Unfold Env2 : mydb_of_tactics.

Example eval_2: (*Derivare var*)
"n" =[ Env2 ] => 100.
Proof.
  eapply Var.
Qed.

Example eval_3: (*Derivare add*)
("x1" +' "x2") =[ Env2 ] => Env2 "x12".
Proof.
  - eapply Add.
  -- eapply Var.
  -- eapply Var.
  -- unfold Env2. unfold update. simpl. trivial.
Qed.

Compute negb ( Nat.ltb 2 (Env2 "x")).

Compute negb (Nat.ltb 120 12).
Locate ">=".
Print "<=".
Compute le_S 2 3.

Example eval_4_1: (*Derivare sub*)
(122 -' "x12") =[ Env2 ] => 2.
Proof.
  - eapply Sub.
    -- apply Const.
    -- apply Var.
    -- unfold Env2. unfold update. simpl. unfold ge. apply le_S. apply le_S. apply le_n.
    -- simpl. trivial.
Qed.
Example eval_4_2: (*Derivare sub*)
(200 -' "x12") =[ Env2 ] => 80.
Proof.
  - eapply Sub.
    -- apply Const.
    -- apply Var.
    -- unfold Env2. unfold update. simpl. unfold ge. apply le_S. eauto 80. (* Normal, ar trebui sa aplicam le_S de 80 de ori*)
    -- simpl. trivial.
Qed.
Example eval_4_3: (*Derivare sub*)
(140 -' ("x2" +' "x12") -' 0) =[ Env2 ] => 0.
Proof.
  - eapply Sub.
    -- eapply Sub.
      --- eapply Const.
      --- eapply Add.
          ---- eapply Var.
          ---- eapply Var.
          ---- trivial.
      --- unfold Env2. unfold update. simpl. apply le_n. (* sau eauto. *)
      --- simpl. trivial.
    -- eapply Const.
    -- eauto.
    -- simpl. trivial.
Qed.

Definition Env3 := update (update ( fun x => 100) "2" 2) "n" 10.

#[local] Hint Unfold Env3 : mydb_of_tactics.

Example eval_4_4: (*Derivare sub*)
(200 -' "x12") =[ Env2 ] => 80.
Proof.
eauto 100 with mydb_of_tactics.
Qed.

Example eval_5: (*Derivare div*)
(140 /' 2 /'"2") =[ Env3 ] => 35.
Proof.
  - eapply Div.
    -- eapply Div.
      --- eapply Const.
      --- eapply Const.
      --- unfold not. intros H1. inversion H1.
      --- simpl. trivial.
    -- eapply Var.
    -- unfold Env3. unfold update. simpl. unfold not. intros H1. inversion H1.
    -- simpl. trivial.
Qed.


#[local] Hint Constructors Cond : mydb_of_tactics.

 (* EXPRESII EVALUARE CONDITII*)

Example beval_1: (*Derivare NotT+EQ*)
 (! 1 =' 1) ={ Env2 }=> false.
Proof.
  eapply NotT.
  eapply Beq.
   - eapply Const.
   - eapply Const.
   - simpl. trivial.
Qed.

Example beval_2: (*Derivare NotT+EQ+BandF*)
 (! "x12" =' 120 &&' 2='2 ) ={ Env2 }=> false.
Proof.
  eapply AndF.
  eapply NotT.
  eapply Beq.
    - eapply Var.
    - eapply Const.
    - simpl. trivial.
Qed.

Example beval_3: (*Derivare NotF+EQ+Less+BandT*)
 (! "x12" =' 10 &&' 130-'"x12" <' 30/'2 ) ={ Env2 }=> true.
Proof.
  eapply AndT.
    - eapply NotF. eapply Beq.
      -- eapply Var.  
      -- eapply Const.
      -- simpl. trivial.
    - eapply lessThan.
      -- eapply Sub.
          --- eapply Const.
          --- eapply Var.
          --- unfold ge. unfold Env2. unfold update. simpl. eauto 11.
          --- simpl. trivial.
      -- eapply Div.
          --- apply Const.
          --- apply Const.
          --- unfold not. intros H1. inversion H1.
          --- simpl. trivial.
      -- unfold Nat.ltb. unfold Nat.leb. trivial.
Qed.

#[local] Hint Constructors bool_evaluations : mydb_of_tactics.
#[local] Hint Unfold Nat.ltb : mybd_of_tactics.
#[local] Hint Unfold Nat.leb : mybd_of_tactics.


Example beval_3_1: (*Derivare NotF+EQ+Less+BandT*)
 (! "x12" =' 10 &&'  !130-'"x12" <' 30/'2/'2 ) ={ Env2 }=> true.
Proof.
eauto 20 with mydb_of_tactics.
Qed.

(* Statements *)

Inductive Stmt :=
| skip : Stmt 
| assign : string -> Exp -> Stmt
| seq : Stmt -> Stmt -> Stmt
| ite : Cond -> Stmt -> Stmt -> Stmt (* if-then-else *)
| it  : Cond -> Stmt -> Stmt (* if-then *)
| dowhile : Stmt -> Cond -> Stmt
| forr : Stmt -> Cond -> Stmt -> Stmt -> Stmt 
(* forr ( i=1, j=2) (i<n) (i=i+1) (
  //codd
)*)
.


(*
                  .
Skip ----------------------------
       < skip , sigma > => sigma   //nu se modifica cu nimic environmentul

                     <x,sigma> => <i>
Assign -------------------------------------------
        <x ::= a, sigma> => <update sigma x i>


      <s1, sigma> => <s1>  <s2,sigma1> => <sigma2> 
Seq ----------------------------------------------
        <s1;;s2, sigma> => <sigma2>

            <c, sigma> => <true> <s1,sigma> => sigma2
iteT -------------------------------------------------
               <ite c s1 s2, sigma> => <sigma2>


            <c, sigma> => <false> <s2,sigma> => sigma2
iteF -------------------------------------------------
                <ite c s1 s2, sigma> => <sigma2>

            <c, sigma> => <true> <s1,sigma> => sigma2
itT -------------------------------------------------
                <ite c s1, sigma> => <sigma2>

            <c, sigma> => <false>
itF -------------------------------------------------
                <ite c s1, sigma> => <sigma>

            <c, sigma> => <false> 
whileF -------------------------------
        <while c s, sigma> => <sigma>


            <c, sigma> => <true> <s ;; while c s, sigma> => <sigma2> 
whileT --------------------------------------------------------------
                  <while c s, sigma> => <sigma2>

            <s, sigma> => <sigma2>  <c, sigma2> => <false> 
doWhileF --------------------------------------------------
                  <dowhile s C, sigma> => <sigma2>

            <s, sigma> => <sigma2> <c, sigma2> => <true> <dowhile s c,sigma2> => sigma3 
doWhileT -------------------------------------------------------------------------------
                  <dowhile s C, sigma> => <sigma3>

        <s1,sigma> => <sigma2> <cond, sigma2> => false   //deci daca conditia din for nu este adevarata, atunci env final nu va avea modificarile din s1
forF_1  -------------------------------------------------- //daca conditia este de la prima iteratie false

         <cond, sigma> => false   //deci daca conditia din for nu este adevarata, atunci env final nu va avea modificarile din s1
forF_2  -------------------------------------------------- //daca conditia este de la o iteratie >1 false
          (forr s1 cond s2 s3, sigma) => <sigma>

      <s1, sigma> => sigma2   <cond, sigma2> => true  <s3,sigma2> => sigma3  <s2,sigma3> => sigma4 <(forr s1 cond s2 s3),sigma4> => sigma5  //s2 se va executa la final
forT_1 ----------------------------------------------------------------------------------------------
      <forr s1 cond s2 s3 , sigma> => sigma5

       <cond, sigma> => true  <s3,sigma> => sigma2  <s2,sigma2> => sigma3  <(forr s1 cond s2 s3),sigma3> => sigma4 //s1 nu se va mai executa
forT_2 --------------------------------------------------------------------------------------------------------------
      <forr s1 cond s2 s3 , sigma> => sigma3

*)
Notation "S1 ;; S2" := (seq S1 S2) (right associativity, at level 99).
Notation "X ::= A" := (assign X A) (at level 95).

Reserved Notation "S1 =|| Sigma ||=> Sigma'"
         (at level 99).


Inductive statements_eval : Stmt -> Env -> Env -> Prop :=
| Skip     :  forall sigma,
               ( skip ) =|| sigma ||=> sigma
| Assign   :   forall sigma sigma1 var exp1 i1,
               exp1 =[ sigma ]=> i1 
            -> sigma1 = update sigma var i1
            -> (var ::= exp1) =|| sigma ||=> sigma1
| Seq      :   forall sigma1 sigma2 sigma s1 s2,
               s1 =|| sigma ||=> sigma1
            -> s2 =|| sigma1 ||=> sigma2
            -> (s1 ;; s2) =|| sigma ||=> sigma2
| iteT     :   forall cond1 s1 s2 sigma sigma1,
               cond1 ={ sigma }=> true
            -> s1 =|| sigma ||=> sigma1
            -> ( ite cond1 s1 s2) =|| sigma ||=> sigma1
| iteF     :   forall cond1 s1 s2 sigma sigma1,
               cond1 ={ sigma }=> false
            -> s2 =|| sigma ||=> sigma1
            -> ( ite cond1 s1 s2) =|| sigma ||=> sigma1
| itT      :   forall cond1 s1 sigma sigma1,
               cond1 ={ sigma }=> true
            -> s1 =|| sigma ||=> sigma1
            -> (it cond1 s1) =|| sigma ||=> sigma1
| itF      :  forall cond1 s1 sigma,
              cond1 ={ sigma }=> false
            -> (it cond1 s1) =|| sigma ||=> sigma
| doWhileF :  forall s1 cond1 sigma sigma1,
              s1 =|| sigma ||=> sigma1
            -> cond1 ={ sigma1 }=> false
            -> (dowhile s1 cond1) =|| sigma ||=> sigma1
| doWhileT :  forall s1 cond1 sigma sigma1 sigma2,
              s1 =|| sigma ||=> sigma1
            -> cond1 ={ sigma1 }=> true
            -> (dowhile s1 cond1) =|| sigma1 ||=> sigma2
            -> (dowhile s1 cond1) =|| sigma ||=> sigma2
| forF_1   : forall sigma sigma2 s1 cond s2 s3,
              s1 =|| sigma ||=> sigma2
            -> cond ={ sigma2 }=> false
            -> (forr s1 cond s2 s3) =|| sigma ||=> sigma
| forF_2   : forall sigma s1 cond s2 s3,
             cond ={ sigma }=> false
            -> (forr s1 cond s2 s3) =|| sigma ||=> sigma
|forT_1    : forall sigma sigma2 sigma3 sigma4 sigma5 s1 cond s2 s3,
              s1 =|| sigma ||=> sigma2
            -> cond ={ sigma2 }=> true
            -> s3 =|| sigma2 ||=> sigma3
            -> s2 =|| sigma3 ||=> sigma4
            -> (forr s1 cond s2 s3) =|| sigma4 ||=> sigma5
            -> (forr s1 cond s2 s3) =|| sigma ||=> sigma5
|forT_2    : forall sigma sigma2 sigma3 sigma4 s1 cond s2 s3,
              cond ={ sigma }=> true
            -> s3 =|| sigma ||=> sigma2
            -> s2 =|| sigma2 ||=> sigma3
            -> (forr s1 cond s2 s3) =|| sigma3 ||=> sigma4
            -> (forr s1 cond s2 s3) =|| sigma ||=> sigma4
where "S =|| sigma ||=> sigma2" := (statements_eval S sigma sigma2).

Definition Env4 := update (update ( fun x => 0) "x1" 10) "x2" 20.

Definition Env5 := update (update Env4 "x1" 20) "x2" 10.

#[local] Hint Constructors statements_eval : mydb_of_tactics.

Example eeval_1 : (*Assign + Seq*)
("x1" ::=20;;
"x2" ::=10) =|| Env4 ||=> Env5.
Proof.
(*eauto with mydb_of_tactics.*)
eapply Seq.
  -eapply Assign.
    -- eapply Const.
    -- trivial.
  -eapply Assign.
    -- eapply Const.
    -- trivial.
Qed.

Example eeval_2 : (*Assign + Seq + it + ite + skip*)
(ite ( 3=' 4)
   ( "i" ::= 20 )
    ( skip );;
 it ( ! "i" <' 20-10 )
    ("i" ::= "i"-'10)
) =|| Env4 ||=> Env4.
Proof.
(*eauto 10 with mydb_of_tactics.*)
  eapply Seq.
  - eapply iteF.
    -- eapply Beq.
        --- eapply Const.
        --- eapply Const.
        --- simpl. trivial.
    -- eapply Skip.
  - eapply itF. eapply NotT. eapply lessThan.
    -- eapply Var.
    -- simpl. eapply Const.
    -- unfold Env4. unfold update. simpl. trivial.
Qed.  


Example eeval_3 : (*ALL*)
(
  "i" ::= 1;;
  "n" ::= 2;;
  dowhile (
    "i" ::= "i" +' 1
  )
  ("i" <' "n")
) =|| Env4 ||=> (update (update ( update Env4 "i" 1) "n" 2) "i" 2).
Proof.
(*eauto 10 with mydb_of_tactics.*)
  eapply Seq.
  - eapply Assign.
      -- eapply Const.
      -- trivial.
  - eapply Seq.
    -- eapply Assign.
        --- eapply Const.
        --- trivial.
    -- eapply doWhileF.
        --- eapply Assign.
                ---- eapply Add.
                  ----- eapply Var.
                  ----- eapply Const.
                  ----- simpl. trivial.
                ---- trivial.
        --- eapply lessThan.
                ---- eapply Var.
                ---- eapply Var.
                ---- unfold update. simpl. trivial.
Qed.

Definition Env6 := (update( update (update (update Env4 "i" 1) "n" 2) "i" 2) "i" 3).

Example eeval_4_1 : (*ALL*)
(
  forr (  "i" ::= 1;;"n" ::= 0) ("i" <' "n"+'1) ("i" ::= "i" +' 1) (*daca cond este falsa, atunci in env final nu vor aparea valorile schimbate pt variabilele "i" si "n"*)
  (
    skip
  )
) =|| Env4 ||=> Env4.
Proof.
eapply forF_1.
- eapply Seq.
    --eapply Assign.
        --- eapply Const.
        --- trivial.
    --eapply Assign.
        --- eapply Const.
        --- trivial.
- eapply lessThan.
    -- eapply Var.
    -- eapply Add.
        --- eapply  Var.
        --- eapply Const.
        --- trivial.
    -- simpl. unfold Env4. unfold update. simpl. trivial.
Qed.
Definition Env4_2 := (update( update (update (update Env4 "i" 1) "n" 2) "i" 2) "i" 3).
Example eeval_4_2 : (*ALL*)
(
  forr (  "i" ::= 1;;"n" ::= 2) ("i" <' "n"+'1) ("i" ::= "i" +' 1) (*daca cond este falsa, atunci in env final nu vor aparea valorile schimbate pt variabilele "i" si "n"*)
  (
    skip
  )
) =|| Env4 ||=> Env4_2.
Proof.
eapply forT_1.
- eapply Seq.
    --eapply Assign.
        --- eapply Const.
        --- trivial.
    --eapply Assign.
        --- eapply Const.
        --- trivial.
- eapply lessThan.
    -- eapply Var.
    -- eapply Add.
        --- eapply  Var.
        --- eapply Const.
        --- trivial.
    -- simpl. unfold Env4. unfold update. simpl. trivial.
- eapply Skip.
- eapply Assign.
    -- eapply Add.
        --- eapply Var.
        --- eapply Const.
        --- trivial.
    -- trivial.
- eapply forT_2.
   -- eapply lessThan.
        --- eapply Var.
        --- eapply Add.
            ---- eapply  Var.
            ---- eapply Const.
            ---- trivial.
        --- unfold update. simpl. trivial.
   -- eapply Skip.
   -- eapply  Assign.
        --- eapply Add.
            ---- eapply Var.
            ---- eapply Const.
            ---- trivial.
        --- trivial.
   -- eapply forF_2.
        --- eapply lessThan.
             ---- eapply Var.
             ---- eapply Add.
                  ----- eapply  Var.
                  ----- eapply Const.
                  ----- trivial.
            ---- simpl. trivial.
Qed.
Example eeval_4 : (*ALL*)
(
  "i" ::= 1;;
  "n" ::= 2;;
  dowhile (
    "i" ::= "i" +' 1
  )
  ("i" <' "n"+'1)
) =|| Env4 ||=> Env6.
Proof.
(*eauto 20 with mydb_of_tactics.*)
  eapply Seq.
  - eapply Assign.
    -- eapply Const.
    -- trivial.
  - eapply Seq.
    -- eapply Assign.
        --- eapply Const.
        --- trivial.
    -- eapply doWhileT.
        --- eapply Assign.
            ---- eapply Add.
              ----- eapply Var.
              ----- eapply Const.
              ----- simpl. trivial.
            ---- trivial.
        --- eapply lessThan.
            ---- eapply Var.
            ---- eapply Add.
                  ----- eapply Var.
                  ----- eapply Const.
                  ----- simpl. trivial.
            ---- unfold update. simpl. trivial.
        --- eapply doWhileF.
            ---- eapply Assign.
                  ----- eapply Add.
                    ------ eapply Var.
                    ------ eapply Const.
                    ------ simpl. trivial.
                  ----- unfold Env6. trivial.
            ---- eapply lessThan.
                  ----- eapply Var.
                  ----- eapply Add.
                        ------ eapply Var.
                        ------ eapply Const.
                        ------ simpl. trivial.
                  ----- unfold Env6. unfold update. simpl. trivial.
Qed.

Definition Env7 := (update (update ( update ( update ( update( update ( update ( update ( update (update( update (update (update Env4 "i" 1) "S" 0) "n" 5) "S" 1) "i" 2 ) "S" 3) "i" 3) "S" 6 ) "i" 4 ) "S" 10 ) "i" 5 ) "S" 11) "i" 6).

Definition Env8 :=(update (update( update (update( update (update (update Env4 "i" 1) "S" 0) "n" 2) "S" 1) "i" 2 ) "S" 3) "i" 3).
Example eeval_5 : (*ALL*) (*Programul calculeaza suma primelor 5 numere naturale -5 + 1*)
(
  "i" ::= 1;;
  "S" ::= 0;;
  "n" ::= 5;;
  dowhile (
    ite( "i" =' 5)
      ( "S" ::= "S" +' 1)
    ("S" ::= "S" +' "i");;
    "i" ::= "i" +' 1
  )
  ("i" <' "n"+'1)
) =|| Env4 ||=> Env7.
Proof.
eapply Seq.
    -- eauto 100 with mydb_of_tactics. 
    -- eapply Seq.
        --- eauto 100 with mydb_of_tactics.
        --- eapply Seq.
            ---- eauto 100 with mydb_of_tactics.
            ---- eapply doWhileT.
                  ----- eapply Seq.
                      ------ eauto 100 with mydb_of_tactics.
                      ------ eapply Assign.
                        ------- eauto 100 with mydb_of_tactics.
                        ------- simpl. trivial.
                  ----- eauto 100 with mydb_of_tactics.
                  ----- eapply doWhileT.
                        ------ eauto 100 with mydb_of_tactics.
                        ------ eauto 100 with mydb_of_tactics.
                        ------ simpl. eapply doWhileT.
                            ------- eauto 100 with mydb_of_tactics.
                            ------- eauto 100 with mydb_of_tactics.
                        ------- simpl. eapply doWhileT.
                            + eauto 100 with mydb_of_tactics.
                            + eauto 100 with mydb_of_tactics.
                            + simpl. eapply doWhileF.
                              ++ eapply Seq.
                                +++ eapply iteT.
                                  ++++ eauto 100 with mydb_of_tactics.
                                  ++++ eauto 100 with mydb_of_tactics.
                                +++ eapply Assign.
                                        ++++ eapply Add.
                                          +++++ eapply Var.
                                          +++++ eapply Const.
                                          +++++ trivial.
                                        ++++ simpl. trivial.
                               ++ eauto 100 with mydb_of_tactics.
Qed.


(* Exercise 5.11.1 
Prove that the evaluation of arithmetic expressions is deterministic: *)
(*
Lemma eval_exp_is_deterministic: 
forall exp1 sigma n n',
exp1 =[ sigma ] => n ->
exp1 =[ sigma ] => n' ->
n=n'.
Proof.
intros exp1 sigma n n' H1.
Admitted. *)


















