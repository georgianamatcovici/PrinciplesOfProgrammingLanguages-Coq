Require Import String.
Open Scope string_scope.
(* memorie : string -> nat *)

Definition env : string->nat :=
  fun x => if eqb x "n" then 10 else 0.

Compute env "n".
Compute env "n1".

Definition update   (env : string->nat) (v : string) (n : nat)
                  : (string -> nat) :=
fun x => if eqb x v then n else (env x).

Compute (update env "n" 8) "n".
Compute (update env "n1" 0) "n". (*in env n este 10*) 

(*EX 1*)

Inductive Exp :=
| num : nat -> Exp
| var : string -> Exp
| add : Exp -> Exp -> Exp
| sub : Exp -> Exp -> Exp
| div : Exp -> Exp -> Exp.

Coercion num : nat >-> Exp.
Coercion var : string >-> Exp.


Notation "A +' B" := (add A B)(at level 50, left associativity).
Notation "A -' B" := (sub A B)(at level 50, left associativity).
Notation "A /' B"  := (div A B)(at level 40, left associativity).

Fixpoint expressions_eval (e : Exp)(env : string->nat) : option nat :=
match e with
| num n => Some (n)
| var v => Some (env v)
| add e1 e2 => match expressions_eval e1 env with (*este posibil ca unul dintre operanzi sa contina o impartire la zero(ex: ((2/0)+3))*)
               | Some e1' => match expressions_eval e2 env with
                             | Some e2' => Some( e1' + e2' )
                             | None => None
                              end
               | None => None
               end
| div e1 e2 => match expressions_eval e2 env with
               | None => None
               | Some 0 => None
               | Some e2' => match expressions_eval e1 env with
                             | Some e1' => Some ( Nat.div e1' e2')
                             | None => None
                              end
               end
| sub e1 e2 => match expressions_eval e1 env with
               | None => None
               | Some e1' => match expressions_eval e2 env with
                             | None => None
                             | Some e2' => if Nat.ltb e1' e2' then None else Some(e1' - e2')
                             end
               end
end.

Compute expressions_eval (2) env.
Compute expressions_eval (2 +' 14/'6) env.
Compute expressions_eval (2-'100) env.
Compute expressions_eval (2/'5 +' (4/'(3+' 1/'0))) env.
Compute expressions_eval (4 +' "n" /' "n1" +' 4) env.
Compute expressions_eval (3-'5/'2 +' 4 +' (4 +' "n" -'24 )) env.
Compute expressions_eval (100 /' "n" +' "n" /' 100) (update env "n" 100).

Inductive Cond :=
| base : bool -> Cond
| bnot : Cond -> Cond
| beq  : Exp -> Exp -> Cond 
| less : Exp -> Exp -> Cond
| band : Cond -> Cond -> Cond.

Notation "! A" := (bnot A)(at level 65, left associativity).
Notation "A =' B" := (beq A B)(at level 61).
Notation "X1 !=' X2" := (!(X1 =' X2))(at level 61).
Notation "A >' B" := ( band (bnot (less A B)) ( A !=' B))(at level 61). (* negarea lui < duce la >=, deci trebuie sa punem si x  != y*)
Notation "A <' B" := (less A B)(at level 61).

Notation "A &' B" := ( band A B)(at level 70).
Notation "A |' B" := (bnot( band (bnot (A))(bnot (B)))) (at level 75). (*cel mai prioritar este NOT, urmat de AND, iar mai apoi OR *)
Notation "A <=' B" := ( ( less A B) |' (A =' B) )(at level 61).
Notation "A >=' B" := ( ( A >' B) |' (A =' B) )(at level 61).

(*si evaluatorul pentru boolean expressions va returna option bool pentru ca
poate exista cazul cand comparam 2/0 < 4 --> None*)
Fixpoint bool_expressions (cond : Cond)(env : string->nat) : option bool :=
match cond with
| base true => Some (true)
| base false => Some (false)
| bnot cond1 => match bool_expressions cond1 env with
                | None => None
                | Some cond1' => Some (negb cond1')
                end
| beq exp1 exp2 => match expressions_eval exp1 env with
                   | None => None
                   | Some exp1' => match expressions_eval exp2 env with
                                   | None => None
                                   | Some exp2' => Some ( Nat.eqb exp1' exp2')
                                   end
                   end
| less exp1 exp2 => match expressions_eval exp1 env with
                   | None => None
                   | Some exp1' => match expressions_eval exp2 env with
                                   | None => None
                                   | Some exp2' => Some ( Nat.ltb exp1' exp2')
                                   end
                   end
| band cond1 cond2 => match bool_expressions cond1 env with
                      | None => None
                      | Some cond1' => match bool_expressions cond2 env with
                                       | None => None
                                       | Some cond2' => Some (andb cond1' cond2')
                                      end
                      end
end.

Compute bool_expressions ( 2<'3 |' 4='5-'10) env. (*operatia 5-10 produce None*)
Compute bool_expressions ( "n">'10 &' 4 =' "n"/'2-'18/'3) (update env "n" 20).
Compute bool_expressions ("n" <=' "n" +' "i"-'10) (update (update env "n" 20) "i" 11).
Compute bool_expressions (100 /' "n" +' "n" /' 100 +' 1/'2 >=' 200/'"n"-'2) (update env "n" 100).

(*Locate "<=".
Compute Nat.leb 4 3.*)

(* EX 2*)
Check option (string -> nat).
Inductive Stmt :=
| skip : Stmt 
| assign : string -> Exp -> Stmt
| seq : Stmt -> Stmt -> Stmt
| ite : Cond -> Stmt -> Stmt -> Stmt (* if-then-else *)
| it  : Cond -> Stmt -> Stmt (* if-then *)
| dowhile : Stmt -> Cond -> Stmt.

Notation "A ::= E1" := (assign A E1)(at level 95).
Notation "S1 ;; S2" := (seq S1 S2)(at level 99).

Fixpoint eval (S : Stmt) (env : string->nat) (gas : nat) : string-> nat :=
match gas with
| 0 => env
| S gas1 => match S with
            | skip => env
            | assign s1 exp1 => match expressions_eval exp1 env with
                                | None => env (*in cazul in care expresia returneaza None, atunci env nu se va schimba*)
                                | Some val => update env s1 val
                                end
            | seq s1 s2 => eval s2 (eval s1 env gas1) gas1
            | ite cond1 s1 s2 => match bool_expressions cond1 env with
                                 | None => env (*daca conditia returneaza None, atunci nu se va executa niciuna dintre ramurile if-ului *)
                                 | Some (true) => eval s1 env gas1
                                 | Some (false) => eval s2 env gas1
                                 end
            | it cond1 s1 => match bool_expressions cond1 env with
                                 | None => env (*daca conditia returneaza None, atunci nu se va executa niciuna dintre ramurile if-ului *)
                                 | Some (true) => eval s1 env gas1
                                 | Some (false) => env
                                 end
            | dowhile s1 cond1 => match eval s1 env gas1 with(*practic do while st1 cond1 se transforma in : st1 while cond1 st1*)
                                  | env2 => match bool_expressions cond1 env2 with
                                            | None => env2
                                            | Some (false) => env2
                                            | Some (true) => eval (dowhile s1 cond1) env2 gas1
                                            end
                                  end
            end
end.

Compute (eval ("n" ::=10 ;; "i"::=100)env 10) "i".

Compute (eval (
    "n"::=20;;
    it("n"<'"n"/'0)
    ("n"::=100)
)env 10) "n".

Compute (eval (
    "n"::=20;;
    ite("n">'"n"-'100)
    ("n"::=100)
    ("n" ::=0)
)env 10) "n". (*n ramane 20 intrucat in implenetarea if-ului, daca in conditie
apare None, atunci nu se va executa nicio ramura a acestuia*)

Compute (eval (
    "n" ::=1;;
    "i"::= 1;;
    dowhile(
    "i"::="i"+'1;;
    it ("i"<='2)("i" ::= "i"+'2);;
    "n"::="n"+'1
    )
    ("n"<='1)
)env 100) "i".

Compute (eval (
ite(10='11 |' (11>='11 &' 3<='10))
("result"::=1)
("result"::=0)
)env 10)"result".

(*EX 3 CMMDC*)
Definition cmmdc ( x y : string) := (*in cazul in care x sau y =0 --> va i returnat cel mai mare*)
it(x='0)
  ("result" ::= y);;
it(y='0 &' x !=' 0)
  ("result" ::= x);;
it(y!='0 &' x!='0)
  ( it( x !=' y ) 
     ( dowhile(
         ite( x >' y ) ( x ::=x -'y ) (y::=y -' x)
        )
        ( x !=' y )
     )
    ;;
    "result" ::= x
  ).

Compute (eval (cmmdc "a" "b") (update (update env "a" 310) "b" 5) 1000) "result".
Compute (eval (cmmdc "a" "b") (update (update env "a" 100) "b" 120) 1000) "result".
Compute (eval (cmmdc "a" "b") (update (update env "a" 10) "b" 1000) 1000) "result". 
Compute (eval (cmmdc "a" "b") (update (update env "a" 4421) "b" 0) 1000) "result".
Compute (eval (cmmdc "a" "b") (update (update env "a" 101) "b" 273) 1000) "result".



Definition fibo ( n : string ) :=
"a" ::= 0 ;;
"b" ::= 1 ;;
"nr"::= 1;;
ite ( n =' 1 ) ("response" ::= 0) (
    dowhile (
      "b"::="b"+'"a";;
      "a"::="b"-'"a";;
     "nr"::="nr"+'1
    )
  ("nr" <' n)
;;
"response" ::= "a"
).
 
Compute (eval (fibo "f") (update env "f" 1) 1000)"response".
Compute (eval (fibo "f") (update env "f" 2) 1000)"response".
Compute (eval (fibo "f") (update env "f" 3) 1000)"response".
Compute (eval (fibo "f") (update env "f" 4) 1000)"response".
Compute (eval (fibo "f") (update env "f" 5) 1000)"response".
Compute (eval (fibo "f") (update env "f" 6) 1000)"response".

Compute (eval (fibo "f") (update env "f" 21) 1000)"response".
Compute (eval (fibo "f") (update env "f" 27) 1000)"response".
