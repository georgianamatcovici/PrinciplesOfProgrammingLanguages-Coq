Require Import String.
Require Import List.
Import ListNotations.

Inductive B :=
| T : B
| F : B
| neg : B -> B
| and : B -> B -> B
| or  : B -> B -> B.

(*ex1*)
Fixpoint interpret (b: B) : bool :=
match b with
|T => true
|F => false
|neg b' => negb (interpret b')
|and b1 b2 => andb (interpret b1) (interpret b2)
|or b1 b2 => orb (interpret b1) (interpret b2)
end. 

Compute (interpret (neg T)).
Compute (interpret (and F T)).
Compute (interpret (or F T)).

(*ex2*)

Inductive Instruction :=
| push : nat -> Instruction
| inv : Instruction
| add : Instruction
| mul : Instruction.

Definition to_bool( n : nat) : bool :=
match n with
| O => false
| S n' => true
end.

Definition to_nat(b: bool) : nat :=
match b with
|true => S O
|false => O
end.

Definition run_instruction (i : Instruction) (stack : list nat) : list nat :=
  match i with
  | push n =>  match n with
               | O => O :: stack
               | S n' => (S O) :: stack
               end
  | inv =>
      match stack with
      | n :: stack' => to_nat(negb (to_bool n)) :: stack'
      | _ => stack
      end
  | add =>
      match stack with
      | n1 :: n2 :: stack' =>
          to_nat(orb (to_bool n1) (to_bool n2) ) :: stack'
      | _ => stack
      end
  | mul =>
      match stack with
      | n1 :: n2 :: stack' =>
          to_nat(andb (to_bool n1) (to_bool n2) ) :: stack'
      | _ => stack
      end
  end.
Compute (run_instruction (push (S O)) nil).
Compute (run_instruction inv ([(S O); O])).
Compute (run_instruction inv ([(O); O])).
Compute (run_instruction add ([(S O); O])).
Compute (run_instruction mul ([(S O); O])).
(*ex3*)

Fixpoint run_instructions
         (stpgm : list Instruction)
         (stack : list nat) :=
match stpgm with
| nil => stack
| i :: stpgm' => run_instructions
                    stpgm'
                  (run_instruction i stack)
end. 
Compute run_instructions
  [push (S O); push O ; mul]
  [].
(*ex4*)
Fixpoint compile (b : B) : list Instruction :=
  match b with
| T => [push (S O)]
| F => [push O]
| neg b' => (compile b') ++ (inv :: nil)
| and b1 b2 => (compile b1) ++ (compile b2) ++ (mul :: nil)
| or b1 b2 => (compile b1) ++ (compile b2) ++ (add :: nil)
  end.

Compute compile (and T F).
Compute compile (or T F).
Compute compile (neg T).
Compute run_instructions
  (compile (and T T))
  [].

(*ex5*)



Lemma soundness_helper:
  forall b instrs stack,
    run_instructions ((compile b) ++ instrs) stack =
    run_instructions instrs (to_nat (interpret b) :: stack).
Proof.
induction b; intros instrs stack.
-simpl. reflexivity.
-simpl. reflexivity.
- simpl. rewrite <- app_assoc.  rewrite IHb. case (interpret b); simpl; reflexivity.
- simpl. rewrite <- app_assoc. rewrite IHb1. rewrite <- app_assoc.
    rewrite IHb2. case (interpret b1); case (interpret b2); simpl; reflexivity. 
- simpl. rewrite <- app_assoc. rewrite IHb1. rewrite <- app_assoc.
    rewrite IHb2. case (interpret b1); case (interpret b2); simpl; reflexivity. 
Qed.
Theorem soundness : 
  forall b,
    run_instructions (compile b) nil =  [to_nat (interpret b)].
Proof.
intros.
  rewrite <- app_nil_r with (l := compile b).
  rewrite soundness_helper.
  simpl.
  reflexivity.
Qed.
