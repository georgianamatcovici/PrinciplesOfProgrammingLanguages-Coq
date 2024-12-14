Require Import String.
(* Check "a". throws 'Error: No interpretation for string "a".' *)
Open Scope string_scope.
Check "a".
Check  "".
Check "abcb".

Definition Env := string -> nat.
Definition env (string : string) :=
if (string_dec string "n")
then 10
else 0.

Definition update (x : string)
(v : nat)
(env : Env) : Env :=
fun y => if (string_dec x y)
then v
else env y.

Inductive AExp :=
|var : string -> AExp
| anum : nat -> AExp
| aplus : AExp -> AExp -> AExp
| amul : AExp -> AExp -> AExp.

Fixpoint aeval (a : AExp) (env : Env) : nat :=
match a with
| var v => env v
| anum v => v
| aplus a1 a2 => (aeval a1 env) + (aeval a2 env)
| amul a1 a2 => (aeval a1 env) * (aeval a2 env)
end.

Coercion var : string >-> AExp.
Coercion anum : nat >-> AExp.
Notation "A +' B" := (aplus A B) (at level 50).
Notation "A *' B" := (amul A B) (at level 40).
Compute aeval (2 +' 3 *' 4) env.
Compute aeval (2 +' 3 *' "n") env.
