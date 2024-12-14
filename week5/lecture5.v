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
Compute (env "n").
