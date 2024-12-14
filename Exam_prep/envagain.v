Require Import String.
(* Check "a". throws 'Error: No interpretation for string "a".' *)
Open Scope string_scope.
Check "a".
Check  "".
Check "abcb".


Definition Env' := string->option nat.
Definition sigma3 :=
fun x =>
if (string_dec x "n")
then Some 10
else if(string_dec x "i")
     then Some 0
     else None. 

Definition Env’ := string -> option nat