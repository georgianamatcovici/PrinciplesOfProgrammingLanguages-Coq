Require Import String.
(* Check "a". throws 'Error: No interpretation for string "a".' *)
Open Scope string_scope.
Check "a".
Check  "".
Check "abcb".
Definition Env := string->nat.

Definition sigma1 := 
fun var => 
if (string_dec var "n")
then 10
else if(string_dec var "i")
     then 1
     else 0.

Definition sigma2 :=
fun x =>
if (string_dec x "n")
then 10
else if(string_dec x "s")
     then 10
     else if(string_dec x "i")
          then 10
          else 0.
