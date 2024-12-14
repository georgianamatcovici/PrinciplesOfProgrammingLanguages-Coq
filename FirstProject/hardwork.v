Inductive  Number :=
|zero
|one
|two
|three
|four
|five
|six
|seven
|eight
|nine
|ten
|eleven
|twelve
|thirteen
|fourteen
|fifteen.


(*Inductive Numbers :=
|zero
|Successor(n: Numbers).
*)

(*Definition Successor (n : Numbers) : Numbers :=
match n with
|zero => one
|one => two
|two => three
|three => four
|four => five
|five => six
|six => seven
|seven => eight
|eight => nine
|nine => ten
|ten => eleven
|eleven => twelve
|twelve => thirteen
|thirteen => fourteen
|fourteen => fifteen
|fifteen => zero
end.

*)



(*Fixpoint Add (n1 n2 : Numbers) : Numbers :=
match (n1, n2) with
| (zero, n2) => n2
| (n1, zero) => n1
| (Successor a, n2) => Successor( Add a n2)
end.
*)

(*Add Successor(zero) zero.*)

Definition Add (n1 n2 : Number) : Number :=
match n1, n2 with
| zero, n2 => n2
| n1, zero => n1
| one, one => two
| one, two => three
| one, three => four
| one, four => five
| one, five => six
| one, six => seven
| one, seven => eight
| one, eight => nine
| one, nine => ten
| one, ten => eleven
| one, eleven => twelve
| one, twelve => thirteen
| one, thirteen => fourteen
| one, fourteen => fifteen
| one, n2 => zero
| two, one => three
| two, two => four
| two, three => five
| two, four => six
| two, five => seven
| two, six => eight
| two, seven => nine
| two, eight => ten
| two, nine => eleven
| two, ten => twelve
| two, eleven => thirteen
| two, twelve => fourteen
| two, thirteen => fifteen
| two, n2 => zero
| three, one => four
| three, two => five
| three, three => six
| three, four => seven
| three, five => eight
| three, six => nine
| three, seven => ten
| three, eight => eleven
| three, nine => twelve
| three, ten => thirteen
| three, eleven => fourteen
| three, twelve => fifteen
| three, n2 => zero
| four, one => five
| four, two => six
| four, three => seven
| four, four => eight
| four, five => nine
| four, six => ten
| four, seven => eleven
| four, eight => twelve
| four, nine => thirteen
| four, ten => fourteen
| four, eleven => fifteen
| four, n2 => zero
| five, one => six
| five, two => seven
| five, three => eight
| five, four => nine
| five, five => ten
| five, six => eleven
| five, seven => twelve
| five, eight => thirteen
| five, nine => fourteen
| five, ten => fifteen
| five, n2 => zero
| six, one => seven
| six, two => eight
| six, three => nine
| six, four => ten
| six, five => eleven
| six, six => twelve
| six, seven => thirteen
| six, eight => fourteen
| six, nine => fifteen
| six, n2 => zero
| seven, one => eight
| seven, two => nine
| seven, three => ten
| seven, four => eleven
| seven, five => twelve
| seven, six => thirteen
| seven, seven => fourteen
| seven, eight => fifteen
| seven, n2 => zero
| eight, one => nine
| eight, two => ten
| eight, three => eleven
| eight, four => twelve
| eight, five => thirteen
| eight, six => fourteen
| eight, seven => fifteen
| eight, n2 => zero
| nine, one => ten
| nine, two => eleven
| nine, three => twelve
| nine, four => thirteen
| nine, five => fourteen
| nine, six => fifteen
| nine, n2 => zero
| ten, one => eleven
| ten, two => twelve
| ten, three => thirteen
| ten, four => fourteen
| ten, five => fifteen
| ten, n2 => zero
| eleven, one => twelve
| eleven, two => thirteen
| eleven, three => fourteen
| eleven, four => fifteen
| eleven, n2 => zero
| twelve, one => thirteen
| twelve, two => fourteen
| twelve, three => fifteen
| twelve, n2 => zero
| thirteen, one => fourteen
| thirteen, two => fifteen
| thirteen, n2 => zero
| fourteen, one => fifteen
| fourteen, n2 => zero
| n1, n2 => zero
end.

Compute Add five four.
Compute Add ten four.

Definition Sub (n1 n2 : Number) : Number :=
match n1, n2 with
| zero, n2 => zero
| n1, zero => n1
| one, n2 => zero
| two, one => one
| two, n2 => zero
| three, one => two
| three, two => one
| three, n2 => zero
| four, one => three
| four, two => two
| four, three => one
| four, n2 => zero
| five, one => four
| five, two => three
| five, three => two
| five, four => one
| five, n2 => zero
| six, one => five
| six, two => four
| six, three => three
| six, four => two
| six, five => one
| six, n2 => zero
| seven, one => six
| seven, two => five
| seven, three => four
| seven, four => three
| seven, five => two
| seven, six => one
| seven, n2 => zero
| eight, one => seven
| eight, two => six
| eight, three => five
| eight, four => four
| eight, five => three
| eight, six => two
| eight, seven => one
| eight, n2 => zero
| nine, one => eight
| nine, two => seven
| nine, three => six
| nine, four => five
| nine, five => four
| nine, six => three 
| nine, seven => two
| nine, eight => one
| nine, n2 => zero
| ten, one => nine
| ten, two => eight
| ten, three => seven
| ten, four => six
| ten, five => five
| ten, six => four
| ten, seven => three
| ten, eight => two
| ten, nine => one
| ten, n2 => zero
| eleven, one => ten
| eleven, two => nine
| eleven, three => eight
| eleven, four => seven
| eleven, five => six
| eleven, six => five
| eleven, seven => four
| eleven, eight => three
| eleven, nine => two
| eleven, ten => one
| eleven, n2 => zero
| twelve, one => eleven
| twelve, two => ten
| twelve, three => nine
| twelve, four => eight
| twelve, five => seven
| twelve, six => six
| twelve, seven => five
| twelve, eight => four
| twelve, nine => three
| twelve, ten => two
| twelve, eleven => one
| twelve, n2 => zero
| thirteen, one => twelve
| thirteen, two => eleven
| thirteen, three => ten
| thirteen, four => nine
| thirteen, five => eight
| thirteen, six => seven
| thirteen, seven => six
| thirteen, eight => five
| thirteen, nine => four
| thirteen, ten => three
| thirteen, eleven => two
| thirteen, twelve => one
| thirteen, n2 => zero
| fourteen, one => thirteen
| fourteen, two => twelve
| fourteen, three =>eleven
| fourteen, four => ten
| fourteen, five => nine
| fourteen, six => eight
| fourteen, seven => seven
| fourteen, eight => six
| fourteen, nine => five
| fourteen, ten => four
| fourteen, eleven => three
| fourteen, twelve => two
| fourteen, thirteen => one
| fourteen, n2 => zero
| fifteen, one => fourteen
| fifteen, two => thirteen
| fifteen, three => twelve
| fifteen, four => eleven
| fifteen, five => ten
| fifteen, six => nine
| fifteen, seven => eight
| fifteen, eight => seven
| fifteen, nine => six
| fifteen, ten => five
| fifteen, eleven => four
| fifteen, twelve => three
| fifteen, thirteen => two
| fifteen, fourteen => one
| fifteen, n2 => zero
end.

Definition Mul (n1 n2: Number) : Number :=
match n1, n2 with
| zero, n2 => zero
| n1, zero => zero
| one, n2 => n2
| n1, one => n1
| two, two => four
| two, three => six
| two, four => eight
| two, five => ten
| two, six => twelve
| two, seven => fourteen
| two, n2 => zero
| three, two => six
| three, three => nine
| three, four => twelve
| three, five => fifteen
| three, n2 => zero
| four, two => eight
| four, three => twelve
| four, n2 => zero
| five, two =>ten
| five, three =>fifteen
| five, n2 =>zero
| six, two =>twelve
| six, n2 =>zero
| seven, two =>fifteen
| seven, n2 =>zero
| n1, n2 =>zero
end.


Definition ConvertNumber (n: Number ) : nat :=
match n with
|zero => O
|one => S O
|two => S( S O )
|three => S(S( S O ))
|four => S (S(S( S O )))
|five => S(S(S(S( S O ))))
|six => S(S(S(S(S( S O )))))
|seven => S(S(S(S(S(S( S O ))))))
|eight => S(S(S(S(S(S(S( S O )))))))
|nine => S(S(S(S(S(S(S(S( S O ))))))))
|ten => S( S(S(S(S(S(S(S(S( S O )))))))))
|eleven => S(S( S(S(S(S(S(S(S(S( S O ))))))))))
|twelve => S(S(S( S(S(S(S(S(S(S(S( S O )))))))))))
|thirteen =>  S(S(S(S( S(S(S(S(S(S(S(S( S O ))))))))))))
|fourteen =>S( S(S(S(S( S(S(S(S(S(S(S(S( S O )))))))))))))
|fifteen =>S( S( S(S(S(S( S(S(S(S(S(S(S(S( S O ))))))))))))))
end.

(*Definition ConvertNat (n: nat ) : Number :=
match n with
|zero => O
|one => S O
|two => S( S O )
|three => S(S( S O ))
|four => S (S(S( S O )))
|five => S(S(S(S( S O ))))
|six => S(S(S(S(S( S O )))))
|seven => S(S(S(S(S(S( S O ))))))
|eight => S(S(S(S(S(S(S( S O )))))))
|nine => S(S(S(S(S(S(S(S( S O ))))))))
|ten => S( S(S(S(S(S(S(S(S( S O )))))))))
|eleven => S(S( S(S(S(S(S(S(S(S( S O ))))))))))
|twelve => S(S(S( S(S(S(S(S(S(S(S( S O )))))))))))
|thirteen =>  S(S(S(S( S(S(S(S(S(S(S(S( S O ))))))))))))
|fourteen =>S( S(S(S(S( S(S(S(S(S(S(S(S( S O )))))))))))))
|fifteen =>S( S( S(S(S(S( S(S(S(S(S(S(S(S( S O ))))))))))))))
end.
*)
Definition ConvertNat (n: nat ) : Number :=
match n with
|O => zero
|1 => one
|2 => two
|3 => three 
|4 => four 
|5 => five
|6 => six 
|7 => seven 
|8 => eight
|9 => nine
|10 => ten
|11 => eleven 
|12 => twelve 
|13=> thirteen 
|14 => fourteen 
|15 => fifteen 
|_ => zero
end.

Definition Add2( n1 n2: Number) : Number :=
ConvertNat (ConvertNumber n1 + ConvertNumber n2).


Definition Sub2( n1 n2: Number) : nat :=
ConvertNumber n1 - ConvertNumber n2.

Compute Add2 three four.