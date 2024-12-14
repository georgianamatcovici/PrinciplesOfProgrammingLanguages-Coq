Inductive Day :=
|Monday
|Tuesday
|Wednesday
|Thursday
|Friday
|Saturday
|Sunday.

Print Day.
Print bool.
Print nat.
Check 0.
Check(S, 0).

Definition add( n m : nat) : nat :=
n+m.

Print add.
Compute add 3 5.

Definition add2 (a : nat)(b:nat)(c:nat) : nat:=a+b+c.
Compute add2 3 6 7.

Definition next_day(d: Day): Day := 
match d with
|Monday => Tuesday
|Tuesday => Wednesday
|Wednesday => Thursday
|Thursday => Friday
|Friday => Saturday
|Saturday => Sunday
|Sunday => Monday
end.

Definition eq_day (d1 d2 : Day) :=
match (d1, d2) with
|(Monday, Monday) => true
|(Tuesday, Tuesday) => true
|(Wednesday, Wednesday) => true
|(Thursday, Thursday) => true
|(Friday, Friday)=> true
|(Saturday, Saturday) =>true
|(Sunday, Sunday) => true
|_ => false
end.

Inductive Bool :=
| True
| False.

Definition Negation (b1 : Bool) : Bool :=
match b1 with
|True=>False
|False=>True
end.

Print bool.

Definition Conjunction(b1 b2: Bool):Bool :=
match b1, b2 with
| False, False => False
| False, True => False
| True, False => False
| True, True => True
end.

Definition Disjunction(b1 b2: Bool):Bool :=
match b1, b2 with
| False, False => False
| False, True => True
| True, False => True
| True, True => True
end.







