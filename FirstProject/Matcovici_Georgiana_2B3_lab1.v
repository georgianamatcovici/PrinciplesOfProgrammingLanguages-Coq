Inductive Day :=
|Monday
|Tuesday
|Wednesday
|Thursday
|Friday
|Saturday
|Sunday.

(*3*)
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

(*4*)
Inductive Bool :=
| True
| False.

(*5*)
Definition Negation (b1 : Bool) : Bool :=
match b1 with
|True=>False
|False=>True
end.

Print Bool.

Definition Conjunction(b1 b2: Bool):Bool :=
match b1, b2 with
| False, False => False
| False, True => False
| True, False => False
| True, True => True
end.

Compute Conjunction True False.

Definition Disjunction(b1 b2: Bool):Bool :=
match b1, b2 with
| False, False => False
| False, True => True
| True, False => True
| True, True => True
end.




(*6*)
Inductive Number :=
| number : bool -> bool -> bool ->
         bool -> Number.

Definition AddBits (b1 b2 : bool) : bool :=
match b1, b2 with
| false, false => false
| false, true => true
| true, false => true
| true, true => false
end.

Definition Carry (b1 b2 b3 : bool) : bool :=
match b1, b2, b3 with
| false, false, _=> false
| false, true, false => false
| false, true, true => true
| true, false, false => false
| true, false, true => true
| true, true, false => true
| true, true, true => false 
end.


Definition Add (a b : Number) : Number :=
match a, b with
| number m3 m2 m1 m0, number n3 n2 n1 n0 =>
let s0 := (AddBits m0 n0) in
let c0 := Carry m0 n0 false in 
let s1 := AddBits (AddBits m1 n1) c0 in 
let c1 := Carry m1 n1 c0 in
let s2 := AddBits (AddBits m2 n2) c1 in 
let c2 := Carry m2 n2 c1 in
let s3 := AddBits (AddBits m3 n3) c2 in 
let c3 := Carry m3 n3 c2 in
number s3 s2 s1 s0
end.

Definition Zero := number  false false false false.
Definition One := number  false false false true. 
Definition Two := number  false false true false. 
Definition Three := number  false false true true. 
Definition Four := number  false true false false. 
Definition Five := number  false true false true. 
Definition Six := number  false true true false. 
Definition Seven := number  false true true true. 
Definition Eight := number  true false false false. 
Definition Nine := number true false false true.
Definition Ten := number true false true false.
Definition Eleven := number true false true true.
Definition Twelve := number true true false false.
Definition Thirteen := number true true false true.
Definition Fourteen := number true true true false.
Definition Fifteen := number true true true true.

Compute Add One Thirteen.
Compute Add Eleven Two.
Compute Add Seven Eight.
Compute Add Zero Two.
Compute Add Ten Three.

Definition SubBits (b1 b2 : bool) : bool :=
match b1, b2 with
| false, false => false
| false, true  => true
| true, false  => true
| true, true   => false
end.

Definition Borrow (b1 b2 b3 : bool) : bool :=
match b1, b2, b3 with
| false, false, false => false
| false, false, true  => true
| false, true, false  => true
| false, true, true   =>true
| true, false, false  => false
| true, false, true   => true
| true, true, false   => false
| true, true, true    =>true
end.

Definition IsLower (a b : Number) : bool :=
  match a, b with
  | number m3 m2 m1 m0, number n3 n2 n1 n0 =>
    if m3 then
        false 
      else if n3 then
        true 
      else
        if m2 then
          if n2 then false
          else true
        else if n2 then true
        else if m1 then
          if n1 then false
          else true
        else if n1 then true
        else false
  end.

Compute IsLower One Thirteen.
Compute IsLower Eleven Two.
Compute IsLower Seven Eight.
Compute IsLower Nine Three.
Compute IsLower Nine Nine.

(*Daca n1 este mai mic se va returna 0*)
Definition Sub (a b : Number) : Number :=
if IsLower a b then
number false false false false
else
match a, b with 
|number m3 m2 m1 m0, number n3 n2 n1 n0 =>
let r0 := SubBits m0 n0 in
let b1 := Borrow m0 n0 false in
let r1 := SubBits (SubBits m1 n1) b1 in
let b2 := Borrow m1 n1 b1 in
let r2 := SubBits (SubBits m2 n2) b2 in
let b3 := Borrow m2 n2 b2 in
let r3 := SubBits (SubBits m3 n3) b3 in
let b4 := Borrow m3 n3 b3 in
number r3 r2 r1 r0
end.

Compute Sub One Thirteen.
Compute Sub Eleven Two.
Compute Sub Seven Eight.
Compute Sub Nine Three.
Compute Sub Ten Two.
Compute Sub Ten Zero.


Definition MulBits (b1 b2: bool) : bool :=
match b1, b2 with
| true, true   => true
|_,_ => false
end.
 
Inductive BigNumber :=
| bignumber : bool -> bool -> bool ->
         bool -> bool-> bool-> bool -> bool-> BigNumber.

(*Rezultatul va fi pe 8 biti, intr-un BigNumber *)
Definition Mul (n1 n2 : Number) : BigNumber :=
match n1, n2 with
|number m3 m2 m1 m0, number n3 n2 n1 n0 =>
let p0 := MulBits m0 n0 in  
let p1 := MulBits m1 n0 in 
let p2 := MulBits m2 n0 in
let p3 := MulBits m3 n0 in 

let p4 := MulBits m0 n1 in 
let p5 := MulBits m1 n1 in
let p6 := MulBits m2 n1 in
let p7 := MulBits m3 n1 in

let p11 := MulBits m0 n2 in
let p10 := MulBits m1 n2 in
let p9 := MulBits m2 n2 in
let p8 := MulBits m3 n2 in

let p11 := MulBits m0 n2 in
let p10 := MulBits m1 n2 in
let p9 := MulBits m2 n2 in
let p8 := MulBits m3 n2 in

let p15 := MulBits m0 n3 in
let p14 := MulBits m1 n3 in
let p13 := MulBits m2 n3 in
let p12 := MulBits m3 n3 in

let rez0 := p0 in 
let c1 := Carry p1 p4 false in
let rez1 := AddBits p1 p4 in
let rez2 := AddBits (AddBits (AddBits p2 p5) p8) c1 in
let c2 := Carry (Carry p2 p5 p8) c1 false in
let rez3 := AddBits (AddBits (AddBits (AddBits p3 p6) p9) p12) c2 in
let c3 := Carry (Carry p3 p6 p9 ) p12 c2 in
let rez4 := AddBits (AddBits (AddBits p7 p10) p13) c3 in
let c4:= Carry (Carry p7 p10 p13) c3 false in
let rez5 := AddBits (AddBits p11 p14) c4 in
let c5 := Carry p11 p14 c4 in
let rez6 :=AddBits p15 c5 in
let c5 := Carry p15 c5 false in
let rez7 := c5 in
bignumber rez7 rez6 rez5 rez4 rez3 rez2 rez1 rez0
end.

Compute Mul One Two.
Compute Mul Four Two.
Compute Mul Nine Three.
Compute Mul Six Nine.
Compute Mul Zero One.
Compute Mul Three Two.
Compute Mul Two Three.

Definition EqualToZero (n: Number) : bool :=
match n with
 | number n3 n2 n1 n0 =>
      match n3, n2, n1, n0 with
      | false, false, false, false => true
      | _,_,_,_ => false
      end
  end.





Inductive Nat := O : Nat | S : Nat -> Nat.

Definition one := S O.
Definition two := S one.
Definition three := S two.
Definition four := S three.
Definition five := S four.

(*7*)
Fixpoint eq_Nat (n m : Nat) :=
match (n, m) with
| (O, O) => true
| (O, S a) => false
| (S a, O) => false
| (S a, S b) => eq_Nat a b
end. 

Compute eq_Nat O O.
Compute eq_Nat one O.
Compute eq_Nat one one.
Compute eq_Nat one four.
Compute eq_Nat five four.
Compute eq_Nat five five.


(*8*)
Fixpoint add (m n : Nat) : Nat := 
match m with
| O => n
| S k => S(add k n)
end.

Compute add one one.
Compute add one five.
Compute add five one.
Compute add five O.
Compute add O five.


(*9*)
Fixpoint max (m n : Nat) : Nat := 
match (m, n) with
|(O, n) => n
|(m, O) => m
|(S a, S b) => S(max a b)
end.

Compute max one two.
Compute max O one.
Compute max one O.
Compute max four five.
Compute max five four.



