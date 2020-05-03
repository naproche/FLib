Let C,D,E stand for sets.
Let C << D stand for C is an element of D.

Definition. C is nonempty iff C has an element.

Definition. A subset of D is a set C such that every element of C
is an element of D.
Let C [[ D stand for C is a subset of D.

Lemma. If C [[ D [[ E then C [[ E.

[number/-s]
Signature Real. A real number is a notion.
Signature. RR is the set of real numbers.

Let x,y,z denote real numbers.

Signature A1. x + y is a real number.
Let the sum of x and y denote x + y.
Signature M1. x * y is a real number.
Let the product of x and y denote x * y.
Signature. x < y is an atom.
Let x > y stand for y < x.

Axiom A2. x + y = y + x.
Axiom A3. (x + y) + z = x + (y + z).
Signature A4. 0 is a real number such that
for every real number x x + 0 = x.
Signature A5. -x is a real number such that x + (-x) = 0.

Axiom M2. x * y = y * x.
Axiom M3. (x * y) * z = x * (y * z).
Signature M4. 1 is a real number such that 1 !=0 and for every real number x 1 * x = x.
Signature M5. Assume x != 0. 1/x is a real number
such that x * (1/x) = 1.

Axiom i. (x < y and x != y and not y < x)
or (not x < y and x = y and not y < x)
or (not x < y and x != y and y < x).
Axiom ii. If x < y and y < z then x < z.

Let x <= y stand for x < y or x = y.
Let x >= y stand for y <= x.

Axiom D. x * (y + z) = (x * y) + (x * z).
Axiom Mono1. If y < z then x + y < x + z and y + x < z + x.
Axiom Mono2. If x > 0 and y > 0 then x * y > 0.

Definition. x is positive iff x > 0.
Definition. x is negative iff x < 0.

Proposition. If x + y = x + z then y = z.
Proposition. If x + y = x then y = 0.
Proposition. If x + y = 0 then y = -x.
Proposition. -(-x) = x.

Proposition. If x != 0 and x * y = x * z then y = z.
Proof. Let x != 0 and x * y = x * z.
y = 1 * y = ((1/x) * x) * y = (1/x) * (x * y) =
(1/x) * (x * z) = ((1/x) * x) * z = 1 * z = z.
qed.
Proposition. If x != 0 and x * y = x then y = 1.
Proposition. If x != 0 and x * y = 1 then y = 1/x.
Proposition. If x != 0 then 1/(1/x) = x.

Proposition. 0 * x = 0.
Proposition. If x != 0 and y != 0 then x * y != 0.

# Proposition Dist1. (y * x) + (z * x) = (y + z) * x.

Proposition. (-x) * y = -(x * y).
Indeed (x * y) + (z * y) = (x + z) * y.

Proposition. -x = -1 * x.

Proposition. (-x) * (-y) = x * y.

Let x - y stand for x + (-y).
Let \frac{x}{y} stand for x * (1/y).

Proposition. x > 0 iff -x < 0.

Proposition 8. If x > 0 and y < z then x * y < x * z.
Proof. Let x > 0 and y < z.
z - y > y - y = 0.
x * (z - y) > 0.
x * z = (x * (z - y)) + (x * y).
(x * (z - y)) + (x * y)  > 0 + (x * y) (by Mono1).
0 + (x * y) = x * y.
qed.

Proposition. If x != 0 then x * x > 0.
Proposition. 1 > 0.
Proposition Next. x + 1 > x.
Proposition. x - 1 < x.
Proposition. x < y iff -x > -y.
# Proof.
# x < y iff x-y < 0.
# qed.
Proposition. If x < 0 and y < z then x * y > x * z.
Proof. Let x < 0 and y < z.
-x > 0.
(-x)*y < (-x)*z (by 8).
-(x*y) < -(x*z).
qed.


# Proposition. If 0 < x < y then 0 < 1/y < 1/x.

Proposition. If 0 < x then 0 < 1/x.

Definition. Let E be a subset of RR. An upper bound of E is a
real number b such that for all elements x of E x <= b.

Definition. Let E be a subset of RR. E is bounded above iff
E has an upper bound.

Definition. Let E be a subset of RR. A lower bound of E is a
real number b such that for all elements x of E x >= b.

Definition. Let E be a subset of RR. E is bounded below iff
E has a lower bound.

Definition. Let E be a subset of RR such that E is bounded above.
A least upper bound of E is a real number a such that
a is an upper bound of E and for all x if x < a then x is not an upper bound of E.

Definition. Let E be a subset of RR such that E is bounded below.
A greatest lower bound of E is a real number a such that
a is a lower bound of E and for all x if x > a then x is not a
lower bound of E.

Axiom. Assume that E is a nonempty subset of RR such that E is bounded
above. Then E has a least upper bound.



Definition. Let E be a subset of RR. *E = {-x | x << E}.

Lemma. Let E be a subset of RR.
(x is an upper bound of E) iff (-x is a lower bound of *E).


Theorem. Assume that E is a nonempty subset of RR such that E is
bounded below.
Then E has a greatest lower bound.
Proof.
Take a lower bound a of E.
-a is an upper bound of *E.
Take a least upper bound b of *E.
Let us show that -b is a greatest lower bound of E.
-b is a lower bound of E. Let c be a lower bound of E. Then -c is an upper bound of *E.
end. qed.

Signature. A rational number is a real number.
Let p,q,r stand for rational numbers.

Definition. QQ is the set of rational numbers.

# QQ is a subfield of RR:

Lemma. QQ [[ RR.
Axiom. p + q, p * q, 0, -p, 1 are rational numbers.
Axiom. Assume p != 0. 1/p is a rational number.

Axiom. There exists a subset E of QQ such that (E is bounded above and
x is a least upper bound of E).

[integer/-s]

Signature. An integer is a rational number.
Let m,n stand for integers.

Definition. ZZ is the set of integers.

# ZZ is a diskrete subring of QQ

Axiom. m + n, m * n, 0, -m, 1 are integers.

Axiom. There is no integer m such that 0 < m < 1.

Axiom. There exist m,n such that n !=0 /\ p = m * (1/n).

Theorem Archimedes1. ZZ is not bounded above.
Proof. Assume the contrary.
ZZ is nonempty. Take a least upper bound b of ZZ.
Let us show that b - 1 is an upper bound of ZZ.
Let x << ZZ. x + 1 << ZZ. x + 1 <= b.
x = (x + 1) - 1 <= b - 1.
end.
qed.

Theorem Archimedes2. There is an integer m such that x <= m.
Proof. x is not an upper bound of ZZ (by Archimedes1).
Take m << ZZ such that not m <= x.
Then x <= m.
qed.

Definition. NN is the set of positive integers.

Theorem. Assume E [[ NN and 1 << E and for all x << E x + 1 << E.
Then E = NN.
Proof.
Let us show that every element of NN is an element of E. 
	Let n << NN.
	Assume the contrary.
	Define F = { j in NN | not j << E}.
	F is nonempty. F is bounded below.
  Take a greatest lower bound a of F.
	Let us show that a+1 is a lower bound of F.
		Let x << F. x - 1 << ZZ.
		Case x - 1 < 0. Then 0 < x < 1. Contradiction. end.
		Case x - 1 = 0. Then x = 1. not 1 << E. Contradiction. end.
		Case x - 1 > 0. Then x - 1 << NN. x - 1 << F.
			a <= x - 1.
			a + 1 <= (x - 1) + 1 = x.
			end.
	end.
	Then a+1 > a (by Next).
	Contradiction.
end.
qed. 
