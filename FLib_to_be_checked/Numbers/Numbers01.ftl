# [prove off] [check off] [printthesis on]

# page 3

Let A,B stand for sets.
Let x << A denote x is an element of A.
# Let x is member of A denote x is an element of A.
Let x is in A denote x is an element of A.
Let x !<< A denote x is not an element of A.

Signature. The empty set is the set that has no elements.
Let Emptyset denote the empty set.

Definition. A is nonempty iff A has an element.

Definition. A subset of B is a set A such that every element of A
is an element of B. 
Let A [[ B stand for A is a subset of B.
Let B ]] A stand for A is a subset of B.

Definition. A proper subset of B is a subset A of B such that there
is an element of B that is not in A.

Proposition. A [[ A.

Proposition. If A [[ B and B [[ A then A = B.

Definition. A \cup B = {x | x<<A \/ x<<B}.

# page 8

[synonym number/-s]
Signature Real. A real number is a notion.
Signature. RR is the set of real numbers.

Let x,y,z denote real numbers.

# page 5

Signature A1. x + y is a real number.
Let the sum of x and y denote x + y.
Signature M1. x * y is a real number.
Let the product of x and y denote x * y.
Signature. x < y is an atom.
Let x > y stand for y < x.
Let x <= y stand for x < y or x = y.
Let x >= y stand for y <= x.

# page 3

Axiom i. (x < y and x != y and not y < x)
or (not x < y and x = y and not y < x)
or (not x < y and x != y and y < x).
Axiom ii. If x < y and y < z then x < z.

Proposition. x <= y iff not x > y.

Proposition. not x <= y iff y < x.

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

Axiom D. x * (y + z) = (x * y) + (x * z).
# Proposition Dist1. (y * x) + (z * x) = (y + z) * x.

Proposition 1_14_a. If x + y = x + z then y = z.
Proof. Assume x + y = x + z. Then 
y = (-x+x) + y = -x + (x+y) = -x + (x+z) = (-x+x) + z = z.
qed.

Proposition. If x + y = x then y = 0.
# Proposition. If x + y = 0 then y = -x.
Proposition 1_14_d. -(-x) = x.

Proposition 1_15_a. If x != 0 and x * y = x * z then y = z.
Proof. Let x != 0 and x * y = x * z.
y = 1 * y = ((1/x) * x) * y = (1/x) * (x * y) =
(1/x) * (x * z) = ((1/x) * x) * z = 1 * z = z.
qed.
Proposition. If x != 0 and x * y = x then y = 1.
Proposition. If x != 0 and x * y = 1 then y = 1/x.
Proposition. If x != 0 then 1/(1/x) = x.

Proposition 1_16_1. 0 * x = 0.
Proposition. If x != 0 and y != 0 then x * y != 0.
Proposition. (-x) * y = -(x * y).
Proof. (x * y) + (-x * y) = (x + (-x)) * y = 0 * y = 0.
qed.

Proposition. -x = -1 * x.

Proposition 1_16_d. (-x) * (-y) = x * y.
Proof. (-x)*(-y)=-(x*(-y))=-((-y)*x)=-(-(y*x))=y*x=x*y. qed.

Let x - y stand for x + (-y).
Let \frac{x}{y} stand for x * (1/y).


Axiom 1_17_i. If y < z then x + y < x + z and y + x < z + x.
Axiom 1_17_ii. If x > 0 and y > 0 then x * y > 0.

Definition. x is positive iff x > 0.
Definition. x is negative iff x < 0.


Proposition 1_18_a. x > 0 iff -x < 0.

Proposition 1_18_b. If x > 0 and y < z then x * y < x * z.
Proof. Let x > 0 and y < z.
z - y > y - y = 0.
x * (z - y) > 0.
x * z = (x * (z - y)) + (x * y).
(x * (z - y)) + (x * y)  > 0 + (x * y) (by 1_17_i).
0 + (x * y) = x * y.
qed.

Proposition 1_18_bb. If x > 0 and y < z then y * x < z * x.


Proposition 1_18_d. If x != 0 then x * x > 0.
Proposition 1_18_dd. 1 > 0.
Proposition. x < y iff -x > -y.
Proof.
x < y <=> x - y < 0. 
x - y < 0 <=> (-y) + x < 0. 
(-y) + x < 0 <=> (-y)+(-(-x)) < 0.
(-y)+(-(-x)) < 0 <=> (-y)-(-x) < 0.
(-y)-(-x) < 0 <=> -y < -x .
qed.

Proposition 1_18_c. If x < 0 and y < z then x * y > x * z.
Proof. Let x < 0 and y < z.
-x > 0.
(-x)*y < (-x)*z (by 1_18_b).
-(x*y) < -(x*z).
qed.

Proposition 1_18_cc. If x < 0 and y < z then y * x > z * x.

Proposition Next. x + 1 > x.
Proposition. x - 1 < x.

Proposition. If 0 < x then 0 < 1/x.

Proposition. Assume 0 < x < y. Then 1/y < 1/x.
Proof by case analysis.
Case 1/x < 1/y. Then
1 = x * (1/x) = (1/x) * x < (1/x) * y = y * (1/x) < y * (1/y) = 1. 
Contradiction. 
1/y < 1/x.
end.

Case 1/x = 1/y. Then
1 = x * (1/x) < y * (1/y) = 1. 
Contradiction. 
1/y < 1/x.
end.

Case 1/y < 1/x. obvious.

1/x < 1/y or 1/x = 1/y or 1/y < 1/x.

qed.

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

Axiom. There exists a subset A of QQ such that (A is bounded above and
x is a least upper bound of A).

Theorem. RR = {x << RR | there exists A [[ QQ such that 
                         A is bounded above and x is a least upper
                         bound of A}.

[synonym integer/-s]

Signature. An integer is a rational number.
Let a,b stand for integers.

Definition. ZZ is the set of integers.

# ZZ is a discrete subring of QQ

Axiom. a + b, a * b, 0, -a, 1 are integers.

Axiom. There is no integer a such that 0 < a < 1.

Axiom. There exist integers a and b such that a !=0 /\ p = \frac{b}{a}.

Theorem Archimedes1. ZZ is not bounded above.
Proof. Assume the contrary.
ZZ is nonempty. Take a least upper bound b of ZZ.
Let us show that b - 1 is an upper bound of ZZ.
Let x << ZZ. x + 1 << ZZ. x + 1 <= b.
x = (x + 1) - 1 <= b - 1.
end.
qed.



Theorem Archimedes2. There is an integer a such that x <= a.
Proof.#  x is not an upper bound of ZZ (by Archimedes1).
Take a << ZZ such that not a <= x.
Then x <= a.
qed.

Definition. NN is the set of positive integers.
Let m,n stand for positive integers.

Definition. {x} = {y << RR | y = x}.

Lemma. ZZ = (*NN \cup {0}) \cup NN.

Theorem. Assume A [[ NN and 1 << A and for all n << A n + 1 << A.
Then A = NN.
Proof.
Let us show that every element of NN is an element of A. 
	Let n << NN.
	Assume the contrary.
	Define F = { j in NN | not j << A}.
	F is nonempty. F is bounded below.
  Take a greatest lower bound a of F.
	Let us show that a+1 is a lower bound of F.
		Let x << F. x - 1 << ZZ.
		Case x - 1 < 0. Then 0 < x < 1. Contradiction. end.
		Case x - 1 = 0. Then x = 1. not 1 << A. Contradiction. end.
		Case x - 1 > 0. Then x - 1 << NN. not x - 1 << A. 
        Proof. Assume the contrary. x = (x-1) + 1. qed.
			a <= x - 1.
			a + 1 <= (x - 1) + 1 = x.
			end.
	end.
	Then a+1 > a (by Next).
	Contradiction.
end.
qed.

Lemma. There exists m << ZZ such that m-1 <= p < m.
Proof.
Define F = { j in ZZ | p < j}.
F is nonempty. F is bounded below.
Take a greatest lower bound m of F.
m-1 <= p.
Proof. Assume the contrary. Then p < m-1. qed.
Qed.

Theorem 1_20_a. Let x > 0. Then there is a positive integer n such that
n * x > y.
Proof. Take an integer a such that a > \frac{y}{x}.
Take a positive integer n such that n > a.
n > \frac{y}{x} and n * x > (\frac{y}{x})*x = y.
qed.

Theorem 1_20_b. Let x < y. Then there exists p << QQ such that
x < p < y.
Proof. Assume x < y. Then y - x > 0.
Take a positive integer n such that 
n*(y-x) > 1 (by 1_20_a).
# [prove off]
Take an integer m such that
# m -1 <= 
n*x < m.
[/prove]
Then
n * x < m = (m - 1) + 1 <= (n*x) + 1 < (n*x) + (n*(y-x))
= n * (x + (y - x)) = n * y.
m <=(n*x) + 1 < n * y.
Let us show that m < n*y.
Case m < (n*x) + 1. end.
Case m = (n*x) + 1. end.
end.
\frac{m}{n} < \frac{n*y}{n}. Indeed m < n*y and 1/n > 0.
Then
\frac{n*x}{n} < \frac{m}{n} < \frac{n*y}{n} = y.
Let p = \frac{m}{n}. Then p << QQ. x = \frac{n*x}{n} < p < y.
qed.

