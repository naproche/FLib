#
# Real numbers
# (Marcel Schütz, 2020)
#

[read ForTheLib/NumberTheory/rationals.ftl]
[read ForTheLib/Sets/set-systems.ftl]


# 1. Definition

Signature AnaRe000. A real number is a notion.

Definition AnaRe005. REAL = {x | x is a real number}.


Axiom AnaRe010. Every rational number is a real number.

Axiom AnaRe015. Let Q be a nonempty subset of RAT that has an upper bound in RAT. Then Q has a
least upper bound in REAL.

Axiom AnaRe020. Let Q be a nonempty subset of RAT that has an upper bound in RAT. Let x,y be least
upper bounds of Q in REAL. Then x = y.

Axiom AnaRe025. Every real number is the least upper bound of some subset of RAT in REAL.


Definition AnaRe030. An irrational number is a real number that is not a rational number.


# 2. The set of real numbers

Theorem AnaRe035. REAL is an uncountable set.

Proof. [prove off] qed.


# 3. The extended real numbers

Signature AnaRe040. \infty is an element.

Let +\infty stand for \infty.


Definition AnaRe045. An extended real number is an object x such that x is a real number or
x = \infty or x = -\infty.


Definition AnaRe050. EXTREAL = {x | x is an extended real number}.


Proposition AnaRe055. EXTREAL is a set.

Proof. [prove off] qed.


Proposition AnaRe060. REAL \subsetneq EXTREAL.

Proof. [prove off] qed.


Axiom AnaRe065. \infty is greater than every real number.

Axiom AnaRe070. -\infty is less than every real number.


Proposition AnaRe075. Every real number is an extended real number.


# 4. Intervals

Definition AnaRe080. Let x,y be extended real numbers. [x,y] = {z in EXTREAL | x \leq z \leq y}.

Definition AnaRe085. Let x,y be extended real numbers. ]x,y] = {z in EXTREAL | x < z \leq y}.

Definition AnaRe090. Let x,y be extended real numbers. [x,y[ = {z in EXTREAL | x \leq z < y}.

Definition AnaRe095. Let x,y be extended real numbers. ]x,y[ = {z in EXTREAL | x < z < y}.


Definition AnaRe100. An interval is a subset A of REAL such that there are extended real numbers x,y
such that A = [x,y] or A = [x,y[ or A = ]x,y] or A = ]x,y[.

Definition AnaRe105. An halfopen interval is a subset A of REAL such that there are extended real
numbers x,y such that A = [x,y[ or A = ]x,y].


Proposition AnaRe120. REAL = ]-\infty, \infty[.

Proof. [prove off] qed.


# 5. Arithmetic

# 5.1 Sum

Axiom AnaRe125. Let x,y be real numbers. Then x + y is a real number.


Axiom AnaRe130. Let x,y,z be real numbers. Then

  x + (y + z) = (x + y) + z.


Axiom AnaRe135. Let x,y be real numbers. Then

  x + y = y + x.


Axiom AnaRe140. Let x be a real number. Then

  x + 0 = x.


# 5.2 Difference

Axiom AnaRe145. Let x,y be real numbers. Then x - y is a real number.


Axiom AnaRe150. Let x,y be real numbers. Then

  (x - y) + y = x.


Axiom AnaRe155. Let x be a real number. Then

  -x = 0 - x.


Proposition AnaRe156. Let x,y be real numbers. x + (y - x) = y.

Proof. [prove off] qed.


# 5.3 Product

Axiom AnaRe160. Let x,y be real numbers. Then x \cdot y is a real number.


Axiom AnaRe165. Let x,y,z be real numbers. Then

  x \cdot (y \cdot z) = (x \cdot y) \cdot z.


Axiom AnaRe170. Let x,y be real numbers. Then

  x \cdot y = y \cdot x.


Axiom AnaRe175. Let x be a real number. Then

  x \cdot 1 = x.


Axiom AnaRe180. Let x,y,z be real numbers. x \cdot (y + z) = (x \cdot y) + (x \cdot z).


# 5.4 Quotient

Axiom AnaRe185. Let x,y be real numbers. Assume that y \neq 0. Then x/y is a real number.


Axiom AnaRe190. Let x,y be real numbers. Assume that y \neq 0. Then

  (x/y) \cdot y = x.



# 5.6 Exponentiation

Axiom AnaRe195. Let x be a real number. Then

  x^{0} = 1.


Axiom AnaRe200. Let x be a real number and n be a natural number. Then

  x^{n + 1} = x^{n} \cdot x.


Axiom AnaRe205. Let x be a real number and n be a natural number. Then

  x^{-n} = 1/(x^{n}).


# 5.7 Absolute value

Axiom AnaRe210. Let x be a real number. If x is nonnegative then

  |x| = x.


Axiom AnaRe215. Let x be a real number. If x is negative then

  |x| = -x.


# 6. Ordering

Axiom AnaRe219. Let x,y be real numbers. x \leq y iff x < y or x = y.


Axiom AnaRe220. Let x be a real number. Then

  not x < x.


Axiom AnaRe225. Let x,y be real numbers. Then

  x < y or x = y or x > y.


Axiom AnaRe230. Let x,y,z be real numbers. Then

  x < y < z  =>  x < z.


Axiom AnaRe235. Let x,y,z be real numbers. Then

  x < y  =>  x + z < y + z.


Axiom AnaRe240. Let x,y,z be real numbers. Assume that z > 0. Then

  x < y  =>  x \cdot z < y \cdot z.


Proposition AnaRe241. Let x,y be real numbers. Assume x < y. Then 0 < y - x.

Proof. [prove off] qed.


Proposition AnaRe242. Let x,y,z be real numbers. Assume that z is positive. Assume x = y - z. Then 
x is less than y.

Proof. [prove off] qed.


Proposition AnaRe243. Let x,y,a,b be real numbers. Assume x \leq a and y \leq b. Then
x + y \leq a + b.

Proof. [prove off] qed.


Proposition AnaRe244. Let x,y,z be real numbers. Assume that x \leq y \leq z. Then x \leq z.

Proof. [prove off] qed.


Proposition AnaRe245. Let x,y be real numbers. Assume y > 0. Then x - y < x.

Proof. [prove off] qed.


Proposition AnaRe246. Let x,y,z be real numbers. Assume y < z. Then x + y < x + z.

Proof. [prove off] qed.


Proposition AnaRe247. Let x,y,z be real numbers. Assume x \leq y < z. Then x < z.

Proof. [prove off] qed.


# 7. Roots

Proposition AnaRe255. Let x be a nonnegative real number and n be a positive natural number. There
is a nonnegative real number y such that y^{n} = x.

Proof. [prove off] qed.


Proposition AnaRe256. Let x,y,z be a nonnegative real number and n be a positive natural number.
Then

  y^{n} = x = z^{n}  =>  y = z.

Proof. [prove off] qed.


Definition AnaRe257. Let x be a nonnegative real number and n be a positive natural number.
root(x,n) is a nonnegative real number such that

  root(x,n)^{n} = x.

Let sqrt(x) stand for root(x,2).


# 8. Open and closed sets

Proposition AnaRe260. Let A be a subset of REAL. Then every element of A is a real number.


# 8.1 Open sets

Axiom AnaRe265. Let A be a subset of REAL. A is open in REAL iff for all x \in A there is a positive
real number epsilon such that

  ]x - epsilon, x + epsilon[ \subseteq A.


Axiom AnaRe270. Let I be an interval. I is open iff I is open in REAL.


Proposition AnaRe271. Let I be an open interval. Then I = ]a,b[ for some extended real numbers a,b.

Proof. [prove off] qed.


Corollary AnaRe275. \emptyset is open in REAL.

Corollary AnaRe280. REAL is open in REAL.


Axiom AnaRe285. Let A,B be subsets of REAL. Assume that A \subseteq B. A is open in B iff
A = B \cap U for some subset U of REAL that is open in REAL.


Proposition AnaRe290. Let A be a subset of REAL. Let X be a set. Assume that
X = {U | U is a subset of A that is open in A}. X is closed under arbitrary unions.

Proof. [prove off] qed.


Proposition AnaRe295. Let A be a subset of REAL. Let X be a set. Assume that
X = {U | U is a subset of A that is open in A}. X is closed under finite intersections.

Proof. [prove off] qed.


# 8.2 Closed sets

Axiom AnaRe300. Let A be a subset of REAL. A is closed in REAL iff REAL \setminus A is open in
REAL.

Axiom AnaRe305. Let I be an interval. I is open iff I is open in REAL.


Corollary AnaRe310. \emptyset is closed in REAL.

Corollary AnaRe315. REAL is closed in REAL.


Axiom AnaRe320. Let A,B be subsets of REAL. Assume that A \subseteq B. A is closed in B iff
A \setminus B is open in B.


Proposition AnaRe321. Let I be a closed interval. Then I = [a,b] for some  real numbers a,b or
I = ]-\infty,\infty[.

Proof. [prove off] qed.


Proposition AnaRe325. Let A be a subset of REAL. Let X be a set. Assume that
X = {U | U is a subset of A that is closed in A}. X is closed under arbitrary intersections.

Proof. [prove off] qed.


Proposition AnaRe330. Let A be a subset of REAL. Let X be a set. Assume that
X = {U | U is a subset of A that is closed in A}. X is closed under finite unions.

Proof. [prove off] qed.
