#
# Families and tuples
# (Marcel Schütz, 2020)
#

#[prove off][check off]
[read FLib/Structures/NumberTheory/naturals.ftl]
[read FLib/Structures/Foundations/maps.ftl]
#[prove on][check on]


# 1. Families

# 1.1 Definitions

Definition FoundFam000. A family is a function.

Definition FoundFam005. Let I be an entity. A family over I is a family F such that dom(F) = I.


# 1.2 Subfamilies

Axiom FoundFam010. Let F be a family and x be an entity. x \in F iff x is a value of F.

Definition FoundFam015. Let F be a family. A subfamily of F is a family G such that G \subseteq F.


# 1.3 Families and classes

Definition FoundFam020. A family of classes is a family F such that every value of F is a class.


# 2. Sequences

Definition FoundFam025. A sequence is a family over NAT.


# 3. Tuples

Signature FoundFam030. Let n be a natural number. A tuple over n is a notion.

Axiom FoundFamxxx. Let n be a natural number and T be a tuple over n. Then dom(T) = {1, \ldots, n}.

Let a tuple stand for a tuple over some positive natural number.


Axiom FoundFamxxx. Let S,T be tuples. If dom(S) = dom(T) and S(x) = T(x) for all x \in dom(S) then
S = T.


Axiom FoundFamxxx. Let T be a tuple and x be an entity. x \in T iff x \in T(1).

# We need this axiom for tuples that represent structures, e.g. (X,+,0).


Axiom FoundFamxxx. Let S,T be tuples. Assume that dom(S) = dom(T) and S(x) = T(x) for all
x \in dom(S). Then S = T.


Let the first   component of t stand for t(1).
Let the second  component of t stand for t(2).
Let the third   component of t stand for t(3).
Let the fourth  component of t stand for t(4).
Let the fifth   component of t stand for t(5).
Let the sixth   component of t stand for t(6).
Let the seventh component of t stand for t(7).
Let the eigth   component of t stand for t(8).
Let the ninth   component of t stand for t(9).

Let the first   entry of t stand for t(1).
Let the second  entry of t stand for t(2).
Let the third   entry of t stand for t(3).
Let the fourth  entry of t stand for t(4).
Let the fifth   entry of t stand for t(5).
Let the sixth   entry of t stand for t(6).
Let the seventh entry of t stand for t(7).
Let the eigth   entry of t stand for t(8).
Let the ninth   entry of t stand for t(9).


# 3.1 Patterns for tuples

# 3.1.1 2-tuple


Let a couple        stand for a tuple over 2.
Let a double        stand for a tuple over 2.
Let an ordered pair stand for a tuple over 2.
Let a duad          stand for a tuple over 2.
Let a twin          stand for a tuple over 2.
Let a dual          stand for a tuple over 2.


Axiom FoundFam090. Let x0,x1 be entities. (x0,x1) is a couple.

Axiom FoundFam095. Let x0,x1 be entities. (x0,x1)(1) = x0.
Axiom FoundFam100. Let x0,x1 be entities. (x0,x1)(2) = x1.


# 3.1.2 3-tuple

Let a triple  stand for a tuple over 3.
Let a treble  stand for a tuple over 3.
Let a triplet stand for a tuple over 3.
Let a triad   stand for a tuple over 3.


Signature FoundFam105. Let x0,x1,x2 be entities. (x0,x1,x2) is a triple.

Axiom FoundFam110. Let x0,x1,x2 be entities. (x0,x1,x2)(1) = x0.
Axiom FoundFam115. Let x0,x1,x2 be entities. (x0,x1,x2)(2) = x1.
Axiom FoundFam120. Let x0,x1,x2 be entities. (x0,x1,x2)(3) = x2.

Let f(a,b,c) stand for f((a,b,c)).


# 3.1.3 4-tuple

Let a quadruple stand for a tuple over 4.
Let a quad      stand for a tuple over 4.
Let a tetrad    stand for a tuple over 4.

Signature FoundFam125. Let x0,x1,x2,x3 be entities. (x0,x1,x2,x3) is a quadruple.

Axiom FoundFam130. Let x0,x1,x2,x3 be entities. (x0,x1,x2,x3)(1) = x0.
Axiom FoundFam135. Let x0,x1,x2,x3 be entities. (x0,x1,x2,x3)(2) = x1.
Axiom FoundFam140. Let x0,x1,x2,x3 be entities. (x0,x1,x2,x3)(3) = x2.
Axiom FoundFam145. Let x0,x1,x2,x3 be entities. (x0,x1,x2,x3)(4) = x3.

Let f(a,b,c,d) stand for f((a,b,c,d)).


# 3.1.4 5-tuple

Let a quintuple stand for a tuple over 5.
Let a pentuple  stand for a tuple over 5.
Let a quint     stand for a tuple over 5.
Let a pentad    stand for a tuple over 5.


Signature FoundFam150. Let x0,x1,x2,x3,x4 be entities. (x0,x1,x2,x3,x4) is a quintuple.

Axiom FoundFam155. Let x0,x1,x2,x3,x4 be entities. (x0,x1,x2,x3,x4)(1) = x0.
Axiom FoundFam160. Let x0,x1,x2,x3,x4 be entities. (x0,x1,x2,x3,x4)(2) = x1.
Axiom FoundFam165. Let x0,x1,x2,x3,x4 be entities. (x0,x1,x2,x3,x4)(3) = x2.
Axiom FoundFam170. Let x0,x1,x2,x3,x4 be entities. (x0,x1,x2,x3,x4)(4) = x3.
Axiom FoundFam175. Let x0,x1,x2,x3,x4 be entities. (x0,x1,x2,x3,x4)(5) = x4.

Let f(a,b,c,d,e) stand for f((a,b,c,d,e)).


# 3.1.5 6-tuple

Let a sextuple stand for a tuple over 6.
Let a hextuple stand for a tuple over 6.

Signature FoundFam180. Let x0,x1,x2,x3,x4,x5 be entities. (x0,x1,x2,x3,x4,x5) is a sextuple.

Axiom FoundFam185. Let x0,x1,x2,x3,x4,x5 be entities. (x0,x1,x2,x3,x4,x5)(1) = x0.
Axiom FoundFam190. Let x0,x1,x2,x3,x4,x5 be entities. (x0,x1,x2,x3,x4,x5)(2) = x1.
Axiom FoundFam195. Let x0,x1,x2,x3,x4,x5 be entities. (x0,x1,x2,x3,x4,x5)(3) = x2.
Axiom FoundFam200. Let x0,x1,x2,x3,x4,x5 be entities. (x0,x1,x2,x3,x4,x5)(4) = x3.
Axiom FoundFam205. Let x0,x1,x2,x3,x4,x5 be entities. (x0,x1,x2,x3,x4,x5)(5) = x4.
Axiom FoundFam210. Let x0,x1,x2,x3,x4,x5 be entities. (x0,x1,x2,x3,x4,x5)(6) = x5.

Let f(a,b,c,d,e,g) stand for f((a,b,c,d,e,g)).


# 3.1.6 7-tuple

Let a septuple stand for a tuple over 7.
Let a heptuple stand for a tuple over 7.

Signature FoundFam215. Let x0,x1,x2,x3,x4,x5,x6 be entities. (x0,x1,x2,x3,x4,x5,x6) is a heptuple.

Axiom FoundFam220. Let x0,x1,x2,x3,x4,x5,x6 be entities. (x0,x1,x2,x3,x4,x5,x6)(1) = x0.
Axiom FoundFam225. Let x0,x1,x2,x3,x4,x5,x6 be entities. (x0,x1,x2,x3,x4,x5,x6)(2) = x1.
Axiom FoundFam230. Let x0,x1,x2,x3,x4,x5,x6 be entities. (x0,x1,x2,x3,x4,x5,x6)(3) = x2.
Axiom FoundFam235. Let x0,x1,x2,x3,x4,x5,x6 be entities. (x0,x1,x2,x3,x4,x5,x6)(4) = x3.
Axiom FoundFam240. Let x0,x1,x2,x3,x4,x5,x6 be entities. (x0,x1,x2,x3,x4,x5,x6)(5) = x4.
Axiom FoundFam245. Let x0,x1,x2,x3,x4,x5,x6 be entities. (x0,x1,x2,x3,x4,x5,x6)(6) = x5.
Axiom FoundFam250. Let x0,x1,x2,x3,x4,x5,x6 be entities. (x0,x1,x2,x3,x4,x5,x6)(7) = x6.


# 3.1.7 8-tuple

Let an octuple stand for a tuple over 8.

Signature FoundFam255. Let x0,x1,x2,x3,x4,x5,x6,x7 be entities. (x0,x1,x2,x3,x4,x5,x6,x7) is an
octuple.

[checktime 3]
Axiom FoundFam260. Let x0,x1,x2,x3,x4,x5,x6,x7 be entities. (x0,x1,x2,x3,x4,x5,x6,x7)(1) = x0.
Axiom FoundFam265. Let x0,x1,x2,x3,x4,x5,x6,x7 be entities. (x0,x1,x2,x3,x4,x5,x6,x7)(2) = x1.
Axiom FoundFam270. Let x0,x1,x2,x3,x4,x5,x6,x7 be entities. (x0,x1,x2,x3,x4,x5,x6,x7)(3) = x2.
Axiom FoundFam275. Let x0,x1,x2,x3,x4,x5,x6,x7 be entities. (x0,x1,x2,x3,x4,x5,x6,x7)(4) = x3.
Axiom FoundFam280. Let x0,x1,x2,x3,x4,x5,x6,x7 be entities. (x0,x1,x2,x3,x4,x5,x6,x7)(5) = x4.
Axiom FoundFam285. Let x0,x1,x2,x3,x4,x5,x6,x7 be entities. (x0,x1,x2,x3,x4,x5,x6,x7)(6) = x5.
Axiom FoundFam290. Let x0,x1,x2,x3,x4,x5,x6,x7 be entities. (x0,x1,x2,x3,x4,x5,x6,x7)(7) = x6.
Axiom FoundFam295. Let x0,x1,x2,x3,x4,x5,x6,x7 be entities. (x0,x1,x2,x3,x4,x5,x6,x7)(8) = x7.
[/checktime]


# 3.1.8 9-tuple

Let a nonuple stand for a tuple over 9.

Signature FoundFam300. Let x0,x1,x2,x3,x4,x5,x6,x7,x8 be entities. (x0,x1,x2,x3,x4,x5,x6,x7,x8) is a
nonuple.

[checktime 4]
Axiom FoundFam305. Let x0,x1,x2,x3,x4,x5,x6,x7,x8 be entities. (x0,x1,x2,x3,x4,x5,x6,x7,x8)(1) = x0.
Axiom FoundFam310. Let x0,x1,x2,x3,x4,x5,x6,x7,x8 be entities. (x0,x1,x2,x3,x4,x5,x6,x7,x8)(2) = x1.
Axiom FoundFam315. Let x0,x1,x2,x3,x4,x5,x6,x7,x8 be entities. (x0,x1,x2,x3,x4,x5,x6,x7,x8)(3) = x2.
Axiom FoundFam320. Let x0,x1,x2,x3,x4,x5,x6,x7,x8 be entities. (x0,x1,x2,x3,x4,x5,x6,x7,x8)(4) = x3.
Axiom FoundFam325. Let x0,x1,x2,x3,x4,x5,x6,x7,x8 be entities. (x0,x1,x2,x3,x4,x5,x6,x7,x8)(5) = x4.
Axiom FoundFam330. Let x0,x1,x2,x3,x4,x5,x6,x7,x8 be entities. (x0,x1,x2,x3,x4,x5,x6,x7,x8)(6) = x5.
Axiom FoundFam335. Let x0,x1,x2,x3,x4,x5,x6,x7,x8 be entities. (x0,x1,x2,x3,x4,x5,x6,x7,x8)(7) = x6.
Axiom FoundFam340. Let x0,x1,x2,x3,x4,x5,x6,x7,x8 be entities. (x0,x1,x2,x3,x4,x5,x6,x7,x8)(8) = x7.
Axiom FoundFam345. Let x0,x1,x2,x3,x4,x5,x6,x7,x8 be entities. (x0,x1,x2,x3,x4,x5,x6,x7,x8)(9) = x8.
[/checktime]


# 4. Products

# 4.1 Products over families of classes

Axiom FoundFam350. Let A be a family of classes. Prod(A) is a class such that

  Prod(A) = {a | a is a family over dom(A) and a(i) \in A(i) for all i \in dom(a)}.


Proposition FoundFam355. Let A be a family of classes. Assume that some value of A is empty. Then
Prod(A) is empty.

Proof.
  Assume the contrary. Take an element x of Prod(A). Take i \in dom(A) such that A(i) = \emptyset.
  Then x(i) \in A(i). Indeed Prod(A) = {a | a is a family over dom(A) and a(j) \in A(j) for all
  j \in dom(a)} (by FoundFam350). Hence we have a contradiction.
qed.


# 4.2 Cartesian products

Axiom FoundFam380. Let x,y be classes. x \times y is a class such that x \times y = {(a,b) | a \in x
and b \in y}.


Proposition FoundFam400. Let x be a class. x \times \emptyset = \emptyset.


Proposition FoundFam405. Let x be a class. \emptyset \times x = \emptyset.


Proposition FoundFam415. Let x,y be classes and u,v be entities. (u,v) \in x \times y iff u \in x
and v \in y.

Proof.
  x \times y = {(a,b) | a \in x and b \in y} (by FoundFam380).
qed.


Proposition FoundFam420. Let u,v,x,y be classes. Then

  (u \cup v) \times (x \cup y) =
  (((u \times x) \cup (v \times y)) \cup (u \times y)) \cup (v \times x).

Proof. [prove off] qed.


Corollary FoundFam425. Let x,y,z be classes. Then

  x \times (y \cup z) = (x \times y) \cup (x \times z).

Proof. [prove off] qed.


Corollary FoundFam430. Let x,y,z be classes. Then

  (x \cup y) \times z = (x \times z) \cup (y \times z).

Proof. [prove off] qed.


Proposition FoundFam435. Let u,v,x,y be classes. Then

  (u \cap v) \times (x \cap y) = (u \times x) \cap (v \times y).

Proof. [prove off] qed.


Corollary FoundFam440. Let x,y,z be classes. Then

  x \times (y \cap z) = (x \times y) \cap (x \times z).

Proof. [prove off] qed.


Corollary FoundFam445. Let x,y,z be classes. Then

  (x \cap y) \times z = (x \times z) \cap (y \times z).

Proof. [prove off] qed.


Corollary FoundFam450. Let x,y be classes. Then

  (x \times y) \cap (y \times x) = (x \cap y) \times (x \cap y).


# 4.3 The projection

Signature FoundFam060. Let A be an entity. The projection of A is a notion.

Axiom FoundFam061. Let A be a family of classes and p be the projection of A. Let j be an element of
dom(A). Then p_{j} is a map from Prod(A) to A(j).

Axiom FoundFam062. Let A be a family of classes and p be the projection of A. Let j be an element of
dom(A). Then p_{j}(x) = x(j) for all x \in Prod(A).


Axiom FoundFam064. Let X,Y be classes and p be the projection of X \times Y. Then p_{1} is a map
from X \times Y to X.

Axiom FoundFam065. Let X,Y be classes and p be the projection of X \times Y. Then p_{1}(x,y) = x for
all x \in X and all y \in Y.

Axiom FoundFam066. Let X,Y be classes and p be the projection of X \times Y. Then p_{2} is a map
from X \times Y to Y.

Axiom FoundFam067. Let X,Y be classes and p be the projection of X \times Y. Then p_{2}(x,y) = y for
all x \in X and all y \in Y.


# 4.4 Products of maps

Axiom FoundFam068. Let X,Y,A,B be classes. Let f be a map from A to X and g be a map from B to Y.
f \times g is a map from A \times B to X \times Y.

Axiom FoundFam069. Let X,Y,A,B be classes. Let f be a map from A to X and g be a map from B to Y.
For all a \in A and all b \in B we have (f \times g)(a,b) = (f(a),g(b)).


# 5. Exponentiation

# 5.1 Exponentiation of classes

Axiom FoundFam470. Let x,y be classes. x^{y} is a class such that

  x^{y} = {f | f is a family over y such that every value of f lies in x}.


# 5.2 Exponentiation of classes with natural numbers

Axiom FoundFam475. Let x be a class. x^{0} = `{\emptyset}`.

Axiom FoundFan480. Let x be a class. x^{1} = x.


Axiom FoundFam490. Let x be a class and n be a natural number that is greater than 1. x^{n} is a
class such that

  x^{n} = {t | t is a tuple over n such that t(u) \in x for all u \in dom(t)}.


# 6 Disjoint unions

Axiom FoundFam500. Let A be a family of classes. Coprod(A) is a class such that

  Coprod(A) = {x | x \in A(i) \times `{i}` for some i \in dom(A)}.


Axiom FoundFam505. Let x,y be classes. x \uplus y = (x \times `{0}`) \cup (y \times `{1}`).


Proposition FoundFam510. Let x,y be classes. x \uplus y is a class.


# 6.1 The inclusion

Signature FoundFam520. Let A be an entity. The inclusion of A is a notion.

Axiom FoundFam525. Let A be a family of classes and i be the inclusion of A. Let j be an element
of dom(A). Then i_{j} is a map from A(j) to Coprod(A).

Axiom FoundFam530. Let A be a family of classes and i be the inclusion of A. Let j be an element
of dom(A). Then for all x \in A(j) we have i_{j}(x) = (x,j).


Axiom FoundFam535. Let X,Y be classes and i be the inclusion of X \uplus Y. i_{1} is a map
from X to X \uplus Y.

Axiom FoundFam540. Let X,Y be classes and i be the inclusion of X \uplus Y. i_{1}(x) = (x,0)
for all x \in X.

Axiom FoundFam545. Let X,Y be classes and i be the inclusion of X \uplus Y. i_{2} is a map
from Y to X \uplus Y.

Axiom FoundFam550. Let X,Y be classes and i be the inclusion of X \uplus Y. i_{2}(y) = (y,1)
for all y \in Y.
