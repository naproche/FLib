#
# Families
# (Marcel Schütz, 2020)
#

#[prove off]
[read ForTheLib/NumberTheory/naturals.ftl]
[read ForTheLib/Foundations/functions.ftl]
#[prove on]


# 1. Families

# 1.1 Definitions

Definition FoundFam000. A family is a function.

Definition FoundFam005. Let I be an object. A family over I is a family F such that dom(F) = I.


# 1.2 Subfamilies

Axiom FoundFam010. Let F be a family and x be an object. x \in F iff x is a value of F.

Definition FoundFam015. Let F be a family. A subfamily of F is a family G such that G \subseteq F.


# 1.3 Families and classes

Definition FoundFam020. A family of classes is a family F such that every value of F is a class.


# 2. Sequences

Definition FoundFam025. A sequence is a family over NAT.

Definition FoundFam030. Let n be a natural number. A sequence of length n is a family over
{1, \ldots, n}.

Definition FoundFam035. A finite sequence is a sequence of length (some natural number).

Let a tuple stand for a finite sequence.


Proposition FoundFam040. Let n be a natural number and s be a sequence of length n. dom(s) = {1, \ldots, n}.


# 3. Tuples

Definition FoundFam045. Let t be a tuple. Assume that 1 \in dom(t). The first   component of t is t(1).

Definition FoundFam050. Let t be a tuple. Assume that 2 \in dom(t). The second  component of t is t(2).

Definition FoundFam055. Let t be a tuple. Assume that 3 \in dom(t). The third   component of t is t(3).

Definition FoundFam060. Let t be a tuple. Assume that 4 \in dom(t). The fourth  component of t is t(4).

Definition FoundFam065. Let t be a tuple. Assume that 5 \in dom(t). The fifth   component of t is t(5).

Definition FoundFam070. Let t be a tuple. Assume that 6 \in dom(t). The sixth   component of t is t(6).

Definition FoundFam075. Let t be a tuple. Assume that 7 \in dom(t). The seventh component of t is t(7).

Definition FoundFam080. Let t be a tuple. Assume that 8 \in dom(t). The eigth   component of t is t(8).

Definition FoundFam085. Let t be a tuple. Assume that 9 \in dom(t). The ninth   component of t is t(9).


# 3.1 2-tuple


Let a couple        stand for a sequence of length 2.
Let a double        stand for a sequence of length 2.
Let an ordered pair stand for a sequence of length 2.
Let a duad          stand for a sequence of length 2.
Let a twin          stand for a sequence of length 2.
Let a dual          stand for a sequence of length 2.


Axiom FoundFam090. Let x0,x1 be objects. (x0,x1) is a couple.

Axiom FoundFam095. Let x0,x1 be objects. (x0,x1)(1) = x0.
Axiom FoundFam100. Let x0,x1 be objects. (x0,x1)(2) = x1.


# 3.2 3-tuple

Let a triple  stand for a sequence of length 3.
Let a treble  stand for a sequence of length 3.
Let a triplet stand for a sequence of length 3.
Let a triad   stand for a sequence of length 3.


Signature FoundFam105. Let x0,x1,x2 be objects. (x0,x1,x2) is a triple.

Axiom FoundFam110. Let x0,x1,x2 be objects. (x0,x1,x2)(1) = x0.
Axiom FoundFam115. Let x0,x1,x2 be objects. (x0,x1,x2)(2) = x1.
Axiom FoundFam120. Let x0,x1,x2 be objects. (x0,x1,x2)(3) = x2.


# 3.3 4-tuple

Let a quadruple stand for a sequence of length 4.
Let a quad      stand for a sequence of length 4.
Let a tetrad    stand for a sequence of length 4.

Signature FoundFam125. Let x0,x1,x2,x3 be objects. (x0,x1,x2,x3) is a quadruple.

Axiom FoundFam130. Let x0,x1,x2,x3 be objects. (x0,x1,x2,x3)(1) = x0.
Axiom FoundFam135. Let x0,x1,x2,x3 be objects. (x0,x1,x2,x3)(2) = x1.
Axiom FoundFam140. Let x0,x1,x2,x3 be objects. (x0,x1,x2,x3)(3) = x2.
Axiom FoundFam145. Let x0,x1,x2,x3 be objects. (x0,x1,x2,x3)(4) = x3.


# 3.4 5-tuple

Let a quintuple stand for a sequence of length 5.
Let a pentuple  stand for a sequence of length 5.
Let a quint     stand for a sequence of length 5.
Let a pentad    stand for a sequence of length 5.


Signature FoundFam150. Let x0,x1,x2,x3,x4 be objects. (x0,x1,x2,x3,x4) is a quintuple.

Axiom FoundFam155. Let x0,x1,x2,x3,x4 be objects. (x0,x1,x2,x3,x4)(1) = x0.
Axiom FoundFam160. Let x0,x1,x2,x3,x4 be objects. (x0,x1,x2,x3,x4)(2) = x1.
Axiom FoundFam165. Let x0,x1,x2,x3,x4 be objects. (x0,x1,x2,x3,x4)(3) = x2.
Axiom FoundFam170. Let x0,x1,x2,x3,x4 be objects. (x0,x1,x2,x3,x4)(4) = x3.
Axiom FoundFam175. Let x0,x1,x2,x3,x4 be objects. (x0,x1,x2,x3,x4)(5) = x4.


# 3.5 6-tuple

Let a sextuple stand for a sequence of length 6.
Let a hextuple stand for a sequence of length 6.

Signature FoundFam180. Let x0,x1,x2,x3,x4,x5 be objects. (x0,x1,x2,x3,x4,x5) is a sextuple.

Axiom FoundFam185. Let x0,x1,x2,x3,x4,x5 be objects. (x0,x1,x2,x3,x4,x5)(1) = x0.
Axiom FoundFam190. Let x0,x1,x2,x3,x4,x5 be objects. (x0,x1,x2,x3,x4,x5)(2) = x1.
Axiom FoundFam195. Let x0,x1,x2,x3,x4,x5 be objects. (x0,x1,x2,x3,x4,x5)(3) = x2.
Axiom FoundFam200. Let x0,x1,x2,x3,x4,x5 be objects. (x0,x1,x2,x3,x4,x5)(4) = x3.
Axiom FoundFam205. Let x0,x1,x2,x3,x4,x5 be objects. (x0,x1,x2,x3,x4,x5)(5) = x4.
Axiom FoundFam210. Let x0,x1,x2,x3,x4,x5 be objects. (x0,x1,x2,x3,x4,x5)(6) = x5.


# 3.6 7-tuple

Let a septuple stand for a sequence of length 7.
Let a heptuple stand for a sequence of length 7.

Signature FoundFam215. Let x0,x1,x2,x3,x4,x5,x6 be objects. (x0,x1,x2,x3,x4,x5,x6) is a heptuple.

Axiom FoundFam220. Let x0,x1,x2,x3,x4,x5,x6 be objects. (x0,x1,x2,x3,x4,x5,x6)(1) = x0.
Axiom FoundFam225. Let x0,x1,x2,x3,x4,x5,x6 be objects. (x0,x1,x2,x3,x4,x5,x6)(2) = x1.
Axiom FoundFam230. Let x0,x1,x2,x3,x4,x5,x6 be objects. (x0,x1,x2,x3,x4,x5,x6)(3) = x2.
Axiom FoundFam235. Let x0,x1,x2,x3,x4,x5,x6 be objects. (x0,x1,x2,x3,x4,x5,x6)(4) = x3.
Axiom FoundFam240. Let x0,x1,x2,x3,x4,x5,x6 be objects. (x0,x1,x2,x3,x4,x5,x6)(5) = x4.
Axiom FoundFam245. Let x0,x1,x2,x3,x4,x5,x6 be objects. (x0,x1,x2,x3,x4,x5,x6)(6) = x5.
Axiom FoundFam250. Let x0,x1,x2,x3,x4,x5,x6 be objects. (x0,x1,x2,x3,x4,x5,x6)(7) = x6.


# 3.7 8-tuple

Let an octuple stand for a sequence of length 8.

Signature FoundFam255. Let x0,x1,x2,x3,x4,x5,x6,x7 be objects. (x0,x1,x2,x3,x4,x5,x6,x7) is an octuple.

[checktime 3]
Axiom FoundFam260. Let x0,x1,x2,x3,x4,x5,x6,x7 be objects. (x0,x1,x2,x3,x4,x5,x6,x7)(1) = x0.
Axiom FoundFam265. Let x0,x1,x2,x3,x4,x5,x6,x7 be objects. (x0,x1,x2,x3,x4,x5,x6,x7)(2) = x1.
Axiom FoundFam270. Let x0,x1,x2,x3,x4,x5,x6,x7 be objects. (x0,x1,x2,x3,x4,x5,x6,x7)(3) = x2.
Axiom FoundFam275. Let x0,x1,x2,x3,x4,x5,x6,x7 be objects. (x0,x1,x2,x3,x4,x5,x6,x7)(4) = x3.
Axiom FoundFam280. Let x0,x1,x2,x3,x4,x5,x6,x7 be objects. (x0,x1,x2,x3,x4,x5,x6,x7)(5) = x4.
Axiom FoundFam285. Let x0,x1,x2,x3,x4,x5,x6,x7 be objects. (x0,x1,x2,x3,x4,x5,x6,x7)(6) = x5.
Axiom FoundFam290. Let x0,x1,x2,x3,x4,x5,x6,x7 be objects. (x0,x1,x2,x3,x4,x5,x6,x7)(7) = x6.
Axiom FoundFam295. Let x0,x1,x2,x3,x4,x5,x6,x7 be objects. (x0,x1,x2,x3,x4,x5,x6,x7)(8) = x7.
[/checktime]


# 3.8 9-tuple

Let a nonuple stand for a sequence of length 9.

Signature FoundFam300. Let x0,x1,x2,x3,x4,x5,x6,x7,x8 be objects. (x0,x1,x2,x3,x4,x5,x6,x7,x8) is a nonuple.

[checktime 4]
Axiom FoundFam305. Let x0,x1,x2,x3,x4,x5,x6,x7,x8 be objects. (x0,x1,x2,x3,x4,x5,x6,x7,x8)(1) = x0.
Axiom FoundFam310. Let x0,x1,x2,x3,x4,x5,x6,x7,x8 be objects. (x0,x1,x2,x3,x4,x5,x6,x7,x8)(2) = x1.
Axiom FoundFam315. Let x0,x1,x2,x3,x4,x5,x6,x7,x8 be objects. (x0,x1,x2,x3,x4,x5,x6,x7,x8)(3) = x2.
Axiom FoundFam320. Let x0,x1,x2,x3,x4,x5,x6,x7,x8 be objects. (x0,x1,x2,x3,x4,x5,x6,x7,x8)(4) = x3.
Axiom FoundFam325. Let x0,x1,x2,x3,x4,x5,x6,x7,x8 be objects. (x0,x1,x2,x3,x4,x5,x6,x7,x8)(5) = x4.
Axiom FoundFam330. Let x0,x1,x2,x3,x4,x5,x6,x7,x8 be objects. (x0,x1,x2,x3,x4,x5,x6,x7,x8)(6) = x5.
Axiom FoundFam335. Let x0,x1,x2,x3,x4,x5,x6,x7,x8 be objects. (x0,x1,x2,x3,x4,x5,x6,x7,x8)(7) = x6.
Axiom FoundFam340. Let x0,x1,x2,x3,x4,x5,x6,x7,x8 be objects. (x0,x1,x2,x3,x4,x5,x6,x7,x8)(8) = x7.
Axiom FoundFam345. Let x0,x1,x2,x3,x4,x5,x6,x7,x8 be objects. (x0,x1,x2,x3,x4,x5,x6,x7,x8)(9) = x8.
[/checktime]


# 4. Operations on families

# 4.1 Products

Axiom FoundFam350. Let A be a family of classes. Prod(A) is a class such that

  Prod(A) = {a | a is a family over dom(A) and a(i) \in A(i) for all i \in dom(a)}.


Proposition FoundFam355. Let A be a family of classes. Assume that some value of A is empty. Then Prod(A) is
empty.

Proof.
  Assume the contrary. Take an element x of Prod(A). Take i \in dom(A) such that A(i) = \emptyset.
  Then x(i) \in A(i) (by FoundFam350). Contradiction.
qed.


# 4.2 Exponentiation

Axiom FoundFam360. Let x,y be classes. x^{y} is a class such that

  x^{y} = {f | f is a family over y such that every value of f lies in x}.


Axiom FoundFam370. Let x be a class and n be a natural number. x^{n} is a class such that

  x^{n} = {f | f is a sequence of length n such that every value of f lies in x}.


Axiom FoundFam380. Let x,y be classes. x \times y = Prod((x,y)).


Proposition FoundFam390. Let x,y be classes. (x,y) is a family of classes.

Proof.
   dom((x,y)) = {1,2}. (x,y)(1) = x and (x,y)(2) = y. For all values v of (x,y) we have v = (x,y)(u)
   for some u \in dom((x,y)).
qed.


Proposition FoundFam395. Let x,y be classes. x \times y is a class.


Proposition FoundFam400. Let x be a class. x \times \emptyset = \emptyset.

Proof. [prove off] qed.


Proposition FoundFam405. Let X be a class. \emptyset \times X = \emptyset.

Proof. [prove off] qed.


Proposition FoundFam410. Let X,Y be classes. X \times Y = {(x,y) | x \in X and y \in Y}.

Proof. [prove off] qed.


Proposition FoundFam415. Let X,Y be classes and x,y be objects. (x,y) \in X \times Y iff x \in X and y \in Y.

Proof. [prove off] qed.


# 4.3 Disjoint union

Axiom FoundFam430. Let A be a family of classes. Coprod(A) is a class such that

  Coprod(A) = {x | x \in A(i) \times `{i}` for some i \in dom(A)}.


Axiom FoundFam435. Let x,y be classes. x \uplus y = Coprod((x,y)).


Proposition FoundFam440. Let x,y be classes. x \uplus y is a class.
