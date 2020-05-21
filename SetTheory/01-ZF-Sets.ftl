# 1-ZF-Sets

# Here we introduce a new notion "zfsets" which are the set-theoretical sets. So we can distinguish the real sets
# (zfsets) with (proper) classes (sets).
# We stated the ZF-axioms for zfsets, so we can proof which sets are zfsets and which sets are proper classes.

# /VV is now the set of all zfsets, using foundation we see that /VV is a proper class.

# An axiom is that every object of a set is a zfset (since a proper class cannot be an element of a class).
# Therefore we have to pay attention which set-constructions we define.
# For example we must not define pairs {a,b} where a or b might be a proper class which would lead to an axiomatic contradiction.

# We did not introduce functions yet, so we do not have replacement.

# Later on we introduce ordinals, the class /Ord of all ordinals, some basic lemmata about ordinals and /NN, the set of natural numbers.

# Main Results:

# - /VV is a proper class
# - /Ord is a proper class
# - x zfset, x /subset /Ord => /bigcup x /in /Ord
# - ordinals are totally ordered
# - /NN is a zfset
# - /NN /in /Lim


[synonym zfset/-s]

Signature. A ZFset is a notion.

Axiom. Let x be a ZFset. Then x is a set.


# General Syntax

Let x /in y stand for x is an element of y.
Let x /notin y stand for x is not an element of y.
Let x /neq y stand for x != y.


# Pretyped Variables

Let w,x,y,z,W,X,Y,Z stand for ZFSets.
Let a,b,c,d,A,B,C,D stand for sets.


# Introduction of Emptyset, Universe

Axiom. Let a, b be sets. (Forall c (c /in a <=> c /in b)) => a = b.
Axiom. Let a be a set. Let b be an object. Let b /in a. Then b is a ZFset.

Definition Emptyset. The empty set is {ZFset x | x /neq x}.
Let /emptyset stand for the empty set.

Definition. Let a be a set. a is empty iff a = /emptyset.
Definition. Let a be a set. a is nonempty iff exists b (b /in a).

Lemma. Let a be a set. Let a be nonempty. Then a /neq /emptyset.
Lemma. Let a be a set. Let a /neq /emptyset. Then exists x (x /in a).

Definition Universe. The universe is {ZFset x | x = x}.
Let /VV stand for the universe.

Definition Subset. A subset of A is a set B such that
forall c (c /in B => c /in A).
Let B /subset A stand for B is a subset of A.

Lemma. Let a,b be sets. Let a /subset b /\ b /subset a. Then a = b.

Lemma. /VV is a set.

# Here we distinguish between "sets" (these refer to classes) and "ZFsets" (set theoretical sets).




# ZF-Axioms



Axiom Empty. /emptyset is a ZFset.

Definition PairGen. Let a,b be ZFsets. The pair of a and b is {ZFset c | c = a \/ c = b}.
Let <a , b> denote the pair of a and b.

Axiom Pair. Let x, y /in /VV. Then <x, y> /in /VV.

Lemma PairAlt. Forall x,y exists z forall b (b /in z iff b = x \/ b = y).
Proof. Let x,y be ZFsets. Define f = {ZFset b | b = x \/ b = y}.
Then f = <x, y>.
Then f is a ZFset (by Pair). Then (forall b (b /in f iff b = x \/ b = y)).
qed.


Definition UnionGen. Let a be a ZFset. The unionsing of a is
{ZFset b | exists w (w /in a /\ b /in w)}. 
Let /bigcup a denote the unionsing of a.

Axiom Union. Let x /in /VV. Then /bigcup x /in /VV.

Lemma UnionAlt. Forall x exists y forall z (z /in y iff exists w (w /in x /\ z /in w)).
Proof. Let x be a ZFset. Define f = {ZFset b | exists w (w /in x /\ b /in w)}.
Then f = /bigcup x.
Then f is a ZFset (by Union). Then forall z (z /in f iff exists w (w /in x /\ z /in w)).
qed.



Axiom Sep. Let x /in /VV. Let a /subset x. Then a /in /VV.


Definition PowerGen. The power set of X is
{ZFset x | x /subset X}.
Let /P X stand for the power set of X.


Axiom Power. Let x be a ZFset. Then /P x is a ZFset.

Lemma PowerAlt. Forall x exists y forall z (z /in y iff z /subset x).
Proof. Let x be a ZFset. Define f = {ZFset b | b /subset x}. Then f is a ZFset (by Power).
Then forall z (z /in f iff z /subset x).
qed.


# Axiom Rep. MISSING (later, when we define functions).


Axiom Found. Let A be a nonempty set. Then there is a ZFset b such that 
(b /in A /\ forall c (c /in b => c /notin A)).

Lemma FoundTest0. Forall x (x /notin x).
Proof by contradiction. Assume the contrary. Take a ZFset x such that x /in x.
Then <x, x> is a nonempty ZFset.
Forall y /in <x, x> (y = x).
Forall y /in <x, x> (x /in y /\ x /in <x, x>).
Contradiction.
qed.

Lemma FoundTest1. /VV is not a ZFset.

Lemma. Let x be a ZFset. Let a = {x}. Then a is a ZFset.
Proof. x is a ZFset. Define A = {ZFset b | b = x}. Then A = <x, x>.
Then A is a ZFset (by Pair).
A = a.
qed.




# Arithmetic


Definition Union. The union of X and Y is 
{ZFset x | x /in X or x /in Y}.
Let X /cup Y stand for the union of X and Y.

Definition Intersection. The intersection of A and B is 
{ZFset x | x /in A and x /in B}.
Let A /cap B stand for the intersection of A and B.

Definition Difference. The difference of X and Y is 
{ZFset x | x /in X and x /notin Y}.
Let X /setminus Y stand for the difference of X and Y.

Definition BigIntersection. The bigintersection of A is
{ZFset x | forall y (y /in A => x /in y)}.
Let /bigcap A stand for the bigintersection of A.

Definition Singleton. The singleton set of X is
{ZFset x | x = X}.
Let <X> stand for the singleton set of X.





[synonym class/-es]

Signature. A proper class is a notion.

Axiom. Let L be a proper class. Then L is a set.
Axiom. Let a be a set. a is a proper class iff a /notin /VV.


Lemma. /VV is a proper class.






# Ordinals


Definition transitive. Let A be a set. A is transitive iff forall x,y (y /in A /\ x /in y => x /in A).
Let Trans(A) stand for A is transitive.

Lemma. Trans(/emptyset).

[synonym ordinal/-s]

Signature. An ordinal is a notion.

Let alpha, beta, gamma, delta stand for ordinals.

Axiom. Let alpha be an ordinal. Then alpha is a ZFset.

Signature. x + y is a ZFset.
Signature. 0 is a ZFset.
Signature. 1 is a ZFset.

Lemma. Let alpha be an ordinal. Then alpha is a set.

Axiom. Let alpha be a ZFset. alpha is an ordinal iff ( Trans(alpha) /\ forall y (y /in alpha => Trans(y) )).

Definition Trans. The class of transitives is
{ZFset x | Trans(x)}.
Let /Trans stand for the class of transitives.

Definition Ord. The class of ordinals is
{set x | x is an ordinal}.
Let /Ord stand for the class of ordinals.

Axiom. 0 = /emptyset.

Lemma. 0 is an ordinal.

Axiom. Let alpha be a ZFset. Then alpha + 1 is {ZFset x | x /in alpha \/ x = alpha }.

Axiom. 1 = 0 + 1.

Lemma. /Ord is a set and /Trans is a set.

Lemma. /emptyset /in /Trans and /emptyset /in /Ord.

Lemma. /Ord /subset /Trans.

Lemma. Let alpha be an ordinal. Then alpha + 1 is an ordinal.
Proof. alpha + 1 is transitive. Forall x /in alpha + 1 (x is transitive).
qed.

Lemma. Let alpha be an ordinal. Let x be an object. Let x /in alpha. Then x is an ordinal.

Lemma. Trans(/Ord).

Lemma. /Ord is a proper class.

Lemma. Let A be a set. Let A /subset /Ord. Let A /neq /emptyset.
Then /bigcap A is an ordinal.
Proof. /bigcap A is transitive.
A /neq /emptyset. Take a ZFset x such that x /in A.
/bigcap A is a ZFset.
qed.

Lemma. Let x be a ZFSet. Let x /subset /Ord. Then /bigcup x is an ordinal.
Proof. /bigcup x is transitive.
qed.

Lemma. Forall alpha (alpha /in alpha + 1).

Lemma. Let alpha be an ordinal. Then alpha = /emptyset \/ /emptyset /in alpha.
Proof. Let alpha /neq /emptyset. Take a ZFset b such that 
(b /in alpha /\ forall c (c /in b => c /notin alpha)).
qed.

Lemma. Forall alpha, beta (alpha /in beta \/ beta /in alpha \/ alpha = beta).

Proof by contradiction. Assume the contrary.
Define A = {ordinal alpha | exists beta (not (alpha /in beta \/ beta /in alpha \/ alpha = beta)) }.
A is nonempty.
Take a ZFset alpha such that (alpha /in A /\ forall c (c /in alpha => c /notin A)).
alpha is an ordinal.
Define B = {ordinal beta |  (not (alpha /in beta \/ beta /in alpha \/ alpha = beta))}.
B is nonempty.
Take a ZFset beta such that (beta /in B /\ forall c (c /in beta => c /notin B)).
beta is an ordinal.
Not (alpha /in beta \/ beta /in alpha \/ alpha = beta).
#Let alpha1 be a ZFset. Let alpha1 /in alpha. Then (alpha1 /in beta \/ beta /in alpha1 \/ alpha1 = beta).
#Then alpha1 /in beta.
#Let beta1 be a ZFset. Let beta1 /in beta. Then (alpha /in beta1 \/ beta1 /in alpha \/ alpha = beta1).
#Then beta1 /in alpha.
alpha /subset beta.
beta /subset alpha.
alpha = beta.
Contradiction.
qed.


Lemma. Let A /subset /Ord. Let A /neq /emptyset. Then exists alpha (alpha /in A /\ forall beta /in A (alpha = beta \/ alpha /in beta)).
Proof.
qed.

Lemma. Let alpha, beta be ordinals. Let alpha /in beta. Then alpha /subset beta.

Signature. Let A be a set. The minimum of A is a notion.

Axiom.  Let A /subset /Ord. Let A /neq /emptyset. Let alpha be an ordinal. alpha is the minimum of A iff (alpha /in A /\ forall beta /in A (alpha = beta \/ alpha /in beta)).

Lemma. Let A /subset /Ord. Let A /neq /emptyset. Let alpha, beta be ordinals. Let alpha, beta be the minimum of A. Then alpha = beta.

Signature. A successor ordinal is a notion.
Signature. A limit ordinal is a notion.

Axiom successor. Let alpha be an ordinal. alpha is a successor ordinal iff exists beta (alpha = beta + 1).

Definition Succ. The class of successor ordinals is
{ordinal alpha | alpha is a successor ordinal }.
Let /Succ stand for the class of successor ordinals.

Lemma. 1 /in /Succ.
Lemma. 0 /notin /Succ.

Axiom limit. Let gamma be an ordinal. gamma is a limit ordinal iff (gamma /neq /emptyset /\ gamma /notin /Succ).

Definition Lim. The class of limit ordinals is
{ordinal alpha | alpha is a limit ordinal }.
Let /Lim stand for the class of limit ordinals.

Lemma. 0 /notin /Lim.
Lemma. 1 /notin /Lim.


Axiom Infinity. Exists x (/emptyset /in x /\ forall y /in x ((y + 1) /in x) ).




# Natural Numbers


[synonym number/-s]

Signature. A natural number is a notion.

Let k,l,m,n stand for natural numbers.

Axiom. Let n be a natural number. Then n is an ordinal.


Definition. The class of inductive sets is
{ZFSet x |  (/emptyset /in x /\ forall y /in x ((y + 1) /in x) ) }.
Let /Ind stand for the class of inductive sets.

Definition. The class of natnumbers is /bigcap /Ind.
Let /NN stand for the class of natnumbers.

Axiom. Let alpha be a zfset. alpha is a natural number iff alpha /in /NN.

Lemma. 0 is a natural number.
Lemma. 1 is a natural number.
Proof. 1 is a zfset.
  1 = 0 + 1.
  0 /in /NN.
  1 /in /NN.
qed.
Lemma. Let n be a natural number. Then n + 1 is a natural number.
Proof. n /in /NN. Then n + 1 /in /NN.
qed.

Lemma. Let n /in /NN. Let n /neq /emptyset. Then n /in /Succ.
Proof. Define M = {ordinal alpha | alpha /in /NN /\ (alpha = /emptyset \/ alpha /in /Succ)}.
  Then M /in /Ind.
  Proof. /emptyset /in M.
    Forall y /in M (y+1) /in M.
  end.
  Then M = /NN.
qed.

Lemma. /NN is a ZFset.

Lemma. /NN /subset /Ord.
Proof. /NN /cap /Ord /in /VV.
/NN /cap /Ord /in /Ind.
Then /NN = /NN /cap /Ord.
qed.

Lemma. /NN is transitive.
Proof. Define A = {set n | n /in /NN /\ forall x /in n (x /in /NN)}.
Then /emptyset /in A.
Forall x /in A (x + 1 /in A).
Then A = /NN.
qed.

Lemma. /NN /in /Ord.

Lemma. /NN /in /Lim.







Lemma. Contradiction.







