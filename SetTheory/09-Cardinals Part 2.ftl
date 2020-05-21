# 9-Cardinals Part 2

# This section alignes with section 4 and 6. We need some the Mostowsi Collapse, but only the results, not the construction.
# Here we start with the Goedel Ordering and show that it is a strong wellorder so we can apply TCol.

# Main results:

# - forall x,y /in /VV (x /times y /in /VV)
# - goedel is a strong wellorder
# - forall infinite x /in /VV x /tilde (x /times x)




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

Definition Universe. The universe is {ZFset x | x = x}.
Let /VV stand for the universe.

Definition Subset. A subset of A is a set B such that
forall c (c /in B => c /in A).
Let B /subset A stand for B is a subset of A.

Axiom. Let a, b be sets. Let a /subset b /\ b /subset a. Then a = b.


# Arithmetic


Definition Union. The union of A and B is 
{ZFset x | x /in A or x /in B}.
Let A /cup B stand for the union of A and B.

Definition BigUnion. The bigunion of A is
{ZFset b | exists w (w /in A /\ b /in w)}. 
Let /bigcup A denote the bigunion of A.

Definition Intersection. The intersection of A and B is 
{ZFset x | x /in A and x /in B}.
Let A /cap B stand for the intersection of A and B.

Definition BigIntersection. The bigintersection of A is
{ZFset x | forall y (y /in A => x /in y)}.
Let /bigcap A stand for the bigintersection of A.

Definition Difference. The difference of A and B is 
{ZFset x | x /in A and x /notin B}.
Let A /setminus B stand for the difference of A and B.

Definition Singleton. The singleton of X is
{ZFset x | x = X}.
Let <X> stand for the singleton of X.

Definition Pair. Let a,b be ZFsets. The pair of a and b is {ZFset c | c = a \/ c = b}.
Let <a , b> denote the pair of a and b.

Definition Power. The power set of X is
{ZFset x | x /subset X}.
Let /PP X stand for the power set of X.



[synonym class/-es]

Signature. A proper class is a notion.

Axiom. Let L be a proper class. Then L is a set.
Axiom. Let a be a set. a is a proper class iff a /notin /VV.



# Ordered pairs

Axiom OPair1. Let a,b /in /VV. Then (a,b) is a zfset.
Axiom OPair2. (x,y) = (X,Y) => x = X /\ y = Y.

Definition 105a. The cartesian product of A and B is
{set x | exists a,b (x = (a,b) /\ a /in A /\ b /in B)}.
Let A /times B stand for the cartesian product of A and B.



# Relations

[synonym relation/-s]

Definition Relation. A relation is a set R such that 
R /subset /VV /times /VV.
Let a - R - b stand for (a,b) /in R.

Axiom Relation1. Let R be a relation. x /in R => exists a,b /in /VV (x = (a,b)).

Definition Domain. Let R be a relation. The reldomain of R is
{zfset a | exists z (a - R - z)}.
Let reldomain(R) stand for the reldomain of R.

Definition Range. Let R be a relation. The relrange of R is
{zfset a | exists z (z - R - a)}.
Let relrange(R) stand for the relrange of R.

Definition Domain. Let R be a relation. The relfield of R is
relrange(R) /cup reldomain(R).
Let relfield(R) stand for the relfield of R.

Definition. Let R be a relation. Let x /in /VV. The smallerset of R rel x is
{zfset y | y - R - x}.
Let sset(R,x) stand for the smallerset of R rel x.

Definition. Let R be a relation. Let A /subset relfield(R). The relrestriction of R to A is a relation RR such that
forall x,y /in /VV (x - RR - y iff (x - R - y /\ x,y /in A)).
Let R /restrict A stand for the relrestriction of R to A.

Lemma. Let R be a relation. Let A /subset relfield(R). Then relfield(R /restrict A) /subset A.



# Attributes of relations

Definition. Let R be a relation. R is reflexive iff forall x /in relfield(R) (x - R - x).
Let ref(R) stand for R is reflexive.

Definition. Let R be a relation. R is irreflexive iff forall x /in relfield(R) (not (x - R - x)).
Let irref(R) stand for R is irreflexive.

Definition. Let R be a relation. R is symmetric iff forall x,y (x - R - y => y - R - x).
Let sym(R) stand for R is symmetric.

Definition. Let R be a relation. R is antisymmetric iff forall x,y (x - R - y /\ y - R - x => x = y).
Let antisym(R) stand for R is antisymmetric.

Definition. Let R be a relation. R is reltransitive iff forall x,y,z /in relfield(R) (x - R - y /\ y - R - z => x - R - z).
Let reltrans(R) stand for R is reltransitive.

Definition. Let R be a relation. R is connex iff forall x,y /in relfield(R) (x - R - y \/ y - R - x \/ x = y).
Let con(R) stand for R is connex.

# Kinds of relations

Signature. An equivalence relation is a notion.
Axiom. Let R be an equivalence relation. Then R is a relation.
Axiom. Let R be a relation. R is an equivalence relation iff ref(R) /\ sym(R) /\ reltrans(R).
Let eqrel(R) stand for R is an equivalence relation.

Definition. Let R be an equivalence relation. The equivalence class of x modulo R is {zfset y | y - R - x}.
Let [x]-R stand for the equivalence class of R modulo x.

Signature. A partial order is a notion.
Axiom. Let R be a partial order. Then R is a relation.
Axiom. Let R be a relation. Then R is a partial order iff ref(R) /\ reltrans(R) /\ antisym(R).

Signature. A linear order is a notion.
Axiom. Let R be a linear order. Then R is a relation.
Axiom. Let R be a relation. Then R is a linear order iff con(R) /\ (R is a partial order).

Signature. A partial order on A is a notion.
Axiom. Let A be a set. Let R be a partial order on A. Then R is a partial order.
Axiom. Let R be a relation. Let A be a set. Then R is a partial order on A iff (R is a partial order) /\ relfield(R) = A.

Signature. A strict partial order is a notion.
Axiom. Let R be a strict partial order. Then R is a relation.
Axiom. Let R be a relation. Then R is a strict partial order iff reltrans(R) /\ irref(R).

Lemma. Let R be a strict partial order. Let relfield(R) /neq /emptyset. Then R is not a partial order.

Signature. A strict linear order is a notion.
Axiom. Let R be a strict linear order. Then R is a relation.
Axiom. Let R be a relation. Then R is a strict linear order iff con(R) /\ (R is a strict partial order).



# Functions

Let M stand for a set.
Let func stand for a function.
Let the value of f at x stand for f[x].
Let the domain of f stand for Dom(f).

Axiom. Let f be a function. The domain of f is a set.

[synonym zffunction/-s]
Signature. A zffunction is a notion.
Axiom. Let f be a zffunction. Then f is a function.
Axiom. Let f be a function. f is a zffunction iff forall x /in Dom(f) f[x] /in /VV.

Let f is defined on M stand for M /subset Dom(f).

Let f,g,h,F,G,H stand for zffunction.

Definition Range. Let f be a zffunction. The range of f is
{f[x] | x /in Dom(f)}.
Let ran(f) stand for the range of f.

Definition Image. Let f be a zffunction. Let M be a set. The image of M under f is
{f[x] | x /in Dom(f) /cap M}.
Let f^[M] stand for the image of M under f.

Definition FunctionImage. Let f be a function. Let M be a set. The functionimage of M under f is
{f[x] | x /in Dom(f) /cap M /\ f[x] /in /VV}.
Let f /caret [M] stand for the functionimage of M under f.

Definition Composition. Let f and g be zffunctions. Let ran(f) /subset Dom(g). The composition of g and f is
a function h such that Dom(h) = Dom(f) and forall x /in Dom(f) h[x] = g[f[x]].
Let g /circ f stand for the composition of g and f.
Lemma. Let f and g be zffunctions. Let ran(f) /subset Dom(g). Then g /circ f is a zffunction.

Definition Map. A map from A to B is a zffunction F such that
Dom(F) = A and ran(F) /subset B.
Let F : A /rightarrow B stand for F is a map from A to B.

Definition PMap. A partial map from A to B is a zffunction F such that
Dom(F) /subset A and ran(F) /subset B.
Let F : A /harpoonright B stand for F is a partial map from A to B.

Definition Restriction. Let f be a zffunction. Let M /subset Dom(f). The restriction of f to M is a function g such that
Dom(g) = M and forall x /in M /cap Dom(f) (g[x] = f[x]).
Let f /upharpoonright M stand for the restriction of f to M.
Lemma. Let f be a zffunction. Let M /subset Dom(f). Then f /upharpoonright M is a zffunction.

Signature. Id is a function.
Axiom. Dom(Id) = /VV.
Axiom. Forall x (Id[x] = x).
Lemma. Id is a zffunction.
Axiom. Forall M Id^[M] = M.

Definition Surjective. Let F be a zffunction. Assume F : A /rightarrow B. F is surjective from A to B
iff ran(F) = B.

Definition Injective. Let f be a zffunction. f is injective iff
forall x,y /in Dom(f) (f[x] = f[y] => x = y).

Definition Bijective. Let F be a zffunction. F is bijective from A to B
iff F : A /rightarrow B and Dom(F) = A and ran(F) = B and F is injective.
Let F : A /leftrightarrow B stand for F is bijective from A to B.

Axiom. Forall M (Id /upharpoonright M : M /leftrightarrow M).

Axiom. Let f and g be functions. f = g iff Dom(f) = Dom(g) and forall x /in Dom(f) (f[x] = g[x]).
Axiom. Let f and g be zffunctions. f = g iff Dom(f) = Dom(g) and forall x /in Dom(f) (f[x] = g[x]).


Definition. Let f be an injective zffunction. The inverse of f is a function g such that
Dom(g) = ran(f) and (forall x /in ran(f) forall y /in Dom(f) (g[x] = y iff f[y] = x)).
Let f^{-1} stand for the inverse of f.
Lemma. Let f be an injective zffunction. Then f^{-1} is a zffunction.

Axiom. Let f be a zffunction. Let A,B be sets. Let f : A /leftrightarrow B.
Then f^{-1} : B /leftrightarrow A.

Definition SetofFunctions. ^{A}B = {zffunction f | f : A /rightarrow B}.






# ZF-Axioms



Axiom Empty. /emptyset is a ZFset.

Axiom Pair. Let x, y /in /VV. Then <x, y> /in /VV.

Axiom Union. Let x /in /VV. Then /bigcup x /in /VV.

Axiom Sep. Let x /in /VV. Let a /subset x. Then a /in /VV.

Axiom Power. Let x be a ZFset. Then /PP x is a ZFset.

Axiom Rep. Let f be a zffunction. Let x /in /VV. Then f^[x] /in /VV.

Axiom Found. Let A be a nonempty set. Then there is a ZFset b such that 
(b /in A /\ forall c (c /in b => c /notin A)).

Axiom. Forall x /in /VV x /notin x.
Axiom. Let x /in /VV. Then <x> /in /VV.
Axiom. Let x,y /in /VV. Then x /cup y /in /VV.



# Ordinals


Definition transitive. Let A be a set. A is transitive iff forall x,y (y /in A /\ x /in y => x /in A).
Let Trans(A) stand for A is transitive.

Lemma. Let A be a set. A is transitive iff forall x /in A (x /subset A).

Lemma. Trans(/emptyset).

[synonym ordinal/-s]

Signature. An ordinal is a notion.

Let alpha, beta, gamma, delta stand for ordinals.

Axiom. Let alpha be an ordinal. Then alpha is a ZFset.

Signature. alpha + beta is an ordinal.
Signature. x /plus 1 is a zfset.
Signature. 0 is an ordinal.
Signature. 1 is an ordinal.

Axiom. Let alpha be a ZFset. alpha is an ordinal iff ( Trans(alpha) /\ forall y (y /in alpha => Trans(y) )).

Definition Trans. The class of transitives is
{ZFset x | Trans(x)}.
Let /Trans stand for the class of transitives.

Definition Ord. The class of ordinals is
{set x | x is an ordinal}.
Let /Ord stand for the class of ordinals.

Lemma. Let alpha, beta /in /Ord. Then alpha /cup beta /in /Ord.
Proof.
Trans(alpha /cup beta).
alpha /cup beta /in /VV.
qed.

Axiom. 0 = /emptyset.

Axiom. Let alpha be an ordinal. Then alpha + 1 is {ZFset x | x /in alpha \/ x = alpha }.
Axiom. Let x be a zfset. Then x /plus 1 is {ZFset y | y /in x \/ y = x }.
Axiom. Let alpha be an ordinal. Then alpha + 1 = alpha /plus 1.


Axiom. 1 = 0 + 1.

Signature. A successor ordinal is a notion.
Signature. A limit ordinal is a notion.

Axiom successor. Let alpha be an ordinal. alpha is a successor ordinal iff exists beta (alpha = beta + 1).

Definition Succ. The class of successor ordinals is
{ordinal alpha | alpha is a successor ordinal }.
Let /Succ stand for the class of successor ordinals.

Axiom limit. Let gamma be an ordinal. gamma is a limit ordinal iff (gamma /neq /emptyset /\ gamma /notin /Succ).

Definition Lim. The class of limit ordinals is
{ordinal alpha | alpha is a limit ordinal }.
Let /Lim stand for the class of limit ordinals.

Axiom. Let x be an ordinal. Then x = /emptyset \/ x /in /Succ \/ x /in /Lim.

Axiom Infinity. Exists x (/emptyset /in x /\ forall y /in x ((y /plus 1) /in x) ).

Axiom. Let alpha be an ordinal. Then alpha + 1 is an ordinal.
Axiom. Let alpha be an ordinal. Let x be an object. Let x /in alpha. Then x is an ordinal.
Axiom. Forall alpha, beta (alpha /in beta \/ beta /in alpha \/ alpha = beta).
Axiom. Let A /subset /Ord. Let A /neq /emptyset. Then exists alpha (alpha /in A /\ forall beta /in A (alpha = beta \/ alpha /in beta)).
Axiom. Let alpha, beta be ordinals. Let alpha /in beta. Then alpha /subset beta.

Signature. Let alpha /in /Succ. alpha - 1 is an ordinal.

Axiom. Let alpha /in /Succ. Let beta be an ordinal. alpha - 1 = beta iff alpha = beta + 1.

Axiom. Let x /in /Lim. Let y /in x. Then y + 1 /in x.




# Natural Numbers


[synonym number/-s]

Signature. A natural number is a notion.

Let k,l,m,n stand for natural numbers.

Axiom. Let n be a natural number. Then n is an ordinal.
Axiom. Let n be a natural number. Then n + 1 is a natural number.

Definition. The class of inductive sets is
{ZFSet x |  (/emptyset /in x /\ forall y /in x ((y /plus 1) /in x) ) }.
Let /Ind stand for the class of inductive sets.

Definition. The class of natnumbers is /bigcap /Ind.
Let /NN stand for the class of natnumbers.

Axiom. Let alpha be an ordinal. alpha is a natural number iff alpha /in /NN.

Axiom. /NN /in /Lim.

Axiom. 0, 1 are natural numbers.

Axiom. Let n /in /NN. Let n /neq /emptyset. Then n /in /Succ.




# Ordinal Arithmetic


Signature. alpha * beta is an ordinal.
Signature. alpha ^ beta is an ordinal.


# Addition

Axiom. Let alpha be an ordinal. Then alpha + 0 = alpha.
Axiom. Let alpha, beta be ordinals. Let beta /in /Succ. Let gamma = beta - 1.
  Then alpha + beta = (alpha + gamma) + 1.
Axiom. Let alpha, beta be ordinals. Let beta /in /Lim. Then alpha + beta = {zfset x | exists gamma /in beta (x /in (alpha + gamma))}.

Axiom. Forall alpha (0 + alpha = alpha).
Axiom. Forall alpha, beta, gamma /in /Ord (beta /in gamma => alpha + beta /in alpha + gamma).
Axiom. Forall alpha, beta /in /Ord (alpha /subset alpha+beta).
Axiom. Forall alpha, beta /in /Ord (beta /subset alpha + beta).
Axiom. Forall m,n /in /NN forall x /in (m + n) (x /in m \/ exists i /in n x = m + i).


# Multiplication

Axiom. Let alpha be an ordinal. Then alpha * 0 = 0.
Axiom. Let alpha, beta be ordinals. Let beta /in /Succ. Let gamma = beta - 1.
  Then alpha * beta = (alpha * gamma) + alpha.
Axiom. Let alpha, beta be ordinals. Let beta /in /Lim. Then alpha * beta = {zfset x | exists gamma /in beta (x /in alpha * gamma)}.

Axiom. Forall alpha /in /Ord (alpha * 1 = alpha).
Axiom. Forall alpha /in /Ord (0 * alpha = 0).
Axiom. Forall alpha /in /Ord (1 * alpha = alpha).
Axiom. Forall alpha, beta /in /Ord (beta /neq /emptyset => alpha /subset alpha * beta).
Axiom. Forall alpha, beta /in /Ord (beta /neq 0 => alpha + 1 /subset alpha + beta).
Axiom. Forall alpha, beta /in /Ord (alpha /neq 0 => beta /subset alpha * beta).


# Power

Axiom. Let alpha be an ordinal. Then alpha ^ 0 = 1.
Axiom. Let alpha, beta be ordinals. Let beta /in /Succ. Let gamma = beta - 1.
  Then alpha ^ beta = (alpha ^ gamma) * alpha.
Axiom. Let alpha, beta be ordinals. Let beta /in /Lim. Then alpha + beta = {zfset x | exists gamma /in beta (x /in alpha ^ gamma)}.

Axiom. Forall alpha /in /Ord alpha ^ 1 = alpha.

Axiom. Let alpha, beta be ordinals. Let beta /in /Lim. Then alpha + beta /in /Lim.

Axiom. Forall m,n /in /NN m+n /in /NN.
Axiom. Forall m,n /in /NN m*n /in /NN.
Axiom. Forall m,n /in /NN m^n /in /NN.






# Cardinals

Axiom AC. Let x be a ZFset. Then exists alpha exists f (f : alpha /leftrightarrow x).

Definition SameCardinality. Let x, y be ZFsets. x and y are equipotent iff
exists f (f : x /leftrightarrow y).
Let x /tilde y stand for x and y are equipotent.

Definition SmallerEqualCardinality. Let x, y be ZFsets. x has cardinality at most that of y iff
exists f (f : x /rightarrow y /\ (f is injective)).
Let x <= y stand for x has cardinality at most that of y.

Definition SmallerCardinality. Let x, y be ZFsets. x has smaller cardinality than y iff
(x <= y) /\ not (x /tilde y).
Let x < y stand for x has smaller cardinality than y.

Axiom.  Let x, y be equipotent. Then y and x are equipotent.
Axiom. Let x,y be equipotent. Let y,z be equipotent. Then x,z are equipotent.
Axiom. Let x, y be zfsets. x /tilde y => (x <= y /\ y <= x).
Axiom. Let x, y, z be ZFsets. Let x <= y /\ y <= z. Then x <= z.
Axiom. Let x,y be ZFsets. Let x /subset y. Then x <= y.

Definition. Let x be a zfset. The cardset of x is 
{ordinal alpha | exists f (f : alpha /leftrightarrow x) }.
Let Cardset(x) stand for the cardset of x.

Definition. Let x be a zfset. The cardinality of x is /bigcap Cardset(x).
Let Card (x) stand for the cardinality of x.

Axiom. Let A be a set. Let A /subset /Ord. Let A /neq /emptyset.
Then /bigcap A is an ordinal.
Axiom. Let x be a zfset. The cardinality of x is an ordinal.
Axiom. Let x be a zfset. Then Card(x) /in Cardset(x).
Axiom. Let x /subset y. Then Card(x) /subset Card(y).
Axiom. Let x, y be zfsets. Let x /tilde y. Then Card(x) = Card(y).
Axiom. Let x, y be zfsets. Let Card(x) = Card(y). Then x /tilde y.

[synonym cardinal/-s]
Signature. A cardinal is a notion.

Axiom. Let kappa be a cardinal. Then kappa is an ordinal.
Axiom. Let kappa be an ordinal. kappa is a cardinal iff exists x (kappa = Card(x)).

Let kappa stand for a cardinal.

Axiom. Let alpha be an ordinal. Then Card(alpha) /subset alpha.
Axiom. Let kappa be a cardinal. Then Card(kappa) = kappa.
Axiom. Let x, y be zfset. Let x <= y. Then Card(x) /subset Card(y).
Axiom. Let x, y be zfsets. Let x <= y. Let y <= x. Then Card(x) = Card(y).
Axiom. Let x, y be zfsets. Let x <= y. Let y <= x. Then x /tilde y.

Definition. The class of cardinals is
{ordinal alpha | alpha is a cardinal}.
Let /Card stand for the class of cardinals.

Axiom. Forall n /in /NN Card(n) = n.
Axiom. Card(/NN) = /NN.

Axiom. Let x be a zfset. Then x < /PP x.
Axiom. /Ord is a proper class.
Axiom. /Card is a proper class.

Axiom. Let kappa be a cardinal. Let /NN /subset kappa. Then kappa /in /Lim.


# Finite Sets

Definition. Let x be a zfset. x is finite iff Card(x) /in /NN.

Axiom. Let x,y be zfsets. Let x be finite. Let y /subset x. Then y is finite.
Axiom. Let x,y be zfsets. Let x,y be finite. Then x /cup y is finite.
Axiom. Let a,b be zfsets. Let a,b be finite. Then (a /cap b is a zfset) and (a /cap b is finite).

Lemma. Forall x,y /in /VV (x /times y /in /VV).
Proof.
Let x,y /in /VV.
Define f[i] = {(i,j) | j /in y} for i in x.
Forall z /in x f[z] /in /VV.
Proof.
  Let z /in x.
  Define g[i] = (z,i) for i in y.
  Then g is a zffunction.
  f[z] = g^[y].
  Then f[z] /in /VV.
end.

Then x /times y /subset /bigcup f^[x].
Proof.
  Let pair /in x /times y. Take sets a,b such that a /in x /\ b /in y /\ pair = (a,b).
  Then pair /in f[a].
end.
Then f^[x] /in /VV.
qed.


Lemma. Forall a,b /in /NN ((a /times b is a zfset) and (Card(a /times b) = a * b)).
Proof.
Forall a,b /in /NN (a /times b is a zfset).
Let a /in /NN.

Define M = {ordinals b | b /in /NN /\ (Card(a /times b) = a * b)}.
Then 0 /in M.
Forall n /in M (n+1) /in M.
Proof.
  Let n /in M. Then (Card(a /times n) = a * n).
  Define A = {(i,n) | i /in a}.
  (a /times (n+1)) /subset (a /times n) /cup A.
  Proof.
    Let pair /in a /times (n+1).
    Take zfsets aa,bb such that aa /in a /\ bb /in (n+1) /\ pair = (aa,bb).
    Then bb /in n \/ bb = n.
    Case bb /in n. Then (aa,bb) /in a /times n. end.
    Case bb = n. Then (aa,bb) = (aa,n). (aa,n) /in A. end.
  end.
  (a /times n) /cup A /subset (a /times (n+1)).
  Proof.
    Let pair /in (a /times n) /cup A.
    Then pair /in (a /times n) \/ pair /in A.
    Case pair /in A.
      Take a zfset i such that i /in a \/ pair = (i,n).
      Then i /in a /\ n /in (n+1).
      Then (i,n) /in a /times (n+1).
    end.
    Case pair /in a /times n.
      Take zfsets aa,bb such that aa /in a /\ bb /in n /\ pair = (aa,bb).
      Then aa /in a /\ bb /in (n+1).
      Then (aa,bb) /in (a /times (n+1)).
    end.
    Then (a /times (n+1)) = (a /times n) /cup A.
  end.
  Forall pair /in A pair /notin (a /times n).
  Proof.
    Let pair /in A. Take zfsets x,y such that pair = (x,y).
    Take a set i such that i /in a /\ (x,y) = (i,n).
    (x,y) = (i,n).
    Then y = n.
    Then y /notin n.
    Then (x,y) /notin a /times n.
    Proof by contradiction. Assume the contrary.
      Then y /in n.
      Contradiction.      
    end.
  end.
  Take a zffunction f such that f : a /times n /leftrightarrow a * n.
  Forall x,y /in /VV ((x,y) /in A => x /in /NN).
  Define g[(x,y)] = x for (x,y) in A.
  Then ran(g) = a.
  Forall x,y /in /VV ((x,y) /in a /times (n+1) => (x,y) /in A \/ (x,y) /in a /times n).
  Forall x,y /in /VV ((x,y) /in A => (x,y) /in Dom(g) /\ g[(x,y)] /in /Ord).

  Define h[(x,y)] =
    Case (x,y) /in a /times n  -> f[(x,y)],
    Case (x,y) /in A -> (a*n) + g[(x,y)]
  for (x,y) in a /times (n+1).

  Then h is a zffunction.
  Proof.
    Let pair /in Dom(h). Take sets x,y such that pair = (x,y).
    Then (x,y) /in a /times (n+1).
    Then h[(x,y)] /in /VV.
    Proof.
      Case (x,y) /in a /times n. end.
      Case (x,y) /in A. end.
    end.
  end.
  ran(h) /subset (a*n) + a.
  Proof.
    Let pair /in a /times (n+1). Take sets x,y such that pair = (x,y).
    Then h[(x,y)] /in (a * n) + a.
    Proof.
      Case (x,y) /in a /times n. Then h[(x,y)] = f[(x,y)].
        f[(x,y)] /in a * n. 
        (a*n) /subset (a*n) + a.
        Then f[(x,y)] /in (a*n) + a.
      end.
      Case (x,y) /in A. Then h[(x,y)] = (a*n) + g[(x,y)].
        g[(x,y)] /in a. 
        Forall ord1,ord2 /in /Ord ((ord1 /in ord2) => (a*n) + ord1 /in (a*n) + ord2).
        Then (a*n) + g[(x,y)] /in (a*n) + a.
      end.
    end.
  end.
  h : a /times (n+1) /rightarrow (a * n) + a.
  
  h is injective.
  Proof.
    Let pair1, pair2 /in a /times (n+1).
    Let pair1 /neq pair2.
    Then h[pair1] /neq h[pair2].
    Proof.
      pair1, pair2 /in A \/ pair1, pair2 /in a /times n \/ (pair1 /in A /\ pair2 /in a /times n) \/ (pair2 /in A /\ pair1 /in a /times n).
      Case pair1, pair2 /in a /times n.
        Then f[pair1] /neq f[pair2].
        f[pair1] = h[pair1].
        f[pair2] = h[pair2].
      end.
      Case pair1, pair2 /in A.
        Then g[pair1] /neq g[pair2].
        Forall ord1,ord2 /in /Ord (ord1 /in ord2 \/ ord2 /in ord1 \/ ord1 = ord2).
        g[pair1],g[pair2] /in /Ord.
        Then g[pair1] /in g[pair2] \/ g[pair2] /in g[pair1].
        Then (a*n) + g[pair1] /in (a*n) + g[pair2] \/ (a*n) + g[pair2] /in (a*n) + g[pair1].
        Then (a*n) + g[pair1] /neq (a*n) + g[pair2].
        pair1 /notin a /times n.
        Take zfsets x1,y1 such that pair1 = (x1,y1).
        Then h[(x1,y1)] = (a*n) + g[(x1,y1)].
        pair2 /notin a /times n.
        Take zfsets x2,y2 such that pair2 = (x2,y2).
        Then h[(x2,y2)] = (a*n) + g[(x2,y2)].
      end.
      Case (pair1 /in A /\ pair2 /in a /times n).
        Take zfsets x2,y2 such that pair2 = (x2,y2).
        h[(x2,y2)] = f[(x2,y2)].
        Then h[pair2] /in a * n.
        pair1 /notin a /times n.
        Take zfsets x1,y1 such that pair1 = (x1,y1).
        h[(x1,y1)] = (a*n) + g[(x1,y1)].
        h[pair1] /notin a * n.
      end.
      Case (pair2 /in A /\ pair1 /in a /times n).
        Take zfsets x1,y1 such that pair1 = (x1,y1).
        h[(x1,y1)] = f[(x1,y1)].
        Then h[pair1] /in a * n.
        pair2 /notin a /times n.
        Take zfsets x2,y2 such that pair2 = (x2,y2).
        h[(x2,y2)] = (a*n) + g[(x2,y2)].
        h[pair2] /notin a * n.
      end.
    end.
  end.
  
  (a*n) + a /subset ran(h).
  Proof.
    Let x /in (a*n) + a.
    Then x /in ran(h).
    Proof.
      x /in (a*n) \/ x /notin (a*n).
      Case x /in a*n.
        Take a set pair such that pair /in a /times n /\ f[pair] = x.
        Then pair /in Dom(h).
        Take sets x1,y1 such that pair = (x1,y1).
        Then h[(x1,y1)] = x.
      end.
      Case x /notin a*n.
        Forall mm,nn /in /NN forall xx /in (mm + nn) (xx /in mm \/ exists i /in nn xx = mm + i).
        (a*n), a /in /NN.
        Then exists i /in a (x = (a*n) + i).
        Take a set i such that i /in a /\ x = (a*n) + i.
        Take a set pair such that pair /in A /\ i = g[pair].
        Take sets x1,y1 such that pair = (x1,y1).
        Then (x1,y1) /notin a /times n.
        Then h[(x1,y1)] = (a * n) + g[(x1,y1)].
        Then h[(x1,y1)] = (a * n) + i.
      end.
    end.
  end.
  Then ran(h) = (a*n) + a.

  Then h : a /times (n+1) /leftrightarrow (a * n) + a.

  Then Card(a /times (n+1)) = (a * n) + a.
  Take an ordinal n1 such that n1 /in /Succ /\ n1 = (n+1).
  a * n1 = (a * n) + a.
  Then Card(a /times (n+1)) = (a * (n+1)).
  Then n+1 /in M.
end.

Then M /in /Ind.
Proof.
  0 /in M.
  Forall n /in M (n+1) /in M.
end.
Then M = /NN.

qed.



Lemma. Let a,b be zfsets. Let a, b be finite. Then (a /times b is a zfset) and (a /times b is finite).
Proof.
Take ordinals m,n such that m = Card(a) /\ n = Card(b).
Take a zffunction f such that f : a /leftrightarrow m.
Take a zffunction g such that g : b /leftrightarrow n.
Forall c,d /in /VV ((c,d) /in a /times b => c /in a /\ d /in b).
Define h1[(c,d)] = c for (c,d) in a /times b.
Define h2[(c,d)] = d for (c,d) in a /times b.
h1 is a zffunction.
Proof.
  Let pair /in Dom(h1). Then pair /in a /times b.
  Take zfsets c,d such that pair = (c,d).
  Then h1[pair] /in /VV.
end.
ran(h1) /subset a.
Proof.
  Let pair /in Dom(h1). Then pair /in a /times b.
  Take zfsets c,d such that pair = (c,d) /\ c /in a.
  Then h1[pair] /in a.
end.
h2 is a zffunction.
Proof.
  Let pair /in Dom(h2). Then pair /in a /times b.
  Take zfsets c,d such that pair = (c,d).
  Then h2[pair] /in /VV.
end.
ran(h2) /subset b.
Proof.
  Let pair /in Dom(h2). Then pair /in a /times b.
  Take zfsets c,d such that pair = (c,d) /\ d /in b.
  Then h2[pair] /in b.
end.

Then f /circ h1 : a /times b /rightarrow m.
Then g /circ h2 : a /times b /rightarrow n.

Define h[pair] = ((f /circ h1)[pair],(g /circ h2)[pair]) for pair in a /times b.

Then h is a zffunction.
Proof.
  Let pair /in a /times b.
  Then (f /circ h1)[pair] /in m.
  Then (g /circ h2)[pair] /in n.
  Then h[pair] /in /VV.
end.
Then h : a /times b /rightarrow m /times n.
Proof.
  Let pair /in a /times b.
  Then (f /circ h1)[pair] /in m.
  Then (g /circ h2)[pair] /in n.
  Then h[pair] /in m /times n.
end.
h is injective.
Proof.
  Let pair1, pair2 /in a /times b. Let pair1 /neq pair2.
  Then h[pair1] /neq h[pair2].
  Proof.
    Take zfsets x1,y1 such that x1 /in a /\ y1 /in b /\ pair1 = (x1,y1).
    Take zfsets x2,y2 such that x2 /in a /\ y2 /in b /\ pair2 = (x2,y2).
    Then x1 /neq x2 \/ y1 /neq y2.
    Case x1 /neq x2.
      h1[(x1,y1)] = x1.
      h1[(x2,y2)] = x2.
      Then f[x1] /neq f[x2].
      Then (f /circ h1)[(x1,y1)] /neq (f /circ h1)[(x2,y2)].
      Then forall aa1,aa2 /in /VV ((f /circ h1)[(x1,y1)],aa1) /neq ((f /circ h1)[(x2,y2)],aa2).
      ((f /circ h1)[(x1,y1)],(g /circ h2)[(x1,y1)]) /neq ((f /circ h1)[(x2,y2)],(g /circ h2)[(x2,y2)]).
    end.
    Case y1 /neq y2.
      h2[(x1,y1)] = y1.
      h2[(x2,y2)] = y2.
      Then g[y1] /neq g[y2].
      Then (g /circ h2)[(x1,y1)] /neq (g /circ h2)[(x2,y2)].
      Then forall aa1,aa2 /in /VV (aa1,(g /circ h2)[(x1,y1)]) /neq (aa2,(g /circ h2)[(x2,y2)]).
      ((f /circ h1)[(x1,y1)],(g /circ h2)[(x1,y1)]) /neq ((f /circ h1)[(x2,y2)],(g /circ h2)[(x2,y2)]).
    end.
  end.
end.

Then h : a /times b /leftrightarrow ran(h).
Then Card(a /times b) = Card(ran(h)).
ran(h) /subset m /times n.
m /times n is finite.
Then ran(h) is finite.
Then a /times b is finite.

qed.



Lemma. Let a1,a2,b1,b2 be zfsets. Let Card(a1) = Card(a2) /\ Card(b1) = Card(b2).
Then (a1 /times b1) /tilde (a2 /times b2).
Proof.
a1 /tilde a2.
b1 /tilde b2.
Take a zffunction f such that f : a1 /leftrightarrow a2.
Take a zffunction g such that g : b1 /leftrightarrow b2.

Define h1[(c,d)] = c for (c,d) in a1 /times b1.
Define h2[(c,d)] = d for (c,d) in a1 /times b1.
h1 is a zffunction.
Proof.
  Let pair /in Dom(h1). Then pair /in a1 /times b1.
  Take zfsets c,d such that pair = (c,d).
  Then h1[pair] /in /VV.
end.
ran(h1) /subset a1.
Proof.
  Let pair /in Dom(h1). Then pair /in a1 /times b1.
  Take zfsets c,d such that pair = (c,d) /\ c /in a1.
  Then h1[pair] /in a1.
end.
h2 is a zffunction.
Proof.
  Let pair /in Dom(h2). Then pair /in a1 /times b1.
  Take zfsets c,d such that pair = (c,d).
  Then h2[pair] /in /VV.
end.
ran(h2) /subset b1.
Proof.
  Let pair /in Dom(h2). Then pair /in a1 /times b1.
  Take zfsets c,d such that pair = (c,d) /\ d /in b1.
  Then h2[pair] /in b1.
end.

Then f /circ h1 : a1 /times b1 /rightarrow a2.
Then g /circ h2 : a1 /times b1 /rightarrow b2.

Define h[pair] = ((f /circ h1)[pair],(g /circ h2)[pair]) for pair in a1 /times b1.

Then h is a zffunction.
Proof.
  Let pair /in a1 /times b1.
  Then (f /circ h1)[pair] /in a2.
  Then (g /circ h2)[pair] /in b2.
  Then h[pair] /in /VV.
end.
Then h : a1 /times b1 /rightarrow a2 /times b2.
Proof.
  Dom(h) = a1 /times b1.
  Let pair /in a1 /times b1.
  Then (f /circ h1)[pair] /in a2.
  Then (g /circ h2)[pair] /in b2.
  Then h[pair] /in a2 /times b2.
end.
h is injective.
Proof.
  Let pair1, pair2 /in a1 /times b1. Let pair1 /neq pair2.
  Then h[pair1] /neq h[pair2].
  Proof.
    Take zfsets x1,y1 such that x1 /in a1 /\ y1 /in b1 /\ pair1 = (x1,y1).
    Take zfsets x2,y2 such that x2 /in a1 /\ y2 /in b1 /\ pair2 = (x2,y2).
    Then x1 /neq x2 \/ y1 /neq y2.
    Case x1 /neq x2.
      h1[(x1,y1)] = x1.
      h1[(x2,y2)] = x2.
      Then f[x1] /neq f[x2].
      Then (f /circ h1)[(x1,y1)] /neq (f /circ h1)[(x2,y2)].
      Then forall aa1,aa2 /in /VV ((f /circ h1)[(x1,y1)],aa1) /neq ((f /circ h1)[(x2,y2)],aa2).
      ((f /circ h1)[(x1,y1)],(g /circ h2)[(x1,y1)]) /neq ((f /circ h1)[(x2,y2)],(g /circ h2)[(x2,y2)]).
    end.
    Case y1 /neq y2.
      h2[(x1,y1)] = y1.
      h2[(x2,y2)] = y2.
      Then g[y1] /neq g[y2].
      Then (g /circ h2)[(x1,y1)] /neq (g /circ h2)[(x2,y2)].
      Then forall aa1,aa2 /in /VV (aa1,(g /circ h2)[(x1,y1)]) /neq (aa2,(g /circ h2)[(x2,y2)]).
      Proof by contradiction. Assume the contrary.
        Take aa1,aa2 /in /VV such that (aa1,(g /circ h2)[(x1,y1)]) = (aa2,(g /circ h2)[(x2,y2)]).
        Take zfsets bb1,bb2 such that bb1 = (g /circ h2)[(x1,y1)] /\ bb2 = (g /circ h2)[(x2,y2)].
        Then (aa1,bb1) = (aa2,bb2).
        Then aa1=aa2 /\ bb1 = bb2.
        Then (g /circ h2)[(x1,y1)] = (g /circ h2)[(x2,y2)].
        Contradiction.
      end.
      ((f /circ h1)[(x1,y1)],(g /circ h2)[(x1,y1)]) /neq ((f /circ h1)[(x2,y2)],(g /circ h2)[(x2,y2)]).
    end.
  end.
end.

Then h : a1 /times b1 /leftrightarrow ran(h).

a2 /times b2 /subset ran(h).
Proof.
  Let pair /in a2 /times b2. Take zfsets x2,y2 such that x2 /in a2 /\ y2 /in b2 /\ pair = (x2,y2).
  Take a zfset x1 such that x1 /in a1 /\ f[x1] = x2.
  Take a zfset y1 such that y1 /in b1 /\ g[y1] = y2.
  Then (x1,y1) /in a1 /times b1.
  h1[(x1,y1)] = x1.
  h2[(x1,y1)] = y1.
  Then (f /circ h1)[(x1,y1)] = x2.
  Then (g /circ h2)[(x1,y1)] = y2.
  Then h[(x1,y1)] = (x2,y2).
  Then pair /in ran(h).
end.


qed.






# Alefs

Signature. Plus is a zffunction.
Axiom. Plus : /Ord /rightarrow /Card.
Axiom. Let alpha /in /Ord. Then Plus[alpha] = {ordinal beta | forall kappa /in /Card (alpha /in kappa => beta /in kappa)}.

Axiom. Let n /in /NN. Then Plus[n] = n+1.

Signature. Alef is a zffunction.
Axiom. Alef : /Ord /rightarrow /Ord.
Axiom. Alef[/emptyset] = /NN.
Axiom. Let alpha /in /Succ. Let beta /in /Ord. Let alpha = beta + 1. Then Alef[beta] /in /Ord /\ Alef[alpha] = Plus[Alef[beta]].
Axiom. Let alpha /in /Lim. Then Alef[alpha] = {zfset x | exists beta /in alpha x /in Alef[beta]}.

Axiom. Let x /in /VV. Let x /subset /Card. Then Card(/bigcup x) = /bigcup x.
Axiom. Let x /in /VV. Let x /subset /Card. Then (/bigcup x) /in /Card.
Axiom. Let alpha /in /Ord. Then Alef[alpha] /in /Card.
Axiom. Forall alpha, beta (alpha /in beta => Alef[alpha] /in Alef[beta]).
Axiom. Forall alpha /in /Ord (alpha /subset Alef[alpha]).
Axiom. Let kappa be a cardinal. Let /NN /subset kappa. Then exists alpha (alpha /in /Ord /\ kappa = Alef[alpha]).










# Wellfounded Relations


Definition. Let R be a relation.  R is wellfounded iff
(forall A ((A /neq /emptyset /\ A /subset reldomain(R)) => (exists x /in A (forall y /in A (not (y - R - x)))))).

Definition. Let R be a relation. R is strongly wellfounded iff
(R is wellfounded) /\ (forall x /in relfield(R) sset(R,x) /in /VV).

Signature. A wellorder is a notion.
Axiom. Let R be a wellorder. Then R is a relation.
Axiom. Let R be a relation. Then R is a wellorder iff (R is wellfounded) and (R is a strict linear order).

Signature. A strong wellorder is a notion.
Axiom. Let R be a strong wellorder. Then R is a relation.
Axiom. Let R be a relation. Then R is a strong wellorder iff (R is strongly wellfounded) and (R is a wellorder).

Definition. Let R be a strongly wellfounded relation. R is extensional iff forall x,y /in reldomain(R) (sset(R,x) = sset(R,y) => x = y).
Let ext(R) stand for R is extensional.

Axiom. Let R be a strong wellorder. Then R is extensional.




# Mostowski Collapse


Let SWR stand for a strongly wellfounded relation.
Signature. TCol /res SWR is a function.

Axiom. Let R be a strongly wellfounded relation. Dom(TCol /res R) = reldomain(R).
Axiom. Let R be a strongly wellfounded relation. Then (TCol /res R) is a zffunction.
Axiom. Let R be a strongly wellfounded relation. Then forall x /in (reldomain(R))  (((TCol /res R) [x]) = ((TCol /res R)^[sset(R,x)])).

Signature. eps is an object.
Axiom. eps is a relation.
Axiom. Forall x,y /in /VV (x - eps - y iff x /in y).
Axiom. reldomain(eps) = /VV.
Axiom. eps is strongly wellfounded.
Axiom. Let A /subset /Ord. (eps /restrict A) is a strong wellorder.

Axiom. Let x be a zfset. Let x /subset /Ord. Then /bigcup x /in /Ord.

Definition. Let x be a zfset. Let x /subset /Ord. The epsrestriction of x is
eps /restrict (x /cup (<(/bigcup x) + 1>)).
Let epsrest(x) stand for the epsrestriction of x.

Axiom. Let x be a zfset. Let x /subset /Ord. Then reldomain(epsrest(x)) = x.
Axiom. Let x be a zfset. Let x /subset /Ord. Then epsrest(x) is a strong wellorder.

Axiom. Let R be a strongly wellfounded relation. Let R be extensional. Then (TCol /res R) is injective.

Axiom. Let R be a strongly wellfounded relation. Let R be extensional. Then forall x,y /in reldomain(R) ( x - R - y iff (TCol /res R)[x] /in (TCol /res R)[y]).

Axiom. Let R be a strong wellorder. Let reldomain(R) /in /VV. Then ran(TCol /res R) /in /Ord.

Axiom. Let R be a strong wellorder. Let reldomain(R) be a proper class. Then ran(TCol /res R) = /Ord.



# Order-type


Definition. Let R be a strong wellorder. The relordertype of R is ran(TCol /res R).
Let relotp(R) stand for the relordertype of R.

Axiom. Let R be a strong wellorder. Then relotp(R) /in /Ord \/ relotp(R) = /Ord.

Definition. Let x be a zfset. Let x /subset /Ord. The ordertype of x is ran(TCol /res epsrest(x)).
Let otp(x) stand for the ordertype of x.

Axiom. Let x be a zfset. Let x /subset /Ord. Then otp(x) /in /Ord.

Axiom. Let alpha be an ordinal. Let x /subset alpha. Then otp(x) /subset alpha.





# Transitive Closure


Definition. Let R be a strongly wellfounded relation. Let x /subset reldomain(R). The class of transclosed sets of x resp R is
{zfset z | z /subset reldomain(R) /\ x /subset z /\ forall u /in z forall v /in sset(R,u) v /in z}.
Let TCsets(R,x) stand for the class of transclosed sets of x resp R.

Definition. Let R be a strongly wellfounded relation. Let x /subset reldomain(R). The transitive closure of x resp R is
/bigcap TCsets(R,x).
Let TC(R,x) stand for the transitive closure of x resp R.

Axiom. Let R be a strongly wellfounded relation. Let x /subset reldomain(R). Let TC(R,x) /in /VV. Then TC(R,x) /subset reldomain(R).

Axiom. Let R be a strongly wellfounded relation. Let x /subset reldomain(R). Let TC(R,x) /in /VV. Then TC(R,x) /in TCsets(R,x).

Axiom. Let R be a strongly wellfounded relation.
Then forall x /in /VV (x /subset reldomain(R) => TC(R,x) /in /VV).

Definition. Let x /in /VV. The transitive closure of x is
TC(eps,x).
Let TC(x) stand for the transitive closure of x.














# Goedel Ordering

Definition. Let a1,a2,b1,b2 /in /Ord. (a1,b1) isgoedelsmallerthan (a2,b2) iff
(a1 /cup b1 /in a2 /cup b2) \/ (a1 /cup b1 = a2 /cup b2 /\ a1 /in a2)
\/ (a1 /cup b1 = a2 /cup b2 /\ a1 = a2 /\ b1 /in b2).
Let (a, b) <2 (c,d) stand for (a,b) isgoedelsmallerthan (c,d).



Signature. goedel is an object.
Axiom. goedel is a relation.
Axiom. relfield(goedel) = /Ord /times /Ord.
Axiom. Forall a,b,c,d /in /Ord ( (a, b) - goedel - (c,d) iff (a, b) <2 (c,d)).

Lemma. goedel is a strict linear order.
Proof.
goedel is connex.
Proof.
  Forall pair1, pair2 /in /Ord /times /Ord (pair1 - goedel - pair2 \/ pair2 - goedel - pair1 \/ pair1 = pair2).
  Proof.
    Let pair1, pair2 /in /Ord /times /Ord.
    Take ordinals a,b,c,d such that pair1 = (a,b) /\ pair2 = (c,d).
    Then (pair1 - goedel - pair2 \/ pair2 - goedel - pair1 \/ pair1 = pair2).
    Proof.
      Forall alpha, beta /in /Ord alpha /cup beta /in /Ord.
      Proof.
        Let alpha, beta /in /Ord.
        Trans(alpha /cup beta).
        alpha /cup beta = /bigcup <alpha, beta>.
        alpha /cup beta /in /VV.
      end.
      Then a /cup b, c /cup d /in /Ord.
      Forall alpha, beta /in /Ord (alpha /in beta \/ beta /in alpha \/ alpha = beta).
      Take ordinals alpha, beta such that a /cup b = alpha /\ c /cup d = beta.
      Then (alpha /in beta \/ beta /in alpha \/ alpha = beta).
      Case alpha /in beta. Then (a,b) <2 (c,d). end.
      Case beta /in alpha. Then (c,d) <2 (a,b). end.
      Case alpha = beta. Then a /in c \/ c /in a \/ a = c.
        Case a /in c. Then (a,b) <2 (c,d). end.
        Case c /in a. Then (c,d) <2 (a,b). end.
        Case a = c. Then b /in d \/ d /in b \/ b = d.
          Case b /in d. Then (a,b) <2 (c,d). end.
          Case d /in b. Then (c,d) <2 (a,b). end.
          Case b = d. Then (a,b) = (c,d). end.
        end.        
      end.
    end.
  end.
end.

goedel is irreflexive.
Proof.
  Forall pair /in /Ord /times /Ord (not (pair - goedel - pair)).
  Proof.
    Let pair /in /Ord /times /Ord.
    Take ordinals a,b such that pair = (a,b).
    Then not ((a,b) <2 (a,b)).
  end.
end.

goedel is reltransitive.
Proof.
  Forall pair1, pair2, pair3 /in /Ord /times /Ord (pair1 - goedel - pair2 /\ pair2 - goedel - pair3 => pair1 - goedel - pair3).
  Proof.
    Let pair1, pair2, pair3 /in /Ord /times /Ord.
    Let (pair1 - goedel - pair2 /\ pair2 - goedel - pair3).
    Take ordinals a1,b1 such that pair1 = (a1,b1).
    Take ordinals a2,b2 such that pair2 = (a2,b2).
    Take ordinals a3,b3 such that pair3 = (a3,b3).
    Then (a1,b1) <2 (a2,b2).
    Then (a1 /cup b1 /in a2 /cup b2) \/ (a1 /cup b1 = a2 /cup b2 /\ a1 /in a2)
    \/ (a1 /cup b1 = a2 /cup b2 /\ a1 = a2 /\ b1 /in b2).
    Then (pair1 - goedel - pair3).
    Proof.
      Case (a1 /cup b1 /in a2 /cup b2).
        (a2,b2) <2 (a3,b3).
        Then (a2 /cup b2 /in a3 /cup b3) \/ (a2 /cup b2 = a3 /cup b3 /\ a2 /in a3)
        \/ (a2 /cup b2 = a3 /cup b3 /\ a2 = a3 /\ b2 /in b3).
        Then (a2 /cup b2 /in a3 /cup b3) \/ (a2 /cup b2 = a3 /cup b3).
        Then a1 /cup b1 /in a3 /cup b3.
        Proof.
          Case a2 /cup b2 = a3 /cup b3. end.
          Case a2 /cup b2 /in a3 /cup b3.
            Then (a1 /cup b1 /in a2 /cup b2) /\ (a2 /cup b2 /in a3 /cup b3).
            Trans(a3 /cup b3). 
            Then (a2 /cup b2 /subset a3 /cup b3).
            Then (a1 /cup b1 /in a3 /cup b3).
          end.
        end.
        Then (a1,b1) <2 (a3,b3).
        (a1,b1), (a3,b3) /in /Ord /times /Ord.
        Then (a1,b1) - goedel - (a3,b3).
      end.
    
      Case (a1 /cup b1 = a2 /cup b2 /\ a1 /in a2).
        (a2,b2) <2 (a3,b3).
        Then (a2 /cup b2 /in a3 /cup b3) \/ (a2 /cup b2 = a3 /cup b3 /\ a2 /in a3)
        \/ (a2 /cup b2 = a3 /cup b3 /\ a2 = a3 /\ b2 /in b3).
        Case (a2 /cup b2 /in a3 /cup b3). Then a1 /cup b1 /in a3 /cup b3.
          Then (a1,b1) <2 (a3,b3). (a1,b1) = pair1 /\ (a3,b3) = pair3.
        end.
        Case (a2 /cup b2 = a3 /cup b3 /\ a2 /in a3). Then a1 /cup b1 = a3 /cup b3.
          a1 /in a3.
          Then (a1,b1) <2 (a3,b3). (a1,b1) = pair1 /\ (a3,b3) = pair3.
          Then (a1,b1) - goedel - (a3,b3).
        end.
        Case (a2 /cup b2 = a3 /cup b3 /\ a2 = a3 /\ b2 /in b3). Then a1 /cup b1 = a3 /cup b3.
          a1 /in a3.
          Then (a1,b1) <2 (a3,b3). (a1,b1) = pair1 /\ (a3,b3) = pair3.
        end.
      end.

      Case (a1 /cup b1 = a2 /cup b2 /\ a1 = a2 /\ b1 /in b2).
        (a2,b2) <2 (a3,b3).
        Then (a2 /cup b2 /in a3 /cup b3) \/ (a2 /cup b2 = a3 /cup b3 /\ a2 /in a3)
        \/ (a2 /cup b2 = a3 /cup b3 /\ a2 = a3 /\ b2 /in b3).
        Case (a2 /cup b2 /in a3 /cup b3). Then a1 /cup b1 /in a3 /cup b3.
          Then (a1,b1) <2 (a3,b3). (a1,b1) = pair1 /\ (a3,b3) = pair3.
        end.
        Case (a2 /cup b2 = a3 /cup b3 /\ a2 /in a3). Then a1 /cup b1 = a3 /cup b3.
          a1 /in a3.
          Then (a1,b1) <2 (a3,b3). (a1,b1) = pair1 /\ (a3,b3) = pair3.
        end.
        Case (a2 /cup b2 = a3 /cup b3 /\ a2 = a3 /\ b2 /in b3). Then a1 /cup b1 = a3 /cup b3.
          a1 = a3.
          b1 /in b3.
          Then (a1,b1) <2 (a3,b3). (a1,b1) = pair1 /\ (a3,b3) = pair3.
        end.
      end.


    end.
  end.
end.

end.


Lemma. reldomain(goedel) = /Ord /times /Ord.
Proof.
reldomain(goedel) /subset /Ord /times /Ord.
Proof.
  relfield(goedel) = /Ord /times /Ord.
end.
/Ord /times /Ord /subset reldomain(goedel).
Proof.
  Let pair /in /Ord /times /Ord. Take ordinals a,b such that pair = (a,b).
  Then (a,b) <2 (a+1,b).
  Proof.
    a /cup b /subset (a+1) /cup b.
    a /cup b, (a+1) /cup b /in /Ord.
    Take ordinals alpha, beta such that alpha = a /cup b /\ beta = (a+1) /cup b.
    Then alpha /subset beta. Then alpha /in beta \/ alpha = beta.
    Then a /cup b /in (a+1) /cup b \/ a /cup b = (a+1) /cup b.
  end.
  Then (a,b) - goedel - (a+1,b).
  (a+1,b) /in /VV.
  Proof.
    a+1,b /in /VV.
    Forall x,y /in /VV (x,y) /in /VV.
  end.
  Then exists z ((a,b) - goedel - z).
  Then (a,b) /in reldomain(goedel).
end.
qed.



Lemma. goedel is wellfounded.
Proof.
reldomain(goedel) /subset /Ord /times /Ord.
Let A be a set. Let A /subset /Ord /times /Ord. Let A /neq /emptyset.
Define B = {ordinals alpha | exists beta /in /Ord (beta /subset alpha /\ ((alpha,beta) /in A \/ (beta,alpha) /in A))}.
Then B /neq /emptyset.
Proof.
  Take an object pair such that pair /in A. Take ordinals a,b such that pair = (a,b).
  Then a /subset b \/ b /subset a. Then a /in B \/ b /in B.
end.
Take a set min such that min /in B /\ forall h /in min h /notin B.
Define C = {ordinals beta | beta = min \/ (beta /in min /\ (beta,min) /in A)}.
Then C /neq /emptyset.
Proof.
  min /in B. Take an ordinal beta such that beta /subset min /\ ((beta,min) /in A \/ (min,beta) /in A).
  Then beta /in C \/ min /in C.
end.
Take a set min2 such that min2 /in C /\ forall h /in min2 h /notin C.
Then min2 /in min \/ min2 = min.

Case min2 /in min. Then (min2, min) /in A. min2 /cup min = min.
  Let pair = (min2,min). Then forall pair2 /in sset(goedel,pair) pair2 /notin A.
  Proof.
    Let pair2 /in sset(goedel,pair). Then pair2 /in /Ord /times /Ord.
    Take ordinals a,b such that pair2 = (a,b).
    Then pair2 /notin A.
    Proof by contradiction. Assume the contrary. Then pair2 /in A.
      Then a /in b \/ b /in a \/ a = b.
      Case a = b. Then a /in B. Then min /in b \/ min = b.
        Case min /in b.
          Then (min2,min) <2 (a,b). Then not ((a,b) <2 (min2,min)). Contradiction.
        end.
        Case min = b.
          Then min2 /in a \/ min2 = a.
          Case min2 = a. Then (a,b) = (min2, min). Contradiction. end.
          Case min2 /in a. Then (min2,min) <2 (a,b). 
            Then not ((a,b) <2 (min2,min)).
            Contradiction. 
          end.
        end.
      end.
      Case a /in b. Then b /in B. Then min /in b \/ min = b.
        Case min = b.
          Then min2 /in a \/ a = min2.
          Case min2 = a. Then (a,b) = (min2, min). Contradiction. end.
          Case min2 /in a. Then (min2,min) <2 (a,b). 
            Then not ((a,b) <2 (min2,min)).
            Contradiction. 
          end.
        end.
        Case min /in b. Then (min2,min) <2 (a,b). 
          Then not ((a,b) <2 (min2,min)).
          Contradiction. 
        end.
      end.
      Case b /in a. Then a /in B. Then min /in a \/ min = a.
        Case min = a. Then min2 /in a. Then (min2,min) <2 (a,b). 
          Then not ((a,b) <2 (min2,min)).
          Contradiction.
        end.
        Case min /in a. Then (min2,min) <2 (a,b). 
          Then not ((a,b) <2 (min2,min)).
          Contradiction.
        end.
      end.
    end.
  end.
end.

Case min2 = min.
  Define D = {ordinals alpha | (min, alpha) /in A}.
  Then D /neq /emptyset.
  Proof.
    Take an ordinal beta such that beta /subset min /\ ((min,beta) /in A \/ (beta,min) /in A).
    Then beta /in min \/ beta = min.
    Case beta /in min. Then (min,beta) /in A. Then beta /in D. end.
    Case beta = min. Then (min,min) /in A. Then min /in D. end.
  end.
  Take an ordinal min3 such that min3 /in D /\ forall a /in min3 a /notin D.
  Let pair = (min,min3). 
  Then min /cup min3 = min.
  Proof.
    min /in B. Take an ordinal alpha such that alpha /subset min /\ ((min,alpha) /in A \/ (alpha,min) /in A).
    Case (min, alpha) /in A. Then min3 /subset alpha. end.
    Case (alpha, min) /in A. Then alpha = min \/ alpha /in min.
    end.
  end.
  Then forall pair2 /in sset(goedel,pair) pair2 /notin A.
  Proof.
    Let pair2 /in sset(goedel,pair). Then pair2 /in /Ord /times /Ord.
    Take ordinals a,b such that pair2 = (a,b).
    Then pair2 /notin A.
    Proof by contradiction. Assume the contrary. Then pair2 /in A.
      a /in b \/ b /in a \/ a = b.
      Case a = b. Then a /cup b = a. Then min /in a \/ a = min.
        Case min /in a. Then (min,min3) <2 (a,b). Then not ((a,b) <2 (min,min3)). Contradiction.
        end.
        Case a = min. Then min3 /in b \/ min3 = b.
          Then (min,min3) <2 (a,b). Then not ((a,b) <2 (min,min3)). Contradiction.
        end.
      end.
      Case a /in b. Then a /cup b = b. Then min /in b \/ min = b.
        Case min /in b.
          Then (min,min3) <2 (a,b). Then not ((a,b) <2 (min,min3)). Contradiction.
        end.
        Case min = b. Then a /in min. Contradiction. end.
      end.
      Case b /in a. Then a /cup b = a. Then min /in a \/ min = a.
        Then (min,min3) <2 (a,b). Then not ((a,b) <2 (min,min3)). Contradiction.
      end.      
    end.
  end.
end.

qed.







Lemma. goedel is a strong wellorder.
Proof.
goedel is a wellorder.
Forall x /in relfield(goedel) sset(goedel,x) /in /VV.
Proof.
  relfield(goedel) /subset /Ord /times /Ord.
  Let pair /in /Ord /times /Ord.
  Take ordinals a,b such that pair = (a,b).
  Then sset(goedel,pair) /in /VV.
  Proof.
    Trans(a /cup b).
    a /cup b /in /Ord.
    Let c = (a /cup b)+1.
    Then sset(goedel, pair) /subset c /times c.
    Proof.
      Let pair2 /in sset(goedel,pair).
      Take ordinals a2,b2 such that pair2 = (a2,b2).
      Then (a2,b2) <2 (a,b).
      Then (a2 /cup b2 /in a /cup b) \/ (a2 /cup b2 = a /cup b /\ a2 /in a)
      \/ (a2 /cup b2 = a /cup b /\ a2 = a /\ b2 /in b).
      Then a2 /cup b2 /subset a /cup b.
      a2 /cup b2 /in /Ord.
      Then a2 /cup b2 = a /cup b \/ a2 /cup b2 /in a /cup b.
      Then a2 /cup b2 /in c.
      Then a2 /in c /\ b2 /in c.
      Then pair2 /in c /times c.
    end.
  end.
end.
qed.


Lemma. reldomain(goedel) is a proper class.
Proof by contradiction. Assume the contrary.
Then reldomain(goedel) /in /VV.
reldomain(goedel) = /Ord /times /Ord.
Define f[(a,b)] = a for (a,b) in /Ord /times /Ord.
Then f is a zffunction.
Proof.
  Let x /in Dom(f). Take ordinals a,b such that x = (a,b).
  Then f[x] = a.
end.
Then /Ord /subset f^[/Ord /times /Ord].
Proof.
  Let a /in /Ord.
  Then f[(a,0)] = a.
  Then a /in f^[/Ord /times /Ord].
end.
Then /Ord /in /VV.
Contradiction.
qed.


Lemma. TCol /res goedel : /Ord /times /Ord /leftrightarrow /Ord.

Signature. Goed is a notion.
Axiom. Goed is a function.
Axiom. Goed = TCol /res goedel.
Lemma. Goed is a zffunction.
Lemma. Goed : /Ord /times /Ord /leftrightarrow /Ord.
Lemma. Let a1,a2,b1,b2 /in /Ord.
Then (a1,b1),(a2,b2) /in /Ord /times /Ord /\ Goed[(a1,b1)], Goed[(a2,b2)] /in /Ord.
Proof.
(a1,b1),(a2,b2) /in /Ord /times /Ord.
qed.

Lemma. Let a1,a2,b1,b2 /in /Ord. Let (a1,b1) <2 (a2,b2).
Then Goed[(a1,b1)], Goed[(a2,b2)] /in /Ord /\ Goed[(a1,b1)] /in Goed[(a2,b2)].
Proof.
Take sets x,y such that x,y /in reldomain(goedel) /\ x = (a1,b1) /\ y = (a2,b2).
Then x - goedel - y.
Then x /in sset(goedel,y).
(TCol /res goedel)[y] = (TCol /res goedel)^[sset(goedel,y)].
(TCol /res goedel)[x] /in (TCol /res goedel)^[sset(goedel,y)].
Then (TCol /res goedel)[x] /in (TCol /res goedel)[y].
qed.

# This lemma was already proven for general strong wellorders R, but it seems that Naproche attaches too many attributes to goedel.
# Even restating the lemma and stating that goedel fullfills all assumptions Naproche cannot proof this, so we just reproof the lemma.



# The Inverse of the Goedel Pairing

Lemma. Goed^{-1} : /Ord /leftrightarrow /Ord /times /Ord.

Signature. pr1 is a notion.
Axiom. pr1 is a function.
Axiom. pr1 : /VV /times /VV /rightarrow /VV.
Lemma. Dom(pr1) = /VV /times /VV.
Lemma. Forall x,y /in /VV (x,y) /in Dom(pr1).
Proof.
Let x,y /in /VV. Then (x,y) /in /VV /times /VV.
qed.
Axiom. Forall x,y /in /VV pr1[(x,y)] = x.

Signature. pr2 is a notion.
Axiom. pr2 is a function.
Axiom. pr2 : /VV /times /VV /rightarrow /VV.
Lemma. Dom(pr2) = /VV /times /VV.
Lemma. Forall x,y /in /VV (x,y) /in Dom(pr2).
Proof.
Let x,y /in /VV. Then (x,y) /in /VV /times /VV.
qed.
Axiom. Forall x,y /in /VV pr2[(x,y)] = y.

Signature. Goed1 is a notion.
Axiom. Goed1 is a function.
Lemma. /Ord /times /Ord /subset /VV /times /VV.
Proof.
Let pair /in /Ord /times /Ord.
Take ordinals a,b such that pair = (a,b).
Then pair /in /VV /times /VV.
qed.
Axiom. Goed1 = pr1 /circ Goed^{-1}.

Signature. Goed2 is a notion.
Axiom. Goed2 is a function.
Axiom. Goed2 = pr2 /circ Goed^{-1}.

Lemma. Goed1 : /Ord /rightarrow /Ord.
Proof.
Dom(Goed1) = /Ord.
Let a /in /Ord.
Then Goed^{-1}[a] /in /Ord /times /Ord.
Take ordinals b,c such that Goed^{-1}[a] = (b,c).
Goed1[a] = (pr1 /circ Goed^{-1})[a].
(pr1 /circ Goed^{-1})[a] = pr1[(b,c)].
pr1[(b,c)] = b.
qed.

Lemma. Goed2 : /Ord /rightarrow /Ord.
Proof.
Dom(Goed2) = /Ord.
Let a /in /Ord.
Then Goed^{-1}[a] /in /Ord /times /Ord.
Take ordinals b,c such that Goed^{-1}[a] = (b,c).
Goed2[a] = (pr2 /circ Goed^{-1})[a].
(pr2 /circ Goed^{-1})[a] = pr2[(b,c)].
pr2[(b,c)] = c.
qed.

Lemma. Forall alpha /in /Ord (Goed1[alpha],Goed2[alpha]) /in /Ord /times /Ord.

Lemma. Forall alpha /in /Ord  Goed[(Goed1[alpha],Goed2[alpha])] = alpha.
Proof.
Let alpha /in /Ord.
Then Goed[Goed^{-1}[alpha]] = alpha.

(Goed1[alpha],Goed2[alpha]) = Goed^{-1}[alpha].
Proof.
  Goed^{-1}[alpha] /in /Ord /times /Ord.
  Take ordinals a,b such that Goed^{-1}[alpha] = (a,b).
  Goed1[alpha] = (pr1 /circ Goed^{-1})[alpha].
  (pr1 /circ Goed^{-1})[alpha] = pr1[(a,b)].
  Then Goed1[alpha] = a.
  Goed2[alpha] = (pr2 /circ Goed^{-1})[alpha].
  (pr2 /circ Goed^{-1})[alpha] = pr2[(a,b)].
  Then Goed2[alpha] = b.
  Then (Goed1[alpha],Goed2[alpha]) = (a,b).
end.

qed.




Lemma. Forall alpha /in /Ord (sset(goedel,(0,alpha)) = alpha /times alpha).
Proof.
Let alpha /in /Ord.
sset(goedel,(0,alpha)) /subset alpha /times alpha.
Proof.
  Let pair /in sset(goedel,(0,alpha)).
  Then pair /in /Ord /times /Ord.
  Take ordinals a,b such that pair = (a,b).
  (a,b) <2 (0,alpha).
  Then a /cup b /in alpha \/ a /cup b = alpha.
  Case a /cup b /in alpha.
    Then a /in alpha /\ b /in alpha.
    Then (a,b) /in alpha /times alpha.
  end.
  Case a /cup b = alpha.
    Then a = alpha \/ b = alpha.
    Case a = alpha. Then (0,alpha) <2 (a,b). Contradiction. end.
    Case b = alpha.
      Then a /in 0 \/ a = 0.
      Contradiction.
    end.
  end.
end.
alpha /times alpha /subset sset(goedel,(0,alpha)).
Proof.
  Let pair /in alpha /times alpha.
  Take sets a,b such that a,b /in alpha /\ pair = (a,b).
  Then a /cup b /subset alpha.
  a /cup b /neq alpha.
  Then a /cup b /in alpha.
  Proof.
    a /cup b /in /Ord.
    Forall o1,o2 /in /Ord (o1 /in o2 \/ o2 /in o1 \/ o1 = o2).
    Take ordinals o1,o2 such that a /cup b = o1 /\ alpha = o2.
    Then a /cup b /in alpha \/ a /cup b = alpha \/ alpha /in a /cup b.
  end.
  Then (a,b) <2 (0,alpha).
  Then pair /in sset(goedel,(0,alpha)).
end.
qed.



Lemma. Forall alpha /in /Ord ((0,alpha) /in /Ord /times /Ord /\ sset(goedel,(0,alpha)) /subset Dom(Goed)  /\
Goed /upharpoonright sset(goedel,(0,alpha)) : sset(goedel,(0,alpha)) /leftrightarrow Goed[(0,alpha)]).
Proof.
Let alpha /in /Ord.
Then (0,alpha) /in /Ord /times /Ord /\ sset(goedel,(0,alpha)) /subset Dom(Goed).
Goed[(0,alpha)] = Goed^[sset(goedel,(0,alpha))].
Then Goed /upharpoonright sset(goedel,(0,alpha)) : sset(goedel,(0,alpha)) /rightarrow Goed[(0,alpha)].
Proof.
  Dom(Goed /upharpoonright sset(goedel,(0,alpha))) = sset(goedel,(0,alpha)).
  Let pair /in sset(goedel,(0,alpha)).
  Then (Goed /upharpoonright sset(goedel,(0,alpha)))[pair] = Goed[pair].
  Goed[pair] /in Goed^[sset(goedel,(0,alpha))].
  Then (Goed /upharpoonright sset(goedel,(0,alpha)))[pair] /in Goed[(0,alpha)].
end.
Goed /upharpoonright sset(goedel,(0,alpha)) is injective.
ran(Goed /upharpoonright sset(goedel,(0,alpha))) /subset Goed[(0,alpha)].
Proof.
  Let x /in ran(Goed /upharpoonright sset(goedel,(0,alpha))).
  ran(Goed /upharpoonright sset(goedel,(0,alpha))) = {zfset z | exists zz /in sset(goedel,(0,alpha)) (Goed /upharpoonright sset(goedel,(0,alpha)))[zz] = z}.
  Take a set y such that y /in sset(goedel,(0,alpha)) /\ (Goed /upharpoonright sset(goedel,(0,alpha)))[y] = x.
  Then x /in Goed^[sset(goedel,(0,alpha))].
  Then x /in Goed[(0,alpha)].
end.
Goed[(0,alpha)] /subset ran(Goed /upharpoonright sset(goedel,(0,alpha))).
Proof.
  Let x /in Goed[(0,alpha)]. Then x /in Goed^[sset(goedel,(0,alpha))].
  Take a set y such that y /in sset(goedel,(0,alpha)) /\ Goed[y] = x.
  Then (Goed /upharpoonright sset(goedel,(0,alpha)))[y] = x.
  Then x /in ran(Goed /upharpoonright sset(goedel,(0,alpha))).
end.
qed.


Lemma. Forall alpha /in /Ord alpha /times alpha /tilde Goed[(0,alpha)].
Proof.
Let alpha /in /Ord.
alpha /times alpha = sset(goedel,(0,alpha)).
Goed /upharpoonright sset(goedel,(0,alpha)) : sset(goedel,(0,alpha)) /leftrightarrow Goed[(0,alpha)].
qed.



Lemma. Goed[(0,/NN)] = /NN.
Proof.
/NN <= /NN /times /NN.
Proof.
  Define f[n] = (n,0) for n in /NN.
  Then f is a zffunction.
  f : /NN /rightarrow /NN /times /NN.
  f is injective.
end.
Then /NN <= Goed[(0,/NN)].
Proof. 
  /NN /times /NN /tilde Goed[(0,/NN)].
  Take a zffunction f such that f : /NN /times /NN /leftrightarrow Goed[(0,/NN)].
  Take an injective zffunction g such that g : /NN /rightarrow /NN /times /NN.
  Then f /circ g is an injective zffunction.
  f /circ g : /NN /rightarrow Goed[(0,/NN)].
end.

Goed[(0,/NN)] /in /Ord.
Then Goed[(0,/NN)] = /NN \/ /NN /in Goed[(0,/NN)].
Case Goed[(0,/NN)] = /NN. end.

Case /NN /in Goed[(0,/NN)].
  Goed[(0,/NN)] = Goed^[sset(goedel,(0,/NN))].
  sset(goedel,(0,/NN)) = /NN /times /NN.
  Then /NN /in Goed^[/NN /times /NN].
  /NN /times /NN /subset Dom(Goed).
  Goed^[/NN /times /NN] = {zfset z | exists x /in /NN /times /NN (z = Goed[x])}.
  Take a set pair such that pair /in /NN /times /NN /\ /NN = Goed[pair].
  Take ordinals a,b such that a,b /in /NN /\ pair = (a,b).
  Then (a,b) /in Dom(Goed).
  Goed[(a,b)] = Goed^[sset(goedel,(a,b))].
  Then /NN = Goed^[sset(goedel,(a,b))].

  Take an ordinal c such that c = (a /cup b) + 1.
  sset(goedel,(a,b)) /subset c /times c.
  Proof.
    Let pair2 /in sset(goedel,(a,b)). Then pair2 /in /Ord /times /Ord.
    Take ordinals a2,b2 such that pair2 = (a2,b2).
    Then (a2,b2) <2 (a,b).
    Then a2 /cup b2 /in a /cup b \/ a2 /cup b2 = a /cup b.
    Then a2 /subset a /cup b /\ b2 /subset a /cup b.
    Then a2,b2 /in c.
    Then pair2 /in c /times c.
  end.
  
  a /subset b \/ b /subset a.
  Then a /cup b = a \/ a /cup b = b.
  Then a /cup b /in /NN.
  Then c /in /NN.
  Then c is finite.
  Then c /times c is finite.
  Then c /times c < /NN.
  Proof.
    not (c /times c /tilde /NN).
    Take a zffunction f such that f : c /times c /leftrightarrow Card(c /times c).
    Then f is injective.
    f : c /times c /rightarrow /NN.
  end.
  
  sset(goedel,(a,b)) /tilde /NN.
  Proof.
    sset(goedel,(a,b)) /subset Dom(Goed).
    Goed /upharpoonright sset(goedel,(a,b)) : sset(goedel,(a,b)) /leftrightarrow Goed^[sset(goedel,(a,b))].
    Proof.
      Dom(Goed /upharpoonright sset(goedel,(a,b))) = sset(goedel,(a,b)).
      ran(Goed /upharpoonright sset(goedel,(a,b))) = { zfset x | exists z /in sset(goedel,(a,b)) x = Goed[z]}.
      Goed^[sset(goedel,(a,b))] = { zfset x | exists z /in sset(goedel,(a,b)) x = Goed[z]}.
      Then ran(Goed /upharpoonright sset(goedel,(a,b))) = Goed^[sset(goedel,(a,b))].
      Proof.
        ran(Goed /upharpoonright sset(goedel,(a,b))) /subset Goed^[sset(goedel,(a,b))].
        Goed^[sset(goedel,(a,b))] /subset ran(Goed /upharpoonright sset(goedel,(a,b))).
      end.
      Goed is injective.
      Then Goed /upharpoonright sset(goedel,(a,b)) is injective.
      Proof.
        Let x,y /in Dom(Goed /upharpoonright sset(goedel,(a,b))).
        Let (Goed /upharpoonright sset(goedel,(a,b)))[x] = (Goed /upharpoonright sset(goedel,(a,b)))[y].
        (Goed /upharpoonright sset(goedel,(a,b)))[x] = Goed[x].
        (Goed /upharpoonright sset(goedel,(a,b)))[y] = Goed[y].
        Then Goed[x] = Goed[y].
        Then x = y.
      end.
    end.
    Goed^[sset(goedel,(a,b))] = /NN.
  end.
  
  sset(goedel,(a,b)) <= c /times c.
  Then /NN <= c /times c.
  Forall x,y /in /VV (x <= y /\ y <= x => x /tilde y).
  Then c /times c /tilde /NN.
  Contradiction.
end.

qed.





Lemma. Forall alpha /in /Ord (Goed[(0,Alef[alpha])] = Alef[alpha]).
Proof.
Define phi[alpha] = 
  Case Goed[(0,Alef[alpha])] = Alef[alpha] -> 0,
  Case Goed[(0,Alef[alpha])] /neq Alef[alpha] -> 1
for alpha in /Ord.

Then phi[0] = 0.

Forall alpha /in /Ord (forall beta /in alpha phi[beta] = 0 => phi[alpha] = 0).
Proof.
  Let alpha /in /Ord. Let forall beta /in alpha phi[beta] = 0.
  Then forall beta /in alpha (Goed[(0,Alef[beta])] = Alef[beta]).
  Goed[(0,Alef[alpha])], (Alef[alpha] /times Alef[alpha]) /in /VV.
  Goed[(0,Alef[alpha])] /tilde (Alef[alpha] /times Alef[alpha]).

  Alef[alpha] <= Alef[alpha] /times Alef[alpha].
  Proof.
    Define f[n] = (n,0) for n in Alef[alpha].
    Then f is a zffunction.
    f : Alef[alpha] /rightarrow Alef[alpha] /times Alef[alpha].
    f is injective.
  end.
  Then Alef[alpha] <= Goed[(0,Alef[alpha])].
  Proof. 
    Alef[alpha] /times Alef[alpha] /tilde Goed[(0,Alef[alpha])].
    Take a zffunction f such that f : Alef[alpha] /times Alef[alpha] /leftrightarrow Goed[(0,Alef[alpha])].
    Take an injective zffunction g such that g : Alef[alpha] /rightarrow Alef[alpha] /times Alef[alpha].
    Then f /circ g is an injective zffunction.
    f /circ g : Alef[alpha] /rightarrow Goed[(0,Alef[alpha])].
    Proof.
      Dom(f /circ g) = Alef[alpha].
      ran(f /circ g) /subset Goed[(0,Alef[alpha])].
#      Proof.
#        Let x /in Alef[alpha].
#        Then g[x] /in Alef[alpha] /times Alef[alpha].
#        Then (f /circ g)[x] /in Goed[(0,Alef[alpha])].
#      end.
    end.
  end.
  
  Goed[(0,Alef[alpha])],Alef[alpha]  /in /Ord.
  Then Goed[(0,Alef[alpha])] = Alef[alpha] \/ Alef[alpha] /in Goed[(0,Alef[alpha])].
  Proof.  
    Alef[alpha] <= Goed[(0,Alef[alpha])].
    Then Alef[alpha] /subset Card(Goed[(0,Alef[alpha])]).
    Card(Goed[(0,Alef[alpha])]) /subset Goed[(0,Alef[alpha])].
    Then Alef[alpha] /subset Goed[(0,Alef[alpha])].
    Forall a,b /in /Ord (a /in b \/ b /in a \/ a = b).
    Goed[(0,Alef[alpha])],Alef[alpha]  /in /Ord.
    Take ordinals a,b such that a = Alef[alpha] /\ b = Goed[(0,Alef[alpha])].
    Then a /in b \/ b /in a \/ a = b.
    Goed[(0,Alef[alpha])] /notin Alef[alpha].
  end.

  Case Goed[(0,Alef[alpha])] = Alef[alpha]. end.
  
  Case Alef[alpha] /in Goed[(0,Alef[alpha])].
    Goed[(0,Alef[alpha])] = Goed^[sset(goedel,(0,Alef[alpha]))].
    sset(goedel,(0,Alef[alpha])) = Alef[alpha] /times Alef[alpha].
    Then Alef[alpha] /in Goed^[Alef[alpha] /times Alef[alpha]].
    Alef[alpha] /times Alef[alpha] /subset Dom(Goed).
    Goed^[Alef[alpha] /times Alef[alpha]] = {zfset z | exists x /in Alef[alpha] /times Alef[alpha] (z = Goed[x])}.
    Take a set pair such that pair /in Alef[alpha] /times Alef[alpha] /\ Alef[alpha] = Goed[pair].
    Take ordinals a,b such that a,b /in Alef[alpha] /\ pair = (a,b).
    Then (a,b) /in Dom(Goed).
    Goed[(a,b)] = Goed^[sset(goedel,(a,b))].
    Then Alef[alpha] = Goed^[sset(goedel,(a,b))].
    
    Take an ordinal c such that c = (a /cup b) + 1.
    sset(goedel,(a,b)) /subset c /times c.
    Proof.
      Let pair2 /in sset(goedel,(a,b)). Then pair2 /in /Ord /times /Ord.
      Take ordinals a2,b2 such that pair2 = (a2,b2).
      Then (a2,b2) <2 (a,b).
      Then a2 /cup b2 /in a /cup b \/ a2 /cup b2 = a /cup b.
      Then a2 /subset a /cup b /\ b2 /subset a /cup b.
      Then a2,b2 /in c.
      Then pair2 /in c /times c.
    end.
    
    a /subset b \/ b /subset a.
    Then a /cup b = a \/ a /cup b = b.
    Then a /cup b /in Alef[alpha].
    Alef[alpha] /in /Lim.
    Proof.
      Alef[alpha] /in /Card.
      alpha = 0 \/ 0 /in alpha.
      Case alpha = 0. Then Alef[alpha] = /NN. end.
      Case 0 /in alpha. Then /NN /in Alef[alpha]. end.
    end.
    Then c /in Alef[alpha].
    Then Card(c) /in Alef[alpha].
    c /times c /tilde Card(c) /times Card(c).
    Card(c) /times Card(c) < Alef[alpha].
    Proof.
      Card(c) /in /Card.
      /NN /in Card(c) \/ Card(c) = /NN \/ Card(c) /in /NN.
      Case Card(c) /in /NN.
        Then Card(c) /times Card(c) is finite.
        Then Card(c) /times Card(c) < /NN.
        Proof.
          not (Card(c) /times Card(c) /tilde /NN).
          Take a zffunction f such that f : Card(c) /times Card(c) /leftrightarrow Card(Card(c) /times Card(c)).
          Then f is injective.
          f : Card(c) /times Card(c) /rightarrow /NN.
        end.
        /NN <= Alef[alpha].
        Then Card(c) /times Card(c) <= Alef[alpha].
        not (Card(c) /times Card(c) /tilde Alef[alpha]).
      end.
      Case Card(c) = /NN.
        Then Card(c) = Alef[0]. 0 /in alpha.
        Then Card(c) /in Alef[alpha].
        Goed[(0,Alef[0])] = Alef[0].
        Goed[(0,Alef[0])] /tilde Alef[0] /times Alef[0].
        Then Card(c) /times Card(c) /tilde /NN.
        Then Card(c) /times Card(c) <= Alef[alpha].
        not (Card(c) /times Card(c) /tilde Alef[alpha]).
      end.
      Case /NN /in Card(c).
        Card(c) /in /Card.
        Take an ordinal beta such that Card(c) = Alef[beta].
        Alef[beta] /in Alef[alpha].
        Then beta /in alpha.
        Proof.
          alpha /in beta \/ beta /in alpha \/ alpha = beta.
          Case alpha = beta. Contradiction. end.
          Case beta /in alpha. end.
          Case alpha /in beta. Then Alef[alpha] /in Alef[beta]. Contradiction. end.
        end.
        Goed[(0,Alef[beta])] = Alef[beta].
        Goed[(0,Alef[beta])] /tilde Alef[beta] /times Alef[beta].
        Then Card(c) /times Card(c) /tilde Alef[beta].
        Then Card(c) /times Card(c) <= Alef[alpha].
        not (Card(c) /times Card(c) /tilde Alef[alpha]).
      end.
    end.
    
    Then c /times c <= Alef[alpha].
    
    sset(goedel,(a,b)) /tilde Alef[alpha].
    Proof.
      sset(goedel,(a,b)) /subset Dom(Goed).
      Goed /upharpoonright sset(goedel,(a,b)) : sset(goedel,(a,b)) /leftrightarrow Goed^[sset(goedel,(a,b))].
      Proof.
        Dom(Goed /upharpoonright sset(goedel,(a,b))) = sset(goedel,(a,b)).
        ran(Goed /upharpoonright sset(goedel,(a,b))) = { zfset x | exists z /in sset(goedel,(a,b)) x = Goed[z]}.
        Goed^[sset(goedel,(a,b))] = { zfset x | exists z /in sset(goedel,(a,b)) x = Goed[z]}.
        Then ran(Goed /upharpoonright sset(goedel,(a,b))) = Goed^[sset(goedel,(a,b))].
        Proof.
          ran(Goed /upharpoonright sset(goedel,(a,b))) /subset Goed^[sset(goedel,(a,b))].
          Goed^[sset(goedel,(a,b))] /subset ran(Goed /upharpoonright sset(goedel,(a,b))).
        end.
        Goed is injective.
        Then Goed /upharpoonright sset(goedel,(a,b)) is injective.
        Proof.
          Let x,y /in Dom(Goed /upharpoonright sset(goedel,(a,b))).
          Let (Goed /upharpoonright sset(goedel,(a,b)))[x] = (Goed /upharpoonright sset(goedel,(a,b)))[y].
          (Goed /upharpoonright sset(goedel,(a,b)))[x] = Goed[x].
          (Goed /upharpoonright sset(goedel,(a,b)))[y] = Goed[y].
          Then Goed[x] = Goed[y].
          Then x = y.
        end.
      end.
      Goed^[sset(goedel,(a,b))] = Alef[alpha].
    end.

    sset(goedel,(a,b)) <= c /times c.
    Then Alef[alpha] <= c /times c.
    Forall x,y /in /VV (x <= y /\ y <= x => x /tilde y).
    Then c /times c /tilde Alef[alpha].
    Contradiction.

  end.
  
end.

Define M = {ordinal gamma | phi[gamma] = 0}.
Then M /subset /Ord.
Let N = /Ord /setminus M.
Then N /neq /emptyset \/ N = /emptyset.
Case N = /emptyset. Then /Ord = M. end.
Case N /neq /emptyset.
Take a zfset a such that (a /in N /\ (forall y /in a y /notin N)).
Then forall y /in a phi[y] = 0.
Then phi[a] = 0.
Contradiction. end.

qed.



Lemma. Forall alpha /in /Ord (Alef[alpha] /tilde Alef[alpha] /times Alef[alpha]).
Proof.
Let alpha /in /Ord.
Goed[(0,Alef[alpha])] = Alef[alpha].
Goed[(0,Alef[alpha])] /tilde (Alef[alpha] /times Alef[alpha]).
qed.


Lemma. Forall x /in /VV (Card(x) /notin /NN => x /tilde x /times x).
Proof.
Let x /in /VV. Let Card(x) /notin /NN.
Take a cardinal kappa such that kappa = Card(x).
Then x /tilde kappa.
x /times x /tilde kappa /times kappa.
/NN = kappa \/ /NN /in kappa.
Then exists alpha /in /Ord kappa = Alef[alpha].
Proof.
  Case kappa = /NN. Then kappa = Alef[0]. end.
  Case /NN /in kappa. end.
end.
Take an ordinal alpha such that kappa = Alef[alpha].
Then Alef[alpha] /tilde Alef[alpha] /times Alef[alpha].
Then kappa /tilde kappa /times kappa.
Then x /tilde x /times x.
qed.




Lemma. Contradiction.

