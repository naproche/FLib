# 3-New implementation of pairs

# This is the same as section 2, but now we use the integrated ordered pairs of Naproche.
# We need an axiom such that ordered pairs work as before.
# We also use the integrated functions. So now a function is not a set of ordered paird, but it has a domain and
# for any object in the domain we have an attached value.
# An axiom states that to functions are the same iff the domain is the same and all values are the same.
# Another axiom states that the domain of a function is a set.

# The main results are the same as in section 2 and we get the same contradiction in the end.







# General Syntax

Let x /in y stand for x is an element of y.
Let x /notin y stand for x is not an element of y.
Let x /neq y stand for x != y.


# Pretyped Variables

Let a,b,c,A,B,C,x,y,z,X,Y,Z stand for sets.


# Introduction of Emptyset, Universe

Definition Emptyset. The empty set is {set x | x /neq x}.
Let /emptyset stand for the empty set.

Definition. Let a be a set. a is empty iff a = /emptyset.
Definition. Let a be a set. a is nonempty iff exists b (b /in a).

Lemma. Let a be a set. Let a be nonempty. Then a /neq /emptyset.

Definition Universe. The universe is {set x | x = x}.
Let /VV stand for the universe.

Axiom Extentionality. Forall a, b ( (forall c (c /in a <=> c /in b)) => a = b).

# Attention, the universe is considered as a set itself, so foundation does not hold.



# Arithmetic

Definition Subset. A subset of A is a set B such that
forall c (c /in B => c /in A).
Let B /subset A stand for B is a subset of A.

Lemma SubsetTest. Let A, B be sets. Let A /subset B and B /subset A. Then A = B.

Definition Pair. The pair of A and B is
{set a | a = A \/ a = B}.

Definition Union. The union of X and Y is 
{set x | x /in X or x /in Y}.
Let X /cup Y stand for the union of X and Y.

Definition Intersection. The intersection of X and Y is 
{set x | x /in X and x /in Y}.
Let X /cap Y stand for the intersection of X and Y.

Definition Difference. The difference of X and Y is 
{set x | x /in X and x /notin Y}.
Let X /setminus Y stand for the difference of X and Y.

Definition BigUnion. The union of X is
{set x | exists y (y /in X /\ x /in y)}.
Let /bigcup X stand for the union of X.

Definition BigIntersection. The intersection of X is
{set x | forall y (y /in X => x /in y)}.
Let /bigcap X stand for the intersection of X.

Definition PowerSet. The power set of X is
{set x | x /subset X}.
Let /PP X stand for the power set of X.

Definition Singleton. The singleton of X is
{set x | x = X}.
Let <X> stand for the singleton of X.

Lemma. Let X be a set. Then <X> is a set.
# Lemma. Let X /in A. Then <X> /subset A.

# WARNING: Somehow we do not have access to "<x>". unrecognized: theSingletonOf(X) 







# Ordered pairs

Axiom OPair1. Let a,b /in /VV. Then (a,b) is a set.
Axiom OPair2. (x,y) = (X,Y) => x = X /\ y = Y.

Definition 105a. The cartesian product of A and B is
{set x | exists a,b (x = (a,b) /\ a /in A /\ b /in B)}.
Let A /times B stand for the cartesian product of A and B.

Lemma TestProduct1. Forall x /in A /times B exists a,b (a /in A /\ b /in B /\ x = (a,b)).



# Relations

[synonym relation/-s]

Definition Relation. A relation is a set R such that 
R /subset /VV /times /VV.
Let a - R - b stand for (a,b) /in R.

Lemma Relation1. Let R be a relation. x /in R => exists a,b /in /VV (x = (a,b)).

Lemma Relation2. Let R be a relation. Let S be a set. Let S = {(y,z) | y, z /in /VV /\ (y,z) /in R}. Then R /subset S.
Proof. Forall x /in R exists a,b /in /VV (x = (a,b)).
# This takes longer than it should
Let x /in R. Take a,b /in /VV such that x = (a,b).
Then x /in S.
qed.




# Functions

Let M stand for a set.
Let f,g,h,F,G,H stand for functions.
Let the value of f at x stand for f[x].
Let the domain of f stand for Dom(f).

Axiom. Let f be a function. The domain of f is a set.
Axiom. Let f be a function. Let x /in Dom(f). Then f[x] is a set.

Let f is defined on M stand for M /subset Dom(f).

Definition Range. Let f be a function. The range of f is
{f[x] | x /in Dom(f)}.
Let ran(f) stand for the range of f.

Definition Image. Let f be a function. Let M be a set. The image of M under f is
{f[x] | x /in Dom(f) /cap M}.
Let f^[M] stand for the image of M under f.

Definition Composition. Let f and g be functions. Let ran(f) /subset Dom(g). The composition of g and f is
a function h such that Dom(h) = Dom(f) and forall x /in Dom(f) h[x] = g[f[x]].
Let g /circ f stand for the composition of g and f.

Definition Map. A map from A to B is a function F such that
Dom(F) = A and ran(F) /subset B.
Let F : A /rightarrow B stand for F is a map from A to B.

Definition PMap. A partial map from A to B is a function F such that
Dom(F) /subset A and ran(F) /subset B.
Let F : A /harpoonright B stand for F is a partial map from A to B.

Definition Restriction. Let f be a function. Let M /subset Dom(f). The restriction of f to M is a function g such that
Dom(g) = M and forall x /in M /cap Dom(f) (g[x] = f[x]).
Let f /upharpoonright M stand for the restriction of f to M.

Signature. Id is a function.
Axiom. Dom(Id) = /VV.
Axiom. Forall x (Id[x] = x).

Lemma. ran(Id) = /VV.
Lemma. Forall M (Id^[M] = M).
Lemma. Id : /VV /rightarrow /VV.

Definition Surjective. Let F be a function. Assume F : A /rightarrow B. F is surjective from A to B
iff ran(F) = B.

Definition Injective. f is injective iff
forall x,y /in Dom(f) (f[x] = f[y] => x = y).

Definition Bijective. Let F be a function. F is bijective from A to B
iff F : A /rightarrow B and Dom(F) = A and ran(F) = B and F is injective.
Let F : A /leftrightarrow B stand for F is bijective from A to B.

Lemma. Id is surjective from /VV to /VV.
Lemma. Id is injective.
Lemma. Id : /VV /leftrightarrow /VV.
Lemma. Id /upharpoonright M : M /leftrightarrow M.
Proof. Id /upharpoonright M : M /rightarrow M.
  Proof. Dom(Id /upharpoonright M) = M.
      Let x /in M. Then Id[x] = x.
  end.
  Id /upharpoonright M is injective.
  ran(Id /upharpoonright M) = M.
qed.

Axiom. Let f and g be functions. f = g iff Dom(f) = Dom(g) and forall x /in Dom(f) (f[x] = g[x]).

Definition. Let f be an injective function. The inverse of f is a function g such that
Dom(g) = ran(f) and (forall x /in ran(f) forall y /in Dom(f) (g[x] = y iff f[y] = x)).
Let f^{-1} stand for the inverse of f.

Lemma. Id^{-1} = Id.

Lemma. Let f be bijective from A to B. Then f^{-1} is bijective from B to A.

Definition SetofFunctions. ^{A}B = {function f | f : A /rightarrow B}.

Lemma. Id /in ^{/VV}/VV.



# Various results

Theorem. Let A be a set. There exists an injective function F such that F : A /rightarrow /PP A.
Proof. Define F[x] = {set y | y = x} for x in A.
F: A /rightarrow /PP A.
F is injective.
qed.

Lemma. /PP /VV = /VV.

Lemma. Let A be a set. There is no injective function G such that 
G: /PP A /rightarrow A.
Proof by contradiction.
    Assume the contrary.
    Take an injective function G such that G : /PP A /rightarrow A.
    G^{-1} : ran(G) /rightarrow /PP A.
    Define C = {set u | u /in ran(G) /\ u /notin G^{-1}[u]}.
    C /subset A. C /in ran(G^{-1}).
    Take a set y such that G^{-1}[y] = C. Then y /in C iff y /notin G^{-1}[y].
    y /in C iff y /notin C.
    Contradiction.
qed.


Lemma. Contradiction.

# Contradictory Axioms. So now everything can be proven.
# /PP /VV = /VV and Id is an injective function Id : /PP /VV /rightarrow /VV.
# Therefore we need to distinguish between zf-sets and proper classes.
















