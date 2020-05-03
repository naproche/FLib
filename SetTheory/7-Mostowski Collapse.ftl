# 7-Mostowski Collapse

# Here we reintoduce relations (as sets of ordered pairs) and define different kinds of relations.
# We define eps as the relation "/in" of zfsets and show that it is strongly wellfounded and that it is a wellorder on /Ord.
# Then we define the transitive collapse for any strongly wellordered relation and define the thansitive closure
# for zfsets (for eps as well as for any SWR).

# Main results:

# - TCol is a zffunction
# - The range of TCol is transitive
# - for extensional R TCol is injective (hence bijective onto its image)
# - TCol is a homomorphism between the relations R and eps
# - the range is an ordinal iff the domain of the relation is a zfset; otherwise it is /Ord
# - x /subset alpha => otp(x) /subset alpha






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

Definition field. Let R be a relation. The relfield of R is
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

Definition. Let R be a relation. R is reltransitive iff forall x,y,z (x - R - y /\ y - R - z => x - R - z).
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





# Cardinalities

Axiom AC. Let x be a ZFset. Then exists alpha exists f (f : alpha /leftrightarrow x).

Definition SameCardinality. Let x, y be ZFsets. x and y are equipotent iff
exists f (f : x /leftrightarrow y).

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



[synonym cardinal/-s]
Signature. A cardinal is a notion.

Axiom. Let kappa be a cardinal. Then kappa is an ordinal.
Axiom. Let kappa be an ordinal. kappa is a cardinal iff exists x (kappa = Card(x)).

Let kappa stand for a cardinal.

Axiom. Let alpha be an ordinal. Then Card(alpha) /subset alpha.

Axiom. Let kappa be a cardinal. Then Card(kappa) = kappa.


Definition. The class of cardinals is
{ordinal alpha | alpha is a cardinal}.
Let /Card stand for the class of cardinals.

Axiom. Forall n /in /NN Card(n) = n.
Axiom. Card(/NN) = /NN.





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

Lemma. Let R be a strong wellorder. Then R is extensional.
Proof.
R is connex.
Then (forall x,y /in relfield(R) (x - R - y \/ y - R - x \/ x = y)).
Let x, y /in reldomain(R). Then x,y /in relfield(R). Then (x - R - y \/ y - R - x \/ x = y).
qed.


# Relation-reality-check

Lemma. Let R be a relation. Let forall x,y /in /VV (x - R - y iff x /in y). Then antisym(R).
Proof by contradiction. Assume the contrary. Take x,y such that (x,y /in /VV /\ x - R - y /\ y - R - x /\ x /neq y).
Define A = {zfset z | z = x \/ z = y}.
Contradiction.
# This seems to be enough. I'm surprised that Naproche doesn't need more help to come up with the contradiction by foundation.
qed.

Lemma. Let R be a relation. Let relfield(R) = /Ord. Let forall alpha, beta (alpha - R - beta iff alpha /in beta).
Then R is a strict linear order.
Proof. reltrans(R).
  irref(R).
  (R is a strict partial order).
  Forall alpha, beta /in /Ord (alpha /in beta \/ beta /in alpha \/ alpha = beta).
  con(R).
qed.

Lemma. Let R be a relation. Let forall x,y /in /VV (x - R - y iff x /in y). Then R is strongly wellfounded.
Proof. 
reldomain(R) = /VV.
R is wellfounded.
Proof.
  Let A be a set. Let A /neq /emptyset /\ A /subset /VV. Take a set b such that (b /in A /\ forall c /in b c /notin A).
  Then forall y /in A (not (y - R - b)).
end.
Let x /in /VV. Then sset(R,x) = x.
qed.





# Mostowski Collapse


Let SWR stand for a strongly wellfounded relation.
Signature. TCol /res SWR is a function.

Axiom. Let R be a strongly wellfounded relation. Dom(TCol /res R) = reldomain(R).
Axiom. Let R be a strongly wellfounded relation. Then forall x /in (reldomain(R))  (((TCol /res R) [x]) = ((TCol /res R) /caret [sset(R,x)])).

Lemma. Let R be a strongly wellfounded relation. Then (TCol /res R) is a zffunction.
Proof.
Define phi[n] =
  Case (TCol /res R) [n] /in /VV -> 0,
  Case (TCol /res R) [n] /notin /VV -> 1
for n in reldomain(R).

Forall x /in reldomain(R) (forall y /in sset(R,x) phi[y] = 0 => phi[x] = 0).
Proof.
  Let x /in reldomain(R). Let forall y /in sset(R,x) phi[y] = 0.
  Define f[n] = (TCol /res R) [n] for n in sset(R,x).
  Then (f is a zffunction).
  Proof.
    Let n /in Dom(f). Then f[n] /in /VV.
  end.
  (TCol /res R) /caret [sset(R,x)] = f^[sset(R,x)].
  (TCol /res R) [x] = (TCol /res R) /caret [sset(R,x)].
  Then (TCol /res R) [x] /in /VV.
end.

Define M = {set x | x /in reldomain(R) /\ phi[x] = 0}.
Let N = reldomain(R) /setminus M.
Case N = /emptyset. Then M = reldomain(R). end.
Case N /neq /emptyset.
  R is wellfounded.
  Forall A ((A /neq /emptyset /\ A /subset reldomain(R)) => (exists x /in A (forall y /in A (not (y - R - x))))).
  Take a zfset x such that (x /in N /\ (forall y /in N (not (y - R - x)))).
  Then forall y /in sset(R,x) y /notin N.
  Then forall y /in sset(R,x) phi[y] = 0.
  Then phi[x] = 0.
  Contradiction.
end.

qed.

Lemma. Let R be a strongly wellfounded relation. Then forall x /in (reldomain(R))  ((TCol /res R) [x] = (TCol /res R)^[sset(R,x)]).
Proof.
TCol /res R is a zffunction.
Let x /in reldomain(R).
Then (TCol /res R) /caret [sset(R,x)] = (TCol /res R)^[sset(R,x)].
qed.


Signature. eps is an object.
Axiom. eps is a relation.
Axiom. Forall x,y /in /VV (x - eps - y iff x /in y).
Lemma. reldomain(eps) = /VV.
Lemma. eps is strongly wellfounded.
Lemma. Forall x /in /VV sset(eps,x) = x.
Lemma. eps is extensional.

Lemma. Let A /subset /Ord. (eps /restrict A) is a strong wellorder.
Proof.
relfield(eps /restrict A) /subset A.
reldomain(eps /restrict A) /subset /Ord.
(eps /restrict A) is wellfounded.
Proof.
  Let B /subset reldomain(eps /restrict A). Let B /neq /emptyset. Then B /subset /Ord.
  Take a set x such that x /in B /\ forall y /in x (y /notin B).
  Then forall y ((y - eps - x) => (y /notin B)).
  Then forall y ((y - (eps /restrict A) - x) => (y /notin B)).
end.
(eps /restrict A) is strongly wellfounded.
Proof.
  Let x /in relfield(eps /restrict A). Then sset((eps /restrict A),x) /subset x.
  Then sset((eps /restrict A),x) /in /VV.
end.
(eps /restrict A) is a strict linear order.
Proof.
  (eps /restrict A) is connex.
  Proof.
    Let x,y /in relfield(eps /restrict A). Then x,y /in A.
    Then x,y /in /Ord. Forall alpha, beta /in /Ord (alpha /in beta \/ beta /in alpha \/ alpha = beta).
    Then x /in y \/ y /in x \/ x = y.
  end.
  (eps /restrict A) is irreflexive.
  (eps /restrict A) is reltransitive.
  Proof.
    Let x, y, z /in /VV. Let x - (eps /restrict A) - y /\ y - (eps /restrict A) - z.
    Then x,y,z /in /Ord /\ x /in y /\ y /in z.
    Then x /in z.
    Then x - (eps /restrict A) - z.
  end.
end.
qed.



Lemma. Let x be a zfset. Let x /subset /Ord. Then /bigcup x /in /Ord.
Proof.
Trans(/bigcup x).
Proof.
  Let y /in /bigcup x. Take a set z such that z /in x /\ y /in z.
  Let y1 /in y. Then y1 /in z.
  Then y1 /in /bigcup x.
end.
qed.

# This is just a shortcut for the restirction of the relation eps such that the domain is x.
Definition. Let x be a zfset. Let x /subset /Ord. The epsrestriction of x is
eps /restrict (x /cup (<(/bigcup x) + 1>)).
Let epsrest(x) stand for the epsrestriction of x.

Lemma. Let x be a zfset. Let x /subset /Ord. Then reldomain(epsrest(x)) = x.
Proof.
((/bigcup x)+1) /in x /cup (<(/bigcup x) + 1>).
Let y /in x.
Then y /in ((/bigcup x) + 1).
Proof.
  y, /bigcup x /in /Ord.
  Forall alpha, beta /in /Ord (alpha /in beta \/ beta /in alpha \/ alpha = beta).
  Then y /in /bigcup x \/ /bigcup x /in y \/ y = /bigcup x.
  y /subset (/bigcup x).
end.
Then y - (epsrest(x)) - ((/bigcup x) + 1).
Then y /in reldomain(epsrest(x)).
Let z /in reldomain(epsrest(x)). Take a zfset a such that z - (epsrest(x)) - a.
Then z /in a /\ z,a /in (x /cup </bigcup x + 1>). Then z /in x.
qed.

Lemma. Let x be a zfset. Let x /subset /Ord. Then x /cup <(/bigcup x)+1> /subset /Ord.

Lemma. Let x be a zfset. Let x /subset /Ord. Then epsrest(x) is a strong wellorder.




Lemma. Forall x /in /VV (TCol /res eps)[x] = x.
Proof.

Define phi[n] =
  Case (TCol /res eps)[n] = n -> 0,
  Case (TCol /res eps)[n] /neq n -> 1
for n in /VV.

Forall x /in /VV (forall y /in x phi[y] = 0 => phi[x] = 0).
Proof.
  Let x /in /VV. Let forall y /in x phi[y] = 0.
  Then forall y /in x (TCol /res eps)[y] = y. (TCol /res eps)[x] = (TCol /res eps)^[x].
  Then (TCol /res eps)[x] /subset x. x /subset (TCol /res eps)[x].
end.

  Define M = {zfset z | z /in /VV /\ phi[z] = 0}.
  Then M /subset /VV.
  Let N = /VV /setminus M.
  Then N /neq /emptyset \/ N = /emptyset.
  Case N = /emptyset. Then /VV /subset M. M /subset /VV. Then /VV = M. end.
  Case N /neq /emptyset.
  Take a zfset a such that (a /in N /\ (forall y /in a y /notin N)).
  Then forall y /in a phi[y] = 0.
  Then phi[a] = 0.
  Contradiction. end.

qed.




Lemma. Let R be a strongly wellfounded relation. Let R be extensional. Then Trans(ran(TCol /res R)).
Proof.
Let x /in ran(TCol /res R). Take a zfset a such that a /in reldomain(R) /\ x = (TCol /res R)[a].
Let y /in x. Then y /in (TCol /res R)^[sset(R,a)].
Take a zfset b such that b /in sset(R,a) /\ y = (TCol /res R)[b].
Then y /in ran(TCol /res R).
qed.



Lemma. Let R be a strongly wellfounded relation. Let R be extensional. Then (TCol /res R) is injective.
Proof.
Define A = {zfset x | x /in ran(TCol /res R) /\ exists y,z (y /neq z /\ y,z /in reldomain(R) /\ (TCol /res R)[y] = x /\ (TCol /res R)[z] = x)}.
Then A is a set.
Case A = /emptyset. 
  Then forall y,z /in reldomain(R) (y /neq z => (TCol /res R)[y] /neq (TCol /res R)[z]).
  Then (TCol /res R) is injective. 
end.

Case A /neq /emptyset. A /subset ran(TCol /res R). Take a zfset x such that x /in A /\ forall y /in x y /notin A.
  Take zfsets y1, y2 such that (y1 /neq y2 /\ y1,y2 /in reldomain(R) /\ (TCol /res R)[y1] = x /\ (TCol /res R)[y2] = x).
  Forall u1 /in sset(R,y1) (u1 /in sset(R,y2)).
  Proof.
    Let u1 /in sset(R,y1). (TCol /res R)[y1] = (TCol /res R)^[sset(R,y1)]. Then (TCol /res R)[u1] /in x. Then (TCol /res R)[u1] /in (TCol /res R)^[sset(R,y2)].
    Take a zfset u2  such that u2 /in sset(R,y2) /\ (TCol /res R)[u1] = (TCol /res R)[u2].
    Then (TCol /res R)[u1] /notin A.
    Then u1 = u2.
    Proof by contradiction. Assume the contrary. Then u1 /neq u2.
      Let w = (TCol /res R)[u1]. w /notin A. w /in ran(TCol /res R) /\ exists y,z (y /neq z /\ y,z /in reldomain(R) /\ (TCol /res R)[y] = (TCol /res R)[u1] /\ (TCol /res R)[z] = (TCol /res R)[u1]). 
      Then w /in A. Contradiction.
    end.
  end.
  Forall u1 /in sset(R,y2) (u1 /in sset(R,y1)).
  Proof.
    Let u1 /in sset(R,y2). (TCol /res R)[y2] = (TCol /res R)^[sset(R,y2)]. Then (TCol /res R)[u1] /in x. Then (TCol /res R)[u1] /in (TCol /res R)^[sset(R,y1)].
    Take a zfset u2  such that u2 /in sset(R,y1) /\ (TCol /res R)[u1] = (TCol /res R)[u2].
    Then (TCol /res R)[u1] /notin A.
    Then u1 = u2.
    Proof by contradiction. Assume the contrary. Then u1 /neq u2.
      Let w = (TCol /res R)[u1]. w /notin A. w /in ran(TCol /res R) /\ exists y,z (y /neq z /\ y,z /in reldomain(R) /\ (TCol /res R)[y] = (TCol /res R)[u1] /\ (TCol /res R)[z] = (TCol /res R)[u1]). 
      Then w /in A. Contradiction.
    end.
  end.
  sset(R,y1) = sset(R,y2). Then y1 = y2. Contradiction.
end.
qed.


Lemma. Let R be a strongly wellfounded relation. Let R be extensional. Then forall x,y /in reldomain(R) ( x - R - y iff (TCol /res R)[x] /in (TCol /res R)[y]).
Proof.
Let x,y /in reldomain(R). 
x - R - y => (TCol /res R)[x] /in (TCol /res R)[y].
Proof.
  Let x - R - y. (TCol /res R)[y] = (TCol /res R)^[sset(R,y)].
end.
(TCol /res R)[x] /in (TCol /res R)[y] => x - R - y.
Proof.
  Let (TCol /res R)[x] /in (TCol /res R)[y]. (TCol /res R)[y] = (TCol /res R)^[sset(R,y)].
  Take a set z such that z /in sset(R,y) /\ (TCol /res R)[x] = (TCol /res R)[z].
  (TCol /res R) is injective. 
  Then forall a,b /in reldomain(R) ((TCol /res R)[a] = (TCol /res R)[b] => a = b).
  (TCol /res R)[x] = (TCol /res R)[z]. Then x = z. Then x - R - y.
end.
qed.



Lemma. Let R be a strong wellorder. Let reldomain(R) /in /VV. Then ran(TCol /res R) /in /Ord.
Proof.
Trans(ran(TCol /res R)).
ran(TCol /res R) /in /VV.
Proof.
  ran(TCol /res R) = (TCol /res R)^[reldomain(R)].
end.

Forall x /in ran(TCol /res R) Trans(x).
Proof.
  Let x /in ran(TCol /res R). Take a set y such that y /in reldomain(R)  /\ x = (TCol /res R)[y].
  Let x1 /in x. Then x1 /in (TCol /res R)^[sset(R,y)]. Take a set y1 such that y1 /in sset(R,y) /\ x1 = (TCol /res R)[y1].
  Let x2 /in x1. Then x2 /in (TCol /res R)^[sset(R,y1)]. Take a set y2 such that y2 /in sset(R,y1) /\ x2 = (TCol /res R)[y2].
  Then y2 /in sset(R,y).
  x = (TCol /res R)^[sset(R,y)].
  Then (TCol /res R)[y2] /in x.
  Then x2 /in x.
end.

qed.

Lemma. Let R be a strong wellorder. Let reldomain(R) be a proper class. Then ran(TCol /res R) = /Ord.
Proof.
Trans(ran(TCol /res R)).

Forall x /in ran(TCol /res R) Trans(x).
Proof.
  Let x /in ran(TCol /res R). Take a set y such that y /in reldomain(R)  /\ x = (TCol /res R)[y].
  Let x1 /in x. Then x1 /in (TCol /res R)^[sset(R,y)]. Take a set y1 such that y1 /in sset(R,y) /\ x1 = (TCol /res R)[y1].
  Let x2 /in x1. Then x2 /in (TCol /res R)^[sset(R,y1)]. Take a set y2 such that y2 /in sset(R,y1) /\ x2 = (TCol /res R)[y2].
  Then y2 /in sset(R,y).
  x = (TCol /res R)^[sset(R,y)].
  Then (TCol /res R)[y2] /in x.
  Then x2 /in x.
end.

Then ran(TCol /res R) /subset /Ord.
Let alpha /in /Ord. Then alpha /in ran(TCol /res R).
Proof by contradiction. Assume the contrary. Then alpha /notin ran(TCol /res R).
  Then forall beta /in /Ord (alpha /in beta => beta /notin ran(TCol /res R)).
  Forall a,b /in /Ord (a /in b \/ b /in a \/ a = b).
  Forall a /in /Ord (a /in ran(TCol /res R) => alpha /notin a /\ alpha /neq a).
  Then ran(TCol /res R) /subset alpha.
  Then ran(TCol /res R) /in /VV.
  (TCol /res R) is injective.
  Then (TCol /res R) : reldomain(R) /leftrightarrow ran(TCol /res R).
  Then (TCol /res R)^{-1} : ran(TCol /res R) /leftrightarrow reldomain(R).
  Then reldomain(R) = ((TCol /res R)^{-1})^[ran(TCol /res R)].
  Then reldomain(R) /in /VV.
  Contradiction.
end.

qed.



# Order-type


Definition. Let R be a strong wellorder. The relordertype of R is ran(TCol /res R).
Let relotp(R) stand for the relordertype of R.

Lemma. Let R be a strong wellorder. Then relotp(R) /in /Ord \/ relotp(R) = /Ord.

Definition. Let x be a zfset. Let x /subset /Ord. The ordertype of x is ran(TCol /res epsrest(x)).
Let otp(x) stand for the ordertype of x.

Lemma. Let x be a zfset. Let x /subset /Ord. Then otp(x) /in /Ord.


Lemma. Let alpha be an ordinal. Let x /subset alpha. Then otp(x) /subset alpha.
Proof.
x /subset /Ord.
Forall y /in x (TCol /res epsrest(x))[y] /subset y.
Proof. 
  Define phi[n] = 
    Case (TCol /res epsrest(x))[n] /subset n -> 0,
    Case (TCol /res epsrest(x))[n] /notin /PP n -> 1
  for n in x.

  Forall y /in x ((forall z /in sset(epsrest(x),y) phi[z] = 0) => phi[y] = 0).
  Proof.
    Let y /in x. Let forall z /in sset(epsrest(x),y) phi[z] = 0.
    (TCol /res epsrest(x))[y] = (TCol /res epsrest(x))^[sset(epsrest(x),y)].
    Then (TCol /res epsrest(x))[y] /subset y.
    Proof.
      Let y1 /in (TCol /res epsrest(x))[y]. Take a set z1 such that z1 /in sset(epsrest(x),y) /\ y1 = (TCol /res epsrest(x))[z1].
      Then y1 /subset z1 /\ z1 /in y.
      y /in /Ord.
      ran(TCol /res epsrest(x)) /subset /Ord.
      y1 = (TCol /res epsrest(x))[z1].
      Then y1 /in /Ord.
      Proof.
        ran(TCol /res epsrest(x)) /subset /Ord.
      end.
      Forall a,b /in /Ord (a /in b \/ b /in a \/ a = b).
      Then y1 /in y \/ y /in y1 \/ y = y1.
      y1 /in y.
      Proof.
        Case y1 /in y. end.
        Case y /in y1. Then y /in z1. Then y /in y. Contradiction. end.
        Case y = y1. Then y /subset z1. Then z1 /in z1. Contradiction. end.
      end.
    end.
  end.
  
  Define M = {zfset z | z /in x /\ phi[z] = 0}.
  Then M /subset x.
  Let N = x /setminus M.
  Then N /neq /emptyset \/ N = /emptyset.
  Case N = /emptyset. Then x /subset M. M /subset x. Then x = M. end.
  Case N /neq /emptyset.
  Take a zfset a such that (a /in N /\ (forall y /in a y /notin N)).
  Forall y /in sset(epsrest(x),a) y /in a.
  Then forall y /in sset(epsrest(x),a) phi[y] = 0.
  Then phi[a] = 0.
  Contradiction. end.  
  
end.

Then ran(TCol /res epsrest(x)) /subset alpha.
Proof.
  Let y /in ran(TCol /res epsrest(x)). Take a set z such that z /in x /\ y = (TCol /res epsrest(x))[z].
  Then y /subset z.
  z /in alpha.
  y, alpha /in /Ord.
  Then y /in alpha \/ alpha /in y \/ alpha = y.
  Then y /in alpha.
  Proof.
    Case y /in alpha. end.
    Case alpha = y. Then alpha /subset z /\ z /in alpha. Contradiction. end.
    Case alpha /in y. Then alpha /in z. z /in alpha. Contradiction. end.
  end.
end.

qed.







Lemma. Let A, B be transitive. Let f be a zffunction. Let f : A /leftrightarrow B. Let forall x, y /in A (x /in y iff f[x] /in f[y]). Then A = B and forall x /in A f[x] = x.
Proof.
Define phi[n] =
  Case f[n] = n -> 0,
  Case f[n] /neq n -> 1
for n in A.

Forall x /in A ((forall y /in x phi[y] = 0) => phi[x] = 0).
Proof.
  Let x /in A. Let forall y /in x phi[y] = 0.
  Forall y /in x (f[y] /in f[x] /\ f[y] = y).
  Then x /subset f[x].
  Then f[x] /subset x.
  Proof.
    Let y /in f[x]. Then y /in ran(f). Take a set z such that z /in A /\ y = f[z].
    Then f[z] /in f[x]. Then z /in x. Then f[z] = z. Then y = z. Then y /in x.
  end.
  Then f[x] = x.
  Then phi[x] = 0.
end.

Forall x /in A f[x] = x.
Proof.
  Define M = {zfset z | z /in A /\ phi[z] = 0}.
  Then M /subset A.
  Let N = A /setminus M.
  Then N /neq /emptyset \/ N = /emptyset.
  Case N = /emptyset. Then A /subset M. M /subset A. Then A = M. end.
  Case N /neq /emptyset.
  Take a zfset a such that (a /in N /\ (forall y /in a y /notin N)).
  Then forall y /in a phi[y] = 0.
  Then phi[a] = 0.
  Contradiction. end.
end.

A /subset B.
B /subset A.
Proof.
  Let x /in B. Take y such that y /in A /\ f[y] = x. Then x = y. Then x /in A.
end.
A = B.
  
qed.











Lemma. Contradiction.
