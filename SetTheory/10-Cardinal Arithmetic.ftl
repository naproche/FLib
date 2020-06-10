# 10-Cardinal Arithmetic

# Here we introduce cardinal arithmetic. To distinguish this from ordinal arithmetic we write +3, *3, ^3 instead of +,*,^.
# We added an axiom that a zffunction with domain in /VV is a zfset, which can be proven if we used the set theoretic implementation of functions,
# where functions are just certain classes of ordered pairs. Since we used the implemented functions, this needs to be an axiom.
# Then we proved that for given zfsets A,B the class of zffunctions from A to B is a zfsets.
# For this we did not need any more axioms, this follows directly from replacement for a nice function.
# Then we proved some important calculation rules for cardinal arithmetic and concluded the first results about the size of the power set, which is one of the main questions of set theory.

# Main results:

# - forall zfsets A,B ^{A}B is a zfset.
# - some calculation rules, the most interesting beeing a^(b+c) = a^b * a^c and (a^b)^c = a^(b*c)
# - forall infinite kappa (kappa = kappa * kappa).
# - forall lambda between 2 and 2^kappa (2^kappa = lambda^kappa).






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

# New Axiom
Axiom. Let f be a zffunction. Let Dom(f) /in /VV. Then f is a zfset.






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
# New
Signature. 2 is an ordinal.

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
# New
Axiom. 2 = 1 + 1.

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

Let kappa, lambda stand for a cardinal.

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

Axiom. Forall x,y /in /VV (x /times y /in /VV).
Axiom. Forall a,b /in /NN ((a /times b is a zfset) and (Card(a /times b) = a * b)).
Axiom. Let a1,a2,b1,b2 be zfsets. Let Card(a1) = Card(a2) /\ Card(b1) = Card(b2).
Then (a1 /times b1) /tilde (a2 /times b2).


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



# Goedel Ordering

Axiom. Forall alpha /in /Ord (Alef[alpha] /tilde Alef[alpha] /times Alef[alpha]).
Axiom. Forall x /in /VV (Card(x) /notin /NN => x /tilde x /times x).




# Cardinal Arithmetic


Lemma. Let A,B /in /VV. Then ^{A}B /in /VV.
Proof.
Forall f /in ^{A}B (f : A /rightarrow B).
Let M = /PP (A /times B).
Define inc[f] = {(a,f[a]) | a /in A} for f in ^{A}B.
Then inc is a zffunction.
Proof.
  Let f /in ^{A}B.
  Then forall a /in A (a,f[a]) /in /VV.
  Define g[a] = (a,f[a]) for a in A.
  Then g is a zffunction.
  inc[f] /subset g^[A].
  Proof.
    Let x /in inc[f]. Take a zfset a such that a /in A /\ x = (a,f[a]).
    Then x /in g^[A].
  end.
  Then inc[f] /in /VV.
end.
Then inc : ^{A}B /rightarrow M.
Proof.
  Let f /in ^{A}B.
  Then forall a /in A (a,f[a]) /in /VV.
  Define g[a] = (a,f[a]) for a in A.
  Then g is a zffunction.
  inc[f] /subset g^[A].
  Proof.
    Let x /in inc[f]. Take a zfset a such that a /in A /\ x = (a,f[a]).
    Then x /in g^[A].
  end.
  g^[A] /subset A /times B.
  Proof.   
    Let x /in g^[A]. Take a zfset a such that a /in A /\ x = g[a].
    Then x = (a,f[a]).
    f : A /rightarrow B.
    f[a] /in B.
    Then x /in A /times B.
  end.
  Then inc[f] /subset A /times B.
  Then inc[f] /in M.
end.

inc is injective.
Proof.
  Let f,g /in ^{A}B. Let f /neq g. Then inc[f] /neq inc[g].
  Proof.
    Dom(f) = Dom(g).
    Exists a /in A (f[a] /neq g[a]).
    Proof by contradiction. Assume the contrary.
      f,g are functions.
      Forall a /in Dom(f) (f[a] = g[a]).
      Then f = g.
      Contradiction.
    end.
    Take a zfset a such that a /in A /\ f[a] /neq g[a].
    Then (a,f[a]) /in inc[f].
    (a,f[a]) /notin inc[g].
    Proof by contradiction. Assume the contrary.
      Then (a,f[a]) /in inc[g].
      Take a zfset b such that b /in A /\ (a,f[a]) = (b,g[b]).
      Take zfsets c1,c2 such that c1 = f[a] /\ c2 = g[b].
      Then (a,c1) = (b,c2).
      Then a = b /\ c1 = c2.
      Contradiction.
    end.
    Then inc[f] /neq inc[g].
  end.
end.

Then inc : ^{A}B /leftrightarrow ran(inc).
Then inc^{-1} : ran(inc) /leftrightarrow ^{A}B.
ran(inc) /subset M.
M /in /VV.
Then ran(inc) /in /VV.

^{A}B = (inc^{-1})^ [ran(inc)].
Then ^{A}B /in /VV.

qed.



Signature. kappa +3 lambda is a cardinal.
Signature. kappa *3 lambda is a cardinal.
Signature. kappa ^3 lambda is a cardinal.

Definition. Let kappa, lambda /in /Card. Let x,y /in /VV. (kappa, lambda) ispairequipotentto (x, y) iff (Card(x) = kappa /\ Card(y) = lambda /\ x /cap y = /emptyset).
Let (a,b) /sim (x, y) stand for (a,b) ispairequipotentto (x, y).

# The Definition of cardinal addition needs too many assumptions. It helps to collect all of them in a new syntax.

Axiom. Let kappa, lambda /in /Card. Let x,y /in /VV. Let (kappa,lambda) /sim (x, y).
Then kappa +3 lambda = Card(x /cup y).

Axiom. Let kappa, lambda /in /Card. Let x,y /in /VV. Let Card(x) = kappa. Let Card(y) = lambda. Let x /cap y = /emptyset.
Then kappa +3 lambda = Card(x /cup y).

Axiom. Let kappa, lambda /in /Card. Then kappa *3 lambda = Card(kappa /times lambda).

Axiom. Let kappa, lambda /in /Card. Then kappa ^3 lambda = Card(^{lambda}kappa).

Lemma. Forall n /in /NN (n + 1 = n +3 1).
Proof.
  Let n /in /NN.
  Let y = <n>.
  Card(n) = n.
  Card(y) = 1.
  Proof.
    Define f[x] = n for x in 1.
    Then f : 1 /leftrightarrow y.
  end.
  n /cap y = /emptyset.
  Then (n,1) /sim (n,y).
  Then n +3 1 = Card(n /cup y).
  n /cup y = n+1.
end.




Lemma. Let alpha, beta, gamma /in /Card. Then alpha *3 (beta +3 gamma) = (alpha *3 beta) +3 (alpha *3 gamma).
Proof.
alpha *3 (beta +3 gamma) = Card( alpha /times (beta +3 gamma)).
Take zfsets xx,yy such that Card(xx) = beta /\ Card(yy) = gamma.
Define x = {(z,0) | z /in xx}.
Define y = {(z,1) | z /in yy}.
(x is a zfset) /\ x /tilde xx.
Proof.
  Define f[z] = (z,0) for z in xx.
  f is a zffunction.
  Proof.
    Let z /in xx. Then f[z] /in /VV.
  end.
  Then f : xx /rightarrow x.
  f is injective.
  Proof.
    Let z1,z2 /in xx. Let z1 /neq z2.
    Then f[z1] /neq f[z2].
  end.
  ran(f) = x.
  Then x = f^[xx].
  Then x /in /VV.
  f : xx /leftrightarrow x.
end.

(y is a zfset) /\ y /tilde yy.
Proof.
  Define f[z] = (z,1) for z in yy.
  f is a zffunction.
  Proof.
    Let z /in yy. Then f[z] /in /VV.
  end.
  Then f : yy /rightarrow y.
  f is injective.
  Proof.
    Let z1,z2 /in yy. Let z1 /neq z2.
    Then f[z1] /neq f[z2].
  end.
  ran(f) = y.
  Then y = f^[yy].
  Then y /in /VV.
  f : yy /leftrightarrow y.
end.

x /cap y = /emptyset /\ Card(x) = beta /\ Card(y) = gamma.
Then (beta,gamma) /sim (x,y).
Then beta +3 gamma = Card(x /cup y).
Then alpha *3 (beta +3 gamma) = Card( alpha /times Card(x /cup y)).
alpha /times (x /cup y) /tilde Card(alpha) /times Card(x /cup y).
Then alpha *3 (beta +3 gamma) = Card(alpha /times (x /cup y)).

alpha /times (x /cup y) = (alpha /times x) /cup (alpha /times y).

(alpha /times x) /cap (alpha /times y) = /emptyset.
Proof by contradiction. Assume the contrary.
  Take a set pair such that pair /in (alpha /times x) /cap (alpha /times y).
  pair /in alpha /times x.
  Take sets a1,b1 such that a1 /in alpha /\ b1 /in x /\ pair = (a1,b1).
  pair /in alpha /times y.
  Take sets a2,b2 such that a2 /in alpha /\ b2 /in y /\ pair = (a2,b2).
  Then (a1,b1) = (a2,b2).
  Then b1 = b2.
  Then b1 /in x /cap y.
  Contradiction.
end.
(alpha /times x) /tilde (alpha /times beta).
Then (alpha *3 beta) = Card(alpha /times x).
(alpha /times y) /tilde (alpha /times gamma).
Then (alpha *3 gamma) = Card(alpha /times y).
Then ((alpha *3 beta), (alpha *3 gamma)) /sim ((alpha /times x), (alpha /times y)).

Then (alpha *3 beta) +3 (alpha *3 gamma) = Card((alpha /times x) /cup (alpha /times y)).

qed.


Lemma. Forall kappa /in /Card (kappa ^3 0 = 1).
Proof.
Let kappa /in /Card.
Forall f,g /in ^{0}kappa (f = g).
Define f[n] = 0 for n in 0.
Then f : 0 /rightarrow kappa.
f is a zffunction.
Then f /in ^{0}kappa.
Then ^{0}kappa = {f}.
Then ^{0}kappa /tilde 1.
Proof.
  Define g[n] = f for n in 1.
  Then g is a zffunction.
  g : 1 /leftrightarrow ^{0}kappa.
end.
qed.


Lemma. Forall kappa /in /Card (kappa /neq 0 => 0 ^3 kappa = 0).
Proof.
Let kappa /in /Card. Let kappa /neq 0.
Then ^{kappa}0 = /emptyset.
qed.

Lemma. Forall kappa /in /Card (kappa ^3 1 = kappa).
Proof.
Let kappa /in /Card.
Forall g /in ^{1}kappa 0 /in Dom(g).
Define f[g] = g[0] for g in ^{1}kappa.
f is a zffunction.
Proof.
  Let g /in Dom(f).
  Then g[0] /in /VV.
  Then f[g] /in /VV.
end.
Then f : ^{1}kappa /rightarrow kappa.
Proof.
  Let g /in ^{1}kappa.
  0 /in Dom(g).
  Then g[0] /in kappa.
  Then f[g] /in kappa.
end.
f is injective.
Proof.
  Let g1,g2 /in ^{1}kappa.
  Let f[g1] = f[g2].
  g1,g2 are functions.
  Dom(g1) = Dom(g2).
  Forall x /in Dom(g1) (g1[x] = g2[x]).
  Then g1 = g2.
end.
ran(f) = kappa.
Proof.
  Let x /in kappa.
  Define g[n] = x for n in 1.
  Then g /in ^{1}kappa.
  f[g] = x.
  Then x /in ran(f).
end.
Then f : ^{1}kappa /leftrightarrow kappa.
qed.


Lemma. Forall kappa /in /Card (1 ^3 kappa = 1).
Proof.
Let kappa /in /Card.
Forall f,g /in ^{kappa}1 (f = g).
Proof.
  Let f,g /in ^{kappa}1.
  Then f,g are functions.
  Dom(f) = Dom(g).
  Forall x /in kappa f[x] = 0.
  Forall x /in kappa g[x] = 0.
  Then forall x /in Dom(f) f[x] = g[x].
  Then f = g.
end.
Define f[n] = 0 for n in kappa.
Then f : kappa /rightarrow 1.
f is a zffunction.
Then f /in ^{kappa}1.
Then ^{kappa}1 = {f}.
Then ^{kappa}1 /tilde 1.
Proof.
  Define g[n] = f for n in 1.
  Then g is a zffunction.
  g : 1 /leftrightarrow ^{kappa}1.
end.
qed.


Lemma. Forall x1,x2,y1,y2 /in /VV ( x1 /tilde x2 /\ y1 /tilde y2 => ^{x1}y1 /tilde ^{x2}y2).
Proof.

Forall x1,x2,y1,y2 /in /VV ( x1 /tilde x2 /\ y1 /tilde y2 => ^{x1}y1 <= ^{x2}y2).
Proof.
  Let x1,x2,y1,y2 /in /VV.
  Let x1 /tilde x2.
  Let y1 /tilde y2.
  Take a zffunction f such that f : x2 /leftrightarrow x1.
  Take a zffunction g such that g : y1 /leftrightarrow y2.

  Forall h /in ^{x1}y1 (h /circ f : x2 /rightarrow y1).
  Define bij[h] = g /circ (h /circ f) for h in ^{x1}y1.
  Then bij is a zffunction.
  Proof.
    Let h /in ^{x1}y1. Then h /circ f is a zffunction.
    Then g /circ (h /circ f) is a zffunction.
    Dom(g /circ (h /circ f)) /in /VV.
    Then bij[h] /in /VV.
  end.
  bij : ^{x1}y1 /rightarrow ^{x2}y2.
  Proof.
    Let h /in ^{x1}y1.
    Then h /circ f : x2 /rightarrow y1.
    Then g /circ (h /circ f) : x2 /rightarrow y2.
    g /circ (h /circ f) is a zffunction.
    Then bij[h] /in ^{x2}y2.
  end.

  bij is injective.
  Proof.
    Let h1,h2 /in ^{x1}y1.
    Let h1 /neq h2.
    Then exists a /in x1 (h1[a] /neq h2[a]).
    Proof by contradiction. Assume the contrary.
      h1,h2 are functions.
      Dom(h1) = Dom(h2).
      Forall a /in Dom(h1) h1[a] = h2[a].
      Then h1 = h2.
      Contradiction.
    end.
    Take a zfset a such that a /in x1 /\ h1[a] /neq h2[a].
    Take a zfset b such that b /in x2 /\ f[b] = a.
    Then (h1 /circ f)[b] /neq (h2 /circ f)[b].
    g is injective. 
    Then (g /circ (h1 /circ f))[b] /neq (g /circ (h2 /circ f))[b].
    Then (g /circ (h1 /circ f)) /neq (g /circ (h2 /circ f)).
    Then bij[h1] /neq bij[h2].
  end.
  
  Then ^{x1}y1 <= ^{x2}y2.
end.

Let x1,x2,y1,y2 /in /VV.
Let x1 /tilde x2.
Let y1 /tilde y2.

Then ^{x1}y1 <= ^{x2}y2.
Then ^{x2}y2 <= ^{x1}y1.
Then ^{x1}y1 /tilde ^{x2}y2.

qed.



Lemma. Let alpha, beta, gamma /in /Card. Then (alpha ^3 (beta +3 gamma) = (alpha ^3 beta) *3 (alpha ^3 gamma)).
Proof.
Take zfsets xx,yy such that Card(xx) = beta /\ Card(yy) = gamma.
Define x = {(z,0) | z /in xx}.
Define y = {(z,1) | z /in yy}.
(x is a zfset) /\ x /tilde xx.
Proof.
  Define f[z] = (z,0) for z in xx.
  f is a zffunction.
  Proof.
    Let z /in xx. Then f[z] /in /VV.
  end.
  Then f : xx /rightarrow x.
  f is injective.
  Proof.
    Let z1,z2 /in xx. Let z1 /neq z2.
    Then f[z1] /neq f[z2].
  end.
  ran(f) = x.
  Then x = f^[xx].
  Then x /in /VV.
  f : xx /leftrightarrow x.
end.

(y is a zfset) /\ y /tilde yy.
Proof.
  Define f[z] = (z,1) for z in yy.
  f is a zffunction.
  Proof.
    Let z /in yy. Then f[z] /in /VV.
  end.
  Then f : yy /rightarrow y.
  f is injective.
  Proof.
    Let z1,z2 /in yy. Let z1 /neq z2.
    Then f[z1] /neq f[z2].
  end.
  ran(f) = y.
  Then y = f^[yy].
  Then y /in /VV.
  f : yy /leftrightarrow y.
end.

x /cap y = /emptyset /\ Card(x) = beta /\ Card(y) = gamma.
Then (beta,gamma) /sim (x,y).
beta +3 gamma /tilde x /cup y.
Then ^{beta +3 gamma}alpha /tilde ^{x /cup y}alpha.

^{x /cup y}alpha /tilde ^{x}alpha /times ^{y}alpha.
Proof.
  Define phi[f] = (f /upharpoonright x, f /upharpoonright y) for f in ^{x /cup y}alpha.
  Then phi : ^{x /cup y}alpha /rightarrow ^{x}alpha /times ^{y}alpha.
  Proof.
    Dom(phi) = ^{x /cup y}alpha.
    phi is a zffunction.
    Proof.
      Let f /in ^{x /cup y}alpha.
      Then f /upharpoonright x /in /VV.
      Proof.
        Let z /in x. Then (f /upharpoonright x)[z] /in /VV.
        Then f /upharpoonright x is a zffunction.
        Dom(f /upharpoonright x) = x.
        Then Dom(f /upharpoonright x) /in /VV.
      end.
      f /upharpoonright y /in /VV.
      Proof.
        Let z /in y. Then (f /upharpoonright y)[z] /in /VV.
        Then f /upharpoonright y is a zffunction.
        Dom(f /upharpoonright y) = y.
        Then Dom(f /upharpoonright y) /in /VV.
      end.
      Then phi[f] /in /VV.
    end.
    ran(phi) /subset ^{x}alpha /times ^{y}alpha.
    Proof.
      Let f /in ^{x /cup y}alpha.
      Then f /upharpoonright x /in ^{x}alpha.
      Proof.
        Dom(f /upharpoonright x) = x.
        Forall z /in x (f /upharpoonright x)[z] = f[z].
        f : x /cup y /rightarrow alpha.
        Forall z /in x f[z] /in alpha.
        Then forall z /in x (f /upharpoonright x)[z] /in alpha.
        Then ran(f /upharpoonright x) /subset alpha.
      end.
      Then f /upharpoonright y /in ^{y}alpha.
      Proof.
        Dom(f /upharpoonright y) = y.
        Forall z /in y (f /upharpoonright y)[z] = f[z].
        f : x /cup y /rightarrow alpha.
        Forall z /in y f[z] /in alpha.
        Then forall z /in y (f /upharpoonright y)[z] /in alpha.
        Then ran(f /upharpoonright y) /subset alpha.
      end.
      Then phi[f] /in ^{x}alpha /times ^{y}alpha.
    end.
  end.
  
  Forall f, g /in ^{x /cup y}alpha (f /neq g => phi[f] /neq phi[g]).
  Proof.
    Let f,g /in ^{x /cup y}alpha. Let f /neq g.
    Then exists z /in x /cup y (f[z] /neq g[z]).
    Proof by contradiction. Assume the contrary.
      f,g are functions.
      Dom(f) = Dom(g).
      Forall z /in Dom(f) f[z] = g[z].
      Then f = g.
      Contradiction.
    end.
    Take a zfset z such that z /in x /cup y /\ f[z] /neq g[z].
    Take zfsets a1,b1 such that a1 = (f /upharpoonright x) /\ b1 = (f /upharpoonright y).
    Take zfsets a2,b2 such that a2 = (g /upharpoonright x) /\ b2 = (g /upharpoonright y).
    Then phi[f] = (a1,b1).
    Then phi[g] = (a2,b2).     
    Then phi[f] /neq phi[g].
    Proof.
      Case z /in x.
        Then (f /upharpoonright x)[z] /neq (g /upharpoonright x)[z].
        Then (f /upharpoonright x) /neq (g /upharpoonright x).
        Then (f /upharpoonright x) /neq (g /upharpoonright x).
        Then a1 /neq a2. 
        Then (a1,b1) /neq (a2,b2).
      end.
      Case z /in y. Then (f /upharpoonright y) /neq (g /upharpoonright y).
        Then b1 /neq b2. 
        Then (a1,b1) /neq (a2,b2).
      end.
    end.
  end.
  Then phi is injective.
  
  ran(phi) = ^{x}alpha /times ^{y}alpha.
  Proof.
    Let pair /in ^{x}alpha /times ^{y}alpha.
    Take a set A such that A = ^{x}alpha.
    Take a set B such that B = ^{y}alpha.
    Then pair /in A /times B.
    Take zfsets f1,f2 such that f1 /in A /\ f2 /in B /\ pair = (f1,f2).
    Then f1 : x /rightarrow alpha.
    Then f2 : y /rightarrow alpha.
    Define f[n] =
      Case n /in x -> f1[n],
      Case n /in y -> f2[n]
    for n in x /cup y.
    Then f : x /cup y /rightarrow alpha.
    Proof.
      f is a zffunction.
      Proof.
        let z /in x /cup y. Then f[z] /in /VV.
      end.
      ran(f) /subset alpha.
      Proof.
        Let z /in x /cup y. Then f[z] /in alpha.
        Proof.
          Case z /in x. end.
          Case z /in y. end.
        end.
      end.
    end.
    
    f /upharpoonright x = f1.
    Proof.
      f1,(f /upharpoonright x) are functions.
      Dom(f1) = Dom(f /upharpoonright x).
      Forall z /in Dom(f1) f1[z] = (f /upharpoonright x)[z].
    end.  
    f /upharpoonright y = f2.
    Proof.
      f2,(f /upharpoonright y) are functions.
      Dom(f2) = Dom(f /upharpoonright y).
      Forall z /in Dom(f2) f2[z] = (f /upharpoonright y)[z].
    end.   
    Then phi[f] = (f1,f2).
    Then pair /in ran(phi).
  end.
  
  Then phi : ^{x /cup y}alpha /leftrightarrow ^{x}alpha /times ^{y}alpha.
end.

^{beta +3 gamma}alpha /tilde ^{x}alpha /times ^{y}alpha.
Proof.
  Take zfsets A,B,C such that A = ^{beta +3 gamma}alpha /\ B = ^{x /cup y}alpha /\ C = ^{x}alpha /times ^{y}alpha.
  ^{beta +3 gamma}alpha /tilde ^{x /cup y}alpha.
  ^{x /cup y}alpha /tilde ^{x}alpha /times ^{y}alpha.
  Then A /tilde B /\ B /tilde C.
  Then A /tilde C.
end.

x /tilde beta.
Then ^{x}alpha /tilde ^{beta}alpha.
Then alpha ^3 beta = Card(^{x}alpha).

y /tilde gamma.
Then ^{y}alpha /tilde ^{gamma}alpha.
Then alpha ^3 gamma = Card(^{y}alpha).

(alpha ^3 beta) *3 (alpha ^3 gamma) = Card(Card(^{x}alpha) /times Card(^{y}alpha)).
Card(^{x}alpha) /times Card(^{y}alpha) /tilde ^{x}alpha /times ^{y}alpha.
Then (alpha ^3 beta) *3 (alpha ^3 gamma) /tilde ^{x}alpha /times ^{y}alpha.
^{x}alpha /times ^{y}alpha /tilde (alpha ^3 beta) *3 (alpha ^3 gamma).

Then (alpha ^3 (beta +3 gamma) /tilde (alpha ^3 beta) *3 (alpha ^3 gamma)).
Proof.
  Forall A,B,C /in /VV (A /tilde B /\ B /tilde C => A /tilde C).
  Take a zfset A such that A = (alpha ^3 (beta +3 gamma)).
  Take a zfset B such that B = ^{x}alpha /times ^{y}alpha.
  Take a zfset C such that C = (alpha ^3 beta) *3 (alpha ^3 gamma).
  Then A /tilde B /\ B /tilde C.
  Then A /tilde C.
end.

qed.


Definition. Let alpha, beta, gamma /in /VV. Let f /in ^{beta /times gamma}alpha. Let F be a zffunction.
F /partial (f,alpha,beta,gamma) iff (Dom(F) = gamma /\ forall b /in gamma ((F[b] is a zffunction) /\ Dom(F[b]) = beta /\ forall a /in beta (F[b])[a] = f[(a,b)])).

Lemma. Let alpha, beta, gamma /in /VV. Let f /in ^{beta /times gamma}alpha. Let F be a zffunction. Let F /partial (f,alpha,beta,gamma).
Then F /in ^{gamma}(^{beta}alpha).
Proof.
Forall b /in gamma F[b] /in ^{beta}alpha.
Proof.
  Let b /in gamma.
  Then (F[b] is a zffunction) /\ Dom(F[b]) = beta.
  ran(F[b]) /subset alpha.
  Proof.
    Let a /in beta.
    Then f[(a,b)] /in alpha.
    Then (F[b])[a] /in alpha.
  end.
end.
qed.



Lemma. Let alpha, beta, gamma /in /Card. Then (alpha ^3 (beta *3 gamma) = (alpha ^3 beta) ^3 gamma).
Proof.
Forall f /in ^{beta /times gamma}alpha forall a /in beta forall b /in gamma (a,b) /in Dom(f).
Forall f /in ^{beta /times gamma}alpha exists F (F /partial (f,alpha,beta,gamma)).
Proof.
  Let f /in ^{beta /times gamma}alpha.
  Forall b /in gamma exists g ( Dom(g) = beta /\ forall a /in beta g[a] = f[(a,b)]).
  Proof.
    Let b /in gamma.
    Define g[a] = f[(a,b)] for a in beta.
    Then Dom(g) = beta.
    g is a zffunction.
    Proof.
      Let a /in beta. Then g[a] /in /VV.
    end.
    Forall a /in beta g[a] = f[(a,b)].
  end.
  Define F[b] = (Choose a zffunction g such that ( Dom(g) = beta /\ forall a /in beta g[a] = f[(a,b)]) in g) for b in gamma.
  Then F is a zffunction.
  Proof.
    Let b /in gamma.
    Then F[b] is a zffunction.
    Dom(F[b]) /in /VV.
    Then F[b] /in /VV.
  end.
  Dom(F) = gamma.
  Forall b /in gamma ((F[b] is a zffunction) /\ Dom(F[b]) = beta /\ forall a /in beta (F[b])[a] = f[(a,b)]).
  Then F /partial (f,alpha,beta,gamma).
end.
Define phi[f] = (Choose a zffunction F such that (F /partial (f,alpha,beta,gamma)) in F) for f in ^{beta /times gamma}alpha.

phi is a zffunction.
Proof.
  Let f /in ^{beta /times gamma}alpha.
  Then phi[f] is a zffunction.
  Dom(phi[f]) /in /VV.
  Then phi[f] /in /VV.
end.
phi : ^{beta /times gamma}alpha /rightarrow ^{gamma}(^{beta}alpha).
Proof.
  Let f /in ^{beta /times gamma}alpha.
  Then phi[f] is a zffunction.
  Take a zffunction F such that F = phi[f].
  Then F /partial (f,alpha,beta,gamma).
  Then F /in ^{gamma}(^{beta}alpha).
end.

phi is injective.
Proof.
  Let f1,f2 /in ^{beta /times gamma}alpha. Let f1 /neq f2.
  Then exists pair /in beta /times gamma (f1[pair] /neq f2[pair]).
  Proof by contradiction. Assume the contrary.
    f1,f2 are functions.
    Dom(f1) = Dom(f2).  
    Forall pair /in Dom(f1) f1[pair] = f2[pair].
    Then f1 = f2. 
    Contradiction.
  end.
  Take a zfset pair such that pair /in beta /times gamma /\ f1[pair] /neq f2[pair].
  Take zfsets a,b such that a /in beta /\ b /in gamma /\ pair = (a,b).
  Then phi[f1] /neq phi[f2].
end.

ran(phi) = ^{gamma}(^{beta}alpha).
Proof.
  Let F /in ^{gamma}(^{beta}alpha).
  Forall b /in gamma F[b] /in ^{beta}alpha.
  Forall pair /in beta /times gamma exists a,b /in /VV (a /in beta /\ b /in gamma /\ pair = (a,b)).
  Define f[pair] = (Choose zfsets a,b such that a /in beta /\ b /in gamma /\ pair = (a,b) in (F[b])[a]) for pair in beta /times gamma.
  Then f : beta /times gamma /rightarrow alpha.
  Proof.
    Let pair /in beta /times gamma.
    Take zfsets a,b such that a /in beta /\ b /in gamma /\ pair = (a,b) /\ f[pair] = (F[b])[a].
    Then F[b] /in ^{beta}alpha.
    Then (F[b])[a] /in alpha.
    Then f[pair] /in alpha.
  end.
  F /partial (f,alpha,beta,gamma).
  Proof.
    Dom(F) = gamma.
    Forall b /in gamma ((F[b] is a zffunction) /\ Dom(F[b]) = beta /\ forall a /in beta (F[b])[a] = f[(a,b)]).
    Proof.
      Let b /in gamma.
      Then F[b] is a zffunction.
      Dom(F[b]) = beta.
      Forall a /in beta (F[b])[a] = f[(a,b)].
      Proof.
        Let a /in beta.
        Then (a,b) /in beta /times gamma.
        Take zfsets aa,bb such that aa /in beta /\ bb /in gamma /\ (a,b) = (aa,bb) /\ f[(a,b)] = (F[bb])[aa].
        Then a = aa /\ b = bb.
        Then f[(a,b)] = (F[b])[a].
      end.
    end.
  end.
  Then phi[f] = F.
  Proof.
    Take a zffunction G such that G = phi[f].
    Then G /partial (f,alpha,beta,gamma).
    Then F = G.
    Proof.
      F,G are functions.
      Then (F = G iff Dom(F) = Dom(G) /\ forall val /in Dom(F) F[val] = G[val]).
      Dom(F) = Dom(G).
      Forall b /in gamma F[b] = G[b].
      Proof.
        Let b /in gamma.
        Then F[b] = G[b].
        Proof.
          F[b], G[b] are functions.
          Then (F[b] = G[b] iff Dom(F[b]) = Dom(G[b]) /\ forall val /in Dom(F[b]) F[b][val] = G[b][val]).
          Dom(F[b]) = beta /\ Dom(G[b]) = beta.
          Forall a /in beta (F[b])[a] = (G[b])[a].
          Proof.
            Let a /in beta.
            Then (F[b])[a] = f[(a,b)].
            (G[b])[a] = f[(a,b)].
          end.
        end.
      end.
    end.
  end.
  Then F /in ran(phi).
end.

Then phi : ^{beta /times gamma}alpha /leftrightarrow ^{gamma}(^{beta}alpha).

Then ^{beta /times gamma}alpha /tilde ^{gamma}(^{beta}alpha).

beta *3 gamma /tilde beta /times gamma.
alpha ^3 (beta *3 gamma) /tilde ^{beta *3 gamma}alpha.
Then alpha ^3 (beta *3 gamma) /tilde ^{beta /times gamma}alpha.
Proof.
  Take zfsets x1,x2 such that x1 = beta *3 gamma /\ x2 = beta /times gamma.
  Then ^{x1}alpha /tilde ^{x2}alpha.
  alpha ^3 (x1) /tilde ^{x1}alpha.
  Then alpha ^3 (x1) /tilde ^{x2}alpha.
end.

^{beta}alpha /tilde alpha ^3 beta.
Then ^{gamma}(^{beta}alpha) /tilde ^{gamma}(alpha ^3 beta).
^{gamma}(alpha ^3 beta) /tilde (alpha ^3 beta) ^3 gamma.
Then ^{gamma}(^{beta}alpha) /tilde (alpha ^3 beta) ^3 gamma.

Then (alpha ^3 (beta *3 gamma) = (alpha ^3 beta) ^3 gamma).
Proof.
  Take a zfset x1 such that x1 = (alpha ^3 (beta *3 gamma)).
  Take a zfset x2 such that x2 = ^{beta /times gamma}alpha.
  Take a zfset x3 such that x3 = ^{gamma}(^{beta}alpha).
  Take a zfset x4 such that x4 = (alpha ^3 beta) ^3 gamma.
  Then x1 /tilde x2 /\ x2 /tilde x3 /\ x3 /tilde x4.
  Then x1 /tilde x4.
end.

qed.













Lemma. Forall kappa /in /Card (/NN /subset kappa => kappa *3 kappa = kappa).
Proof.
Let kappa /in /Card. Let /NN /subset kappa.
Then kappa /tilde kappa /times kappa.
qed.


Lemma. Let kappa, lambda /in /Card. Let /NN /subset kappa. Let lambda /neq 0. Then kappa *3 lambda = kappa /cup lambda.
Proof.
Forall a,b /in /Ord (a /subset b \/ b /subset a).
kappa /subset lambda \/ lambda /subset kappa.
Case kappa /subset lambda.
  Then kappa /cup lambda = lambda.
  lambda <= kappa /times lambda.
  Proof.
    Define f[n] = (0,n) for n in lambda.
    Then f : lambda /rightarrow kappa /times lambda.
    Proof.
      Let n /in lambda. 0 /in kappa.
      Then (0,n) /in kappa /times lambda.
      Then f[n] /in kappa /times lambda.
    end.
    f is injective.
    Proof.
      Let m,n /in lambda.
      Let m /neq n.
      Then (0,m) /neq (0,n).
      Then f[m] /neq f[n].
    end.
  end.
  kappa /times lambda /subset lambda /times lambda.
  lambda /times lambda /tilde lambda.
  Then kappa /times lambda <= lambda.
  Then kappa *3 lambda = lambda.
end.
Case lambda /subset kappa.
  Then kappa /cup lambda = kappa.
  kappa <= kappa /times lambda.
  Proof.
    Define f[n] = (n,0) for n in kappa.
    Then f : kappa /rightarrow kappa /times lambda.
    Proof.
      Let n /in kappa. 0 /in lambda.
      Then (n,0) /in kappa /times lambda.
      Then f[n] /in kappa /times lambda.
    end.
    f is injective.
    Proof.
      Let m,n /in kappa.
      Let m /neq n.
      Then (m,0) /neq (n,0).
      Then f[m] /neq f[n].
    end.
  end.
  kappa /times lambda /subset kappa /times kappa.
  kappa /times kappa /tilde kappa.
  Then kappa /times lambda <= kappa.
  Then kappa *3 lambda = kappa.
end.
qed.




Lemma. Let kappa, lambda /in /Card. Let /NN /subset kappa. Then kappa +3 lambda = kappa /cup lambda.
Proof.
Define x = {(z,0) | z /in kappa}.
Define y = {(z,1) | z /in lambda}.
(x is a zfset) /\ x /tilde kappa.
Proof.
  Define f[z] = (z,0) for z in kappa.
  f is a zffunction.
  Proof.
    Let z /in kappa. Then f[z] /in /VV.
  end.
  Then f : kappa /rightarrow x.
  f is injective.
  Proof.
    Let z1,z2 /in kappa. Let z1 /neq z2.
    Then f[z1] /neq f[z2].
  end.
  ran(f) = x.
  Then x = f^[kappa].
  Then x /in /VV.
  f : kappa /leftrightarrow x.
end.
(y is a zfset) /\ y /tilde lambda.
Proof.
  Define f[z] = (z,1) for z in lambda.
  f is a zffunction.
  Proof.
    Let z /in lambda. Then f[z] /in /VV.
  end.
  Then f : lambda /rightarrow y.
  f is injective.
  Proof.
    Let z1,z2 /in lambda. Let z1 /neq z2.
    Then f[z1] /neq f[z2].
  end.
  ran(f) = y.
  Then y = f^[lambda].
  Then y /in /VV.
  f : lambda /leftrightarrow y.
end.
x /cap y = /emptyset /\ Card(x) = kappa /\ Card(y) = lambda.
Then (kappa,lambda) /sim (x,y).
kappa +3 lambda /tilde x /cup y.

Forall a,b /in /Ord (a /subset b \/ b /subset a).
kappa /subset lambda \/ lambda /subset kappa.
Case kappa /subset lambda.
  Then kappa /cup lambda = lambda.
  lambda <= kappa +3 lambda.
  x /cup y /subset lambda /times 2.
  Then kappa +3 lambda <= lambda /times 2.
  lambda *3 2 = lambda /cup 2.
  Then lambda /times 2 /tilde lambda.
  Then kappa +3 lambda <= lambda.
  Then kappa +3 lambda /tilde lambda.
end.
Case lambda /subset kappa.
  Then kappa /cup lambda = kappa.
  kappa <= kappa +3 lambda.
  x /cup y /subset kappa /times 2.
  Then kappa +3 lambda <= kappa /times 2.
  kappa *3 2 = kappa /cup 2.
  Then kappa /times 2 /tilde kappa.
  Then kappa +3 lambda <= kappa.
  Then kappa +3 lambda /tilde kappa.
end.
qed.



Lemma. Forall n /in /NN /setminus <0> forall kappa /in /Card (/NN /subset kappa => kappa ^3 n = kappa).
Proof.
Let kappa /in /Card. Let /NN /subset kappa.
Forall n /in /NN (kappa ^3 (n+1) = (kappa ^3 n) *3 (kappa ^3 1)).
Proof.
  Forall alpha, beta, gamma /in /Card (alpha ^3 (beta +3 gamma) = (alpha ^3 beta) *3 (alpha ^3 gamma)).
  Let n /in /NN.
  Then kappa, n, 1 /in /Card.
  Then n+1 = n +3 1.
end.

Define phi[n] =
  Case kappa ^3 n = kappa -> 0,
  Case kappa ^3 n /neq kappa -> 1
for n in /NN.

Then phi[1] = 0.

Forall n /in /NN (phi[n] = 0 => phi[n+1] = 0).
Proof.
  Let n /in /NN. Let phi[n] = 0.
  Then kappa ^3 n = kappa.
  kappa ^3 (n+1) = (kappa ^3 n) *3 (kappa ^3 1).
  Then kappa ^3 (n+1) = kappa *3 kappa.
  Then kappa ^3 (n+1) = kappa.
end.

Define M = {zfset n | n /in /NN /\ (n = 0 \/ phi[n] = 0)}.
Then 0 /in M.
Forall n /in M (n+1) /in M.
Proof.
  Let n /in M.
  Then (n+1) /in M.
  Proof.
    Case n = 0. Then n + 1 = 1. 1 /in M. end.
    Case phi[n] = 0. Then phi[n+1] /in M. Then (n+1) /in M. end.
  end.
end.
Then M /in /Ind.
Then M = /NN.

qed.



Lemma. Let kappa, lambda /in /Card. Let /NN /subset kappa. Let 2 /subset lambda. Let lambda /subset (2 ^3 kappa).
Then lambda ^3 kappa = 2 ^3 kappa.
Proof.
2 ^3 kappa /subset lambda ^3 kappa.
Proof.
  ^{kappa}2 /subset ^{kappa}lambda.
end.
lambda ^3 kappa /subset (2 ^3 kappa) ^3 kappa.
Proof.
  ^{kappa}lambda /subset ^{kappa}(2 ^3 kappa).
  Take zfsets x1,x2 such that x1 = ^{kappa}lambda /\ x2 = ^{kappa}(2 ^3 kappa).
  Then lambda ^3 kappa = Card(x1).
  Then (2 ^3 kappa) ^3 kappa = Card(x2).
end.
(2 ^3 kappa) ^3 kappa = 2 ^3 (kappa *3 kappa).
kappa *3 kappa = kappa.
Then 2 ^3 (kappa *3 kappa) = 2 ^3 kappa.
Then lambda ^3 kappa /subset 2 ^3 kappa.
qed.



Lemma. Contradiction.
