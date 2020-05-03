# 6-Arithmetic

# Here we introduce ordinal addition/multiplication/potentiation and show some basic/intuitive facts.
# Then we go on with finite sets and show some closedness properties.
# Then we define the Plus-function for cardinals and the Alefs.

# Main results:

# - facts about addition/multiplication/potentiation
# - facts about finite sets
# - all infinite cardinals are limit ordinals
# - forall alpha Alef[alpha] /in /Card
# - alpha /in beta => Alef[alpha] /in Alef[beta]
# - for all infinite cardinals kappa there is alpha with kappa = Alef[alpha]
# - exists kappa (kappa = Alef[kappa])




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

Signature. f ^^ n is an object.
Axiom. Let f be a zffunction. Let ran(f) /subset Dom(f). Let n /in /NN. Then f ^^ n is a function.
Axiom. Let f be a zffunction. Let ran(f) /subset Dom(f). Let n /in /NN. Then Dom(f^^n) = Dom(f).
Axiom. Let f be a zffunction. Let ran(f) /subset Dom(f). Let x /in Dom(f). Then (f
^^0)[x] = x.
Axiom. Let f be a zffunction. Let ran(f) /subset Dom(f). Let n /in /NN. Let x /in Dom(f). Then (f^^n)[x] /in Dom(f) /\ (f^^(n+1))[x] = f[((f^^n)[x])].
Axiom. Let f be a zffunction. Let ran(f) /subset Dom(f). Then forall n /in /NN (f^^n is a zffunction).
Axiom. Let f be a zffunction. Let ran(f) /subset Dom(f). Then forall n /in /NN ((f^^n is a zffunction) /\ (ran(f^^n) /subset Dom(f))).
Axiom. Let f be a zffunction. Let ran(f) /subset Dom(f). Let n /in /NN. Let n /neq /emptyset. Then ran(f ^^ n) /subset ran(f).






# Ordinal Arithmetic


Signature. alpha * beta is an ordinal.
Signature. alpha ^ beta is an ordinal.


# Addition

Axiom. Let alpha be an ordinal. Then alpha + 0 = alpha.
Axiom. Let alpha, beta be ordinals. Let beta /in /Succ. Let gamma = beta - 1.
  Then alpha + beta = (alpha + gamma) + 1.
Axiom. Let alpha, beta be ordinals. Let beta /in /Lim. Then alpha + beta = {zfset x | exists gamma /in beta (x /in (alpha + gamma))}.

Lemma. Forall alpha (0 + alpha = alpha).
Proof.
Define phi[alpha] =
  Case 0 + alpha = alpha -> 0,
  Case 0 + alpha /neq alpha -> 1
for alpha in /Ord.
Forall alpha /in /Ord (forall beta /in alpha phi[beta] = 0 => phi[alpha] = 0).
Proof.
  Let alpha /in /Ord. Let forall beta /in alpha phi[beta] = 0.
  alpha = 0 \/ alpha /in /Lim \/ alpha /in /Succ.
  Case alpha = 0. end.
  Case alpha /in /Succ.
    Take an ordinal beta such that alpha = beta + 1.
    Then 0 + beta = beta.
    0 + alpha = (0 + beta) + 1.
  end.
  Case alpha /in /Lim.
    Then 0 + alpha = {zfset x | exists beta /in alpha (x /in (0 + beta))}.
    alpha /subset 0 + alpha.
    Proof.
      Let x /in alpha.
      Then x + 1 /in alpha.
      Then 0 + (x+1) = x+1.
      Then x /in 0 + (x+1).
      Then x /in 0 + alpha.
    end.
    0 + alpha /subset alpha.
    Proof.
      Let x /in 0 + alpha.
      Take a set beta such that beta /in alpha /\ x /in (0 + beta).
      Then x /in beta.
      Then x /in alpha.
    end.
  end.
end.

Define M = {ordinal beta | phi[beta] = 0}.
Let N = /Ord /setminus M.
Case N = /emptyset. Then M = /Ord. end.
Case N /neq /emptyset.
  Take a set x such that x /in N /\ forall y /in x y /notin N.
  Then x /in /Ord /\ forall y /in x phi[y] = 0.
  Then phi[x] = 0.
  Contradiction.
end.

qed.

Lemma. Forall alpha, beta, gamma /in /Ord (beta /in gamma => alpha + beta /in alpha + gamma).
Proof.
Let alpha /in /Ord.
Define phi[gamma] =
  Case forall beta /in gamma (alpha + beta /in alpha + gamma) -> 0,
  Case not (forall beta /in gamma (alpha + beta /in alpha + gamma)) -> 1
for gamma in /Ord.

Forall gamma /in /Ord (forall gamma1 /in gamma phi[gamma1] = 0 => phi[gamma] = 0).
Proof.
  Let gamma /in /Ord. Let forall gamma1 /in gamma phi[gamma1] = 0.
  Then forall beta /in gamma (alpha + beta /in alpha + gamma).
  Proof.
    gamma = 0 \/ gamma /in /Lim \/ gamma /in /Succ.
    Case gamma = 0. end.
    Case gamma /in /Lim. Then alpha + gamma = {zfset x | exists delta /in gamma (x /in alpha + delta)}.
      Let beta /in gamma.
      Then beta + 1 /in gamma.
      alpha + (beta + 1) = (alpha + beta) + 1.
      Then alpha + beta /in alpha + (beta + 1).
      Then alpha + beta /in alpha + gamma.
    end.
    Case gamma /in /Succ. Take an ordinal delta such that gamma = delta + 1.
      Then alpha + gamma = (alpha + delta) + 1.
      Let beta /in delta.
      Then beta = delta \/ beta /in delta.
      Case beta = delta. Then alpha + beta /in alpha + gamma. end.
      Case beta /in delta.
        delta /in gamma. Then phi[delta] = 0.
        Then alpha + beta /in alpha + delta. 
        Then alpha + beta /in alpha + gamma. 
      end.
    end.
  end.
end.

Then forall gamma /in /Ord phi[gamma] = 0.
Proof.
Define M = {ordinal beta | phi[beta] = 0}.
Let N = /Ord /setminus M.
Case N = /emptyset. Then M = /Ord. end.
Case N /neq /emptyset.
  Take a set x such that x /in N /\ forall y /in x y /notin N.
  Then x /in /Ord /\ forall y /in x phi[y] = 0.
  Then phi[x] = 0.
  Contradiction.
end.
end.

qed.



Lemma. Forall alpha, beta /in /Ord (alpha /subset alpha+beta).
Proof.
Let alpha /in /Ord.
Define phi[beta] =
  Case alpha /subset alpha + beta -> 0,
  Case not (alpha /subset alpha + beta) -> 1
for beta in /Ord.

Forall beta /in /Ord (forall gamma /in beta phi[gamma] = 0 => phi[beta] = 0).
Proof.
  Let beta /in /Ord. Let forall gamma /in beta phi[gamma] = 0.
  beta = 0 \/ beta /in /Lim \/ beta /in /Succ.
  Case beta = 0. end.
  Case beta /in /Lim.
    Then alpha + beta = {zfset x | exists gamma /in beta (x /in (alpha + gamma))}.
  end.
  Case beta /in /Succ.
    Take an ordinal gamma such that beta = gamma + 1.
    Then alpha + beta = (alpha + gamma) + 1.
    alpha /subset alpha + gamma.
    alpha + gamma /subset (alpha + gamma) + 1.
    Then alpha /subset (alpha + gamma) + 1.
  end.
end.

Define M = {ordinal beta | phi[beta] = 0}.
Let N = /Ord /setminus M.
Case N = /emptyset. Then M = /Ord. end.
Case N /neq /emptyset.
  Take a set x such that x /in N /\ forall y /in x y /notin N.
  Then x /in /Ord /\ forall y /in x phi[y] = 0.
  Then phi[x] = 0.
  Contradiction.
end.

qed.

Lemma. Forall alpha, beta /in /Ord (beta /subset alpha + beta).
Proof.
Let alpha /in /Ord.
Define phi[beta] =
  Case beta /subset alpha + beta -> 0,
  Case not (beta /subset alpha + beta) -> 1
for beta in /Ord.

Forall beta /in /Ord (forall gamma /in beta phi[gamma] = 0 => phi[beta] = 0).
Proof.
  Let beta /in /Ord. Let forall gamma /in beta phi[gamma] = 0.
  beta = 0 \/ beta /in /Lim \/ beta /in /Succ.
  Case beta = 0. end.
  Case beta /in /Lim.
    Then alpha + beta = {zfset x | exists gamma /in beta (x /in (alpha + gamma))}.
    Let x /in beta.
    Then x /subset alpha + x.
    x + 1 /in beta.
    x /in (alpha + x) + 1.
    alpha + (x+1) = (alpha + x) + 1.
    Then x /in alpha + (x+1).
    Then x /in alpha + beta.
  end.
  Case beta /in /Succ.
    Take an ordinal gamma such that beta = gamma + 1.
    Then alpha + beta = (alpha + gamma) + 1.
    gamma /subset alpha + gamma.
    Then gamma /in (alpha + gamma) + 1.
    Then beta /subset alpha + beta.
  end.
end.

Define M = {ordinal beta | phi[beta] = 0}.
Let N = /Ord /setminus M.
Case N = /emptyset. Then M = /Ord. end.
Case N /neq /emptyset.
  Take a set x such that x /in N /\ forall y /in x y /notin N.
  Then x /in /Ord /\ forall y /in x phi[y] = 0.
  Then phi[x] = 0.
  Contradiction.
end.

qed.


Lemma. Forall m,n /in /NN forall x /in (m + n) (x /in m \/ exists i /in n x = m + i).
Proof.
Let m /in /NN.
Define M = {ordinal k | k /in /NN /\ (forall x /in (m + k) (x /in m \/ exists i /in k x = m + i))}.
Then 0 /in M.
Forall n /in M (n + 1) /in M.
Proof.
  Let n /in M.
  Then forall x /in (m + (n+1)) (x /in m \/ exists i /in (n+1) x = m + i).
  Proof.
    m + (n+1) = (m + n) + 1.
    Let x /in m + (n+1). Then x /in m + n \/ x = m + n.
    n+1 /in /NN. 
  end.
end.
Then M /in /Ind.
Then M = /NN.
qed.




# Multiplication

Axiom. Let alpha be an ordinal. Then alpha * 0 = 0.
Axiom. Let alpha, beta be ordinals. Let beta /in /Succ. Let gamma = beta - 1.
  Then alpha * beta = (alpha * gamma) + alpha.
Axiom. Let alpha, beta be ordinals. Let beta /in /Lim. Then alpha * beta = {zfset x | exists gamma /in beta (x /in alpha * gamma)}.

Lemma. Forall alpha /in /Ord (alpha * 1 = alpha).
Proof.
Let alpha /in /Ord.
1 = 0+1.
Then alpha * 1 = (alpha * 0) + alpha.
Then alpha * 1 = alpha.
qed.

Lemma. Forall alpha /in /Ord (0 * alpha = 0).
Proof.
Define phi[alpha] =
  Case 0 * alpha = 0 -> 0,
  Case 0 * alpha /neq 0 -> 1
for alpha in /Ord.
Forall alpha /in /Ord (forall beta /in alpha phi[beta] = 0 => phi[alpha] = 0).
Proof.
  Let alpha /in /Ord. Let forall beta /in alpha phi[beta] = 0.
  alpha = 0 \/ alpha /in /Lim \/ alpha /in /Succ.
  Case alpha = 0. end.
  Case alpha /in /Succ.
    Take an ordinal beta such that alpha = beta + 1.
    Then 0 * beta = 0.
    0 * alpha = (0 * beta) * 0.
  end.
  Case alpha /in /Lim.
    Forall gamma /in /Ord (gamma * alpha = {zfset x | exists beta /in alpha (x /in (gamma * beta))}).
    Then 0 * alpha = {zfset x | exists beta /in alpha (x /in (0 * beta))}.
    Let x /in 0 * alpha.
    Take a set beta such that beta /in alpha /\ x /in (0 * beta).
    Contradiction.
    Then 0 * alpha = 0.
  end.
end.

Define M = {ordinal beta | phi[beta] = 0}.
Let N = /Ord /setminus M.
Case N = /emptyset. Then M = /Ord. end.
Case N /neq /emptyset.
  Take a set x such that x /in N /\ forall y /in x y /notin N.
  Then x /in /Ord /\ forall y /in x phi[y] = 0.
  Then phi[x] = 0.
  Contradiction.
end.

qed.


Lemma. Forall alpha /in /Ord (1 * alpha = alpha).
Proof.
Define phi[alpha] =
  Case 1 * alpha = alpha -> 0,
  Case 1 * alpha /neq alpha -> 1
for alpha in /Ord.
Forall alpha /in /Ord (forall beta /in alpha phi[beta] = 0 => phi[alpha] = 0).
Proof.
  Let alpha /in /Ord. Let forall beta /in alpha phi[beta] = 0.
  alpha = 0 \/ alpha /in /Succ \/ alpha /in /Lim.
  Case alpha = 0. end.
  Case alpha /in /Succ.
    Take a ordinal beta such that alpha = beta + 1.
    Then 1 * beta = beta.
    1 * alpha = beta + 1.
    Then 1 * alpha = alpha.
  end.
  Case alpha /in /Lim.
    Then 1 * alpha = {zfset x | exists gamma /in alpha (x /in 1 * gamma)}.
    alpha /subset 1 * alpha.
    Proof.
      Let x /in alpha.
      Then x + 1 /in alpha.
      Then 1 * (x+1) = x+1.
      Then x /in 1 * (x+1).
      Then x /in 1 * alpha.
    end.
    1 * alpha /subset alpha.
    Proof.
      Let x /in 1 * alpha.
      Take a set gamma such that gamma /in alpha /\ x /in 1 * gamma.
      Then x /in gamma.
      Then x /in alpha.
    end.
  end.
end.

Define M = {ordinal beta | phi[beta] = 0}.
Let N = /Ord /setminus M.
Case N = /emptyset. Then M = /Ord. end.
Case N /neq /emptyset.
  Take a set x such that x /in N /\ forall y /in x y /notin N.
  Then x /in /Ord /\ forall y /in x phi[y] = 0.
  Then phi[x] = 0.
  Contradiction.
end.

qed.


Lemma. Forall alpha, beta /in /Ord (beta /neq /emptyset => alpha /subset alpha * beta).
Proof.
Let alpha /in /Ord.
Define phi[beta] =
  Case alpha /subset alpha * beta -> 0,
  Case not (alpha /subset alpha * beta) -> 1
for beta in /Ord /setminus <0>.

Forall beta /in /Ord /setminus <0> (forall gamma /in beta /setminus <0> phi[gamma] = 0 => phi[beta] = 0).
Proof.
  Let beta /in /Ord /setminus <0>. Let forall gamma /in beta /setminus <0> phi[gamma] = 0.
  beta /in /Lim \/ beta /in /Succ.
  Case beta /in /Lim.
    Then alpha * beta = {zfset x | exists gamma /in beta (x /in (alpha * gamma))}.
    1 /in beta.
    alpha = alpha * 1.
    Then alpha /subset alpha * beta.
  end.
  Case beta /in /Succ.
    Take an ordinal gamma such that beta = gamma + 1.
    Then alpha * beta = (alpha * gamma) + alpha.
    Case gamma /neq 0.
      Then gamma /in beta /setminus <0>.
      alpha /subset alpha * gamma.
      Then alpha /subset (alpha * gamma) + alpha.
    end.
    Case gamma = 0. end.
  end.
end.

Define M = {ordinal beta | beta /neq 0 /\ phi[beta] = 0}.
Let N = (/Ord /setminus <0>) /setminus M.
Case N = /emptyset. Then M = /Ord /setminus <0>. end.
Case N /neq /emptyset.
  Take a set x such that x /in N /\ forall y /in x y /notin N.
  Then x /in /Ord /setminus <0> /\ forall y /in x /setminus <0> (phi[y] = 0).
  Proof.
    Let y /in x /setminus <0>. Then y /in /Ord /setminus <0> /\ y /notin N.
    Then y /in M.
    Then phi[y] = 0.
  end.
  Then phi[x] = 0.
  Contradiction.
end.

qed.


Lemma. Forall alpha, beta /in /Ord (beta /neq 0 => alpha + 1 /subset alpha + beta).
Proof.
Let alpha /in /Ord.
Define phi[beta] =
  Case alpha + 1 /subset alpha + beta -> 0,
  Case not (alpha + 1 /subset alpha + beta) -> 1
for beta in /Ord /setminus <0>.

Forall beta /in /Ord /setminus <0> (forall gamma /in beta /setminus <0> phi[gamma] = 0 => phi[beta] = 0).
Proof.
  Let beta /in /Ord /setminus <0>. Let forall gamma /in beta /setminus <0> phi[gamma] = 0.
  beta /in /Lim \/ beta /in /Succ.
  Case beta /in /Lim.
    Then alpha + beta = {zfset x | exists gamma /in beta (x /in (alpha + gamma))}.
    1 /in beta.
    alpha /in alpha + 1.
    Then alpha /in alpha + beta.
    Then alpha + 1 /subset alpha + beta.
  end.
  Case beta /in /Succ.
    Take an ordinal gamma such that beta = gamma + 1.
    Then alpha + beta = (alpha + gamma) + 1.
    Case gamma /neq 0.
      Then gamma /in beta /setminus <0>.
      alpha + 1 /subset alpha + gamma.
      Then alpha + 1 /subset (alpha + gamma) + 1.
    end.
    Case gamma = 0. end.
  end.
end.

Define M = {ordinal beta | beta /neq 0 /\ phi[beta] = 0}.
Let N = (/Ord /setminus <0>) /setminus M.
Case N = /emptyset. Then M = /Ord /setminus <0>. end.
Case N /neq /emptyset.
  Take a set x such that x /in N /\ forall y /in x y /notin N.
  Then x /in /Ord /setminus <0> /\ forall y /in x /setminus <0> (phi[y] = 0).
  Proof.
    Let y /in x /setminus <0>. Then y /in /Ord /setminus <0> /\ y /notin N.
    Then y /in M.
    Then phi[y] = 0.
  end.
  Then phi[x] = 0.
  Contradiction.
end.

qed.

Lemma. Forall alpha, beta /in /Ord (alpha /neq 0 => beta /subset alpha * beta).
Proof.
Let alpha /in /Ord. Let alpha /neq 0.
Define phi[beta] =
  Case beta /subset alpha * beta -> 0,
  Case not (beta /subset alpha * beta) -> 1
for beta in /Ord.

Forall beta /in /Ord (forall gamma /in beta phi[gamma] = 0 => phi[beta] = 0).
Proof.
  Let beta /in /Ord. Let forall gamma /in beta phi[gamma] = 0.
  beta = 0 \/ beta /in /Lim \/ beta /in /Succ.
  Case beta = 0. end.
  Case beta /in /Lim.
    Then alpha * beta = {zfset x | exists gamma /in beta (x /in (alpha * gamma))}.
    Then beta /subset alpha * beta.
    Proof.
      Let x /in beta.
      Then x /subset alpha * x.
      x + 1 /in beta.
      x /in (alpha * x) + 1.
      (alpha * x) + 1 /subset (alpha * x) + alpha.
      x /in (alpha * x) + alpha.
      x+1 /in /Succ.
      Take an ordinal y such that y /in /Succ /\ y = x+1.
      alpha * y = (alpha * x) + alpha.
      Then x /in alpha * (x+1).
      Then x /in alpha * beta.
    end.
  end.
  Case beta /in /Succ.
    Take an ordinal gamma such that beta = gamma + 1.
    Then alpha * beta = (alpha * gamma) + alpha.
    gamma /subset alpha * gamma.
    Then gamma /in (alpha * gamma) + 1.
    (alpha * gamma) + 1 /subset (alpha * gamma) + alpha.
    Then gamma /in alpha * beta.
    Then beta /subset alpha * beta.
  end.
end.

Define M = {ordinal beta | phi[beta] = 0}.
Let N = /Ord /setminus M.
Case N = /emptyset. Then M = /Ord. end.
Case N /neq /emptyset.
  Take a set x such that x /in N /\ forall y /in x y /notin N.
  Then x /in /Ord /\ forall y /in x phi[y] = 0.
  Then phi[x] = 0.
  Contradiction.
end.

qed.




# Power

Axiom. Let alpha be an ordinal. Then alpha ^ 0 = 1.
Axiom. Let alpha, beta be ordinals. Let beta /in /Succ. Let gamma = beta - 1.
  Then alpha ^ beta = (alpha ^ gamma) * alpha.
Axiom. Let alpha, beta be ordinals. Let beta /in /Lim. Then alpha + beta = {zfset x | exists gamma /in beta (x /in alpha ^ gamma)}.

Lemma. Forall alpha /in /Ord alpha ^ 1 = alpha.
Proof.
Let alpha /in /Ord.
1 = 0+1.
Then alpha ^ 1 = (alpha ^ 0) * alpha.
Then alpha ^ 1 = alpha.
qed.







Lemma. Let alpha, beta be ordinals. Let beta /in /Lim. Then alpha + beta /in /Lim.
Proof by contradiction. Assume the contrary. Then alpha + beta = /emptyset \/ alpha + beta /in /Succ.
  alpha + beta /neq /emptyset.
  Proof. alpha /in alpha + 1. 1 /in beta. end.
  Then alpha + beta /in /Succ.
  Take an ordinal gamma such that alpha + beta = gamma + 1.
  Then gamma /in alpha + beta.
  alpha + beta = {zfset x | exists n /in beta (x /in alpha + n)}.
  Take an ordinal n such that n /in beta /\ gamma /in alpha + n.
  Then gamma + 1 /in alpha + (n + 1).
  Proof. alpha + (n+1) = (alpha + n) + 1.
    gamma /in alpha + n.    
  end.
  Then gamma + 1 /in alpha + beta.
  Contradiction.
qed.



Lemma. Forall m,n /in /NN m+n /in /NN.
Proof.
Let m /in /NN. Then forall n /in /NN m+n /in /NN.
Proof.
  Define phi[n] =
    Case m+n /in /NN -> 0,
    Case m+n /notin /NN -> 1
  for n in /NN.
  Forall n /in /NN (phi[n] = 0 => phi[n+1] = 0).
  Proof.
    Let n /in /NN. Let phi[n] = 0.
    Then m+n /in /NN.
    Then (m+n)+1 /in /NN.
    m + (n+1) = (m+n) + 1.
    Then m + (n+1) /in /NN. 
    Then phi[n+1] = 0.
  end.
  Define M = {ordinal n | n /in /NN /\ phi[n] = 0}.
  Then 0 /in M /\ forall n /in M (n+1) /in M.
  Then M /in /Ind.
  Then M = /NN.
end.
qed.

Lemma. Forall m,n /in /NN m*n /in /NN.
Proof.
Let m /in /NN. Then forall n /in /NN m*n /in /NN.
Proof.
  Define phi[n] =
    Case m*n /in /NN -> 0,
    Case m*n /notin /NN -> 1
  for n in /NN.
  Forall n /in /NN (phi[n] = 0 => phi[n+1] = 0).
  Proof.
    Let n /in /NN. Let phi[n] = 0.
    Then m*n /in /NN.
    Then (m*n) + m /in /NN.
    Take an ordinal n1 such that n1 /in /Succ /\ n1 = n + 1.
    m * n1 = (m*n) + m.
    Then m * (n+1) /in /NN. 
    Then phi[n+1] = 0.
  end.
  Define M = {ordinal n | n /in /NN /\ phi[n] = 0}.
  Then 0 /in M /\ forall n /in M (n+1) /in M.
  Then M /in /Ind.
  Then M = /NN.
end.
qed.

Lemma. Forall m,n /in /NN m^n /in /NN.
Proof.
Let m /in /NN. Then forall n /in /NN m^n /in /NN.
Proof.
  Define phi[n] =
    Case m^n /in /NN -> 0,
    Case m^n /notin /NN -> 1
  for n in /NN.
  Forall n /in /NN (phi[n] = 0 => phi[n+1] = 0).
  Proof.
    Let n /in /NN. Let phi[n] = 0.
    Then m^n /in /NN.
    Then (m^n) * m /in /NN.
    Take an ordinal n1 such that n1 /in /Succ /\ n1 = n+1.
# Sometimes it stops here, so we just need to rename n+1, so Naproche directly thinks of n+1 as a successor ordinal.
    m ^ (n1) = (m^n) * m.
    Then m ^ (n+1) /in /NN. 
    Then phi[n+1] = 0.
  end.
  Define M = {ordinal n | n /in /NN /\ phi[n] = 0}.
  Then 0 /in M /\ forall n /in M (n+1) /in M.
  Then M /in /Ind.
  Then M = /NN.
end.
qed.







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





# Finite Sets

Definition. Let x be a zfset. x is finite iff Card(x) /in /NN.

Lemma. Let x,y be zfsets. Let x be finite. Let y /subset x. Then y is finite.
Proof.
Card(x) /in /NN.
Card(y) /subset Card(x).
Forall a,b /in /Ord (a /in b \/ b /in a \/ a = b).
Card(x), Card(y) /in /Ord.
Take ordinals a,b such that a = Card(x) \/ b = Card(y).
Then Card(y) /in Card(x) \/ Card(y) = Card(x) \/ Card(x) /in Card(y).
Then Card(y) /in /NN.
qed.

Lemma. Let x,y be zfsets. Let x,y be finite. Then x /cup y is finite.
Proof.
Let y1 = y /setminus x.
Then x /cup y = x /cup y1.
y1 is finite.
Take ordinals m,n such that Card(x) = m /\ Card(y1) = n.
Then Card(x /cup y) /subset m+n.
Proof.
  Take a zffunction f such that f : x /leftrightarrow m.
  Take a zffunction g such that g : y1 /leftrightarrow n.
  Define h[z] =
    Case z /in x -> f[z],
    Case z /in y1 -> m + g[z]
  for z in x /cup y1.
  Then h is a zffunction.
  Proof.
    Let z /in Dom(h). Then z /in x \/ z /in y1.
    Then h[z] /in /VV.
  end.
  h : x /cup y1 /rightarrow m+n.
  Proof.
    Let z /in x /cup y1. Then z /in x \/ z /in y1.
    Then h[z] /in m+n.
    Proof.
      Case z /in x. Then h[z] /in m. m /subset m+n. Then h[z] /in m+n. end.
      Case z /in y1. 
        Take a set i such that i /in n /\ i = g[z].
        Then h[z] = m+i.
        Forall a,b,c /in /Ord (b /in c => a+b /in a+c).
        Then m + i /in m + n.
      end.
    end.
  end.
  h is injective.
  Proof.
    Let a,b /in x /cup y1.
    Let a /neq b.
    Then h[a] /neq h[b].
    Proof.
      a,b /in x \/ a,b /in y1 \/ (a /in x /\ b /in y1) \/ (a /in y1 /\ b /in x).
      Case a,b /in x. 
        Then f[a] /neq f[b].
        h[a] = f[a] /\ h[b] = f[b].
      end.
      Case a,b /in y1. 
        Forall ord1,ord2 /in /Ord (ord1 /in ord2 \/ ord2 /in ord1 \/ ord1 = ord2).
        g[a], g[b] /in /Ord.
        Then g[a] /in g[b] \/ g[b] /in g[a] \/ g[a] = g[b].
        g[a] /neq g[b].
        Then g[a] /in g[b] \/ g[b] /in g[a].
        Then m + g[a] /in m + g[b] \/ m + g[b] /in m + g[a].
        Then h[a] /in h[b] \/ h[b] /in h[a].
      end.
      Case a /in x /\ b /in y1.
        Then h[a] /in m /\ h[b] /notin m.
      end.
      Case a /in y1 /\ b /in x.
        Then h[b] /in m /\ h[a] /notin m.
      end.
    end.
  end.
  ran(h) = m+n.
  Proof.
    Let a /in m+n. 
    Then a /in ran(h).
    Proof.
      Then a /in m \/ a /notin m.
      Case a /in m. Take a set b such that b /in x /\ f[b] = a.
        Then h[b] = a.
      end.
      Case a /notin m.
        Exists b /in n a = m+b.
        Take a set b such that b /in n /\ a = m+b.
        Take a set c such that c /in y1 /\ g[c] = b.
        Then h[c] = a.
      end.
    end.
  end.  
  Then h : x /cup y1 /leftrightarrow m+n.
  Then m+n /in Cardset(x /cup y).
  Card(x /cup y) = /bigcap Cardset(x /cup y).
  Then Card(x /cup y) /subset m+n.
end.

Then Card(x /cup y) /in /NN.
qed.



Lemma. Let a,b be zfsets. Let a,b be finite. Then (a /cap b is a zfset) and (a /cap b is finite).
Proof.
a /cap b /subset a.
qed.





Lemma. Let kappa be a cardinal. Let /NN /subset kappa. Then kappa /in /Lim.
Proof by contradiction. Assume the contrary. Then kappa /notin /Lim.
Then kappa /in /Succ \/ kappa = /emptyset.
kappa /neq /emptyset. Then kappa /in /Succ.
Take an ordinal alpha such that kappa = alpha + 1.
Then /NN /subset alpha.
Take a zfset x such that kappa = Card(x).
Take a zffunction f such that f : kappa /leftrightarrow x.

Define g[beta] =
  Case beta /in /NN /\ beta /neq /emptyset -> beta-1,
  Case beta = /emptyset -> alpha,
  Case beta /notin /NN -> beta
for beta in alpha.

Then g is a zffunction.
Proof.
  Let beta /in Dom(g).
  Then g[beta] /in /VV.
end.

Dom(g) = alpha.

Forall a,b /in alpha ( g[a] = g[b] => a = b).
Proof.
  Let a,b /in alpha. Then g[a] = g[b] => a = b.
  Proof.
  Case g[a] = alpha. Then a = /emptyset. end.
  Case g[a] /in /NN. Then a /in /NN /\ a /neq /emptyset. Then a = g[a] + 1. end.
  Case g[a] /notin /NN /\ g[a] /neq alpha. Then g[a] = a. end.
  end.
end.
Then g is injective.



ran(g) = (alpha + 1).
#Proof.
#  Let beta /in alpha + 1.
#  Case beta = alpha. Then beta = g[0].
#  end.
#  Case beta /in alpha /\ beta /in /NN. Then beta + 1 /in /NN. Then beta + 1 /in alpha.
#    Then beta = g[beta + 1].
#  end.
#  Case beta /in alpha /\ beta /notin /NN. Then beta = g[beta].
#  end.
#end.

Then g : alpha /leftrightarrow alpha + 1.

Then f /circ g : alpha /leftrightarrow x.
Proof. f /circ g : alpha /rightarrow x.
  f /circ g is injective.
  ran(f /circ g) = x.
end.

Then alpha /in Cardset(x).
Then kappa /in alpha.
Then alpha /in alpha.
Contradiction.
qed.






# Alefs




Signature. Plus is a zffunction.
Axiom. Plus : /Ord /rightarrow /Card.
Axiom. Let alpha /in /Ord. Then Plus[alpha] = {ordinal beta | forall kappa /in /Card (alpha /in kappa => beta /in kappa)}.

Lemma. Let n /in /NN. Then Plus[n] = n+1.
Proof. n /in Plus[n]. 
  n+1 /subset Plus[n].
  Proof. 
    n /subset Plus[n].
    Proof.
      Let m /in n.
      Forall kappa /in /Card (n /in kappa => n /subset kappa).
      Then m /in Plus[n].
    end.
    n /in Plus[n].
  end.
  n+1 /in /Card.
  Plus[n] /subset n+1.
qed.

Signature. Alef is a zffunction.
Axiom. Alef : /Ord /rightarrow /Ord.
Axiom. Alef[/emptyset] = /NN.
Axiom. Let alpha /in /Succ. Let beta /in /Ord. Let alpha = beta + 1. Then Alef[beta] /in /Ord /\ Alef[alpha] = Plus[Alef[beta]].
Axiom. Let alpha /in /Lim. Then Alef[alpha] = {zfset x | exists beta /in alpha x /in Alef[beta]}.


Lemma. Let x /in /VV. Let x /subset /Card. Then Card(/bigcup x) = /bigcup x.
Proof.
Trans(/bigcup x).
/bigcup x, Card(/bigcup x) /in /Ord.
Take ordinals alpha, beta such that alpha = Card(/bigcup x) /\ beta = /bigcup x.
Then alpha /in beta \/ beta /in alpha \/ alpha = beta.
alpha /subset beta.
Proof. Id /upharpoonright beta : beta /leftrightarrow beta.
end.
beta /notin alpha.
Then alpha /in beta \/ alpha = beta.
Case alpha = beta. end.
Case alpha /in beta.
  Take a cardinal kappa such that (kappa /in x /\ alpha /in kappa).
  Take a zffunction f such that f : alpha /leftrightarrow beta.
  Then kappa /subset beta.
  Then Card(kappa) /subset Card(beta).
  kappa /subset alpha.
  Contradiction.
end.
qed.

Lemma. Let x /in /VV. Let x /subset /Card. Then (/bigcup x) /in /Card.

Lemma. Let alpha /in /Ord. Then Alef[alpha] /in /Card.
Proof.
Define phi[n] = 
  Case Alef[n] /in /Card -> 0,
  Case Alef[n] /notin /Card -> 1
for n in /Ord.

phi[0] = 0.

Forall x /in /Ord ((forall y /in x phi[y] = 0) => phi[x] = 0).
Proof.
  Let x /in /Ord. Let forall y /in x phi[y] = 0.
  Then phi[x] = 0.
  Proof.
  Case x = /emptyset. end.
  Case x /in /Succ. Take an ordinal z such that x = z + 1. Alef[z] /in /Ord. Then Alef[x] = Plus[Alef[z]]. end.
  Case x /in /Lim. Then Alef[x] = {zfset z | exists beta /in x z /in Alef[beta]}.
    Then Alef[x] = /bigcup Alef^[x].
    Proof. Alef[x] /subset /bigcup Alef^[x].
      Proof. Let z /in Alef[x]. Take beta /in x such that z /in Alef[beta].
        Then z /in /bigcup Alef^[x].
      end.
    end.
    Alef^[x] /subset /Card.
    x /in /VV. x /subset Dom(Alef).
    Alef^[x] /in /VV.
    Proof.
      Forall y /in x Alef[y] /in /VV.
      x /in /VV.
      x /subset Dom(Alef).
      Then Alef^[x] /in /VV.
    end.
    Then /bigcup Alef^[x] /in /Card.
  end.
  end.
end.

Define M = {ordinal gamma | phi[gamma] = 0}.
Then /emptyset /in M. M /subset /Ord.
Let N = /Ord /setminus M.
Assume N /neq /emptyset.
Take a zfset x such that (x /in N /\ (forall y /in x y /notin N)).
Then forall y /in x phi[y] = 0.
Then phi[x] = 0.
Contradiction.

qed.


Lemma. Forall alpha, beta (alpha /in beta => Alef[alpha] /in Alef[beta]).
Proof.
Define phi[n] =
  Case forall m /in n (Alef[m] /in Alef[n]) -> 0,
  Case exists m /in n (Alef[m] /notin Alef[n]) -> 1
for n in /Ord.

phi[0] = 0.

Forall x /in /Ord (forall y /in x phi[y] = 0 => phi[x] = 0).
Proof.
  Let x /in /Ord. Let forall y /in x phi[y] = 0.
  Case x = /emptyset. end.
  Case x /in /Lim. Then Alef[x] = {zfset z | exists gamma /in x (z /in Alef[gamma])}.
    Let alpha /in x.
    Then Alef[alpha] /subset Alef[x].
    alpha + 1 /in x.
    Alef[alpha] /in Alef[alpha + 1].
    Proof. Alef[alpha + 1] = Plus[Alef[alpha]].
      Alef[alpha] /in Plus[Alef[alpha]].
    end.
    Then Alef[alpha] /in Alef[x].
  end.
  Case x /in /Succ. Take an ordinal z such that x = z + 1.
    Then Alef[x] = Plus[Alef[z]].
    Let alpha /in x. Then alpha /subset z.
    Then alpha /in z \/ alpha = z.
    Alef[alpha] /in Alef[x].
    Proof.
      Case alpha = z. Then Alef[x] = Plus[Alef[alpha]].
        Forall a /in /Ord a /in Plus[a].
        Alef[alpha] /in Plus[Alef[alpha]].
      end.
      Case alpha /in z. Then Alef[alpha] /in Alef[z].
        Alef[z] /in Plus[Alef[z]].
        Proof.
          Take an ordinal a such that a = Alef[z].
          Then a /in Plus[a].
        end.
        Alef[z] /in Alef[x].
        Alef[z] /subset Alef[x].
      end.
    end.
  end.
end.

Define M = {ordinal alpha | phi[alpha] = 0}.
Then /emptyset /in M. M /subset /Ord.
Let N = /Ord /setminus M.
Assume N /neq /emptyset.
Take a zfset x such that (x /in N /\ (forall y /in x y /notin N)).
Then forall y /in x phi[y] = 0.
Then phi[x] = 0.
Contradiction.
Then M = /Ord.

Then forall alpha phi[alpha] = 0.

qed.



Lemma. Forall alpha /in /Ord (alpha /subset Alef[alpha]).

Proof.
Define phi[alpha] =
  Case alpha /subset Alef[alpha] -> 0,
  Case alpha /notin /PP Alef[alpha] -> 1
for alpha in /Ord.

phi[0] = 0.

Forall alpha /in /Ord (forall beta /in alpha phi[beta] = 0 => phi[alpha] = 0).
Proof.
  Let alpha /in /Ord. Let forall beta /in alpha phi[beta] = 0.
  Case alpha = /emptyset. end.
  Case alpha /in /Succ. Take an ordinal gamma such that alpha = gamma + 1.
    Then Alef[gamma] is an ordinal.
    Then Alef[alpha] = Plus[Alef[gamma]].
    alpha /subset Plus[Alef[gamma]].
    Proof.
    Let x be a zfset. Let x /in alpha. Then x = gamma \/ x /in gamma.
    x /in Plus[Alef[gamma]].
    Proof.    
      gamma /subset Alef[gamma].
      gamma /in Plus[Alef[gamma]].
      Case x = gamma. end.
      Case x /in gamma. end.
    end.
    end.
  end.
  Case alpha /in /Lim. Let beta /in alpha. Then beta + 1 /in alpha.
    Then beta + 1 /subset Alef[beta + 1].
    Then beta /in Alef[beta + 1].
    Then beta /in Alef[alpha].
  end.
end.

Define M = {ordinal alpha | phi[alpha] = 0}.
Then /emptyset /in M. M /subset /Ord.
Let N = /Ord /setminus M.
Assume N /neq /emptyset.
Take a zfset x such that (x /in N /\ (forall y /in x y /notin N)).
Then forall y /in x phi[y] = 0.
Then phi[x] = 0.
Contradiction.
Then M = /Ord.

Then forall alpha phi[alpha] = 0.

qed.





Lemma. Let kappa be a cardinal. Let /NN /subset kappa. Then exists alpha (kappa = Alef[alpha]).
Proof. kappa /subset Alef[kappa]. Then kappa = Alef[kappa] \/ kappa /in Alef[kappa].
  Case kappa = Alef[kappa]. end.
  Case kappa /in Alef[kappa].
    kappa /in /Lim.
    Then Alef[kappa] = {zfset x | exists alpha /in kappa x /in Alef[alpha]}.
    Define A = {ordinal alpha | kappa /in Alef[alpha]}.
    Let beta = /bigcap A.
    Trans(beta).
    Proof.
      Let x /in beta. Let y /in x. Then forall alpha (kappa /in Alef[alpha] => x /in alpha).
      Then forall alpha (kappa /in Alef[alpha] => y /in alpha).
      Then y /in beta.
    end.
    beta /in /VV.
    Then beta /in /Ord.
    beta /in A.
    Proof.
      Forall alpha /in A beta /subset alpha.
      Then forall alpha /in A (beta /in alpha \/ beta = alpha).
      Case forall alpha /in A beta /in alpha. Then beta + 1 /subset /bigcap A. Contradiction.
      end.
      Case exists alpha /in A beta = alpha. end.
    end.
    Then kappa /in Alef[beta] /\ forall gamma /in beta kappa /notin Alef[gamma].
    
    beta /in /Succ. Take an ordinal gamma such that beta = gamma + 1.
    Then kappa /notin Alef[gamma].
    Alef[gamma], kappa /in /Ord.
    Take ordinals a, b such that a = Alef[gamma] /\ b = kappa.
    Then a /in b \/ a = b \/ b /in a.
    Then kappa /in Alef[gamma] \/ kappa = Alef[gamma] \/ Alef[gamma] /in kappa.
    Case kappa /in Alef[gamma]. Contradiction. end.
    Case kappa = Alef[gamma]. end.
    Case Alef[gamma] /in kappa.
      kappa /in /Card.
      Then Plus[Alef[gamma]] /subset kappa.
      Proof. Take a cardinal alefgamma such that Alef[gamma] = alefgamma.
        Plus[alefgamma] = {ordinal beta | forall lambda /in /Card (alefgamma /in lambda => beta /in lambda)}.
      end.
      Then Alef[beta] /subset kappa.
      Contradiction.
    end.
  end.
qed.



Lemma. Let f be a zffunction. Let ran(f) /subset Dom(f). Let n /in /NN. Let x /in Dom(f). Then (f^^n)[x] /in Dom(f) /\ (f^^(n+1))[x] = f[((f^^n)[x])]. 


Lemma. Exists kappa (kappa = Alef[kappa]).
Proof.
Define f[n] = 
  Case n = /emptyset -> /NN,
  Case n /in /NN /\ n /neq /emptyset -> (Alef ^^ n)[/NN]
for n in /NN.

Then f is a zffunction.
Proof.
  Let n /in /NN. Then f[n] /in /VV.
  Proof.
    Case n = /emptyset. end.
    Case n /neq /emptyset.
      Then f[n] = (Alef ^^ n)[/NN].
      Then f[n] /in /Ord.
    end.
  end.
end.
Dom(f) = /NN. 
ran(f) /subset /Card.
Proof. Let n /in /NN.
  Then f[n] /in /Card.
  Proof.
  Case n = /emptyset. end.
  Case n /neq /emptyset. Then f[n] = (Alef ^^ n)[/NN].
    Then f[n] /in ran(Alef ^^ n).
    ran(Alef ^^ n) /subset ran(Alef).
  end.
  end.
end.

Forall n /in /NN f[n + 1] = Alef[f[n]].
Proof.
  Let n /in /NN. Then f[n+1] = (Alef ^^ (n+1)) [/NN].
  ((Alef^^n)[/NN]) /in /Ord.
  (Alef ^^ (n+1)) [/NN] = Alef[((Alef^^n)[/NN])].
  ((Alef^^n)[/NN]) = f[n].
  Proof.
    Case n = /emptyset. end.
    Case n /neq /emptyset. end.
  end.
end.


Let alpha = /bigcup ran(f).
ran(f) = f^[/NN].
Then alpha /in /Ord.
Proof. Trans(alpha). 
  alpha /in /VV.
  Proof.
    Forall n /in /NN f[n] /in /VV.
    Then f^[/NN] /in /VV.
    Then ran(f) /in /VV.
    Then /bigcup ran(f) /in /VV.
  end.
end.
alpha /in /Card.
Proof.
  Forall x /subset /Card (x /in /VV => /bigcup x /in /Card).
  ran(f) /subset /Card.
  ran(f) /in /VV.
  Proof.
    Forall n /in /NN f[n] /in /VV.
    Then f^[/NN] /in /VV.    
  end.
end.
alpha /in /Lim.
Then Alef[alpha] = {zfset x | exists beta /in alpha x /in Alef[beta]}.

alpha /subset Alef[alpha].
alpha, Alef[alpha] /in /Ord.
Forall a,b /in /Ord (a /in b \/ b /in a \/ a = b).
Then alpha = Alef[alpha] \/ alpha /in Alef[alpha] \/ Alef[alpha] /in alpha.

Alef[alpha] /notin alpha.

alpha /notin Alef[alpha].
Proof by contradiction. Assume the contrary.
  Then alpha /in Alef[alpha].
  Take an ordinal beta such that beta /in alpha /\ alpha /in Alef[beta].
  Take an ordinal n such that n /in /NN /\ beta /in f[n].
  Then Alef[beta] /in Alef[f[n]].
  f[n+1] = Alef[f[n]].
  Then Alef[beta] /in f[n+1].
  f[n+1] /subset alpha.
  Contradiction.
end.

Then alpha = Alef[alpha].

qed.







Lemma. Contradiction.



