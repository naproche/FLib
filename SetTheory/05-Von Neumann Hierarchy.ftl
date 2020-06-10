# 5-Von Neumann Hierarchy

# Here we define the function V of the Von Neumann Hierarchy and the rank function and proof the main properties.

# Main results:

# - V is a zffunction (forall alpha V[alpha] /in /VV)
# - Ordinal induction (as for complete induction this is a nice lemma, but Naproche cannot apply it since too many assumptions are needed, so we always just copy the proof)
# - beta /in alpha => (V[beta] /in V[alpha] /\ V[beta] /subset V[alpha] /\ Trans(V[alpha]))
# - V[alpha] /cap /Ord = alpha
# - /VV = /bigcup ran(V)
# - rk[x] = /bigcup rk+^[x]





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

Signature. x + y is a ZFset.
Signature. 0 is a ZFset.
Signature. 1 is a ZFset.

Axiom. Let alpha be a ZFset. alpha is an ordinal iff ( Trans(alpha) /\ forall y (y /in alpha => Trans(y) )).

Definition Trans. The class of transitives is
{ZFset x | Trans(x)}.
Let /Trans stand for the class of transitives.

Definition Ord. The class of ordinals is
{set x | x is an ordinal}.
Let /Ord stand for the class of ordinals.

Axiom. 0 = /emptyset.

Axiom. Let alpha be a ZFset. Then alpha + 1 is {ZFset x | x /in alpha \/ x = alpha }.

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

Axiom Infinity. Exists x (/emptyset /in x /\ forall y /in x ((y + 1) /in x) ).

Axiom. Let alpha be an ordinal. Then alpha + 1 is an ordinal.
Axiom. Let alpha be an ordinal. Let x be an object. Let x /in alpha. Then x is an ordinal.
Axiom. Forall alpha, beta (alpha /in beta \/ beta /in alpha \/ alpha = beta).
Axiom. Let A /subset /Ord. Let A /neq /emptyset. Then exists alpha (alpha /in A /\ forall beta /in A (alpha = beta \/ alpha /in beta)).
Axiom. Let alpha, beta be ordinals. Let alpha /in beta. Then alpha /subset beta.

Signature. Let alpha /in /Succ. alpha - 1 is an ordinal.

Axiom. Let alpha /in /Succ. Let beta be a zfset. alpha - 1 = beta iff alpha = beta + 1.

Axiom. Let x /in /Lim. Let y /in x. Then y + 1 /in x.




# Natural Numbers


[synonym number/-s]

Signature. A natural number is a notion.

Let k,l,m,n stand for natural numbers.

Axiom. Let n be a natural number. Then n is an ordinal.
Axiom. Let n be a natural number. Then n + 1 is a natural number.

Definition. The class of inductive sets is
{ZFSet x |  (/emptyset /in x /\ forall y /in x ((y + 1) /in x) ) }.
Let /Ind stand for the class of inductive sets.

Definition. The class of natnumbers is /bigcap /Ind.
Let /NN stand for the class of natnumbers.

Axiom. Let alpha be an ordinal. alpha is a natural number iff alpha /in /NN.

Axiom. /NN /in /Lim.

Axiom. 0, 1 are natural numbers.






# Von Neumann Hierarchy



Signature. V is a function.
Axiom. Dom(V) = /Ord.
Axiom. V[0] = /emptyset.
Axiom. Forall alpha /in /Ord (V[alpha] is a set).

Axiom. alpha /in /Ord => (V[alpha + 1] = {zfset x | x /subset V[alpha]}).
Axiom. Let lambda be an ordinal. Let lambda /in /Lim. Then V[lambda] = {ZFset x | exists alpha (alpha /in lambda /\ x /in V[alpha])}.

Lemma. V is a zffunction.
Proof.
Define phi[alpha] =
  Case V[alpha] /in /VV -> 0,
  Case V[alpha] /notin /VV -> 1
for alpha in /Ord.

phi[0] = 0.

Forall x /in /Ord (forall y /in x phi[y] = 0 => phi[x] = 0).
Proof.
  Let x /in /Ord. Let forall y /in x phi[y] = 0.
  Then x = 0 \/ x /in /Lim \/ x /in /Succ.
  Case x = 0. end.
  Case x /in /Succ. Take an ordinal y such that x = y+1. Then y /in x.
    Then V[y] /in /VV.
    Then V[x] = /PP V[y].
    Then V[x] /in /VV.
  end.
  Case x /in /Lim.
    Define f[alpha] = V[alpha] for alpha in x.
    Then f is a zffunction.
    V[x] = {ZFset y | exists alpha (alpha /in x /\ y /in V[alpha])}.
    Then V[x] /subset /bigcup f^[x].
    Proof.
      Let a /in V[x].
      Take a set alpha such that alpha /in x /\ a /in V[alpha].
      Then alpha /in x /\ a /in f[alpha].
      Then a /in /bigcup f^[x].
    end.
    Then V[x] /in /VV.
  end.
end.

Define M = {zfset z | z /in /Ord /\ phi[z] = 0}.
Then M /subset /Ord.
Let N = /Ord /setminus M.
Then N /neq /emptyset \/ N = /emptyset.
Case N = /emptyset. Then /Ord /subset M. M /subset /Ord. Then M = /Ord. end.
Case N /neq /emptyset.
Take a zfset a such that (a /in N /\ (forall y /in a y /notin N)).
Then forall y /in a phi[y] = 0.
Then phi[a] = 0.
Contradiction. end.

qed.



# Ordinal Induction

Lemma OrdinalInduction. Let phi be a function. Let /Ord /subset Dom(phi). Let forall x ((x /in /Ord /\ forall alpha /in x phi[alpha] = 0) => phi[x] = 0).
Then forall x ( x /in /Ord => phi[x] = 0).
Proof. Define M = {ordinal alpha | phi[alpha] = 0}.
Then /emptyset /in M. M /subset /Ord.
Let N = /Ord /setminus M.
Assume N /neq /emptyset.
Take a zfset x such that (x /in N /\ (forall y /in x y /notin N)).
Then forall y /in x phi[y] = 0.
Then phi[x] = 0.
Contradiction.
Then M = /Ord.
qed.

# Although this is a very useful lemma, there are too many parameters involved, too many assumtions need to be checked.
# Naproche cannot remember this lemma. The proof is not very hard, so we just copy the proof everytime we use ordinal induction (or some similiar induction
# where the essence is foundation).



Lemma. Let alpha, beta be ordinals. Let beta /in alpha. Then V[beta] /in V[alpha] /\ V[beta] /subset V[alpha] /\ Trans(V[alpha]).
Proof.

Define phi1[n] = 
  Case forall m /in n (V[m] /in V[n]) -> 0,
  Case exists m /in n (V[m] /notin V[n]) -> 1
for n in /Ord.

Define phi2[n] = 
  Case forall m /in n V[m] /subset V[n] -> 0,
  Case exists m /in n (V[m] /notin /PP V[n]) -> 1
for n in /Ord.

Define phi3[n] = 
  Case Trans(V[n]) -> 0,
  Case not Trans(V[n]) -> 1
for n in /Ord.

phi1[0] = phi2[0] = phi3[0] = 0.


Forall x /in /Ord (phi1[x] = phi2[x] = phi3[x] = 0).
Proof.

Forall x ((x /in /Ord /\ forall y /in x phi1[y] = phi2[y] = phi3[y] = 0) => phi1[x] = phi2[x] = phi3[x] = 0).
Proof. Let x /in /Ord. Let forall y /in x phi1[y] = phi2[y] = phi3[y] = 0.
  Then forall y /in x forall z /in y (V[z] /in V[y]/\ V[z] /subset V[y] /\ V[y] /in /Trans).
  Then forall z /in x (V[z] /in V[x]).
  Proof.
    Case x /in /Succ. Let y = x-1. Then V[x] = /PP V[y] /\ phi1[y] = phi2[y] = phi3[y] = 0.
      Let z /in x. Then z = y \/ z /in y.
      Then V[z] = V[y] \/ V[z] /subset V[y].
      Then V[z] /in V[x].
    end.
    Case x = /emptyset.
    end.
    Case x /in /Lim. Let z /in x.
      V[x] = {ZFset w | exists gamma (gamma /in x /\ w /in V[gamma])}.
      V[z] /in V[z+1].
      z+1 /in x.
      Proof. z+1 /subset x. z+1 /neq x. z+1 is an ordinal. x is an ordinal. 
      end.
      Then V[z + 1] /subset V[x].
      Then V[z] /in V[x].
    end.
    x /in /Lim \/ x /in /Succ \/ x = /emptyset.
  end.
  
  Forall z /in x (V[z] /subset V[x]).
  Proof.
    Case x /in /Lim. Let z /in x. Then V[z] /subset V[x].
    end.
    Case x = /emptyset.
    end.
    Case x /in /Succ. Let y = x-1. Then V[x] = /PP V[y] /\ phi1[y] = phi2[y] = phi3[y] = 0.
      Let z /in x. Then z = y \/ z /in y.
      Then V[z] /subset V[y].
      Let w /in V[z]. Then w /in V[y]. Then w /subset V[y].
      Then w /in V[x].
    end.
  end.
  
  Forall w /in V[x] (w /subset V[x]).
  Proof.
    Case x = /emptyset.
    end.
    Case x /in /Lim. V[x] = {ZFset w | exists gamma (gamma /in x /\ w /in V[gamma])}.
      Let w /in V[x]. Take a such that a /in x /\ w /in V[a].
      Then w /subset V[a].
      V[a] /subset V[x].
      Then w /subset V[x].
    end.
    Case x /in /Succ. Let y = x-1. Then V[x] = /PP V[y] /\ phi1[y] = phi2[y] = phi3[y] = 0.
      Let w /in V[x]. Then w /subset V[y].
      V[y] /subset V[x].
      Then w /subset V[x].
    end.
  end.
  Then Trans(V[x]).
end.


Forall x /in /Ord phi1[x] = phi2[x] = phi3[x] = 0.
Proof.
Define M = {ordinal y | phi1[y] = phi2[y] = phi3[y] = 0}.
Then /emptyset /in M. M /subset /Ord.
Let N = /Ord /setminus M.
Assume N /neq /emptyset.
Take a zfset x such that (x /in N /\ (forall y /in x y /notin N)).
Then forall y /in x phi1[y] = phi2[y] = phi3[y] = 0.
Then phi1[x] = phi2[x] = phi3[x] = 0.
Contradiction.
Then M = /Ord.
end.

end.

qed.



Lemma. Forall alpha /in /Ord V[alpha] /cap /Ord = alpha.
Proof.
Define phi[n] = 
  Case V[n] /cap /Ord = n -> 0,
  Case V[n] /cap /Ord /neq n -> 1
for n in /Ord.

phi[0] = 0.

Forall x /in /Ord (phi[x] = 0).
Proof.
  Forall x ((x /in /Ord /\ forall y /in x phi[y] = 0) => phi[x] = 0).
  Proof.
    Let x /in /Ord. Let forall y /in x phi[y] = 0.
    Trans(V[x]).
    Then Trans(V[x] /cap /Ord).
    V[x] /in /VV.
    Then V[x] /cap /Ord /in /VV.
    Proof.
      V[x] /cap /Ord /subset V[x].
    end.
    Then (V[x] /cap /Ord) /in /Ord.
    Take an ordinal delta such that delta = V[x] /cap /Ord.
    Case x = /emptyset.
    end.
    Case x /in /Succ. Let y = x-1.
      Then V[x] = /PP V[y].
      V[y] /cap /Ord = y.
      Then y /in delta.
      Then y + 1 /subset delta.
      Then x = delta.
      Proof by contradiction.
        Assume the contrary. Then x /neq delta.
        Then x /in delta.
        Then x /subset V[y].
        Contradiction.
      end.
    end.
    Case x /in /Lim. Then V[x] = {ZFset y | exists alpha (alpha /in x /\ y /in V[alpha])}.
      Forall y /in x (y = V[y] /cap /Ord).
      Forall y /in x (y + 1 /in x).
      Forall y /in x (y /in V[y+1]).
      Then x /subset V[x].
      Then x /subset delta.
      Then x = delta.
      Proof by contradiction. Assume the contrary.
        Then x /neq delta.
        Then x /in delta.
        Then exists alpha /in x (x /in V[alpha]).
        Contradiction.
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
  
end.
qed.


Lemma. Forall x /in /VV (x /subset /bigcup ran(V) => exists beta x /subset V[beta]).
Proof.
Let x /subset /bigcup ran(V). Let x /in /VV.
Define f[y] = choose an ordinal gamma such that y /in V[gamma] in gamma for y in x.
Define g[y] = f[y] + 1 for y in x.
Then f,g are zffunctions.
Let a = /bigcup g^[x].
Then a /in /VV.
Trans(a).
Proof. Let b /in a. Take y /in x such that b /in g[y].
  g[y] /in /Ord.
  Let c /in b. Then c /in g[y].
  Then c /in /bigcup g^[x].
  Then c /in a.
end.
Forall b /in a b /in /Ord.
Proof. Let b /in a. Take y such that y /in x /\ b /in g[y]. g[y] /in /Ord. Then b /in /Ord.
end.
Then a /in /Ord.
Then x /subset V[a].
Proof.
  Let y /in x. Then y /in V[f[y]]. f[y] /in g[y]. Then f[y] /in /bigcup g^[x]. Then f[y] /in a.
  Then V[f[y]] /subset V[a].
  Then y /in V[a].
end.
qed.


Lemma. /VV = /bigcup ran(V).
Proof by contradiction. Assume the contrary.
Let A = /bigcup ran(V). Let B = /VV /setminus A.
Then B /neq /emptyset.
Take a zfset x such that (x /in B /\ forall y /in x y /notin B).
Then x /subset /bigcup ran(V).
Take an ordinal beta such that x /subset V[beta].
Then x /in V[beta + 1].
V[beta + 1] /in ran(V).
Then x /in A.
Contradiction.
qed.










# Rank Function

Signature. rk is a function.
Signature. rk+ is a function.
Axiom. rk : /VV /rightarrow /Ord.
Axiom. rk+ : /VV /rightarrow /Ord.
Lemma. rk, rk+ are zffunctions.
Lemma. Let x /in /VV. Then rk[x] /in /Ord.
Axiom. Let x /in /VV. Then rk[x] = alpha iff x /in V[alpha + 1] /setminus V[alpha].
# Note that this is well-defined.
Axiom. Forall x /in /VV rk+[x] = rk[x] + 1.
Lemma. Let x /in /VV. Let rk[x] = alpha. Then x /notin V[alpha]. 

Lemma. Let x /in y. Then rk[x] /in rk[y].
Proof. Take ordinals alpha, beta such that alpha = rk[x] /\ beta = rk[y].
  Then y /in V[beta + 1].
  Then y /subset V[beta].
  Then x /in V[beta].
  Then rk[x] /neq beta.
  Then alpha /neq beta.
  Then alpha /in beta \/ beta /in alpha.
  Case beta /in alpha. Then V[beta] /subset V[alpha]. Contradiction.
  end.
  Then alpha /in beta.
qed.



Lemma. Forall x /in /VV (rk[x] = /bigcup rk+^[x]).

Proof.
Forall alpha /in /Ord forall x /in V[alpha] (rk[x] = /bigcup rk+^[x]).

Proof.
  Define phi[alpha] = 
    Case forall x /in V[alpha] (rk[x] = /bigcup rk+^[x]) -> 0,
    Case exists x /in V[alpha] (rk[x] /neq /bigcup rk+^[x]) -> 1
  for alpha in /Ord.

  phi[0] = 0.

  Forall alpha ((alpha /in /Ord /\ forall beta /in alpha phi[beta] = 0) => phi[alpha] = 0).
  Proof.
    Let alpha /in /Ord /\ forall beta /in alpha phi[beta] = 0.
    Case alpha = /emptyset.
    end.
    Case alpha /in /Lim.
      Then forall x /in V[alpha] (rk[x] = /bigcup rk+^[x]).
      Proof.
        Let x /in V[alpha]. Take beta /in alpha such that x /in V[beta].
        Then (rk[x] = /bigcup rk+^[x]).
      end.
      Then phi[alpha] = 0.      
    end.
    Case alpha /in /Succ. Take a zfset beta such that alpha = beta+1.
      Then forall x /in V[alpha] (rk[x] = /bigcup rk+^[x]).
      Proof.
        Let x /in V[alpha].
        Case x /in V[beta].
        end.
        Case x /notin V[beta]. Then x /in V[beta + 1] /setminus V[beta]. 
          Forall a /in /VV forall b /in /Ord (rk[a] = b iff a /in V[b + 1] /setminus V[b]).
          Then rk[x] = beta.
          Then /bigcup rk+^[x] /subset beta.
          Proof.
            Let z /in /bigcup rk+^[x]. Take y such that (y /in x /\ z /in rk+[y]).
            Take an ordinal gamma such that gamma = rk[y].
            Then rk[y] /in rk[x].
            Then gamma /in beta.
            Then z /in beta.
          end.
          Let delta = /bigcup rk+^[x].
          Then Trans(delta).
          Proof.
            rk+^[x] /subset /Ord.
            Then Trans(/bigcup rk+^[x]).
          end.
          Then delta /in /Ord.
          Then delta /in beta \/ delta = beta.
          Assume delta /in beta.
            x /subset V[delta].
            Proof.
              Let y /in x. 
              Then rk+[y] /subset delta.
              Proof. rk+[y] /subset /bigcup rk+^[x].
              end.
              y /in V[rk+[y]].
              Proof. y /in /VV. Take an ordinal gamma such that gamma = rk[y].
                Then y /in V[gamma + 1].
              end.
              Then y /in V[delta].
              Proof. rk+[y] /in delta \/ rk+[y] = delta.
                Case rk+[y] /in delta.
                  Then V[rk+[y]] /subset V[delta].
                end.
              end.
            end.
            Then x /in V[delta + 1].
            Then x /in V[beta].
            Proof. delta /in beta. Then delta + 1 /subset beta.
              Take an ordinal delta1 such that delta1 = delta + 1.
              Forall m,n /in /Ord (m /in n \/ n /in m \/ n = m).
              delta1, beta /in /Ord.
              Then delta1 = beta \/ delta1 /in beta \/ beta /in delta1.
              beta /notin delta1.
              Then delta + 1 = beta \/ delta + 1 /in beta.
              Case delta + 1 = beta. end.
              Case delta + 1 /in beta. Then V[delta + 1] /subset V[beta]. end.
            qed.
            Contradiction.
          Then delta = beta.
        end.
      end.
      Then phi[alpha] = 0.
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

end.

Let x /in /VV. Take an ordinal alpha such that x /in V[alpha].
Then rk[x] = /bigcup rk+^[x].

qed.






Lemma. Contradiction.




