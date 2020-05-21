# 4-Cardinals Part 1.

# Starting here we always distinguish between sets and classes since we saw how fast we lead towards a contradiction.
# And we always use the integrated ordered pairs and functions, since it will safe much computing space.
# Otherwise Naproche gets confused very quickly. We only need basic properties of functions: a domain and values
# for every element of the domain. So there is no need to use the existence of a certain ordered pair in the function
# to know if an element is in the domain and which value the function takes on this object.

# Since we now have functions we can state the axiom of replacement.
# But again we have to be careful - the integrated functions are defined very freely, so not all functions we can write down
# are set theoretic functions. The main problem is that the values might be proper classes, so we come to a contradiction
# if we define the image/range of all functions. And replacement obviously is also wrong.
# So we introduce the notion of zffunctions which are functions such that every value is in /VV.
# Just an axiom stating that every value of every function is a zfset won't work, since functions are already implemented,
# so we can easyly proof a contradiction by just wrting down a function such that this axiom does not hold.

# So we continue with our results of section 1. We introduce cardinals and proof some more or less basic facts of cardinals and cardinalities which are sometimes very tedious to proof.

# Main results:

# - Complete Induction on /NN (although this lemma has too many assumptions, so it is easier to just reproof this when needed instead of linking to this lemma, Naproche quickly forgets about this lemma or cannot apply it since it is too long)
# - We introduce f^n for certain functions and show some basic facts
# - being equipotent is an equivalence relation
# - Card(kappa) = kappa for cardinals kappa
# - x /subset y => Card(x) /subset Card(y) (very tedious to formally proof this)
# - (x <= y /\ y <= x) <=> (Card(x) = Card(y))
# - forall n /in /NN Card(n) = n
# - Card(/NN) = /NN
# - x < /PP x
# - /Card is a proper class






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
Lemma. Let f and g be zffunctions. f = g iff Dom(f) = Dom(g) and forall x /in Dom(f) (f[x] = g[x]).


Definition. Let f be an injective zffunction. The inverse of f is a function g such that
Dom(g) = ran(f) and (forall x /in ran(f) forall y /in Dom(f) (g[x] = y iff f[y] = x)).
Let f^{-1} stand for the inverse of f.
Lemma. Let f be an injective zffunction. Then f^{-1} is a zffunction.

Lemma. Let f be a zffunction. Let A,B be sets. Let f : A /leftrightarrow B.
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

Lemma. Forall x /in /VV x /notin x.
Lemma. Let x /in /VV. Then <x> /in /VV.
Proof. <x> = <x,x>. qed.
Lemma. Let x,y /in /VV. Then x /cup y /in /VV.
Proof. x /cup y = /bigcup <x,y>. qed.






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

Lemma. Let x be an ordinal. Then x = /emptyset \/ x /in /Succ \/ x /in /Lim.

Axiom Infinity. Exists x (/emptyset /in x /\ forall y /in x ((y + 1) /in x) ).

Axiom. Let alpha be an ordinal. Then alpha + 1 is an ordinal.
Axiom. Let alpha be an ordinal. Let x be an object. Let x /in alpha. Then x is an ordinal.
Axiom. Forall alpha, beta (alpha /in beta \/ beta /in alpha \/ alpha = beta).

Lemma. Let x /in /Lim. Let y /in x. Then y + 1 /in x.
Proof. y + 1 /subset x. y + 1 /neq x. x /notin y + 1. x, y+1 are ordinals.
qed.

Axiom. Let A /subset /Ord. Let A /neq /emptyset. Then exists alpha (alpha /in A /\ forall beta /in A (alpha = beta \/ alpha /in beta)).
Axiom. Let alpha, beta be ordinals. Let alpha /in beta. Then alpha /subset beta.

Signature. Let A be a set. The minimum of A is a notion.

Axiom.  Let A /subset /Ord. Let A /neq /emptyset. Let alpha be an object. alpha is the minimum of A iff (alpha /in A /\ forall beta /in A (alpha = beta \/ alpha /in beta)).

Lemma. Let A /subset /Ord. Let A /neq /emptyset. Let alpha, beta be ordinals. Let alpha, beta be the minimum of A. Then alpha = beta.

Lemma. Let A /subset /Ord. Let A /neq /emptyset. The minimum of A is an ordinal.

Lemma. Let A /subset /Ord. Let A /neq /emptyset. /bigcap A is the minimum of A.
Proof. Let alpha = /bigcap A.
alpha is an ordinal.
  Proof.  alpha is a ZFset.
          alpha is transitive.
          Proof. Let beta /in alpha. Then forall x /in A beta /in x.
            Let gamma /in beta. Then forall x /in A gamma /in x.
            Then gamma /in alpha.
          end.
  end.
Forall beta /in A (alpha = beta \/ alpha /in beta).
alpha /in A.
qed.

Signature. Let alpha /in /Succ. alpha - 1 is an ordinal.

Axiom. Let alpha /in /Succ. Let beta be a zfset. alpha - 1 = beta iff alpha = beta + 1.
Lemma. 0 = 1 - 1.







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

Lemma. Let n /neq /emptyset. Let n /in /NN. Then n /in /Succ.
Proof. Define M = {ordinal alpha | alpha /in /NN /\ (alpha = /emptyset \/ alpha /in /Succ)}.
Then M /in /Ind.
  Proof. /emptyset /in M.
    Let y /in M. Then y /in /NN. Then ((y + 1) /in /NN /\ (y + 1) /in /Succ).
    Then (y + 1) /in M.
  end.
Then M = /NN.
qed.


Lemma CompleteInduction. Let phi be a function. Let /NN /subset Dom(phi).
Let phi[0] = 0. Let forall n /in /NN (phi[n] = 0 => phi[n + 1] = 0). Then forall n /in /NN phi[n] = 0.
Proof. Define M = {ordinal n | n /in /NN /\ phi[n] = 0}.
Then M /in /Ind.
  Proof. /emptyset /in M.
    Forall y /in M ((y + 1) /in M).
    Proof.
      Let y be an object. Let y /in M. Then y /in /NN. Then phi[y] = 0. Then phi[y + 1] = 0. Then y + 1 /in M.
    end.
    M is a ZFset.
  end.
Then /NN = M.
qed.


Signature. f ^ n is an object.
Axiom. Let f be a zffunction. Let ran(f) /subset Dom(f). Let n /in /NN. Then f ^ n is a function.
Axiom. Let f be a zffunction. Let ran(f) /subset Dom(f). Let n /in /NN. Then Dom(f^n) = Dom(f).
Axiom. Let f be a zffunction. Let ran(f) /subset Dom(f). Let x /in Dom(f). Then (f^0)[x] = x.
Axiom. Let f be a zffunction. Let ran(f) /subset Dom(f). Let n /in /NN. Let x /in Dom(f). Then (f^n)[x] /in Dom(f) /\ (f^(n+1))[x] = f[((f^n)[x])].

Lemma. Let f be a zffunction. Let ran(f) /subset Dom(f). Then forall n /in /NN (f^n is a zffunction).
Proof.
Define phi[n] =
  Case f^n is a zffunction -> 0,
  Case f^n is not a zffunction -> 1
for n in /NN.

Then phi[0] = 0.
Proof.
  Let x /in Dom(f^0). Then (f^0)[x] = x. Then (f^0)[x] /in /VV.
end.

Forall n /in /NN (phi[n] = 0 => phi[n+1] = 0).
Proof.
  Let n /in /NN. Let phi[n] = 0. Then f^n is a zffunction.
  Then f^(n+1) is a zffunction.
  Proof.
    Let x /in Dom(f^(n+1)). Then (f^(n+1))[x] = f[((f^n)[x])].
    Then (f^(n+1))[x] /in /VV.
  end.
end.

Define M = {ordinal n | n /in /NN /\ phi[n] = 0}.
Then /emptyset /in M /\ forall n /in M (n+1) /in M.
Then M /in /Ind.
Then M = /NN.
Then forall n /in /NN (f^n is a zffunction).

qed.

Lemma. Let f be a zffunction. Let ran(f) /subset Dom(f). Then forall n /in /NN ((f^n is a zffunction) /\ (ran(f^n) /subset Dom(f))).
Proof.
Define phi[n] =
  Case ran(f^n) /subset Dom(f) -> 0,
  Case not (ran(f^n) /subset Dom(f)) -> 1
for n in /NN.
Then phi[0] = 0.
Proof.
  Let x /in ran(f^0). Take a set y such that y /in Dom(f) /\ (f^0)[y] = x.
  (f^0)[y] = y.
  Then x = y.
  Then x /in Dom(f).
end.
Forall n /in /NN (phi[n] = 0 => phi[n+1] = 0).
Proof.
  Let n /in /NN. Let phi[n] = 0.
  Let x /in ran(f^(n+1)). Take a set y such that y /in Dom(f) /\ (f^(n+1))[y] = x.
  (f^(n+1))[y] = f[((f^n)[y])].
  Then (f^(n+1))[y] /in ran(f).
  Then (f^(n+1))[y] /in Dom(f).
end.

Define M = {ordinal n | n /in /NN /\ phi[n] = 0}.
Then /emptyset /in M /\ forall n /in M (n+1) /in M.
Then M /in /Ind.
Then M = /NN.
Then forall n /in /NN (ran(f^n) /subset Dom(f)).

qed.



Lemma. Let f be a zffunction. Let ran(f) /subset Dom(f). Then (f ^ 1) = f.
Proof.
  Let g, h be functions. g = h iff (Dom(g)=Dom(h) /\ forall x /in Dom(g) g[x] = h[x]).
  f, (f ^ 1) are zffunctions.
  Dom(f) = Dom((f^1)).
  Forall x /in Dom(f) (f[x] = (f ^ 1)[x]).
  Proof.
  Let x /in Dom(f).
  Then (f^1)[x] = f[((f^0)[x])].
  Proof. 1 = 0+1.
    Then (f^1)[x] = (f^(0+1))[x].
    Forall n /in /NN (f^(n+1))[x] = f[((f^n)[x])].
  end.
  f[(f^0)[x]] = f[x].
  Then (f^1)[x] = f[x].
  end.
qed.

Lemma. Let f be a zffunction. Let ran(f) /subset Dom(f). Let n /in /NN. Let n /neq /emptyset. Then ran(f ^ n) /subset ran(f).
Proof.
Forall k /in /NN forall x /in Dom(f) ((f^k)[x] /in Dom(f) /\ (f^(k+1))[x] = f[((f^k)[x])]). 
Take an ordinal m such that n = m+1. Then m /in /NN. Let x /in Dom(f). Then (f^(m+1))[x] = f[((f^m)[x])].
qed.







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

Lemma.  Let x, y be equipotent. Then y and x are equipotent.
Proof. Take a zffunction f such that f : x /leftrightarrow y.
Then f^{-1} : y /leftrightarrow x.
qed.

Lemma. Let x,y be equipotent. Let y,z be equipotent. Then x,z are equipotent.
Proof. Take a zffunction f such that f : x /leftrightarrow y.
Take a zffunction g such that g : y /leftrightarrow z.
Then g /circ f : x /leftrightarrow z.
Proof.  g /circ f is a function.
        g /circ f is injective.
        Dom(g /circ f) = x.
        ran (g /circ f) = z.
end.
qed.

Lemma. Let x, y be zfsets. x /tilde y => (x <= y /\ y <= x).
Proof.
Let x /tilde y. Take a zffunction f such that f : x /leftrightarrow y.
Then x <= y.
f^{-1} : y /leftrightarrow x.
Then y <= x.
qed.

Lemma. Let x, y, z be ZFsets. Let x <= y /\ y <= z. Then x <= z.
Proof.
Take an injective zffunction f such that f : x /rightarrow y.
Take an injective zffunction g such that g : y /rightarrow z.
Then g /circ f : x /rightarrow z. g /circ f is injective.
qed.

Lemma. Let x,y be ZFsets. Let x /subset y. Then x <= y.
Proof.
Define f[n] = n for n in x.
Then f is a zffunction.
f : x /rightarrow y. f is injective.
qed.

Definition. Let x be a zfset. The cardset of x is 
{ordinal alpha | exists f (f : alpha /leftrightarrow x) }.
Let Cardset(x) stand for the cardset of x.

Definition. Let x be a zfset. The cardinality of x is /bigcap Cardset(x).
Let Card (x) stand for the cardinality of x.

Axiom. Let A be a set. Let A /subset /Ord. Let A /neq /emptyset.
Then /bigcap A is an ordinal.

Lemma. Let x be a zfset. The cardinality of x is an ordinal.
Proof. Cardset(x) /subset /Ord. Cardset(x) /neq /emptyset.
qed.

Lemma. Let x be a zfset. Then Card(x) /in Cardset(x).
Proof. Card(x) is an ordinal.
  Take a set b such that (b /in Cardset(x) /\ forall c /in b c /notin Cardset(x)).
  Then Card(x) = b.
qed.


Lemma. Let x, y be zfsets. Let x /tilde y. Then Card(x) = Card(y).
Proof.
Take an ordinal alpha such that alpha = Card(x).
Take an ordinal beta such that beta = Card(y).
Then alpha /in beta \/ beta /in alpha \/ alpha = beta.

Take a zffunction f such that f : alpha /leftrightarrow x.
Take a zffunction g such that g : beta /leftrightarrow y.
Take a zffunction h such that h : x /leftrightarrow y.

Then h /circ f : alpha /leftrightarrow y.
Proof.
  Dom(h /circ f) = alpha.
  ran(h /circ f) = y.
  h /circ f is injective.
end.
Then Card(y) /subset alpha.

Then h^{-1} /circ g : beta /leftrightarrow x.
Proof.
  Dom(h^{-1} /circ g) = beta.
  ran(h^{-1} /circ g) = x.
  h^{-1} /circ g is injective.
end.
Then Card(x) /subset beta.

Then alpha = beta.

qed.


Lemma. Let x, y be zfsets. Let Card(x) = Card(y). Then x /tilde y.
Proof.
Take an ordinal kappa such that kappa = Card(x).
Take a zffunction f such that f : kappa /leftrightarrow x.
Take a zffunction g such that g : kappa /leftrightarrow y.
Then f^{-1} : x /leftrightarrow kappa.
Then g /circ f^{-1} : x /leftrightarrow y.
Proof.
  g /circ f^{-1} : x /rightarrow y.
  g /circ f^{-1} is injective.
  ran(g /circ f^{-1}) = y.
end.
qed.





[synonym cardinal/-s]
Signature. A cardinal is a notion.

Axiom. Let kappa be a cardinal. Then kappa is an ordinal.
Axiom. Let kappa be an ordinal. kappa is a cardinal iff exists x (kappa = Card(x)).

Let kappa stand for a cardinal.

Definition. The class of cardinals is
{ordinal alpha | alpha is a cardinal}.
Let /Card stand for the class of cardinals.

Lemma. Card(/emptyset) = /emptyset.

Lemma. Let alpha be an ordinal. Then Card(alpha) /subset alpha.
Proof. Id /upharpoonright alpha : alpha /leftrightarrow alpha.
qed.

Lemma. Let kappa be a cardinal. Then Card(kappa) = kappa.
Proof. Card(kappa) /subset kappa.
  Then Card(kappa) /in kappa \/ Card(kappa) = kappa.
  Take a zfset x such that kappa = Card(x).
  Take a zffunction f such that f : kappa /leftrightarrow x.
  Take a zffunction g such that g : Card(kappa) /leftrightarrow kappa.
  Then f /circ g : Card(kappa) /leftrightarrow x.
  Proof. Dom(f /circ g) = Card(kappa).
    ran(f /circ g) = x.
    f /circ g is injective.
  end.
  Then Card(x) /subset Card(kappa).
qed.


Lemma. Let alpha be a cardinal. Let x be a zfset. Let x /subset alpha. Then Card(x) /subset alpha.

Proof by contradiction. Assume the contrary. Then Card(alpha) /in Card(x).
Define f[n] = f /caret [n /cap x] for n in x.
# This is an unusual definition. How do we know that this is welldefined?
# We can easily proof this using foundation, but Naproche surely doesn't know this.
Then Dom(f) = x.
Then f is a zffunction.
Proof.
  Forall y /in x (forall z /in y /cap x f[z] /in /VV => f[y] /in /VV).
  Proof.
    Let y /in x. Let forall z /in y /cap x f[z] /in /VV.
    Define g[z] = f[z] for z in y /cap x.
    Then g is a zffunction.
    Then f[y] = g^[y /cap x].
    Then f[y] /in /VV.
  end.
  Define A = {zfset y | y /in x /\ f[y] /notin /VV}.
  Case A = /emptyset. Then f is a zffunction. end.
  Case A /neq /emptyset.
    Take a set b such that b /in A /\ forall c /in b c /notin A.
    Then b /in x /\ forall z /in b /cap x f[z] /in /VV.
    Then f[b] /in /VV.
    Contradiction.
  end.
end.

Forall n /in x f[n] = f^[n /cap x].
Proof.
  f is a zffunction.
  Then forall a f /caret [a] = f^[a].
  Let n /in x. Then f[n] = f^[n /cap x].
end.


Take a zfset zero such that (zero /in x /\ forall c /in zero (c /notin x)).
Then f[zero] = /emptyset.

Forall y /in x f[y] /in /Ord.
Proof.
  Define phi[n] =
    Case f[n] /in /Ord -> 0,
    Case f[n] /notin /Ord -> 1
  for n in x.
  phi[zero] = 0.
  Forall y /in x (forall z /in (y /cap x) phi[z] = 0 => phi[y] = 0).
  Proof.
    Let y /in x. Let forall z /in (y /cap x) phi[z] = 0.
    f[y] = f^[y /cap x].
    Then f[y] /subset /Ord.
    Proof. Let a /in f[y]. Take a zfset z such that z /in (y /cap x) /\ a = f[z].
      Then phi[z] = 0.
      Then f[z] /in /Ord.
    end.
    Forall a /in f[y] forall b /in a (b /in f[y]).
    Proof.
      Let a /in f[y]. Take a zfset z1 such that z1 /in (y /cap x) /\ a = f[z1].
      Let b /in a. Then b /in f[z1]. f[z1] = f^[z1 /cap x].
      Take a zfset z2 such that z2 /in (z1 /cap x) /\ b = f[z2].
      Then b /in f[y].
    end.
    Then Trans(f[y]).
    f[y] /in /VV.
    Proof.
      f[y] = f^[y /cap x].
      Forall z /in y /cap x f[z] /in /VV.
      y /cap x /in /VV.
      Then f^[y /cap x] /in /VV.
    end.
    Forall z /in f[y] Trans(z).
    f[y] /in /Ord.
    Then phi[y] = 0.
  end.

  Define M = {ordinal gamma | gamma /in x /\ phi[gamma] = 0}.
  Then M /subset x.
  Let N = x /setminus M.
  Then N /neq /emptyset \/ N = /emptyset.
  Case N = /emptyset. Then x /subset M. M /subset x. Then x = M. end.
  Case N /neq /emptyset.
  Take a zfset a such that (a /in N /\ (forall y /in a y /notin N)).
  Then forall y /in a /cap x phi[y] = 0.
  Then phi[a] = 0.
  Contradiction. end.

end.

Then ran(f) /subset /Ord.
ran(f) /in /VV.
Proof.
  ran(f) = f^[x].
end.
Forall a /in ran(f) forall b /in a (b /in ran(f)).
Proof.
  Let a /in ran(f). Take a zfset z1 such that z1 /in x /\ a = f[z1].
  Let b /in a. Then b /in f[z1]. f[z1] = f^[z1 /cap x].
  Take a zfset z2 such that z2 /in (z1 /cap x) /\ b = f[z2].
  Then b /in ran(f).
end.
Then Trans(ran(f)).
Then ran(f) /in /Ord.

Forall y,z /in x (y /neq z => f[y] /neq f[z]).
Proof. let y, z /in x. Let y /neq z.
  Then y /in z \/ z /in y.
  f[y] /neq f[z].
  Proof by contradiction. Assume the contrary.
    Then f[y] = f[z].
    Forall c (c /notin c).
    Case y /in z. Then f[y] /in f[z]. Then f[y] /in f[y]. Contradiction. end.
    Case z /in y. Then f[z] /in f[y]. Then f[z] /in f[z]. Contradiction. end.
    Contradiction.
  end.
end.

f : x /leftrightarrow ran(f).


Forall y /in x f[y] /subset y.
Proof.
  Define phi[n] =
    Case f[n] /subset n -> 0,
    Case f[n] /notin /PP n -> 1
  for n in x.
  phi[zero] = 0.
  Forall y /in x (forall z /in (y /cap x) phi[z] = 0 => phi[y] = 0).
  Proof.
    Let y /in x. Let forall z /in (y /cap x) phi[z] = 0.
    f[y] = f^[y /cap x].
    Let z /in f[y]. Take a zfset a such that a /in y /cap x /\ z = f[a].
    Then f[a] /subset a.
    Then z /subset a.
    a,y,z /in /Ord.
    z /subset a /\ a /in y.
    Forall m,n /in /Ord (m /in n \/ n /in m \/ m = n).
    Then z /in y.
  end.

  Define M = {ordinal gamma | gamma /in x /\ phi[gamma] = 0}.
  Then M /subset x.
  Let N = x /setminus M.
  Then N /neq /emptyset \/ N = /emptyset.
  Case N = /emptyset. Then x /subset M. M /subset x. Then x = M. end.
  Case N /neq /emptyset.
  Take a zfset a such that (a /in N /\ (forall y /in a y /notin N)).
  Then forall y /in a /cap x phi[y] = 0.
  Then phi[a] = 0.
  Contradiction. end.

end.

Then ran(f) /subset alpha.

f^{-1} : ran(f) /leftrightarrow x.

Then Card(x) /subset ran(f).
Then Card(x) /subset alpha.

qed.



Lemma. Let x /subset y. Then Card(x) /subset Card(y).
Proof.
Take cardinals alpha, beta such that alpha = Card(x) /\ beta = Card(y).
Take a zffunction f such that f : alpha /leftrightarrow x.
Take a zffunction g such that g : beta /leftrightarrow y.
Then g^{-1} : y /leftrightarrow beta.
Then (g^{-1}) /circ f : alpha /rightarrow beta.

Define h[n] = ((g^{-1}) /circ f)[n] for n in alpha.
Then h is a zffunction.
Then h = (g^{-1}) /circ f.
Proof. Dom(h) = Dom((g^{-1}) /circ f).
  Forall z /in Dom(h) h[z] = ((g^{-1}) /circ f)[z].
qed.

Then h : alpha /rightarrow beta.
Then ran(h) /subset beta.
h : alpha /leftrightarrow ran(h).
h^{-1} : ran(h) /leftrightarrow alpha.
Then Card(ran(h)) /subset beta.

Take a cardinal gamma such that gamma = Card(ran(h)).
Take a zffunction i such that i : gamma /leftrightarrow ran(h).
Then (h^{-1}) /circ i : gamma /leftrightarrow alpha.
Proof.
  Dom((h^{-1}) /circ i) = gamma.
  ran((h^{-1}) /circ i) = alpha.
  (h^{-1}) /circ i is injective.
end.

Define j[n] = ((h^{-1}) /circ i)[n] for n in gamma.
Then j is a zffunction.
Then j = (h^{-1}) /circ i.
Proof. Dom(j) = Dom((h^{-1}) /circ i).
  Forall z /in Dom(j) j[z] = ((h^{-1}) /circ i)[z].
end.

Then j : gamma /leftrightarrow alpha.
Then f /circ j : gamma /leftrightarrow x.
Proof.
  Dom(f /circ j) = gamma.
  ran(f /circ j) = x.
  f /circ j is injective.
end.
Then Card(x) /subset gamma.
Then Card(x) /subset beta.

qed.


Lemma. Let x, y be zfset. Let x <= y. Then Card(x) /subset Card(y).
Proof.
Take an injective zffunction f such that f : x /rightarrow y.
Then f : x /leftrightarrow ran(f).
Then Card(x) = Card(ran(f)).
ran(f) /subset y.
Then Card(ran(f)) /subset Card(y).
Then Card(x) /subset Card(y).
qed.


Lemma. Let x, y be zfsets. Let x <= y. Let y <= x. Then Card(x) = Card(y).
Proof.
Card(x) /subset Card(y).
Card(y) /subset Card(x).
qed.

Lemma. Let x, y be zfsets. Let x <= y. Let y <= x. Then x /tilde y.
Proof.
Take a zffunction f such that f : Card(x) /leftrightarrow x.
Take a zffunction g such that g : Card(y) /leftrightarrow y.
Card(x) = Card(y).
g : Card(x) /leftrightarrow y.
f^{-1} : x /leftrightarrow Card(x).
Then g /circ f^{-1} : x /leftrightarrow y.
Proof.
  g /circ f^{-1} : x /rightarrow y.
  ran(g /circ f^{-1}) = y.
  g /circ f^{-1} is injective.
end.
qed.


Lemma. Let x be a zfset. Let f be a zffunction. Let x /subset Dom(f). Then Card(f^[x]) /subset Card(x).
Proof.
Forall n /in f^[x] exists y /in x (f[y] = n).
Define g[n] = (Choose a zfset y such that y /in x /\ f[y] = n in y) for n in f^[x].
Then g : f^[x] /rightarrow x.
g is injective.
Then f^[x] <= x.
qed.




Lemma. Forall n /in /NN Card(n) = n.
Proof.
Define phi[n] = 
  Case Card(n) = n -> 0,
  Case Card(n) /neq n -> 1
for n in /NN.
phi[/emptyset] = 0.
        
Forall n /in /NN (phi[n] = 0 => phi[n+1] = 0).
Proof.
  Let n /in /NN. Let phi[n] = 0. Then Card(n) = n.
  Card(n + 1) = (n + 1) \/ Card(n + 1) /in (n + 1).
  Proof. Id /upharpoonright (n + 1) : (n + 1) /leftrightarrow (n + 1).
    Then n + 1 /in Cardset(n + 1).
    Then Card(n+1) /subset (n + 1).
  end.
  Case Card(n + 1) = (n + 1). Then phi[n + 1] = 0.
  end.
  Case Card(n + 1) /in (n + 1).
    Take an ordinal m such that Card(n + 1) = m. Take a zffunction f such that f : m /leftrightarrow (n + 1).
    Take a set i  such that (i /in m /\ f[i] = n).
    m /neq /emptyset.
    m /in /NN.
    Case i = m - 1.
      Then f /upharpoonright (m - 1) : (m - 1) /leftrightarrow n.
      Proof. f /upharpoonright (m - 1) : (m - 1) /rightarrow (n + 1).
        ran(f /upharpoonright (m - 1)) = {f[j] | j /in (m - 1)}.
        Forall j /in (m - 1) f[j] /neq n.
        Proof. Assume the contrary. Take j /in (m - 1) such that f[j] = n.
          Then j /neq i. f[i] = f[j] = n. Contradiction.
        end.
        Then n /notin ran(f /upharpoonright (m - 1)).
        Then ran(f /upharpoonright (m - 1)) /subset n.
        f /upharpoonright (m - 1) is injective.
        ran(f /upharpoonright (m - 1)) = n.
        Proof. Let alpha /in n. Take j /in m such that (f[j] = alpha).
          Then j /neq (m - 1).
          Then j /in (m - 1).
          Then j /in ran(f /upharpoonright (m - 1)).
        end.

      end.
      Then Card(n) /subset (m - 1).
      Then Card(n) /in n.
      Then Card(n) /neq n.
      Contradiction.
    end.

    Case i /neq (m - 1).
      Then i /in (m - 1).
      Define g[j] =
        Case i /neq j -> f[j],
        Case i = j -> f[m-1]
      for j in (m - 1).
      Then g is a zffunction.
      Then g : (m - 1) /leftrightarrow n.
      Proof.
        g : (m - 1) /rightarrow (n + 1).
        Proof.
          Dom(g) = m-1.
          Forall j /in (m-1) g[j] /in (n+1).
        end.
        ran(g) = {f[j] | j /in m /\ j /neq i}.
        Forall j /in m (j /neq i => f[j] /neq n).
        Then ran(g) /subset n.
        ran(g) = n.
        Forall j,k /in (m - 1) (g[j] = g[k] => j = k).
        Proof.
          Let j,k /in (m - 1). Let g[j] = g[k].
          Case j /neq i /\ k /neq i.
            Then g[j] = f[j] /\ g[k] = f[k].
            Then j = k.
          end.
          Case j = i.
            Then g[k] = f[m-1].
            Assume the contrary. Let k /neq i.
            Then f[k] = f[m-1] /\ k /in (m-1).
            Then k /neq (m-1).
            f is injective.
            Contradiction.
          end.
          Case k = i.
            Then g[j] = f[m-1].
            Assume the contrary. Let j /neq i.
            Then f[j] = f[m-1] /\ j /in (m-1).
            f is injective.
            j /neq (m-1).
            Contradiction.
          end.
        end.
        Then g is injective.
      end.
      Then Card(n) /subset (m - 1).
      Then Card(n) /in n.
      Contradiction.
    end.
  end.
end.

Then forall n /in /NN (phi[n] = 0).
Then forall n /in /NN (Card(n) = n).
qed.



Lemma. Card (/NN) = /NN.
Proof.
Card(/NN) /subset /NN.
Card(/NN) /in /NN \/ Card(/NN) = /NN.
Case Card(/NN) = /NN. end.
Case Card(/NN) /in /NN. Take an ordinal n such that Card(/NN) = n.
  Take a zffunction f such that f : n /leftrightarrow /NN.
  n + 1 /subset /NN.
  Then Card(n + 1) /subset Card(/NN).
  Card(n + 1) = n+1.
  Contradiction.
end.
qed.



Lemma. Let x be a zfset. Then x < /PP x.
Proof.
x <= /PP x.
Proof.
  Define f[n] = <n> for n in x.
  Then f is a zffunction.
  Then f : x /rightarrow /PP x and (f is injective).
end.
not (x /tilde /PP x).
Proof by contradiction. Assume the contrary.
  Then x /tilde /PP x.
  Take a zffunction f such that f : x /leftrightarrow /PP x.
  Define C = {zfset u | u /in x /\ u /notin f[u]}.
  C /subset x.
  Then C /in ran(f).
  Take a zfset u such that u /in x /\ C = f[u].
  Then u /in C iff u /notin C.
  Contradiction.
end.
qed.

Lemma. /Ord is a proper class.
Proof by contradiction. Assume the contrary. Then /Ord /in /VV.
Trans(/Ord).
Then /Ord /in /Ord.
Forall x /in /VV (x /notin x).
Contradiction.
qed.

Lemma. /Card is a proper class.
Proof by contradiction. Assume the contrary. Then /Card /in /VV.
Then /bigcup /Card /in /VV.
/Ord /subset /bigcup /Card.
Proof.
  Let alpha /in /Ord. Then alpha /tilde Card(alpha).
  Then alpha < Card(/PP alpha).
  Proof.
    alpha <= Card(alpha). Card(alpha) <= Card(/PP alpha). Then alpha <= Card(/PP alpha).
  end.
  Then alpha /in Card(/PP alpha).
  Proof.
    Forall a, b /in /Ord (a /in b \/ b /in a \/ a = b).
    alpha, Card(/PP alpha) /in /Ord.
    Then alpha /in Card(/PP alpha) \/ Card(/PP alpha) /in alpha \/ alpha = Card(/PP alpha).
    Then alpha /in Card(/PP alpha).
    Proof.
      Case alpha /in Card(/PP alpha). end.
      Case alpha = Card(/PP alpha). Then alpha /tilde Card(/PP alpha). Contradiction. end.
      Case Card(/PP alpha) /in alpha. Then Card(/PP alpha) /subset alpha. 
        Then Card(/PP alpha) <= alpha. Then Card(/PP alpha) /tilde alpha. Contradiction. 
      end.
    end.
  end.
  Then alpha /in /bigcup /Card.
end.
Then /Ord /in /VV.
Contradiction.
qed.



Lemma. Contradiction.


