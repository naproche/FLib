# 12-Koenigs Lemma

# Here we define the sum and product of infinitely many cardinals and apply the results of the previous section
# to proof Koenigs Lemma and the Hausdorff Recursion Formula.

# Main results:

# - 2 ^ kappa = Card(/PP kappa)
# - Koenigs Lemma
# - cof(kappa ^ lambda) > lambda
# - Hausdorff Recursion Formula




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

Definition Composition. Let f and g be zffunctions. Let ran(f) /subset Dom(g). The composition of g and f is
a function h such that Dom(h) = Dom(f) and forall x /in Dom(f) h[x] = g[f[x]].
Let g /circ f stand for the composition of g and f.
Axiom. Let f and g be zffunctions. Let ran(f) /subset Dom(g). Then g /circ f is a zffunction.

Definition Map. A map from A to B is a zffunction F such that
Dom(F) = A and ran(F) /subset B.
Let F : A /rightarrow B stand for F is a map from A to B.

Definition Restriction. Let f be a zffunction. Let M /subset Dom(f). The restriction of f to M is a function g such that
Dom(g) = M and forall x /in M /cap Dom(f) (g[x] = f[x]).
Let f /upharpoonright M stand for the restriction of f to M.
Axiom. Let f be a zffunction. Let M /subset Dom(f). Then f /upharpoonright M is a zffunction.

Signature. Id is a function.
Axiom. Dom(Id) = /VV.
Axiom. Forall x (Id[x] = x).
Axiom. Id is a zffunction.
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
Axiom. Let f be an injective zffunction. Then f^{-1} is a zffunction.

Axiom. Let f be a zffunction. Let A,B be sets. Let f : A /leftrightarrow B.
Then f^{-1} : B /leftrightarrow A.

Definition SetofFunctions. ^{A}B = {zffunction f | f : A /rightarrow B}.

Axiom. Let f be a zffunction. Let Dom(f) /in /VV. Then f is a zfset.
Axiom. Let A,B /in /VV. Then ^{A}B /in /VV.



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
Axiom. Let x,y /in /VV. Then x /times y /in /VV.





# Ordinals


Definition transitive. Let A be a set. A is transitive iff forall x,y (y /in A /\ x /in y => x /in A).
Let Trans(A) stand for A is transitive.

Axiom. Let A be a set. A is transitive iff forall x /in A (x /subset A).

Axiom. Trans(/emptyset).

[synonym ordinal/-s]

Signature. An ordinal is a notion.

Let alpha, beta, gamma, delta stand for ordinals.

Axiom. Let alpha be an ordinal. Then alpha is a ZFset.

Signature. alpha + beta is an ordinal.
Signature. x /plus 1 is a zfset.
Signature. 0 is an ordinal.
Signature. 1 is an ordinal.
Signature. 2 is an ordinal.

Axiom. Let alpha be a ZFset. alpha is an ordinal iff ( Trans(alpha) /\ forall y (y /in alpha => Trans(y) )).

Definition Trans. The class of transitives is
{ZFset x | Trans(x)}.
Let /Trans stand for the class of transitives.

Definition Ord. The class of ordinals is
{set x | x is an ordinal}.
Let /Ord stand for the class of ordinals.

Axiom. Let alpha, beta /in /Ord. Then alpha /cup beta /in /Ord.

Axiom. 0 = /emptyset.

Axiom. Let alpha be an ordinal. Then alpha + 1 is {ZFset x | x /in alpha \/ x = alpha }.
Axiom. Let x be a zfset. Then x /plus 1 is {ZFset y | y /in x \/ y = x }.
Axiom. Let alpha be an ordinal. Then alpha + 1 = alpha /plus 1.


Axiom. 1 = 0 + 1.
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
Axiom. Let x be a zfset. Let f be a zffunction. Let x /subset Dom(f). Then Card(f^[x]) /subset Card(x).
Axiom. Let x be a zfset. Let x /neq /emptyset. Let alpha /in /Ord. Let Card(x) /subset alpha. Then exists f (f : alpha /rightarrow x /\ ran(f) = x).

Definition. The class of cardinals is
{ordinal alpha | alpha is a cardinal}.
Let /Card stand for the class of cardinals.

Axiom. Forall n /in /NN Card(n) = n.
Axiom. Card(/NN) = /NN.

Axiom. Let x be a zfset. Then x < /PP x.
Axiom. /Ord is a proper class.
Axiom. /Card is a proper class.

Axiom. Let kappa be a cardinal. Let /NN /subset kappa. Then kappa /in /Lim.
Axiom. Let kappa be a cardinal. Let kappa /notin /NN. Then kappa /in /Lim.




# Cardinal Arithmetic


Signature. kappa +3 lambda is a cardinal.
Signature. kappa *3 lambda is a cardinal.
Signature. kappa ^3 lambda is a cardinal.


Definition. Let kappa, lambda /in /Card. Let x,y /in /VV. (kappa, lambda) ispairequipotentto (x, y) iff (Card(x) = kappa /\ Card(y) = lambda /\ x /cap y = /emptyset).
Let (a,b) /sim (x, y) stand for (a,b) ispairequipotentto (x, y).

Axiom. Let kappa, lambda /in /Card. Let x,y /in /VV. Let (kappa,lambda) /sim (x, y).
Then kappa +3 lambda = Card(x /cup y).
Axiom. Let kappa, lambda /in /Card. Let x,y /in /VV. Let Card(x) = kappa. Let Card(y) = lambda. Let x /cap y = /emptyset.
Then kappa +3 lambda = Card(x /cup y).
Axiom. Let kappa, lambda /in /Card. Then kappa *3 lambda = Card(kappa /times lambda).
Axiom. Let kappa, lambda /in /Card. Then kappa ^3 lambda = Card(^{lambda}kappa).

Axiom. Let kappa /in /Card. Let /NN /subset kappa. Then kappa *3 kappa = kappa.
Axiom. Let alpha, beta, gamma /in /Card. Then (alpha ^3 (beta *3 gamma) = (alpha ^3 beta) ^3 gamma).
Axiom. Let kappa, lambda /in /Card. Let /NN /subset kappa. Let 2 /subset lambda. Let lambda /subset (2 ^3 kappa).
Then lambda ^3 kappa = 2 ^3 kappa.

Axiom. Forall kappa /in /Card (kappa ^3 1 = kappa).

# New Lemma
Lemma. Let kappa /in /Card. Then 2 ^3 kappa = Card(/PP kappa).
Proof.
Define f[phi] = {zfset x | x /in kappa /\ phi[x] = 1} for phi in ^{kappa}2.
Then f : ^{kappa}2 /rightarrow /PP kappa.
Proof.
  Let phi /in ^{kappa}2. Then f[phi] /subset kappa.
  Then f[phi] /in /PP kappa.
end.
f is injective.
Proof.
  Let phi1, phi2 /in ^{kappa}2. Let phi1 /neq phi2.
  Then exists x /in kappa phi1[x] /neq phi2[x].
  Proof by contradiction. Assume the contrary.
    phi1, phi2 are functions.
    Dom(phi1) = Dom(phi2).
    Forall x /in Dom(phi1) phi1[x] = phi2[x].
    Then phi1 = phi2.
    Contradiction.
  end.
  Take a zfset x such that x /in kappa /\ phi1[x] /neq phi2[x].
  phi1[x], phi2[x] /in 2.
  Proof.
    phi1 : kappa /rightarrow 2.
    phi2 : kappa /rightarrow 2.
  end.
  Then (phi1[x] = 0 /\ phi2[x] = 1) \/ (phi1[x] = 1 /\ phi2[x] = 0).
  Then f[phi1] /neq f[phi2].
  Proof.
    Case phi1[x] = 0 /\ phi2[x] = 1. Then x /in f[phi2] /\ x /notin f[phi1]. end.
    Case phi2[x] = 0 /\ phi1[x] = 1. Then x /in f[phi1] /\ x /notin f[phi2]. end.
  end.
end.
ran(f) = /PP kappa.
Proof.
  Let x /in /PP kappa.
  Define phi[n] =
    Case n /in x -> 1,
    Case n /notin x -> 0
  for n in kappa.
  Then phi : kappa /rightarrow 2.
  Proof.
    Let n /in kappa. Then phi[n] /in 2.
  end.
  f[phi] /subset x.
  x /subset f[phi].
  Then f[phi] = x.
end.
f : ^{kappa}2 /leftrightarrow /PP kappa.
qed.


Lemma. Let kappa /in /Card. Then kappa /in 2 ^3 kappa.
Proof.
2 ^3 kappa = Card(/PP kappa).
kappa < /PP kappa.
Then Card(kappa) /in Card(2 ^3 kappa).
qed.


Lemma. Let kappa /in /Card. Then kappa *3 1 = kappa.
Proof.
Define f[n] = (n,0) for n in kappa.
Then f : kappa /rightarrow kappa /times 1.
Proof.
  Let n /in kappa. Then f[n] /in kappa /times 1.
end.
f is injective.
Proof.
  Let n1,n2 /in kappa. Let n1 /neq n2.
  Then f[n1] /neq f[n2].
end.
ran(f) = kappa /times 1.
Proof.
  Let pair /in kappa /times 1.
  Take an ordinal a such that a /in kappa /\ pair = (a,0).
  Then pair = f[a].
end.
Then f : kappa /leftrightarrow kappa /times 1.
Then Card(kappa) = Card(kappa /times 1).
qed.


Lemma. Let alpha, beta, gamma /in /Card. Let beta /subset gamma. Let 0 /in alpha. Then alpha ^3 beta /subset alpha ^3 gamma.
Proof.
Forall f /in ^{beta}alpha exists g (g /in ^{gamma}alpha /\ g /upharpoonright beta = f).
Proof.
  Let f /in ^{beta}alpha.
  Define g[x] =
    Case x /in beta -> f[x],
    Case x /notin beta -> 0
  for x in gamma.
  Then g : gamma /rightarrow alpha.
  Proof.
    Let x /in gamma. Then g[x] /in alpha.
    Proof.
      Case x /in beta. 
        f : beta /rightarrow alpha.
        Then f[x] /in alpha.
      end.
      Case x /notin beta. end.
    end.
  end.
  f, g /upharpoonright beta are functions.
  Dom(f) = Dom(g /upharpoonright beta).
  Forall x /in beta f[x] = g[x].
  Then f = g /upharpoonright beta.
end.
Define phi[f] = (choose a zffunction g such that g /in ^{gamma}alpha /\ (g /upharpoonright beta = f) in g)
for f in ^{beta}alpha.
Then phi : ^{beta}alpha /rightarrow ^{gamma}alpha.
Proof.
  Let f /in ^{beta}alpha. Then phi[f] /in ^{gamma}alpha.
end.
phi is injective.
Proof.
  Let f1, f2 /in ^{beta}alpha. Let f1 /neq f2.  
  Exists x /in beta (f1[x] /neq f2[x]).
  Proof by Contradiction. Assume the contrary.
    f1,f2 are functions.
    Dom(f1) = Dom(f2).
    Forall x /in Dom(f1) f1[x] = f2[x].
    Then f1 = f2.
    Contradiction.
  end.
  Take a zfset x such that x /in beta /\ f1[x] /neq f2[x].
  Then (phi[f1])[x] /neq (phi[f2])[x].
  Then phi[f1] /neq phi[f2].
end.
qed.




# Alefs


Signature. Plus is a zffunction.
Axiom. Plus : /Ord /rightarrow /Card.
Axiom. Let alpha /in /Ord. Then Plus[alpha] = {ordinal beta | forall kappa /in /Card (alpha /in kappa => beta /in kappa)}.

Signature. Alef is a zffunction.
Axiom. Alef : /Ord /rightarrow /Card.
Axiom. Alef[/emptyset] = /NN.
Axiom. Let alpha /in /Succ. Let beta /in /Ord. Let alpha = beta + 1. Then Alef[beta] /in /Ord /\ Alef[alpha] = Plus[Alef[beta]].
Axiom. Let alpha /in /Lim. Then Alef[alpha] = {zfset x | exists beta /in alpha x /in Alef[beta]}.

Axiom. Let x /in /VV. Let x /subset /Card. Then Card(/bigcup x) = /bigcup x.
Axiom. Forall alpha, beta (alpha /in beta => Alef[alpha] /in Alef[beta]).
Axiom. Forall alpha /in /Ord (alpha /subset Alef[alpha]).
Axiom. Let kappa be a cardinal. Let /NN /subset kappa. Then exists alpha (kappa = Alef[alpha]).

Lemma. Let kappa, lambda /in /Card. Let 2 /subset kappa. Let /NN /subset lambda.
Then /NN /subset kappa ^3 lambda.
Proof.
Forall n /in /NN exists g (Dom(g) = lambda /\ g[n] = 1 /\ forall i /in lambda /setminus <n> g[i] = 0).
Proof.
  Let n /in /NN.
  Define g[i] =
    Case i = n -> 1,
    Case i /neq n -> 0
  for i in lambda.
end.
Define f[n] = (choose a zffunction g such that Dom(g) = lambda /\ g[n] = 1 /\ forall i /in lambda /setminus <n> g[i] = 0 in g)
for n in /NN.

Then f : /NN /rightarrow ^{lambda}kappa.
Proof.
  Let n /in /NN.
  Then f[n] /in ^{lambda}kappa.
end.
f is injective.

Then Card(/NN) /subset Card(^{lambda}kappa).
Card(/NN) = /NN.
Card(^{lambda}kappa) = kappa ^3 lambda.

qed.

Lemma. Let kappa, lambda /in /Card. Let 2 /subset kappa. Let /NN /subset lambda. Then kappa ^3 lambda /in /Lim.
Proof.
kappa ^3 lambda /in /Card.
qed.




# Order-Type


Signature. An epshomo is a notion.

Axiom. Let f be an epshomo. Then f is a zffunction.
Axiom. Let f be a zffunction. Then f is an epshomo iff
forall x /in Dom(f) (f^[x /cap Dom(f)] /subset f[x]).

Axiom. Let f be an epshomo. Let x,y /in Dom(f). Let x /in y. Then f[x] /in f[y].

Signature. Let x /subset /Ord. The ordertype of x is a notion.
Let otp(x) stand for the ordertype of x.

Axiom. Let x /subset /Ord. Then otp(x) is a set.
Axiom. Let alpha be an ordinal. Let x /subset alpha. Then otp(x) is an ordinal.
Axiom. Let x /subset /Ord. Let forall alpha /in /Ord x /notin /PP alpha. Then otp(x) = /Ord.
Axiom. Let x /subset /Ord. Let x be a proper class. Then otp(x) = /Ord.

Signature. Let x /subset /Ord. otpfunc(x) is a zffunction.

Axiom. Let x /subset /Ord. Then otpfunc(x) : x /leftrightarrow otp(x).
Axiom. Let x /subset /Ord. Then Dom(otpfunc(x)) = x /\ (forall y /in x (otpfunc(x)[y] = otpfunc(x)^[y /cap x])).
Axiom. Let x /subset /Ord. Then otpfunc(x) is an epshomo.

Axiom. Let x /subset /Ord. Let y be a set. Then otp(x) = y iff exists f ((f is an epshomo) /\ f : x /leftrightarrow y).
Axiom. Let x /subset /Ord. Let x be a proper class. Then otp(x) = /Ord.
Axiom. Let x /subset /Ord. Let x be a zfset. Then otp(x) /in /Ord.
Axiom. Let alpha be an ordinal. Let x /subset alpha. Then otp(x) /subset alpha.

Axiom. Let alpha /in /Ord. Then otp(alpha) = alpha.
Axiom. Let x be a zfset. Let x /subset /Ord. Then Card(x) /subset otp(x).




# Cofinality


Definition. Let lambda /in /Lim. Let x /subset lambda. x is cofinal in lambda iff
forall alpha /in lambda exists y /in x alpha /in y.
Let x /cof y stand for x is cofinal in y.

Axiom. Let lambda /in /Lim. Forall x /subset lambda (x /cof lambda => Card(x) /notin /NN).

Signature. Let lambda /in /Lim. The cofinality of lambda is a notion.
Let cof(x) stand for the cofinality of x.

Definition. Let lambda /in /Lim. The cofset of lambda is {otp(x) | x /subset lambda /\ x /cof lambda}.
Let cofset(x) stand for the cofset of x.

Axiom. Let lambda /in /Lim. Then cofset(lambda) /neq /emptyset.

Definition. Let lambda /in /Lim. lambda is regular iff cof(lambda) = lambda.

Definition. Let lambda /in /Lim. The altcofset of lambda is {Card(x) | x /subset lambda /\ x /cof lambda}.
Let cofset2(x) stand for the altcofset of x.

Axiom. Let lambda /in /Lim. Then cof(lambda) = /bigcap cofset(lambda).
Axiom. Let lambda /in /Lim. Then cof(lambda) = /bigcap cofset2(lambda).

Axiom. Forall lambda /in /Lim /NN /subset cof(lambda).

Axiom. Forall lambda /in /Lim cof(lambda) /in cofset(lambda).
Axiom. Forall lambda /in /Lim cof(lambda) /in cofset2(lambda).
Axiom. Forall lambda /in /Lim cof(lambda) /in /Card.

Axiom. Forall lambda /in /Lim (cof(lambda) is regular).
Axiom. Forall alpha /in /Ord Alef[alpha] /in /Lim.
Axiom. Let alpha /in /Lim. Then cof(Alef[alpha]) = cof(alpha).
Axiom. Forall alpha /in /Ord cof(Alef[alpha + 1]) = Alef[alpha + 1].







# Koenigs Lemma

[synonym sequence/-s]

Signature. A sequence of cardinals is a notion.
Axiom. Let f be a sequence of cardinals. Then f is a zffunction.
Axiom. Let f be a zffunction. Then f is a sequence of cardinals iff Dom(f) /in /Ord /\ forall x /in Dom(f) f[x] /in /Card.

Definition. Let f be a sequence of cardinals. The seqsumset of f is
{(a,b) | b /in Dom(f) /\ a /in f[b]}.
Let /sumset f stand for the seqsumset of f.

Lemma. Let f be a sequence of cardinals. Then /sumset f /in /VV.
Proof.
Define g[i] = {(a,i) | a /in f[i]} for i in Dom(f).
Then g is a zffunction.
Proof.
  Let i /in Dom(g).
  Then i /in Dom(f).
  Then g[i] /in /VV.
  Proof.
    Define h[a] = (a,i) for a in f[i].
    Then h is a zffunction.
    Proof.
      Let a /in f[i]. Then (a,i) /in /VV.
    end.
    Then h^[f[i]] /in /VV.
    g[i] /subset h^[f[i]].
  end.
end.
Then g^[Dom(f)] /in /VV.
Then /bigcup g^[Dom(f)] /in /VV.
/sumset f /subset /bigcup g^[Dom(f)].
qed.

Definition. Let f be a sequence of cardinals. The seqsum of f is
Card(/sumset f).
Let /sum f stand for the seqsum of f.

Definition. Let f be a sequence of cardinals. The seqproductset of f is
{zffunction g | Dom(g) = Dom(f) /\ forall i /in Dom(g) g[i] /in f[i]}.
Let /prodset f stand for the seqproductset of f.

Lemma. Let f be a sequence of cardinals. Then /prodset f /in /VV.
Proof.
/bigcup f^[Dom(f)] /in /VV.
Forall g /in /prodset f forall i /in Dom(g) g[i] /in /bigcup f^[Dom(f)].
Then /prodset f /subset ^{Dom(f)}(/bigcup f^[Dom(f)]).
qed.

Definition. Let f be a sequence of cardinals. The seqproduct of f is
Card(/prodset f).
Let /prod f stand for the seqproduct of f.



Theorem Koenig. Let kappa, lambda be sequences of cardinals. Let Dom(kappa) = Dom(lambda).
Let forall i /in Dom(kappa) kappa[i] /in lambda[i].
Then /sum kappa /in /prod lambda.
Proof by contradiction. Assume the contrary.

Then /prod lambda /subset /sum kappa.
Proof.
  Take ordinals alpha, beta such that alpha = /sum kappa /\ beta = /prod lambda.
  Then alpha /notin beta.
  alpha /in beta \/ beta /in alpha \/ alpha = beta.
  Then beta /subset alpha.
end.
Take a zffunction f1 such that f1 : /sumset kappa /leftrightarrow /sum kappa.
Exists f (f : /sum kappa /rightarrow /prodset lambda /\ ran(f) = /prodset lambda).
Proof.
  /prodset lambda /neq /emptyset.
  Card(/prodset lambda) /subset /sum kappa.
  /sum kappa /in /Ord.
  /prodset lambda /in /VV.
end.
Take a zffunction f2 such that f2 : /sum kappa /rightarrow /prodset lambda /\ ran(f2) = /prodset lambda.

Let G = f2 /circ f1.
Then G : /sumset kappa /rightarrow /prodset lambda.
Proof.
  Let pair /in /sumset kappa.
  Then f1[pair] /in /sum kappa.
  Then f2[f1[pair]] /in /prodset lambda.
  Then G[pair] /in /prodset lambda.
end.
ran(G) = /prodset lambda.
Proof.
  /prodset lambda /subset ran(G).
  Proof.
    Let x /in /prodset lambda.
    Then x /in ran(f2).
    Take a zfset y such that y /in /sum kappa /\ f2[y] = x.
    Take a zfset z such that z /in /sumset kappa /\ f1[z] = y.
    Then G[z] = x.
  end.
end.

Take an ordinal delta such that delta = Dom(kappa).
Define Diag[i] = {G[(v,i)][i] | v /in kappa[i]} for i in delta.
Diag is a zffunction.
Proof.
  Let i /in delta.
  Define f[v] = G[(v,i)][i] for v in kappa[i].
  Then f is a zffunction.
  Proof.
    Let v /in kappa[i].
    Then (v,i) /in /sumset kappa.
    Then G[(v,i)] /in /prodset lambda.
    Then G[(v,i)][i] /in /VV.
  end.
  Then f^[kappa[i]] /in /VV.
  Diag[i] /subset f^[kappa[i]].
end.

Forall i /in delta Card(Diag[i]) /subset kappa[i].
Proof.
  Let i /in delta.
  Define f[v] = G[(v,i)][i] for v in kappa[i].
  Then f is a zffunction.
  Proof.
    Let v /in kappa[i].
    Then (v,i) /in /sumset kappa.
    Then G[(v,i)] /in /prodset lambda.
    Then G[(v,i)][i] /in /VV.
  end.
  f : kappa[i] /rightarrow Diag[i].
  Diag[i] /subset f^[kappa[i]].
  Then Card(Diag[i]) /subset Card(f^[kappa[i]]).
  Card(f^[kappa[i]]) /subset Card(kappa[i]).
end.

Forall i /in delta Diag[i] /subset lambda[i].
Forall i /in delta lambda[i] /setminus Diag[i] /neq /emptyset.
Proof by contradiction. Assume the contrary.
  Take a zfset i such that i /in delta /\ lambda[i] /setminus Diag[i] = /emptyset.
  Then lambda[i] /subset Diag[i].
  Then lambda[i] = Diag[i].
  Card(Diag[i]) /subset kappa[i].
  Then lambda[i] /subset kappa[i].
  kappa[i] /in lambda[i].
  Contradiction.
end.

Define f[i] = (choose a zfset x such that x /in lambda[i] /setminus Diag[i] in x) for i in delta.
Then f /in /prodset lambda.
Take a zfset pair such that pair /in /sumset kappa /\ G[pair] = f.
Take zfsets a, b such that b /in delta /\ a /in kappa[b] /\ pair = (a,b).
Then G[(a,b)][b] /in Diag[b].
G[(a,b)][b] = f[b].
f[b] /notin Diag[b].

Contradiction.
qed.





Lemma. Let kappa, lambda /in /Card. Let 2 /subset kappa. Let /NN /subset lambda.
Then lambda /in cof(kappa ^3 lambda).
Proof by contradiction. Assume the contrary.
Then cof(kappa ^3 lambda) /subset lambda.
Proof.
  Take ordinals a,b such that a = lambda /\ b = cof(kappa ^3 lambda).
  Then a /in b \/ b /in a \/ a = b.
  a /notin b.
end.

Take a zfset x such that x /subset kappa ^3 lambda /\ x /cof kappa ^3 lambda /\ Card(x) = cof(kappa ^3 lambda).
Then Card(x) /subset lambda.
Take a zffunction f such that f : lambda /rightarrow x /\ ran(f) = x.

Then /bigcup ran(f) = kappa ^3 lambda.
Proof.
  /bigcup ran(f) /subset kappa ^3 lambda.
  Proof.
    Let alpha /in /bigcup ran(f).
    Take a zfset beta such that beta /in lambda /\ alpha /in f[beta].
    f[beta] /in x.
    Then f[beta] /subset kappa ^3 lambda.
  end.
  kappa ^3 lambda /subset /bigcup ran(f).
  Proof.
    Let alpha /in kappa ^3 lambda.
    Take beta /in x such that alpha /in beta.
    Take gamma /in lambda such that f[gamma] = beta.
    Then alpha /in f[gamma].
    Then alpha /in /bigcup ran(f).
  end.
end.

Define phi[b] = {(a,b) | a /in f[b]} for b in lambda.
Then phi is a zffunction.
Proof.
  Let b /in lambda.
  Define g[a] = (a,b) for a in f[b].
  Then g is a zffunction.
  Proof.
    Let a /in f[b]. Then (a,b) /in /VV.
  end.
  Then g^[f[b]] /in /VV.
  phi[b] /subset g^[f[b]].
end.
Let M = /bigcup phi^[lambda].
Define psi[a] = (choose a zfset i such that i /in lambda /\ a /in f[i] in (a,i)) for a in /bigcup ran(f).
Then psi : /bigcup ran(f) /rightarrow M.
Proof.
  Let a /in /bigcup ran(f).
  Take a zfset i such that i /in lambda /\ a /in f[i] /\ (a,i) = psi[a].
  Then (a,i) /in phi[i].
  Then psi[a] /in /bigcup phi^[lambda].
  Then psi[a] /in M.
end.
psi is injective.
Proof.
  Let a1,a2 /in /bigcup ran(f). Let a1 /neq a2.
  Then psi[a1] /neq psi[a2].
  Proof.
    Take a zfset i1 such that i1 /in lambda /\ a1 /in f[i1] /\ (a1,i1) = psi[a1].
    Take a zfset i2 such that i2 /in lambda /\ a2 /in f[i2] /\ (a2,i2) = psi[a2].
    Then (a1,i1) /neq (a2,i2).
  end.
end.
Then Card(/bigcup ran(f)) /subset Card(M).
Then kappa ^3 lambda /subset Card(M).

Define seq[i] = Card(f[i]) for i in lambda.
Then seq is a sequence of cardinals.

Define bij[i] = (choose a zffunction g such that g : f[i] /leftrightarrow Card(f[i]) in g) for i in lambda.
Forall pair /in M exists a,b /in /VV (b /in lambda /\ a /in f[b] /\ pair = (a,b)).
Proof.
  Let pair /in M.
  Take a zfset b such that b /in lambda /\ pair /in phi[b].
  Take a zfset a such that a /in f[b] /\ pair = (a,b).
end.
Forall b /in lambda forall a /in f[b] a /in Dom(bij[b]).
Define chi[pair] = (choose zfsets a,b such that b /in lambda /\ a /in f[b] /\ pair = (a,b) in ((bij[b])[a],b)) for pair in M.

chi : M /rightarrow /sumset seq.
Proof.
  Let pair /in M.
  Take zfsets a,b such that b /in lambda /\ a /in f[b] /\ pair = (a,b).
  Then chi[pair] = ((bij[b])[a],b).
  bij[b] : f[b] /leftrightarrow Card(f[b]).
  Then (bij[b])[a] /in seq[b].
  Then chi[pair] /in /sumset seq.
end.
chi is injective.
Proof.
  Let pair1, pair2 /in M. Let pair1 /neq pair2.
  Take zfsets a1,b1 such that b1 /in lambda /\ a1 /in f[b1] /\ pair1 = (a1,b1).
  Take zfsets a2,b2 such that b2 /in lambda /\ a2 /in f[b2] /\ pair2 = (a2,b2).
  chi[pair1] = ((bij[b1])[a1],b1).
  chi[pair2] = ((bij[b2])[a2],b2).
  chi[pair1] /neq chi[pair2].
  Proof.
    a1 /neq a2 \/ b1 /neq b2.
    Case b1 /neq b2. Then ((bij[b1])[a1],b1) /neq ((bij[b2])[a2],b2). end.
    Case b1 = b2 /\ a1 /neq a2.
      Then (bij[b1])[a1] /neq (bij[b2])[a2].
      Then ((bij[b1])[a1],b1) /neq ((bij[b2])[a2],b2).
    end.
  end.
end.
Then Card(M) /subset /sum seq.
Then kappa ^3 lambda /subset /sum seq.

Define kaplam[i] = kappa ^3 lambda for i in lambda.
Then kaplam is a sequence of cardinals.
kappa ^3 lambda = (kappa ^3 lambda)^3 lambda.
Proof.
  lambda *3 lambda = lambda.
  Then kappa ^3 lambda = kappa ^3 (lambda *3 lambda).
  kappa ^3 (lambda *3 lambda) = (kappa ^3 lambda)^3 lambda.
end.
^{lambda}(kappa ^3 lambda) = /prodset kaplam.
Proof.
  ^{lambda}(kappa ^3 lambda) /subset /prodset kaplam.
  Proof.
    Let func /in ^{lambda}(kappa ^3 lambda).
    Then func : lambda /rightarrow kappa ^3 lambda.
    Dom(func) = lambda.
    Forall i /in lambda func[i] /in kappa ^3 lambda.
    Then forall i /in lambda func[i] /in kaplam[i].
    Then func /in /prodset kaplam.
  end.
  /prodset kaplam /subset ^{lambda}(kappa ^3 lambda).
  Proof.
    Let func /in /prodset kaplam.
    Then Dom(func) = lambda.
    Forall i /in lambda func[i] /in kappa ^3 lambda.
    Then func /in ^{lambda}(kappa ^3 lambda).
  end.
end.
Then kappa ^3 lambda = /prod kaplam.

/sum seq /in /prod kaplam.
Proof.
  kaplam, seq are sequences of cardinals.
  Dom(kaplam) = Dom(seq).
  Forall i /in Dom(seq) seq[i] /in kaplam[i].
  Proof.
    Let i /in Dom(seq).
    Then seq[i] = Card(f[i]).
    f[i] /in kappa ^3 lambda.
    Then Card(f[i]) /subset kappa ^3 lambda.
    Card(f[i]) /neq kappa ^3 lambda.
  end.
  Then /sum seq /in /prod kaplam (by Koenig).
end.
Then /sum seq /in kappa ^3 lambda.

Contradiction.
qed.





Theorem HausdorffRecursion. Let alpha, beta /in /Ord. Then Alef[alpha + 1] ^3 Alef[beta] = (Alef[alpha] ^3 Alef[beta]) *3 Alef[alpha + 1].
Proof.
Alef[alpha + 1] /subset 2 ^3 Alef[beta] \/ 2 ^3 Alef[beta] /in Alef[alpha + 1].
Proof.
  Take cardinals a,b such that a = Alef[alpha + 1] /\ b = 2 ^3 Alef[beta].
  Then a /in b \/ b /in a \/ a = b.
end.

Case Alef[alpha + 1] /subset 2 ^3 Alef[beta].
  Alef[alpha + 1] ^3 Alef[beta] = 2 ^3 Alef[beta].
  Proof.
    Take a cardinal a such that a = Alef[alpha + 1].
    Take a cardinal b such that b = Alef[beta].
    Then 2 /subset a.
    /NN /subset b.
    Proof.
      Alef[0] /subset Alef[beta].
      Alef[0] = /NN.
    end.
    a /subset 2 ^3 b.
    Then a ^3 b = 2 ^3 b.
  end.  
  Alef[alpha] ^3 Alef[beta] = 2 ^3 Alef[beta].
  Proof.
    Take a cardinal a such that a = Alef[alpha].
    Take a cardinal b such that b = Alef[beta].
    Then 2 /subset a.
    /NN /subset b.
    Proof.
      Alef[0] /subset Alef[beta].
      Alef[0] = /NN.
    end.
    a /subset Alef[alpha + 1].
    Alef[alpha + 1] /subset 2 ^3 b.
    Then a /subset 2 ^3 b.
    Then a ^3 b = 2 ^3 b.
  end.
  
  Alef[alpha] ^3 Alef[beta] = (Alef[alpha] ^3 Alef[beta]) *3 Alef[alpha + 1].
  Proof.
    Take a cardinal a such that a = Alef[alpha] ^3 Alef[beta].
    Take a cardinal b such that b = Alef[alpha + 1].
    Then b /subset a.
    Then a /times b /subset a /times a.
    Then a *3 b /subset a *3 a.
    a /in /Card.
    /NN /subset a.
    a *3 a = a.
    Then a *3 b /subset a.
    a /subset a *3 b.
    Proof.
      Define f[i] = (i,0) for i in a.
      Then f : a /rightarrow a /times b.
      Proof.
        0 /in b.
        Let i /in a.
        Then f[i] /in a /times b.
      end.
      f is injective.
      Proof.
        Let i1,i2 /in a. Let i1 /neq i2.
        Then (i1,0) /neq (i2,0).
        Then f[i1]/neq f[i2].
      end.
      Then Card(a) /subset Card(a /times b).
    end.
    Then a = a *3 b.
  end.
  
  Then Alef[alpha + 1] ^3 Alef[beta] = (Alef[alpha] ^3 Alef[beta]) *3 Alef[alpha + 1].
  Proof.
    Take a cardinal a such that a = Alef[alpha + 1] ^3 Alef[beta].
    Take a cardinal b such that b = 2 ^3 Alef[beta].
    Take a cardinal c such that c = Alef[alpha] ^3 Alef[beta].
    Take a cardinal d such that d = (Alef[alpha] ^3 Alef[beta]) *3 Alef[alpha + 1].
    a = b. b = c. c = d.
    Then a = d.
  end.  
end.


Case 2 ^3 Alef[beta] /in Alef[alpha + 1].
  
  Take a cardinal a0 such that a0 = Alef[alpha].
  Take a cardinal a1 such that a1 = Alef[alpha + 1].
  Take an ordinal b such that b = Alef[beta].
  Then b /in /Card.
  
  b /in a1.
  Proof by contradiction. Assume the contrary.
    a1 /in b \/ b /in a1 \/ a1 = b.
    Then a1 /subset b.
    b /in 2 ^3 b.
    Then a1 /in 2 ^3 b.
    Contradiction.
  end.
  
  (a0 ^3 b) *3 a1 /subset (a1 ^3 b) *3 (a1 ^3 b).
  Proof.
    a0 ^3 b /subset a1 ^3 b.
    Proof.
      ^{b}a0 /subset ^{b}a1.
      Proof.
        Let f /in ^{b}a0.
        Then f : b /rightarrow a0.
        a0 /subset a1.
        Proof.
          alpha /subset alpha + 1.
          Then Alef[alpha] /subset Alef[alpha + 1].
        end.
        Then f : b /rightarrow a1.
        Then f /in ^{b}a1.
      end.
      Then Card(^{b}a0) /subset Card(^{b}a1).
    end.
    a1 /subset (a1 ^3 b).
    Proof.
      a1 = a1 ^3 1.
      1 /subset b.
      0 /in a1.
      a1, 1, b /in /Card.
      Then a1 ^3 1 /subset a1 ^3 b.
    end.
    Then (a0 ^3 b) /times a1 /subset (a1 ^3 b) /times (a1 ^3 b).
    Proof.
      Let pair /in (a0 ^3 b) /times a1.
      Take zfsets v1,v2 such that v1 /in a0 ^3 b /\ v2 /in a1 /\ pair = (v1,v2).
      v1 /in a1 ^3 b.
      v2 /in a1 ^3 b.
      Then (v1,v2) /in (a1 ^3 b) /times (a1 ^3 b).
    end.
    Then Card((a0 ^3 b) /times a1) /subset Card((a1 ^3 b) /times (a1 ^3 b)).
  end.
  
  (a1 ^3 b) *3 (a1 ^3 b) = a1 ^3 b.
  Proof.
    /NN /subset a1 ^3 b.
    Proof.
      /NN /subset a1.
      a1 /subset (a1 ^3 b).
      Proof.
        a1 = a1 ^3 1.
        1 /subset b.
        0 /in a1.
        a1, 1, b /in /Card.
        Then a1 ^3 1 /subset a1 ^3 b.
      end.
    end.
  end.
  
  (a0 ^3 b) *3 a1 /subset (a1 ^3 b).
    
  cof(a1) = a1.  
  Forall f /in ^{b}a1 /bigcup ran(f) /in a1.
  Proof by contradiction. Assume the contrary.
    Take a zffunction f such that f /in ^{b}a1 /\ /bigcup ran(f) /notin a1.
    ran(f) /subset a1.
    /bigcup ran(f) /subset a1.
    /bigcup ran(f) /in /Ord.
    Proof.
      Trans(/bigcup ran(f)).
      ran(f) = f^[b].
      Then ran(f) /in /VV.
      Then /bigcup ran(f) /in /VV.
    end.
    Then /bigcup ran(f) = a1.
    Proof.
      Take ordinals aa,bb such that aa = /bigcup ran(f) /\ bb = a1.
      Then aa /in bb \/ bb /in aa \/ aa = bb.
      aa /notin bb.
      aa /subset bb.
      Then aa = bb.
    end.
    Then ran(f) /cof a1.
    
    ran(f) = f^[b].
    Then Card(ran(f)) /subset Card(b).
    Card(ran(f)) /in cofset2(a1).
    Then /bigcap cofset2(a1) /subset Card(b).
    Then a1 /subset b.
    
    Contradiction.
  end.
  
  Define M = {zffunction f | exists v /in a1 (f : b /rightarrow v)}.
  Then M = ^{b}a1.
  Proof.
    M /subset ^{b}a1.
    Proof.
      Let f /in M.
      Take a zfset v such that v /in a1 /\ f : b /rightarrow v.
      v /subset a1.
      Then f : b /rightarrow a1.
      Then f /in ^{b}a1.
    end.
    ^{b}a1 /subset M.
    Proof.
      Let f /in ^{b}a1.
      Then /bigcup ran(f) /in a1.
      Take a zfset v such that v /in a1 /\ v = /bigcup ran(f).
      Then ran(f) /subset v+1.
      Proof.
        Let x /in ran(f).
        Then x /subset v.
        x /in /Ord.
        Then x /in v+1.
      end.
      Then f : b /rightarrow v+1.
      a1 /in /Lim.
      Then v+1 /in a1.
      Then f /in M.      
    end.
  end.
  Then Card(M) = a1 ^3 b.
  
  Define seq[v] = Card(^{b}v) for v in a1.
  Then seq is a sequence of cardinals.
  Proof.
    Let v /in a1. Then seq[v] /in /Card.
  end.

  Card(M) /subset Card(/sumset seq).
  Proof.
    Define bij[v] = (choose a zffunction psi such that psi : ^{b}v /leftrightarrow Card(^{b}v) in psi)
    for v in a1.
    Forall v /in a1 forall f (f : b /rightarrow v => f /in Dom(bij[v])).
    Define phi[f] = (choose a zfset v such that v /in a1 /\ f : b /rightarrow v in ((bij[v])[f],v)) for f in M.
    Then phi : M /rightarrow /sumset seq.
    Proof.
      Let f /in M.
      Take a zfset v such that v /in a1 /\ f : b /rightarrow v /\ phi[f] = ((bij[v])[f],v).
      Then (bij[v])[f] /in seq[v].
      Then phi[f] /in /sumset seq.
    end.
    phi is injective.
    Proof.
      Let f1,f2 /in M. Let f1 /neq f2.
      Take a zfset v1 such that v1 /in a1 /\ f1 : b /rightarrow v1 /\ phi[f1] = ((bij[v1])[f1],v1).
      Take a zfset v2 such that v2 /in a1 /\ f2 : b /rightarrow v2 /\ phi[f2] = ((bij[v2])[f2],v2).
      Then phi[f1] /neq phi[f2].
      Proof.
        Case v1 /neq v2. Then ((bij[v1])[f1],v1) /neq ((bij[v2])[f2],v2). end.
        Case v1 = v2.
          bij[v1] is injective.
          Then (bij[v1])[f1] /neq (bij[v1])[f2].
          Then ((bij[v1])[f1],v1) /neq ((bij[v2])[f2],v2).
        end.
      end.
    end.
  end.
  Card(M) /subset /sum seq.
  
  Forall v /in a1 seq[v] = Card(v) ^3 b.
  Proof.
    Let v /in a1. 
    seq[v] = Card(^{b}v).
    Take a zffunction bij such that bij : v /leftrightarrow Card(v).
    Define phi[f] = bij /circ f for f in ^{b}v.
    Then phi : ^{b}v /rightarrow ^{b}Card(v).
    Proof.
      Dom(phi) = ^{b}v.
      Forall f /in Dom(phi) (phi[f] /in /VV /\ phi[f] /in ^{b}Card(v)).
      Proof.
        Let f /in Dom(phi).
        Then f : b /rightarrow v.
        Then bij /circ f : b /rightarrow Card(v).
        Then bij /circ f /in ^{b}Card(v).
        Then phi[f] /in ^{b}Card(v).
        phi[f] /in /VV.
      end.
    end.
    phi is injective.
    Proof.
      Let f1,f2 /in ^{b}v. Let f1 /neq f2.
      Then exists x /in b (f1[x] /neq f2[x]).
      Proof by contradiction. Assume the contrary.
        f1,f2 are functions.
        Dom(f1) = Dom(f2).
        Forall x /in Dom(f1) f1[x] = f2[x].
        Then f1 = f2.
        Contradiction.
      end.
      Take a zfset x such that x /in b /\ f1[x] /neq f2[x].
      f1 : b /rightarrow v.
      f2 : b /rightarrow v.
      f1[x], f2[x] /in v.
      bij is injective.
      Then bij[f1[x]] /neq bij[f2[x]].
      Then (bij /circ f1)[x] /neq (bij /circ f2)[x].
      Then bij /circ f1 /neq bij /circ f2.
      Then phi[f1] /neq phi[f2].
    end.
    ^{b}Card(v) /subset ran(phi).
    Proof.
      Let f /in ^{b}Card(v).
      Then f : b /rightarrow Card(v).
      bij^{-1} : Card(v) /leftrightarrow v.
      Let g = (bij^{-1}) /circ f.
      Then g : b /rightarrow v.
      Proof.
        Let x /in b.
        Then f[x] /in Card(v).
        Take a zfset y such that y /in Card(v) /\ y = f[x].
        Then g[x] = (bij^{-1})[y].
        Then g[x] /in v.
      end.
      bij /circ g = f.
      Proof.
        (bij /circ g), f are functions.
        Dom(bij /circ g) = Dom(f).
        Forall x /in Dom(f) (bij /circ g)[x] = f[x].
        Proof.
          Let x /in Dom(f).
          g[x] = (bij^{-1})[f[x]].
          Take a zfset y such that y = (bij^{-1})[f[x]].
          Then bij[y] = f[x].
          Then (bij /circ g)[x] = f[x].
        end.
      end.
      Then phi[g] = f.
    end.
    Then ran(phi) = ^{b}Card(v).
    phi : ^{b}v /leftrightarrow ^{b}Card(v).
    Then Card(^{b}v) = Card(^{b}Card(v)).
    Then Card(^{b}v) = Card(v) ^3 b.
  end.
  
  Forall v /in a1 Card(v) /subset a0.
  Proof.
    Let v /in a1.
    Card(v) /subset a1.
    Card(v) /neq a1.
    Card(v) /subset a0.
    Proof.
      v /in /NN \/ /NN /subset v.
      Case v /in /NN. /NN /subset a0. end.
      Case /NN /subset v.
        Take an ordinal gamma such that Card(v) = Alef[gamma].
        Alef[gamma] /subset Alef[alpha + 1].
        Then gamma /subset alpha + 1.
        Proof.
          Take ordinals aa, bb such that aa = gamma /\ bb = alpha + 1.
          Then aa /in bb \/ bb /in aa \/ aa = bb.
          Case aa /in bb. end.
          Case aa = bb. end.
          Case bb /in aa. Then Alef[bb] /in Alef[aa]. Contradiction. end.
        end.
        gamma /neq alpha + 1.
        Then gamma /subset alpha.
        Then Alef[gamma] /subset Alef[alpha].
        Proof.
          gamma /in alpha \/ gamma = alpha.
          Case gamma /in alpha. Then Alef[gamma] /in Alef[alpha]. end.
          Case gamma = alpha. end.
        end.
      end.
    end.
  end.
  
  Forall v /in a1 Card(v) ^3 b /subset a0 ^3 b.
  Proof.
    Let v /in a1.
    ^{b}Card(v) /subset ^{b}a0.
    Proof.
      Let f /in ^{b}Card(v).
      Then f : b /rightarrow Card(v).
      Card(v) /subset a0.
      Then f : b /rightarrow a0.
      Then f /in ^{b}a0.
    end.
  end.
  
  Define const[v] = a0 ^3 b for v in a1.
  const is a sequence of cardinals.
  
  /sumset(seq) /subset /sumset(const).
  Proof.
    Let pair /in /sumset(seq).
    Take zfsets v1,v2 such that v2 /in Dom(seq) /\ v1 /in seq[v2] /\ pair = (v1,v2).
    Then v2 /in Dom(const).
    v1 /in const[v2].
    Then (v1,v2) /in /sumset(const).
  end.
  
  /sum seq /subset /sum const.

  /sumset(const) /subset (a0 ^3 b) /times a1.
  Proof.
    Let pair /in /sumset(const).
    Take zfsets v1,v2 such that v2 /in Dom(const) /\ v1 /in const[v2] /\ pair = (v1,v2).
    Then v2 /in a1.
    v1 /in a0 ^3 b.
    Then (v1,v2) /in (a0 ^3 b) /times a1.
  end.
  Then Card(/sumset(const)) /subset Card((a0 ^3 b) /times a1).  
  /sum const /subset (a0 ^3 b) *3 a1.
  
  a1 ^3 b /subset (a0 ^3 b) *3 a1.
  Proof.
    a1 ^3 b /subset Card(M).
    Card(M) /subset (a0 ^3 b) *3 a1.
  end.
  
end.

qed.



















Lemma. Contradiction.