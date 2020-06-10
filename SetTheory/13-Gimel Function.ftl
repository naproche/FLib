# 13-Gimel Function

# In this section the Beth-Numbers and the Gimel function is introduced.
# We show that the values of the continuum function only depend on the Gimel function on we proof a calculation rule
# for the value of 2 ^ kappa depending on the Gimel function.

# Main results:

# - kappa < Gimel[kappa]
# - for regular cardinals 2 ^ kappa = Gimel[kappa]
# - for singular cardinals 2 ^ kappa = 2 ^ <kappa or 2 ^ kappa = Gimel[2 ^ <kappa]


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
Axiom. Let x, y be zfsets. Let x <= y. Then Card(x) /subset Card(y).

# New Lemma
Lemma. Let x, y be zfsets. Let Card(x) /subset Card(y). Then x <= y.
Proof.
Take a zffunction f such that f : x /leftrightarrow Card(x).
Take a zffunction g such that g : Card(y) /leftrightarrow y.
Then g /circ f : x /rightarrow y.
g /circ f is injective.
qed.

Axiom. Let x, y be zfsets. Let x <= y. Let y <= x. Then Card(x) = Card(y).
Axiom. Let x, y be zfsets. Let x <= y. Let y <= x. Then x /tilde y.
Axiom. Let x be a zfset. Let f be a zffunction. Let x /subset Dom(f). Then Card(f^[x]) /subset Card(x).
Axiom. Let x be a zfset. Let x /neq /emptyset. Let alpha /in /Ord. Let Card(x) /subset alpha. Then exists f (f : alpha /rightarrow x /\ ran(f) = x).

# Changed from /Card to /Cd
Definition. The class of cardinals is
{ordinal alpha | alpha is a cardinal}.
Let /Cd stand for the class of cardinals.

# New Definition
Definition. The class of infinite cardinals is
{ordinal alpha | (alpha is a cardinal) /\ /NN /subset alpha}.
Let /Card stand for the class of infinite cardinals.

Axiom. Forall n /in /NN Card(n) = n.
Axiom. Card(/NN) = /NN.

Axiom. Let x be a zfset. Then x < /PP x.
Axiom. /Ord is a proper class.
Axiom. /Cd is a proper class.
Lemma. /Card is a proper class.
Proof by contradiction. Assume the contrary.
Take a zfset x such that x = /Card.
Let y = <x,/NN>.
Then /Cd /subset /bigcup y.
Proof.
  Let kappa /in /Cd.
  Then kappa /in /Ord.
  Then /NN /in kappa \/ kappa /in /NN \/ kappa = /NN.
  Then /NN /subset kappa \/ kappa /in /NN.
end.
Then /Cd /in /VV.
Contradiction.
qed.

Axiom. Let kappa be a cardinal. Let /NN /subset kappa. Then kappa /in /Lim.
Axiom. Let kappa be a cardinal. Let kappa /notin /NN. Then kappa /in /Lim.




# Cardinal Arithmetic


Signature. kappa +3 lambda is a cardinal.
Signature. kappa *3 lambda is a cardinal.
Signature. kappa ^3 lambda is a cardinal.


Definition. Let kappa, lambda /in /Cd. Let x,y /in /VV. (kappa, lambda) ispairequipotentto (x, y) iff (Card(x) = kappa /\ Card(y) = lambda /\ x /cap y = /emptyset).
Let (a,b) /sim (x, y) stand for (a,b) ispairequipotentto (x, y).

Axiom. Let kappa, lambda /in /Cd. Let x,y /in /VV. Let (kappa,lambda) /sim (x, y).
Then kappa +3 lambda = Card(x /cup y).
Axiom. Let kappa, lambda /in /Cd. Let x,y /in /VV. Let Card(x) = kappa. Let Card(y) = lambda. Let x /cap y = /emptyset.
Then kappa +3 lambda = Card(x /cup y).
Axiom. Let kappa, lambda /in /Cd. Then kappa *3 lambda = Card(kappa /times lambda).
Axiom. Let kappa, lambda /in /Cd. Then kappa ^3 lambda = Card(^{lambda}kappa).

Axiom. Let kappa /in /Cd. Let /NN /subset kappa. Then kappa *3 kappa = kappa.
Axiom. Let alpha, beta, gamma /in /Cd. Then (alpha ^3 (beta *3 gamma) = (alpha ^3 beta) ^3 gamma).
Axiom. Let kappa, lambda /in /Cd. Let /NN /subset kappa. Let 2 /subset lambda. Let lambda /subset (2 ^3 kappa).
Then lambda ^3 kappa = 2 ^3 kappa.

# New Lemma
Lemma. Let alpha /in /Cd. Let alpha /neq 0. Then 0 ^3 alpha = 0.
Proof.
^{alpha}0 = /emptyset.
Proof by contradiction. Assume the contrary.
  Take a zfset f such that f /in ^{alpha}0.
  Then f : alpha /rightarrow 0.
  0 /in alpha. Then f[0] /in 0.
  Contradiction.
end.
qed.
Axiom. Forall kappa /in /Cd (kappa ^3 1 = kappa).
Axiom. Let kappa /in /Cd. Then 2 ^3 kappa = Card(/PP kappa).
Axiom. Let x,y /in /VV. Let x /tilde y. Then /PP x /tilde /PP y.
Axiom. Let x /in /VV. Then Card(/PP x) = 2 ^3 Card(x).
Axiom. Let kappa /in /Cd. Then kappa /in 2 ^3 kappa.
Axiom. Let kappa /in /Cd. Then kappa *3 1 = kappa.
Axiom. Let alpha, beta, gamma /in /Cd. Let beta /subset gamma. Let 0 /in alpha. Then alpha ^3 beta /subset alpha ^3 gamma.
# Better Lemma
Lemma. Let alpha, beta, gamma /in /Cd. Let beta /subset gamma. Let 0 /in alpha \/ 0 /in beta. Then alpha ^3 beta /subset alpha ^3 gamma.
Proof.
Case 0 /in alpha. end.
Case alpha = 0 /\ 0 /in beta.
  Then 0 /in gamma.
  alpha ^3 beta = 0.
  alpha ^3 gamma = 0.
end.
qed.
Axiom. Let alpha, beta, gamma /in /Cd. Let alpha /subset beta. Then alpha ^3 gamma /subset beta ^3 gamma.




# Alefs


Signature. Plus is a zffunction.
Axiom. Plus : /Ord /rightarrow /Cd.
Axiom. Let alpha /in /Ord. Then Plus[alpha] = {ordinal beta | forall kappa /in /Cd (alpha /in kappa => beta /in kappa)}.

Signature. Alef is a zffunction.
Axiom. Alef : /Ord /rightarrow /Cd.
Axiom. Alef[/emptyset] = /NN.
Axiom. Let alpha /in /Succ. Let beta /in /Ord. Let alpha = beta + 1. Then Alef[beta] /in /Ord /\ Alef[alpha] = Plus[Alef[beta]].
Axiom. Let alpha /in /Lim. Then Alef[alpha] = {zfset x | exists beta /in alpha x /in Alef[beta]}.

Axiom. Let x /in /VV. Let x /subset /Cd. Then Card(/bigcup x) = /bigcup x.
Axiom. Forall alpha, beta (alpha /in beta => Alef[alpha] /in Alef[beta]).
# New Lemma
Lemma. Alef is injective.
Proof.
Let alpha, beta /in Dom(Alef). Let alpha /neq beta.
Then Alef[alpha] /neq Alef[beta].
Proof.
  Forall a,b /in /Ord (a /in b \/ b /in a \/ a = b).
  alpha, beta /in /Ord.
  Then alpha /in beta \/ beta /in alpha.
  Then Alef[alpha] /in Alef[beta] \/ Alef[beta] /in Alef[alpha].
end.
qed.
Axiom. Forall alpha /in /Ord (alpha /subset Alef[alpha]).
Axiom. Let kappa be a cardinal. Let /NN /subset kappa. Then exists alpha (kappa = Alef[alpha]).

Axiom. Let kappa, lambda /in /Cd. Let 2 /subset kappa. Let /NN /subset lambda.
Then /NN /subset kappa ^3 lambda.
Axiom. Let kappa, lambda /in /Cd. Let 2 /subset kappa. Let /NN /subset lambda. Then kappa ^3 lambda /in /Lim.



# Order-Type


Signature. An epshomo is a notion.

Axiom. Let f be an epshomo. Then f is a zffunction.
Axiom. Let f be a zffunction. Then f is an epshomo iff
forall x /in Dom(f) (f^[x /cap Dom(f)] /subset f[x]).

Axiom eps. Let f be an epshomo. Let x,y /in Dom(f). Let x /in y. Then f[x] /in f[y].
# New Lemma
Lemma. Let f be a zffunction. Let forall x,y /in Dom(f) (x /in y => f[x] /in f[y]). Then f is an epshomo.
Proof.
Let x /in Dom(f).
Forall y /in x /cap Dom(f) f[y] /in f[x].
Then f^[x /cap Dom(f)] /subset f[x].
qed.

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
Axiom. Forall lambda /in /Lim cof(lambda) /in /Cd.

Axiom. Forall lambda /in /Lim (cof(lambda) is regular).
Axiom. Forall alpha /in /Ord Alef[alpha] /in /Lim.
Axiom. Let alpha /in /Lim. Then cof(Alef[alpha]) = cof(alpha).
Axiom. Forall alpha /in /Ord cof(Alef[alpha + 1]) = Alef[alpha + 1].




# Koenigs Lemma

[synonym sequence/-s]

Signature. A sequence of cardinals is a notion.
Axiom. Let f be a sequence of cardinals. Then f is a zffunction.
Axiom. Let f be a zffunction. Then f is a sequence of cardinals iff Dom(f) /in /Ord /\ forall x /in Dom(f) f[x] /in /Cd.

Definition. Let f be a sequence of cardinals. The seqsumset of f is
{(a,b) | b /in Dom(f) /\ a /in f[b]}.
Let /sumset f stand for the seqsumset of f.

Axiom. Let f be a sequence of cardinals. Then /sumset f /in /VV.

Definition. Let f be a sequence of cardinals. The seqsum of f is
Card(/sumset f).
Let /sum f stand for the seqsum of f.

Definition. Let f be a sequence of cardinals. The seqproductset of f is
{zffunction g | Dom(g) = Dom(f) /\ forall i /in Dom(g) g[i] /in f[i]}.
Let /prodset f stand for the seqproductset of f.

Axiom. Let f be a sequence of cardinals. Then /prodset f /in /VV.

Definition. Let f be a sequence of cardinals. The seqproduct of f is
Card(/prodset f).
Let /prod f stand for the seqproduct of f.

Axiom Koenig. Let kappa, lambda be sequences of cardinals. Let Dom(kappa) = Dom(lambda).
Let forall i /in Dom(kappa) kappa[i] /in lambda[i].
Then /sum kappa /in /prod lambda.




# Beths

Signature. Beth is a zffunction.
Axiom. Beth : /Ord /rightarrow /Cd.
Axiom. Beth[/emptyset] = /NN.
Axiom. Let alpha /in /Succ. Let beta /in /Ord. Let alpha = beta + 1. Then Beth[beta] /in /Cd /\ Beth[alpha] = 2 ^3 Beth[beta].
Axiom. Let alpha /in /Lim. Then Beth[alpha] = {zfset x | exists beta /in alpha x /in Beth[beta]}.


Lemma. Forall alpha /in /Ord /NN /subset Beth[alpha].
Proof.
Define phi[alpha] =
  Case /NN /subset Beth[alpha] -> 0,
  Case not (/NN /subset Beth[alpha]) -> 1
for alpha in /Ord.
Forall alpha /in /Ord (forall beta /in alpha phi[beta] = 0 => phi[alpha] = 0).
Proof.
  Let alpha /in /Ord. Let forall beta /in alpha phi[beta] = 0.
  Case alpha = 0. Then phi[alpha] = 0. end.
  Case alpha /in /Lim. Then Beth[alpha] = {zfset x | exists beta /in alpha x /in Beth[beta]}.
    0 /in alpha. 
    Forall n /in /NN n /in Beth[0].
    Then forall n /in /NN n /in Beth[alpha].
    Then phi[alpha] = 0.
  end.
  Case alpha /in /Succ. Let beta = alpha - 1.
    Then phi[beta] = 0.
    Then /NN /subset Beth[beta].
    Beth[beta] /subset Beth[alpha].
    Proof.
      Beth[alpha] = 2 ^3 Beth[beta].
    end.
    Then /NN /subset Beth[alpha].
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


Lemma. Forall alpha, beta /in /Ord (beta /in alpha => Beth[beta] /in Beth[alpha]).
Proof.
Define phi[alpha] =
  Case forall beta /in alpha Beth[beta] /in Beth[alpha] -> 0,
  Case not (forall beta /in alpha Beth[beta] /in Beth[alpha]) -> 1
for alpha in /Ord.
Forall alpha /in /Ord ((forall beta /in alpha phi[beta] = 0) => phi[alpha] = 0).
Proof.
  Let alpha /in /Ord. Let forall beta /in alpha phi[beta] = 0.
  Then phi[alpha] = 0.
  Proof.
    Case alpha = 0. end.
    Case alpha /in /Lim.
      Then Beth[alpha] = {zfset x | exists beta /in alpha x /in Beth[beta]}.
      Let beta /in alpha.
      Then beta + 1 /in alpha.
      Beth[beta] /in Beth[beta + 1].
      Then Beth[beta] /in Beth[alpha].
    end.
    Case alpha /in /Succ. Let gamma = alpha - 1.
      Then phi[gamma] = 0.
      Let beta /in alpha.
      Then beta /in gamma \/ beta = gamma.
      Then Beth[beta] /in Beth[alpha].
      Proof.
        Case beta = gamma. 
          Then Beth[alpha] = 2 ^3 Beth[beta].
        end.
        Case beta /in gamma.
          Then Beth[beta] /in Beth[gamma].
          Beth[alpha] = 2 ^3 Beth[gamma].
          Then Beth[gamma] /subset Beth[alpha].
        end.
      end.
    end.
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


Signature. An inaccessible cardinal is a notion.
Axiom. Let kappa be an inaccessible cardinal. Then kappa is a cardinal.
Axiom. Let kappa be a cardinal. Then kappa is an inaccessible cardinal iff 
kappa = Alef[kappa] /\ cof(kappa) = kappa.

Signature. A strongly inaccessible cardinal is a notion.
Axiom. Let kappa be an inaccessible cardinal. Then kappa is a cardinal.
Axiom. Let kappa be a cardinal. Then kappa is an inaccessible cardinal iff 
kappa = Beth[kappa] /\ cof(kappa) = kappa.




# Gimel Function

Signature. Gimel is a zffunction.
Axiom. Gimel : /Card /rightarrow /Card.
Lemma. Let kappa /in /Card. Then kappa ^3 cof(kappa) /in /Card.
Axiom. Forall kappa /in /Card Gimel[kappa] = kappa ^3 cof(kappa).

Signature. Let kappa /in /Cd. Let lambda /in /Card. kappa ^< lambda is a set.
Axiom exp. Let kappa /in /Cd. Let lambda /in /Card. kappa ^< lambda = {zfset x | exists v /in lambda x /in kappa ^3 Card(v)}.

Lemma. Let kappa /in /Cd. Let lambda /in /Card. Then kappa ^< lambda /in /Cd.
Proof.
Define M = {kappa ^3 (Card(v)) | v /in lambda}.
Then M /subset /Cd.
M /in /VV.
Proof.
  Define f[v] = kappa ^3 (Card(v)) for v in lambda.
  f is a zffunction.
  Proof.
    Let v /in lambda.
    Then f[v] /in /VV.
  end.
  M /subset f^[lambda].
end.
/bigcup M /in /Cd.
/bigcup M /subset kappa ^< lambda.
Proof.
  Let x /in /bigcup M.
  Take a zfset v such that v /in lambda /\ x /in kappa ^3 (Card(v)).
  Then x /in kappa ^< lambda.
end.
kappa ^< lambda /subset /bigcup M.
Proof.
  Let x /in kappa ^< lambda.
  kappa ^< lambda = {zfset x | exists v /in lambda x /in kappa ^3 Card(v)}.
  Take a zfset v such that v /in lambda /\ x /in kappa ^3 Card(v).
  Then x /in /bigcup M.
end.
qed.

Lemma. Let kappa /in /Card. Then 2 ^< kappa /in /Card.
Proof.
  2 ^< kappa /in /Cd.
  /NN /subset 2 ^< kappa.
  Proof.
    Let n /in /NN.
    2 ^< kappa = {zfset x | exists v /in kappa x /in 2 ^3 Card(v)}.
    n /in kappa.
    Card(n) = n.
    Then n /in 2 ^3 Card(n).
    Then n /in 2 ^< kappa.
  end.
qed.



Lemma. Forall kappa /in /Card kappa /in Gimel[kappa].
Proof.
Let kappa /in /Card.
cof(kappa) /in cofset2(kappa).
Take a zfset x such that x /subset kappa /\ x /cof kappa /\ Card(x) = cof(kappa).
Take a zffunction f such that f : Card(x) /leftrightarrow x.
Define sum[i] = Card(f[i]) for i in Card(x).
Then sum is a sequence of cardinals.
Proof.
  Let i /in Card(x). Then sum[i] /in /Cd.
end.
kappa /subset /sum sum.
Proof. 
  Define bij[i] = (choose a zffunction g such that g : i /leftrightarrow Card(i) in g) for i in kappa.
  Forall i /in kappa exists a /in Card(x) (i /in f[a]).
  Proof.
    Let i /in kappa.
    x /cof kappa.
    Take a zfset y such that y /in x /\ i /in y.
    Take a zfset z such that z /in Card(x) /\ f[z] = y.
  end.
  Forall a /in Card(x) (f[a] /in kappa /\ Dom(bij[f[a]]) = f[a]).
  Define inc[i] = (choose a zfset a such that a /in Card(x) /\ i /in f[a] in ((bij[f[a]])[i],a)) for i in kappa.
  Then inc : kappa /rightarrow /sumset sum.
  Proof.
    Let i /in kappa.
    Take a zfset a such that a /in Card(x) /\ i /in f[a] /\ inc[i] = ((bij[f[a]])[i],a).
    Then (bij[f[a]])[i] /in Card(f[a]).
    Then (bij[f[a]])[i] /in sum[a].
    Then inc[i] /in /sumset sum.
  end.
  inc is injective.
  Proof.
    Let i1, i2 /in kappa. Let i1 /neq i2.
    Then inc[i1] /neq inc[i2].
    Proof.
      Take a zfset a1 such that a1 /in Card(x) /\ i1 /in f[a1] /\ inc[i1] = ((bij[f[a1]])[i1],a1).
      Take a zfset a2 such that a2 /in Card(x) /\ i2 /in f[a2] /\ inc[i2] = ((bij[f[a2]])[i2],a2).
      Case a1 /neq a2. Then ((bij[f[a1]])[i1],a1) /neq ((bij[f[a2]])[i2],a2). end.
      Case a1 = a2. 
        bij[f[a1]] is injective.
        Then (bij[f[a1]])[i1] /neq (bij[f[a1]])[i2].
        Then ((bij[f[a1]])[i1],a1) /neq ((bij[f[a2]])[i2],a2).
      end.
    end.
  end.
  Then Card(kappa) /subset Card(/sumset sum).
  Then kappa /subset /sum sum.
end.
Then kappa /in /sum sum \/ kappa = /sum sum.
Proof.
  kappa, /sum sum /in /Ord.
end.

Define prod[i] = kappa for i in cof(kappa).
Then prod is a sequence of cardinals.
/prod prod = Gimel[kappa].
Proof.
  /prodset prod /subset ^{cof(kappa)}kappa.
  Proof.
    Let func /in /prodset prod.
    Then func is a zffunction.
    Dom(func) = cof(kappa).
    Forall i /in cof(kappa) (func[i] /in prod[i] /\ prod[i] = kappa).    
    Then func : cof(kappa) /rightarrow kappa.
  end.
  ^{cof(kappa)}kappa /subset /prodset prod.
  Proof.
    Let func /in ^{cof(kappa)}kappa.
    Then func is a zffunction.
    Dom(func) = cof(kappa).
    Forall i /in cof(kappa) func[i] /in kappa.
    Then forall i /in cof(kappa) func[i] /in prod[i].
    Then func /in /prodset prod.
  end.
end.

Dom(sum) = Dom(prod).
Forall i /in Dom(sum) sum[i] /in prod[i].
Proof.
  Let i /in Dom(sum).
  Then i /in Card(x).
  Then f[i] /in x.
  Then f[i] /in kappa.
  Then Card(f[i]) /in kappa.
  sum[i] = Card(f[i]).
  prod[i] = kappa.
end.
Then /sum sum /in /prod prod (by Koenig).
Then kappa /in /prod prod.
Proof.
  /prod prod /in /Ord.
  kappa /in /sum sum \/ kappa = /sum sum.
  Case kappa = /sum sum. end.
  Case kappa /in /sum sum. 
    /sum sum /in /prod prod.
    Trans(/prod prod).
  end.
end.

qed.


Lemma. Let kappa /in /Card. Let cof(kappa) = kappa. Then Gimel[kappa] = 2 ^3 kappa.
Proof.
2 /subset kappa.
kappa /subset 2 ^3 kappa.
Then kappa ^3 kappa = 2 ^3 kappa.
Gimel[kappa] = kappa ^3 kappa.
qed.


Signature. Cont is a zffunction.
Axiom. Cont : /Card /rightarrow /Card.
Axiom. Let kappa /in /Card. Then Cont[kappa] = 2 ^3 kappa.

Lemma. Let x, y be sets. Let x /subset /Ord /\ y /subset /Ord. Let f be a zffunction. 
Let f : x /leftrightarrow y. Let f be an epshomo. Then f^{-1} is an epshomo.
Proof.
f^{-1} : y /leftrightarrow x.
Forall a1,a2 /in y (a1 /in a2 => (f^{-1})[a1] /in (f^{-1})[a2]).
Proof.
  Let a1,a2 /in y. Let a1 /in a2.
  Take zfsets b1,b2 such that b1 = (f^{-1})[a1] /\ b2 = (f^{-1})[a2].
  f[b1] = a1. f[b2] = a2.
  b1,b2 /in /Ord.
  Forall c1,c2 /in /Ord (c1 /in c2 \/ c2 /in c1 \/ c1 = c2).
  b1 /in b2 \/ b2 /in b1 \/ b1 = b2.
  Then b1 /in b2. 
  Proof.
    Case b1 = b2. Contradiction. end.
    Case b2 /in b1.
      f is an epshomo.
      b1,b2 /in Dom(f).
      Then f[b2] /in f[b1] (by eps).
      Then a2 /in a1. 
      Contradiction. 
    end.
    Case b1 /in b2. end.
  end.
end.
qed.

Lemma. Let x be a zfset. Let x /subset /Ord. Let y = otp(x).
Then exists f (f : y /leftrightarrow x /\ (f is an epshomo)).
Proof.
Take an epshomo f such that f : x /leftrightarrow y.
Then f^{-1} : y /leftrightarrow x.
x,y /subset /Ord.
f^{-1} is an epshomo.
qed.

Lemma. Let kappa /in /Card. Let cof(kappa) /in kappa. Then 2 ^3 kappa /subset (2 ^< kappa) ^3 cof(kappa).
Proof.
Take a zfset x such that x /subset kappa /\ x /cof kappa /\ otp(x) = cof(kappa).
Exists f (f : cof(kappa) /leftrightarrow x /\ (f is an epshomo)).
Proof.
  x /in /VV. x /subset /Ord. cof(kappa) = otp(x).
end.
Take a zffunction kap such that kap : otp(x) /leftrightarrow x /\ (kap is an epshomo).
Forall i /in cof(kappa) Card(/PP kap[i]) /subset 2 ^< kappa.
Proof.
  Let i /in cof(kappa).
  kap[i] /in kappa.
  Card(/PP kap[i]) = 2 ^3 Card(kap[i]).
  2 ^< kappa = {zfset x | exists v /in kappa x /in 2 ^3 Card(v)}.
  Then 2 ^3 Card(kap[i]) /subset 2 ^< kappa.
end.
Forall i /in cof(kappa) exists f (f : /PP kap[i] /rightarrow 2 ^< kappa /\ (f is injective)).
Proof.
  Let i /in cof(kappa).
  Card(/PP kap[i]) /subset Card(2 ^< kappa).
  /PP kap[i] <= 2 ^< kappa.
end.
Define inj[i] = (Choose a zffunction f such that (f : /PP kap[i] /rightarrow 2 ^< kappa /\ (f is injective)) in f)
for i in cof(kappa).

Forall M /in /PP kappa forall i /in cof(kappa) (M /cap kap[i] /in Dom(inj[i])).
Proof.
  Let M /in /PP kappa.
  Let i /in cof(kappa).
  Dom(inj[i]) = /PP kap[i].
  M /cap kap[i] /subset kap[i].
  M /cap kap[i] /in /PP kap[i].
end.

Forall pair /in /PP kappa /times cof(kappa) exists M,i /in /VV (M /in /PP kappa /\ i /in cof(kappa) /\ pair = (M,i)).
Define Fun[pair] = (Choose zfsets M,i such that M /in /PP kappa /\ i /in cof(kappa) /\ pair = (M,i) in (inj[i])[M /cap kap[i]])
for pair in /PP kappa /times cof(kappa).
Forall M /in /PP kappa forall i /in cof(kappa) (M,i) /in /PP kappa /times cof(kappa).
Forall M /in /PP kappa forall i /in cof(kappa) Fun[(M,i)] = (inj[i])[M /cap kap[i]].
Proof.
  Let M /in /PP kappa.
  Let i /in cof(kappa).
  Let pair = (M,i).
  Then Fun[pair] = Fun[(M,i)].
  Choose zfsets M1,i1 such that M1 /in /PP kappa /\ i1 /in cof(kappa) /\ pair = (M1,i1).
  Then M = M1 /\ i = i1.
  Then Fun[pair] = (inj[i])[M /cap kap[i]].
end.
Forall pair /in /PP kappa /times cof(kappa) exists M1,i1 /in /VV (M1 /in /PP kappa /\ i1 /in cof(kappa) /\ Fun[pair] = (inj[i1])[M1 /cap kap[i1]]).
Proof.
  Let pair /in /PP kappa /times cof(kappa).
  Choose zfsets M,i such that M /in /PP kappa /\ i /in cof(kappa) /\ pair = (M,i).
  Then Fun[pair] = Fun[(M,i)].
  Fun[(M,i)] = (inj[i])[M /cap kap[i]].
end.

Forall M /in /PP kappa forall i /in cof(kappa) (M,i) /in Dom(Fun).
Forall M /in /PP kappa exists f (Dom(f) = cof(kappa) /\ forall i /in cof(kappa) f[i] = Fun[(M,i)]).
Proof.
  Let M /in /PP kappa.
  Define f[i] = Fun[(M,i)] for i in cof(kappa).
  f is a zffunction.
  Proof.
    Let i /in cof(kappa).
    Take a zfset pair such that pair = (M,i).
    Then pair /in /PP kappa /times cof(kappa).
    Take zfsets M1,i1 such that M1 /in /PP kappa /\ i1 /in cof(kappa) /\ 
    (M1,i1) = pair /\ Fun[pair] = (inj[i1])[M1 /cap kap[i1]].
    Then M1 = M /\ i1 = i.
    Fun[pair] = (inj[i])[M /cap kap[i]].
    Then Fun[(M,i)] /in ran(inj[i]).
    Then Fun[(M,i)] /in /VV.
  end.
  Then (Dom(f) = cof(kappa) /\ forall i /in cof(kappa) f[i] = Fun[(M,i)]).
end.

Define G[M] = (Choose a zffunction f such that (Dom(f) = cof(kappa) /\ forall i /in cof(kappa) f[i] = Fun[(M,i)]) in f)
for M in /PP kappa.

G : /PP kappa /rightarrow ^{cof(kappa)}(2 ^< kappa).
Proof.
  Let alpha = ^{cof(kappa)}(2 ^< kappa).
  Forall M /in Dom(G) G[M] /in alpha.
  Proof.
    Let M /in Dom(G).
    Then M /in /PP kappa.
    Take a zffunction f such that (Dom(f) = cof(kappa) /\ forall i /in cof(kappa) f[i] = Fun[(M,i)] /\ G[M] = f).
    Then f : cof(kappa) /rightarrow 2 ^< kappa.
    Proof.
      Let i /in cof(kappa).
      Take a zfset pair such that pair = (M,i).
      Then pair /in /PP kappa /times cof(kappa).
      Take zfsets M1,i1 such that M1 /in /PP kappa /\ i1 /in cof(kappa) /\ 
      (M1,i1) = pair /\ Fun[pair] = (inj[i1])[M1 /cap kap[i1]].
      Then M1 = M /\ i1 = i.
      Fun[pair] = (inj[i])[M /cap kap[i]].
      inj[i] : /PP kap[i] /rightarrow 2 ^< kappa.
      Then (inj[i])[M /cap kap[i]] /in 2 ^< kappa.
      f[i] = Fun[(M,i)].
      Then f[i] /in 2 ^< kappa.
    end.
    Then f /in ^{cof(kappa)}(2 ^< kappa).
    Then G[M] /in alpha.
  end.
  Then G : /PP kappa /rightarrow alpha.
end.

G is injective.
Proof.
  Forall M1, M2 /in Dom(G) (M1 /neq M2 => G[M1] /neq G[M2]).
  Proof.
    Let M1, M2 /in /PP kappa.
    Let M1 /neq M2.
    Then exists z (z /in M1 /setminus M2 \/ z /in M2 /setminus M1).
    Proof.
      (not (M1 /subset M2)) \/ (not (M2 /subset M1)).
    end.
    Take a zfset z such that (z /in M1 /setminus M2 \/ z /in M2 /setminus M1).
    Then z /in kappa.
    Take a zfset i such that i /in cof(kappa) /\ z /in kap[i].
    Then M1 /cap kap[i] /neq M2 /cap kap[i].
    inj[i] is injective.
    Then (inj[i])[M1 /cap kap[i]] /neq (inj[i])[M2 /cap kap[i]].
    Proof.
      M1 /cap kap[i], M2 /cap kap[i] /in /VV.
      Proof.
        M1, M2 /in /VV.
        M1 /cap kap[i] /subset M1.
        M2 /cap kap[i] /subset M2.
      end.
      Take zfsets a1, a2 such that a1 = M1 /cap kap[i] /\ a2 = M2 /cap kap[i].
      Then a1 /neq a2.
      a1,a2 /in Dom(inj[i]).
      Then (inj[i])[a1] /neq (inj[i])[a2].
    end.
    Let pair1 = (M1,i). 
    Then pair1 /in /PP kappa /times cof(kappa).
    Fun[(M1,i)] = (inj[i])[M1 /cap kap[i]].
    Let pair2 = (M2,i). 
    Then pair2 /in /PP kappa /times cof(kappa).
    Fun[(M2,i)] = (inj[i])[M2 /cap kap[i]].
    Then G[M1] /neq G[M2].
    Proof.
      Take a zffunction f1 such that (Dom(f1) = cof(kappa) /\ forall j /in cof(kappa) f1[j] = Fun[(M1,j)] /\ G[M1] = f1).
      Take a zffunction f2 such that (Dom(f2) = cof(kappa) /\ forall j /in cof(kappa) f2[j] = Fun[(M2,j)] /\ G[M2] = f2).
      Then f1 /neq f2.
    end.
  end.
end.

Then Card(/PP kappa) /subset Card(^{cof(kappa)}(2 ^< kappa)).
Card(/PP kappa) = 2 ^3 kappa.
Card(^{cof(kappa)}(2 ^< kappa)) = (2 ^< kappa) ^3 cof(kappa).

qed.



Lemma. Let kappa /in /Card. Let cof(kappa) /in kappa. Let (exists kappap /in /Card /cap kappa forall lambda /in /Card
(kappap /subset lambda /\ lambda /in kappa => 2 ^3 kappap = 2 ^3 lambda)). Then 2 ^3 kappa = 2 ^< kappa.
Proof.
Take a zfset kappap such that kappap /in /Card /cap kappa /\ forall lambda /in /Card
(kappap /subset lambda /\ lambda /in kappa => 2 ^3 kappap = 2 ^3 lambda).
2 ^< kappa = 2 ^3 kappap.
Proof.
  2 ^< kappa = {zfset x | exists v /in kappa x /in 2 ^3 Card(v)}.
  Then 2 ^3 kappap /subset 2 ^< kappa.
  2 ^< kappa /subset 2 ^3 kappap.
  Proof.
    Let x /in 2 ^< kappa.
    Take a zfset v such that v /in kappa /\ x /in 2 ^3 Card(v).
    Card(v) /in kappa.
    kappap /subset Card(v) \/ Card(v) /in kappap.
    Proof.
      Take ordinals aa,bb such that aa = kappap /\ bb = Card(v).
      Then aa /in bb \/ bb /in aa \/ aa = bb.
      Then aa /subset bb \/ bb /in aa.
    end.
    Case kappap /subset Card(v). 
      Card(v) /in /Card.
      Then 2 ^3 Card(v) = 2 ^3 kappap.
    end.
    Case Card(v) /in kappap.
      Then 2 ^3 Card(v) /subset 2 ^3 kappap.
    end.
  end.
end.

2 ^< kappa /subset 2 ^3 kappa.
Proof.
  2 ^3 kappap /subset 2 ^3 kappa.
end.

2 ^3 kappa /subset 2 ^< kappa.
Proof.
  2 ^3 kappa /subset (2 ^< kappa) ^3 cof(kappa).
  2 ^< kappa = 2 ^3 kappap.
  Then 2 ^3 kappa /subset (2 ^3 kappap) ^3 cof(kappa).
  (2 ^3 kappap) ^3 cof(kappa) = 2 ^3 (kappap *3 cof(kappa)).
  2 ^3 (kappap *3 cof(kappa)) /subset 2 ^3 kappap.
  Proof.
    kappap, cof(kappa) /in /Ord.
    Then kappap /in cof(kappa) \/ cof(kappa) /in kappap \/ kappap = cof(kappa).
    Case kappap = cof(kappa).
      Then kappap *3 cof(kappa) = kappap.
    end.
    Case kappap /in cof(kappa).
      Then kappap /subset cof(kappa).
      Then kappap *3 cof(kappa) /subset cof(kappa) *3 cof(kappa).
      Proof.
        kappap /times cof(kappa) /subset cof(kappa) /times cof(kappa).
        Then Card(kappap /times cof(kappa)) /subset Card(cof(kappa) /times cof(kappa)).
      end.
      cof(kappa) *3 cof(kappa) = cof(kappa).
      Then kappap *3 cof(kappa) /subset cof(kappa).
      Then 2 ^3 (kappap *3 cof(kappa)) /subset 2 ^3 cof(kappa).
      Proof.
        Take cardinals aa, bb such that aa = kappap *3 cof(kappa) /\ bb = cof(kappa).
        0 /in 2.
        aa /subset bb.
        Then 2 ^3 aa /subset 2 ^3 bb.
      end.
      2 ^3 cof(kappa) = 2 ^3 kappap.
    end.
    Case cof(kappa) /in kappap.
      Then cof(kappa) /subset kappap.
      Then kappap *3 cof(kappa) /subset kappap *3 kappap.
      Proof.
        kappap /times cof(kappa) /subset kappap /times kappap.
        Then Card(kappap /times cof(kappa)) /subset Card(kappap /times kappap).
      end.
      kappap *3 kappap = kappap.
      Then kappap *3 cof(kappa) /subset kappap.
      Then 2 ^3 (kappap *3 cof(kappa)) /subset 2 ^3 kappap.
      Proof.
        Take cardinals aa, bb such that aa = kappap *3 cof(kappa) /\ bb = kappap.
        0 /in 2.
        aa /subset bb.
        Then 2 ^3 aa /subset 2 ^3 bb.
      end.
    end.
  end.
end.

qed.


Lemma. Let kappa /in /Card. Let cof(kappa) /in kappa. Let (forall kappap /in /Cd /cap kappa exists lambda /in /Cd /cap kappa
(kappap /in lambda /\ 2 ^3 kappap /in 2 ^3 lambda)). Then 2 ^3 kappa = Gimel[2 ^< kappa].
Proof.
Take an ordinal alpha such that kappa = Alef[alpha].
alpha /in /Lim.
Proof by contradiction. Assume the contrary.
  alpha /neq 0.
  Then alpha /in /Succ.
  Take an ordinal beta such that alpha = beta + 1.
  cof(Alef[beta + 1]) = Alef[beta + 1].
  Alef[beta + 1] = kappa.
  Then cof(kappa) = kappa.
  Contradiction.
end.
Then cof(kappa) = cof(alpha).
cof(alpha) /in cofset2(alpha).
Take a zfset xa such that xa /subset alpha /\ xa /cof alpha /\ otp(xa) = cof(alpha).
Let x = Alef^[xa].
x /subset kappa.
Proof.
  Let y /in x.
  Take a zfset ya such that ya /in xa /\ y = Alef[ya].
  Then ya /in alpha.
  Then Alef[ya] /in Alef[alpha].
  Then y /in kappa.
end.
x /cof kappa.
Proof.
  Let lambda /in kappa.
  alpha /in /Lim.
  Then Alef[alpha] = {zfset xx | exists beta /in alpha xx /in Alef[beta]}.
  Take a zfset beta such that beta /in alpha /\ lambda /in Alef[beta].
  Take a zfset b such that b /in xa /\ beta /in b.
  Then Alef[beta] /subset Alef[b].
  Then lambda /in Alef[b].
  Alef[b] /in x.
end.
otp(x) = cof(kappa).
Proof.
  cof(kappa) = otp(xa).
  Exists f (f : cof(kappa) /leftrightarrow xa /\ (f is an epshomo)).
  Proof.
    xa /in /VV. xa /subset /Ord. cof(kappa) = otp(xa).
  end.
  Take a zffunction f such that f : cof(kappa) /leftrightarrow xa /\ (f is an epshomo).
  Let g = Alef /circ f.
  g : cof(kappa) /rightarrow x.
  Proof.
    Dom(g) = cof(kappa).
    Let i /in cof(kappa).
    Then f[i] /in xa.
    Then Alef[f[i]] /in x.
    Then g[i] /in x.
  end.
  g is injective.
  Proof.
    Let a1,a2 /in Dom(g). Let a1 /neq a2.
    Then g[a1] /neq g[a2].
    Proof.
      f is injective.
      Then f[a1] /neq f[a2].
      f[a1], f[a2] /in xa.
      Then f[a1], f[a2] /in /Ord.
      Then Alef[f[a1]] /neq Alef[f[a2]].
    end.
  end.
  ran(g) = x.
  Proof.
    Let y /in x.  
    Take a zfset ya such that ya /in xa /\ y = Alef[ya].
    Take a zfset za such that za /in cof(kappa) /\ f[za] = ya.
    Then g[za] = y.
    Then y /in ran(g).
  end.
  Then g : cof(kappa) /leftrightarrow x.
  g is an epshomo.
  Proof.
    Forall a1,a2 /in Dom(g) (a1 /in a2 => g[a1] /in g[a2]).
    Proof.
      Let a1, a2 /in Dom(g). Let a1 /in a2.
      f is an epshomo.
      a1,a2 /in Dom(f).
      Then f[a1] /in f[a2] (by eps).
      f[a1], f[a2] /in xa.
      Then f[a1], f[a2] /in /Ord.
      Then Alef[f[a1]] /in Alef[f[a2]].
      Then g[a1] /in g[a2].
    end.
  end.
  g^{-1} : x /leftrightarrow cof(kappa).
  x /subset /Ord.
  cof(kappa) /subset /Ord.
  g^{-1} is an epshomo.
  Then otp(x) = cof(kappa).
end.
Exists f (f : cof(kappa) /leftrightarrow x /\ (f is an epshomo)).
Proof.
  x /in /VV. x /subset /Ord. cof(kappa) = otp(x).
end.
Take a zffunction kap such that kap : cof(kappa) /leftrightarrow x /\ (kap is an epshomo).
Forall i1,i2 /in cof(kappa) (i1 /in i2 => kap[i1] /in kap[i2]) (by eps).
Forall i /in cof(kappa) kap[i] /in /Card.
Proof.
  Let i /in cof(kappa).
  Then kap[i] /in x.
  Take a zfset j such that j /in xa /\ kap[i] = Alef[j].
  Alef[j] /in /Cd.
  /NN /subset Alef[j].
  Then Alef[j] /in /Card.
end.
Card(x) = cof(kappa).
cof(kappa) = cof(2 ^< kappa).
Proof.
  cof(2 ^< kappa) /subset cof(kappa).
  Proof.
    Define f[i] = 2 ^3 kap[i] for i in cof(kappa).
    f is a zffunction.
    Proof.
      Let i /in cof(kappa).
      Then f[i] /in /VV.
    end.
    Let M = f^[cof(kappa)].
    Then Card(M) /subset cof(kappa).
    M /subset 2 ^< kappa.
    Proof.
      Let a /in M.
      Take a zfset b such that b /in cof(kappa) /\ a = f[b].
      Then a = 2 ^3 kap[b].
      kap[b] /in kappa.
      kap[b] /in /Cd /cap kappa.
      Take a zfset c such that c /in /Cd /cap kappa /\ kap[b] /in c /\ 2 ^3 kap[b] /in 2 ^3 c.
      Then a /in 2 ^< kappa.
      Proof.
        2 /in /Cd.
        2 ^< kappa = {zfset z | exists v /in kappa z /in 2 ^3 Card(v)}.
        c /in kappa.
        Card(c) = c.
        a /in 2 ^3 Card(c).
      end.
    end.
    M /cof 2 ^< kappa.
    Proof.
      Forall a1 /in 2 ^< kappa exists a2 /in M a1 /in a2.
      Proof.
        Let a /in 2 ^< kappa.
        2 ^< kappa = {zfset z | exists v /in kappa z /in 2 ^3 Card(v)}.
        Take a zfset v such that v /in kappa /\ a /in 2 ^3 Card(v).
        Take a zfset b such that b /in x /\ v /in b.
        Take a zfset c such that c /in cof(kappa) /\ kap[c] = b.
        Card(v) /subset kap[c].
        Then 2 ^3 Card(v) /subset 2 ^3 kap[c].
        Proof.
          Forall alphaa, betaa, gammaa /in /Cd ((betaa /subset gammaa /\ 0 /in alphaa) => alphaa ^3 betaa /subset alphaa ^3 gammaa).
          Take cardinals aa, bb such that aa = Card(v) /\ bb = kap[c].
          2,aa,bb /in /Cd.
          0 /in 2.
          aa /subset bb.
          Then 2 ^3 aa /subset 2 ^3 bb.
        end.
        2 ^3 kap[c] = f[c].
        Then 2 ^3 kap[c] /in M.
        a /in 2 ^3 kap[c].
      end.
    end.
    Then Card(M) /in cofset2(2 ^< kappa).
    Then /bigcap cofset2(2 ^< kappa) /subset Card(M).
    cof(2 ^< kappa) = /bigcap cofset2(2 ^< kappa).
    Then cof(2 ^< kappa) /subset Card(M).
  end.
  
  cof(2 ^< kappa) /notin cof(kappa).
  Proof by contradiction. Assume the contrary.
    Take a cardinal beta such that beta = 2 ^< kappa.
    cof(beta) /in cofset2(beta).
    Take a zfset z such that z /subset beta /\ z /cof beta /\ Card(z) = cof(beta).

    Define ind[delta] = {i /in cof(kappa) | delta /subset 2 ^3 kap[i]} for delta in z.
    Forall delta /in z ind[delta] /neq /emptyset.
    Proof.
      Let delta /in z.
      Then delta /in 2 ^< kappa.
      Forall aa /in /Cd forall bb /in /Card (aa ^< bb = {zfset y | exists v /in bb y /in aa ^3 Card(v)}).
      2 /in /Cd.
      kappa /in /Card.
      Then 2 ^< kappa = {zfset y | exists v /in kappa y /in 2 ^3 Card(v)}.
      Take a zfset v such that v /in kappa /\ delta /in 2 ^3 Card(v).
      Take a zfset a1 such that a1 /in x /\ v /in a1.
      Take a zfset a2 such that a2 /in cof(kappa) /\ kap[a2] = a1.
      Card(v) /in a1.
      Then 2 ^3 Card(v) /subset 2 ^3 kap[a2].
      Then delta /subset 2 ^3 kap[a2].
      Then a2 /in ind[delta].
    end.
    Forall delta /in z /bigcap ind[delta] /in cof(kappa).
    Proof.
      Let delta /in z.
      ind[delta] /subset cof(kappa).
      ind[delta] /neq /emptyset.
      Take a zfset aa such that aa /in ind[delta].
      Then /bigcap ind[delta] /in /VV.
      Proof.
        /bigcap ind[delta] /subset aa.
      end.
      Trans(/bigcap ind[delta]).
      Proof.
        ind[delta] /subset /Ord.
      end.
      Then /bigcap ind[delta] /in /Ord.
      aa /in cof(kappa).
      /bigcap ind[delta] /subset aa.
      Then /bigcap ind[delta] /in aa \/ /bigcap ind[delta] = aa.
      Proof.
        Take ordinals a1,a2 such that a1 = /bigcap ind[delta] /\ a2 = aa.
        Then a1 /in a2 \/ a2 /in a1 \/ a1 = a2.
        a1 /subset a2.
        Then not (a2 /in a1).
      end.
      Then /bigcap ind[delta] /in cof(kappa).
      Proof.
        Case /bigcap ind[delta] /in aa. 
          aa /in cof(kappa).
          Trans(cof(kappa)).
        end.
        Case /bigcap ind[delta] = aa. end.
      end.
    end.
    Define f[delta] = /bigcap ind[delta] for delta in z.
    f is a zffunction.
    Proof.
      Let delta /in Dom(f). Then f[delta] /in cof(kappa).
      Then f[delta] /in /VV.
    end.
    Let zz = f^[z].
    Then zz /subset cof(kappa).
    Proof.
      Let a1 /in zz.
      Take a zfset a2 such that a2 /in z /\ a1 = f[a2].
      Then a1 /in cof(kappa).
    end.
    zz /cof cof(kappa).
    Proof.
      Let a /in cof(kappa).
      kap[a] /in kappa.
      Forall kappap /in /Cd /cap kappa exists lambdap /in /Cd /cap kappa (kappap /in lambdap /\ 2 ^3 kappap /in 2 ^3 lambdap).
      kap[a] /in /Cd /cap kappa.
      Then exists lambdap /in /Cd /cap kappa (kap[a] /in lambdap /\ 2 ^3 kap[a] /in 2 ^3 lambdap).
      Take a cardinal lambda such that lambda /in /Cd /cap kappa /\ kap[a] /in lambda /\ 2 ^3 kap[a] /neq 2 ^3 lambda.
      2 ^3 kap[a] /in 2 ^3 lambda.
      Proof.
        2 ^3 kap[a] /subset 2 ^3 lambda.
        Take ordinals aa, bb such that aa = 2 ^3 kap[a] /\ bb = 2 ^3 lambda.
        Then aa /in bb \/ bb /in aa \/ aa = bb.
        aa /subset bb.
        aa /neq bb.
        Then aa /in bb.
      end.
      Then 2 ^3 kap[a] /in 2 ^< kappa.
      Proof.
        Forall aa /in /Cd forall bb /in /Card (aa ^< bb = {zfset y | exists v /in bb y /in aa ^3 Card(v)}).
        2 /in /Cd.
        kappa /in /Card.
        Then 2 ^< kappa = {zfset y | exists v /in kappa y /in 2 ^3 Card(v)}.
        lambda /in kappa.
        Card(lambda) = lambda.
        2 ^3 kap[a] /in 2 ^3 Card(lambda).
      end.
      Take a zfset b such that b /in z /\ 2 ^3 kap[a] /in b.
      Then f[b] /in zz.
      a /notin ind[b].
      Proof.
        not (b /subset 2 ^3 kap[a]).
      end.
      /bigcap ind[b] /in ind[b].
      Proof by contradiction. Assume the contrary.
        Let n = /bigcap ind[b].
        ind[b] /subset /Ord.
        Forall m /in ind[b] (n /subset m /\ n /neq m).
        Then forall m /in ind[b] n /in m.
        Proof.
          Let m /in ind[b].
          Then m,n /in /Ord.
          Then m /in n \/ n /in m \/ n = m.
          n /subset m /\ n /neq m.
          Then n /in m.
        end.
        Then n /in /bigcap ind[b].
        Contradiction.
      end.
      Then f[b] /in ind[b].
      Then b /subset 2 ^3 kap[f[b]].
      2 ^3 kap[a] /in b.
      Then 2 ^3 kap[a] /in 2 ^3 kap[f[b]].
      Then kap[a] /in kap[f[b]].
      Proof.
        Take ordinals a1,a2 such that a1 = kap[a] /\ a2 = kap[f[b]].
        Then a1 /in a2 \/ a2 /in a1 \/ a1 = a2.
        Case a1 /in a2. end.
        Case a2 /in a1.
          Then 2 ^3 a2 /subset 2 ^3 a1.
          Contradiction.
        end.
        Case a1 = a2. 
          Then 2 ^3 a1 = 2 ^3 a2.
          Contradiction.
        end.
      end.
      Then a /in f[b].
      Proof.
        a, f[b] /in /Ord.
        Then a /in f[b] \/ f[b] /in a \/ a = f[b].
        a, f[b] /in Dom(kap).
        Case a = f[b].
          Then kap[a] = kap[f[b]].
          Contradiction.
        end.
        Case a /in f[b]. end.
        Case f[b] /in a.
          Then kap[f[b]] /in kap[a].
          kap[a] /in kap[f[b]].
          Trans(kap[a]).
          Then kap[a] /in kap[a].
          Contradiction.
        end.
      end.
    end.
    
    Card(zz) /in cofset2(cof(kappa)).
    Then /bigcap cofset2(cof(kappa)) /subset Card(zz).
    Then cof(cof(kappa)) /subset Card(zz).
    cof(cof(kappa)) = cof(kappa).
    Then cof(kappa) /subset Card(zz).
    
    Card(zz) /subset Card(z).
    Card(z) = cof(beta).
    cof(beta) /in cof(kappa).

    Contradiction.
  end.
  
  Take ordinals a1,a2 such that a1 = cof(2 ^< kappa) /\ a2 = cof(kappa).
  Then a1 /in a2 \/ a2 /in a1 \/ a1 = a2.
  a1 /subset a2.
  a1 /notin a2.
  Then a1 = a2.
  
end.

2 ^3 kappa /subset Gimel[2 ^< kappa].
Proof.
  2 ^3 kappa /subset (2 ^< kappa) ^3 cof(kappa).
  cof(kappa) = cof(2 ^< kappa).
  Then (2 ^< kappa) ^3 cof(kappa) = (2 ^< kappa) ^3 cof(2 ^< kappa).
  (2 ^< kappa) ^3 cof(2 ^< kappa) = Gimel[2 ^< kappa].
end.

Gimel[2 ^< kappa] /subset 2 ^3 kappa.
Proof.
  Gimel[2 ^< kappa] = (2 ^< kappa) ^3 cof(2 ^< kappa).
  cof(2 ^< kappa) = cof(kappa).
  Then Gimel[2 ^< kappa] = (2 ^< kappa) ^3 cof(kappa).
  2 ^< kappa /subset 2 ^3 kappa.
  Proof.
    Let a /in 2 ^< kappa.
    2 ^< kappa = {zfset y | exists v /in kappa y /in 2 ^3 Card(v)}.
    Take a zfset v such that v /in kappa /\ a /in 2 ^3 Card(v).
    Then Card(v) /in kappa.
    Then 2 ^3 Card(v) /subset 2 ^3 kappa.
    Then a /in 2 ^3 kappa.
  end.
  Then (2 ^< kappa) ^3 cof(kappa) /subset (2 ^3 kappa) ^3 cof(kappa).
  Proof.
    Take cardinals a,b,c such that a = 2 ^< kappa /\ b = 2 ^3 kappa /\ c = cof(kappa).
    a,b,c /in /Cd.
    Then a /subset b.
    Forall alphaa, betaa, gammaa /in /Cd (alphaa /subset betaa => alphaa ^3 gammaa /subset betaa ^3 gammaa).
    Then a ^3 c /subset b ^3 c.
  end.
  (2 ^3 kappa) ^3 cof(kappa) = 2 ^3 (kappa *3 cof(kappa)).
  cof(kappa) /subset kappa.
  Then kappa *3 cof(kappa) /subset kappa *3 kappa.
  Proof.
    kappa /times cof(kappa) /subset kappa /times kappa.
    Then Card(kappa /times cof(kappa)) /subset Card(kappa /times kappa).
  end.
  kappa *3 kappa = kappa.
  Then kappa *3 cof(kappa) /subset kappa.
  Then 2 ^3 (kappa *3 cof(kappa)) /subset 2 ^3 kappa.
  Proof.
    Take cardinals aa, bb such that aa = (kappa *3 cof(kappa)) /\ bb = kappa.
    2,aa,bb /in /Cd.
    0 /in 2.
    aa /subset bb.
    Then 2 ^3 aa /subset 2 ^3 bb.
  end.
end.

qed.




Lemma. Contradiction.


