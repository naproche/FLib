# 18-Fodors Lemma

# We proof Fodors Lemma.

# Main results:

# - Fodors Lemma
# - the derivation of a club is again closed unbounded in kappa
# - the subset of ordinals with cofinality alpha is stationary in kappa



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

# New Lemma
Lemma. Let lambda /in /Ord. Let lambda /neq 0. Let forall a /in lambda a+1 /in lambda. Then lambda /in /Lim.

Axiom Infinity. Exists x (/emptyset /in x /\ forall y /in x ((y /plus 1) /in x) ).

Axiom. Let alpha be an ordinal. Then alpha + 1 is an ordinal.
Axiom. Let alpha be an ordinal. Let x be an object. Let x /in alpha. Then x is an ordinal.
Axiom TotalOrder. Let alpha,beta /in /Ord. Then alpha /in beta \/ beta /in alpha \/ alpha = beta.
Axiom. Let A /subset /Ord. Let A /neq /emptyset. Then exists alpha (alpha /in A /\ forall beta /in A (alpha = beta \/ alpha /in beta)).
Axiom. Let alpha, beta be ordinals. Let alpha /in beta. Then alpha /subset beta.

Signature. Let alpha /in /Succ. alpha - 1 is an ordinal.

Axiom. Let alpha /in /Succ. Let beta be an ordinal. alpha - 1 = beta iff alpha = beta + 1.

Axiom. Let x /in /Lim. Let y /in x. Then y + 1 /in x.

Axiom. Forall alpha, beta /in /Ord (alpha -<- beta iff alpha /in beta).




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

Axiom. Let x, y be zfsets. Let Card(x) /subset Card(y). Then x <= y.

Axiom. Let x, y be zfsets. Let x <= y. Let y <= x. Then Card(x) = Card(y).
Axiom. Let x, y be zfsets. Let x <= y. Let y <= x. Then x /tilde y.
Axiom. Let x be a zfset. Let f be a zffunction. Let x /subset Dom(f). Then Card(f^[x]) /subset Card(x).
Axiom. Let x be a zfset. Let x /neq /emptyset. Let alpha /in /Ord. Let Card(x) /subset alpha. Then exists f (f : alpha /rightarrow x /\ ran(f) = x).

Definition. The class of cardinals is
{ordinal alpha | alpha is a cardinal}.
Let /Cd stand for the class of cardinals.

Definition. The class of infinite cardinals is
{ordinal alpha | (alpha is a cardinal) /\ /NN /subset alpha}.
Let /Card stand for the class of infinite cardinals.

Axiom. Forall n /in /NN Card(n) = n.
Axiom. Card(/NN) = /NN.

Axiom. Let x be a zfset. Then x < /PP x.
Axiom. /Ord is a proper class.
Axiom. /Cd is a proper class.
Axiom. /Card is a proper class.

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
Axiom Exp0. Let kappa, lambda /in /Cd. Let /NN /subset kappa. Let 2 /subset lambda. Let lambda /subset (2 ^3 kappa).
Then lambda ^3 kappa = 2 ^3 kappa.

Axiom. Let alpha /in /Cd. Let alpha /neq 0. Then 0 ^3 alpha = 0.
Axiom. Forall kappa /in /Cd (kappa ^3 1 = kappa).
Axiom. Let kappa /in /Cd. Then 2 ^3 kappa = Card(/PP kappa).
Axiom. Let x,y /in /VV. Let x /tilde y. Then /PP x /tilde /PP y.
Axiom. Let x /in /VV. Then Card(/PP x) = 2 ^3 Card(x).
Axiom. Let kappa /in /Cd. Then kappa /in 2 ^3 kappa.
Axiom. Let kappa /in /Cd. Then kappa *3 1 = kappa.
Axiom Exp1. Let alpha, beta, gamma /in /Cd. Let beta /subset gamma. Let 0 /in alpha \/ 0 /in beta. Then alpha ^3 beta /subset alpha ^3 gamma.
Axiom Exp2. Let alpha, beta, gamma /in /Cd. Let alpha /subset beta. Then alpha ^3 gamma /subset beta ^3 gamma.




# Alefs


Signature. Plus is a zffunction.
Axiom. Plus : /Ord /rightarrow /Cd.
Axiom. Let alpha /in /Ord. Then Plus[alpha] = {ordinal beta | forall kappa /in /Cd (alpha /in kappa => beta /in kappa)}.
# New Lemma
Lemma. Let alpha /in /Ord. Forall kappa /in /Cd (alpha /in kappa => Plus[alpha] /subset kappa).

Signature. Alef is a zffunction.
Axiom. Alef : /Ord /rightarrow /Cd.
Axiom. Alef[/emptyset] = /NN.
Axiom. Let alpha /in /Succ. Let beta /in /Ord. Let alpha = beta + 1. Then Alef[beta] /in /Ord /\ Alef[alpha] = Plus[Alef[beta]].
Axiom. Let alpha /in /Lim. Then Alef[alpha] = {zfset x | exists beta /in alpha x /in Alef[beta]}.

Axiom. Let x /in /VV. Let x /subset /Cd. Then Card(/bigcup x) = /bigcup x.
Axiom. Forall alpha, beta (alpha /in beta => Alef[alpha] /in Alef[beta]).

# New Lemma
Lemma. Let alpha, beta /in /Ord. Let alpha /subset beta. Then Alef[alpha] /subset Alef[beta].
Proof.
alpha /in beta \/ alpha = beta.
Case alpha /in beta. 
  Then Alef[alpha] /in Alef[beta]. 
  Alef[beta] /in /Ord. 
end.
Case alpha = beta. end.
qed.

Axiom. Alef is injective.
Axiom. Forall alpha /in /Ord (alpha /subset Alef[alpha]).
Axiom. Let kappa be a cardinal. Let /NN /subset kappa. Then exists alpha (kappa = Alef[alpha]).

Axiom. Let kappa, lambda /in /Cd. Let 2 /subset kappa. Let /NN /subset lambda.
Then /NN /subset kappa ^3 lambda.
Axiom. Let kappa, lambda /in /Cd. Let 2 /subset kappa. Let /NN /subset lambda. Then kappa ^3 lambda /in /Lim.


Signature. A successor cardinal is a cardinal.
Signature. A limit cardinal is a cardinal.

Definition. Let kappa be a cardinal. kappa is infinite iff /NN /subset kappa.
Axiom. Let kappa be a cardinal. Then kappa is a successor cardinal iff exists alpha /in /Ord (kappa = Alef[alpha + 1]).
Axiom. Let kappa be a cardinal. kappa is a limit cardinal iff exists lambda /in /Lim (kappa = Alef[lambda]).



# Order-Type


Signature. An epshomo is a notion.

Axiom. Let f be an epshomo. Then f is a zffunction.
Axiom. Let f be a zffunction. Then f is an epshomo iff
forall x /in Dom(f) (f^[x /cap Dom(f)] /subset f[x]).

Axiom eps. Let f be an epshomo. Let x,y /in Dom(f). Let x /in y. Then f[x] /in f[y].
Axiom. Let f be a zffunction. Let forall x,y /in Dom(f) (x /in y => f[x] /in f[y]). Then f is an epshomo.
Axiom. Let x, y be sets. Let x /subset /Ord. Let f be a zffunction. 
Let f : x /leftrightarrow y. Let f be an epshomo. Then f^{-1} is an epshomo.

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

Axiom. Let x /subset /Ord. Let y /in /Ord \/ y = /Ord. Then otp(x) = y iff exists f ((f is an epshomo) /\ f : x /leftrightarrow y).
Lemma. Let x /subset /Ord. Let y /in /Ord \/ y = /Ord. Let exists f ((f is an epshomo) /\ f : x /leftrightarrow y). Then otp(x) = y.
Lemma. Let x /subset /Ord. Let y /in /Ord \/ y = /Ord. Let exists f ((f is an epshomo) /\ f : y /leftrightarrow x). Then otp(x) = y.
Proof.
Take a zffunction g such that ((g is an epshomo) /\ g : y /leftrightarrow x).
y /subset /Ord.
Then g^{-1} is an epshomo.
g^{-1} : x /leftrightarrow y.
Then otp(x) = y.
qed.
Axiom. Let x be a zfset. Let x /subset /Ord. Let y = otp(x). Then exists f (f : y /leftrightarrow x /\ (f is an epshomo)).
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

Axiom. Forall lambda /in /Lim cof(lambda) /subset lambda.
Axiom. Forall lambda /in /Lim (cof(lambda) is regular).
Axiom. Forall alpha /in /Ord Alef[alpha] /in /Lim.
Lemma. Let kappa be a limit cardinal. Then kappa /in /Lim.
Lemma. Let kappa be a successor cardinal. Then kappa /in /Lim.
Proof.
Take an ordinal alpha such that kappa = Alef[alpha + 1].
qed.
Axiom. Let alpha /in /Lim. Then cof(Alef[alpha]) = cof(alpha).
Axiom. Forall alpha /in /Ord cof(Alef[alpha + 1]) = Alef[alpha + 1].
Lemma. Let kappa be a successor cardinal. Then kappa is regular.

# New Lemma

Lemma. Let f be an epshomo. Let alpha /in /Lim. Let alpha /subset Dom(f). Let ran(f) /subset /Ord. Then /bigcup f^[alpha] /in /Lim /\ cof(/bigcup f^[alpha]) = cof(alpha).
Proof.
/bigcup f^[alpha] /in /Ord.
Proof.
  /bigcup f^[alpha] /in /VV.
  f^[alpha] /subset /Ord.
  Then Trans(/bigcup f^[alpha]).
end.
/bigcup f^[alpha] /in /Lim.
Proof.
  /bigcup f^[alpha] /neq 0.
  Proof.
    0,1 /in Dom(f).
    0 /in 1.
    Then f[0] /in f[1] (by eps).
    f[1] /in f^[alpha].
    Then f[0] /in /bigcup f^[alpha].
  end.
  Let a /in /bigcup f^[alpha].
  Take a zfset b such that b /in f^[alpha] /\ a /in b.
  Take a zfset c such that c /in alpha /\ b = f[c].
  c, c+1 /in Dom(f).
  c /in c+1.
  Then f[c] /in f[c+1] (by eps).
  Then a+1 /in f[c+1].
  Proof.
    f[c] /in /Ord.
    a /in f[c].
    a /subset f[c].
    Then a+1 /subset f[c].
    a+1, f[c] /in /Ord.
    Then a+1 /in f[c] \/ f[c] /in a+1 \/ a+1 = f[c] (by TotalOrder).
    f[c] /notin a+1.
    Then a+1 /in f[c] \/ a+1 = f[c].
    f[c] /in f[c+1].
    Case a+1 = f[c]. end.
    Case a+1 /in f[c]. Trans(f[c+1]). end.
  end.
  f[c+1] /in f^[alpha].
  Then a+1 /in /bigcup f^[alpha].
end.

cof(/bigcup f^[alpha]) /subset cof(alpha).
Proof.
  Take a zfset x such that x /subset alpha /\ x /cof alpha /\ Card(x) = cof(alpha).
  Let y = f^[x].
  Then y /subset /bigcup f^[alpha].
  Proof.
    Let a /in y.
    Take a zfset b such that b /in x /\ a = f[b].
    Then b,b+1 /in Dom(f).
    b /in b+1.
    Then f[b] /in f[b+1] (by eps).
    f[b+1] /in f^[alpha].
    Then a /in /bigcup f^[alpha].
  end.
  y /cof /bigcup f^[alpha].
  Proof.
    y /subset /bigcup f^[alpha].
    Let a /in /bigcup f^[alpha].
    Take a zfset b such that b /in f^[alpha] /\ a /in b.
    Take a zfset c such that c /in alpha /\ b = f[c].
    Take a zfset d such that d /in x /\ c /in d.
    c,d /in Dom(f).
    Then f[c] /in f[d] (by eps).
    Then f[d] /in y.
    f[d] /in /Ord.
    Then a /in f[d].
  end.
  Card(y) = Card(x).
  Proof.
    f /upharpoonright x : x /leftrightarrow y.
    Proof.
      Dom(f /upharpoonright x) = x.
      ran(f /upharpoonright x) = y.
      f /upharpoonright x is injective.
      Proof.
        Let a1,a2 /in x.
        Let a1 /neq a2.
        Then f[a1] /neq f[a2].
        Proof.
          Forall b1, b2 /in /Ord (b1 /in b2 \/ b2 /in b1 \/ b1 = b2).
          a1,a2 /in /Ord.
          Then a1 /in a2 \/ a2 /in a1 \/ a1 = a2.
          a1 /in a2 \/ a2 /in a1.
          Case a1 /in a2. 
            a1,a2 /in Dom(f). 
            Then f[a1] /in f[a2] (by eps). 
          end.
          Case a2 /in a1. 
            a1,a2 /in Dom(f).
            Then f[a2] /in f[a1] (by eps). 
          end.
        end.
      end.
    end.
  end.
  Then Card(y) /in cofset2(/bigcup f^[alpha]).
  Then /bigcap cofset2(/bigcup f^[alpha]) /subset Card(y).
end.

cof(alpha) /subset cof(/bigcup f^[alpha]).
Proof.
  Take a limit ordinal lambda such that lambda = /bigcup f^[alpha].
  Take a zfset x such that x /subset lambda /\ x /cof lambda /\ 
  Card(x) = cof(lambda).
  Forall y /in x exists beta /in alpha y /in f[beta].
  Define g[n] = (choose zfset beta such that beta /in alpha /\ n /in f[beta] in beta) 
  for n in x.
  g is a zffunction.
  Proof.
    Let n /in x.
    Then g[n] /in /VV.
  end.
  Let y = g^[x].
  Then y /subset alpha.
  y /cof alpha.
  Proof.
    Let beta /in alpha.
    Then f[beta] /in /bigcup f^[alpha].
    Proof.
      beta, beta + 1 /in Dom(f).
      beta /in beta + 1.
      Then f[beta] /in f[beta + 1] (by eps).
      f[beta + 1] /in f^[alpha].
    end.
    Take a zfset z such that z /in x /\ f[beta] /in z.
    Then g[z] /in y.
    z /in f[g[z]].
    Then f[beta] /in f[g[z]].
    Then beta /in g[z].
    Proof.
      beta, g[z] /in /Ord.
      Then beta /in g[z] \/ g[z] /in beta \/ g[z] = beta.
      Case beta /in g[z]. end.
      Case g[z] /in beta.
        g[z],beta /in Dom(f).
        Then f[g[z]] /in f[beta] (by eps).
        Take ordinals a1,a2 such that a1 = f[beta] /\ a2 = f[g[z]].
        Then a1 /in a2 /\ a2 /in a1.
        Contradiction. 
      end.
      Case g[z] = beta. 
        Then f[beta] = f[g[z]]. 
        Contradiction. 
      end.
    end.
  end.
  Card(y) /subset Card(x).
  Proof.
    g is a zffunction.
    x /subset Dom(g).
    Then Card(g^[x]) /subset Card(x).
  end.
  Card(y) /in cofset2(alpha).
  Then /bigcap cofset2(alpha) /subset Card(y).
  Then /bigcap cofset2(alpha) /subset Card(x).
end.

qed.










# Inductive function composition

Signature. f ^ n is an object.
Axiom. Let f be a zffunction. Let ran(f) /subset Dom(f). Let n /in /NN. Then f ^ n is a function.
Axiom. Let f be a zffunction. Let ran(f) /subset Dom(f). Let n /in /NN. Then Dom(f^n) = Dom(f).
Axiom. Let f be a zffunction. Let ran(f) /subset Dom(f). Let x /in Dom(f). Then (f^0)[x] = x.
Axiom. Let f be a zffunction. Let ran(f) /subset Dom(f). Let x /in Dom(f). Forall n /in /NN ((f^n)[x] /in Dom(f) /\ (f^(n+1))[x] = f[((f^n)[x])]).

Axiom. Let f be a zffunction. Let ran(f) /subset Dom(f). Let n /in /NN. Let n /neq 0. Let x /in Dom(f). Then (x /in Dom(f^(n-1))) /\ (f^(n-1))[x] /in Dom(f) /\ (f^(n))[x] = f[((f^(n-1))[x])].
Axiom. Let f be a zffunction. Let ran(f) /subset Dom(f). Then forall n /in /NN (f^n is a zffunction).
Axiom. Let f be a zffunction. Let ran(f) /subset Dom(f). Then forall n /in /NN ((f^n is a zffunction) /\ (ran(f^n) /subset Dom(f))).
Axiom. Let f be a zffunction. Let ran(f) /subset Dom(f). Then forall n /in /NN (f ^ (n+1) = f /circ (f ^ n)).
Axiom. Let f be a zffunction. Let ran(f) /subset Dom(f). Let n /in /NN. Let n /neq 0. Then ran(f^(n-1)) /subset Dom(f) /\ (f ^ (n) = f /circ (f ^ (n-1))).




# Closed unbounded sets


Definition. The class of cardinals with uncountable cofinality is
{kappa /in /Card | Alef[1] /subset cof(kappa)}.
Let /BigCard stand for the class of cardinals with uncountable cofinality.

Definition. Let kappa /in /Lim. Let C /subset kappa. C is closed in kappa iff
(forall lambda /in /Lim /cap kappa (C /cap lambda /cof lambda => lambda /in C)).
Let C /closed k stand for C is closed in k.

Definition. Let kappa /in /Lim. Let C /subset kappa. C is closed unbounded in kappa iff
(C /cof kappa /\ (C is closed in kappa)).
Let C /club k stand for C is closed unbounded in k.

Definition. Let kappa /in /Lim. The set of clubs in kappa is
{X /subset kappa | X /club kappa}.
Let Cl(k) stand for the set of clubs in k.

Signature. Let M be a set. Let lambda /in /Ord. A sequence of length lambda in M is a zffunction.
Axiom sequence. Let M be a set. Let lambda /in /Ord. Let C be a zffunction. C is a sequence of length lambda in M iff Dom(C) = lambda /\ forall i /in lambda C[i] /in M.
Axiom. Let M be a set. Let lambda /in /Ord. Let C be a sequence of length lambda in M. Then (C is a zffunction) /\ Dom(C) = lambda /\ forall i /in lambda C[i] /in M.

Axiom clubintersection. Let kappa /in /BigCard. Let lambda /in cof(kappa). Let lambda /neq /emptyset. Let C be a sequence of length lambda in Cl(kappa).
Then (C is a zffunction) /\ /bigcap C^[lambda] /subset kappa /\ /bigcap C^[lambda] /club kappa.

Axiom. Let kappa /in /BigCard. Let C,D /subset kappa. Let C,D /club kappa. Then C /cap D /club kappa.

Definition. Let kappa /in /BigCard. The closed unbounded filter on kappa is
{X /subset kappa | exists C /subset X (C /club kappa)}.
Let Club(k) stand for the closed unbounded filter on k.

Axiom. Let kappa /in /BigCard. Let C /subset kappa. Let C /club kappa. Then C /in Club(kappa).
Axiom. Let kappa /in /BigCard. Then kappa /club kappa.
Axiom. Let kappa /in /BigCard. Then Club(kappa) /in /VV.
Axiom. Let kappa /in /BigCard. Then Club(kappa) /neq /emptyset /\ Club(kappa) /subset /PP kappa.
Axiom. Let kappa /in /BigCard. Then /emptyset /notin Club(kappa).

Axiom clubsubset. Let kappa /in /BigCard. Let X /in Club(kappa). Let Y /subset kappa. Let X /subset Y. Then Y /in Club(kappa).
Axiom. Let kappa /in /BigCard. Let X,Y /in Club(kappa). Then X /cap Y /in Club(kappa).
Axiom. Let kappa /in /BigCard. Let lambda /in cof(kappa). Let lambda /neq /emptyset. Let X be a sequence of length lambda in Club(kappa). Then /bigcap X^[lambda] /in Club(kappa). 






# Stationary Sets

Definition. Let kappa /in /BigCard. Let X /subset kappa. X is nonstationary in kappa iff kappa /setminus X /in Club(kappa).

Definition. Let kappa /in /BigCard. The nonstationary ideal of kappa is {X /subset kappa | X is nonstationary in kappa}.
Let NS(k) stand for the nonstationary ideal of k.

Definition. Let kappa /in /BigCard. Let X /subset kappa. X is stationary in kappa iff X /notin NS(kappa).

Axiom stationary. Let kappa /in /BigCard. Let X /subset kappa. X is stationary in kappa iff (forall C /subset kappa (C /club kappa => X /cap C /neq /emptyset)).
Lemma stationary2. Let kappa /in /BigCard. Let X /subset kappa. Let forall C /subset kappa (C /club kappa => X /cap C /neq /emptyset). Then X is stationary in kappa (by stationary).
Axiom. Let kappa /in /BigCard. Let X /in Club(kappa). Then X is stationary in kappa.
Axiom. Let kappa /in /BigCard. /emptyset /neq NS(kappa) /\ NS(kappa) /subset /PP kappa.
Axiom. Let kappa /in /BigCard. kappa /notin NS(kappa).
Axiom. Let kappa /in /BigCard. Let X /in NS(kappa). Let Y /subset X. Then Y /in NS(kappa).
Axiom. Let kappa /in /BigCard. Let X,Y /in NS(kappa). Then X /cup Y /in NS(kappa).

Axiom. Let kappa /in /BigCard. Let lambda /in cof(kappa). Let lambda /neq /emptyset. Let X be a sequence of length lambda in NS(kappa). Then /bigcup X^[lambda] /in NS(kappa).

Axiom. Let kappa /in /BigCard. Let cof(kappa) = kappa. Let X be a sequence of length kappa in /PP kappa. Then forall i /in kappa X[i] /in /VV.

Definition. Let kappa /in /BigCard. Let cof(kappa) = kappa. Let X be a sequence of length kappa in /PP kappa.
The diagonal intersection of X of length kappa is {beta /in kappa | forall i /in beta (X[i] /subset kappa /\ beta /in X[i])}.
Let /triangle(X,k) stand for the diagonal intersection of X of length k.

Definition. Let kappa /in /BigCard. Let cof(kappa) = kappa. Let X be a sequence of length kappa in /PP kappa.
The diagonal union of X of length kappa is {beta /in kappa | exists i /in beta (X[i] /subset kappa /\ beta /in X[i])}.
Let /vartriangle(X,k) stand for the diagonal union of X of length k.

Axiom. Let kappa /in /BigCard. Let X be a sequence of length kappa in Club(kappa). Then X is a sequence of length kappa in /PP kappa.
Axiom. Let kappa /in /BigCard. Let X be a sequence of length kappa in Cl(kappa). Then X is a sequence of length kappa in /PP kappa.
Axiom. Let kappa /in /BigCard. Let X be a sequence of length kappa in NS(kappa). Then X is a sequence of length kappa in /PP kappa.
Axiom. Let kappa /in /BigCard. Let kappa be regular. Let X be a sequence of length kappa in Club(kappa). Then /triangle(X,kappa) /in Club(kappa).
Axiom. Let kappa /in /BigCard. Let kappa be regular. Let X be a sequence of length kappa in NS(kappa). Then /vartriangle(X,kappa) /in NS(kappa).





# Fodors Lemma


Definition. Let kappa /in /BigCard. The set of stationary subsets of kappa is
{C /subset kappa | C is stationary in kappa}.
Let stat(k) stand for the set of stationary subsets of k.

Definition. The set of regular uncountable cardinals is {kappa /in /BigCard | kappa is regular}.
Let /BigRegCard stand for the set of regular uncountable cardinals.

Definition. Let f be a zffunction. f is constant iff exists c /in /VV forall x /in Dom(f) f[x] = c.

Definition. Let f be a zffunction. Let x /in /VV. The preimage of x under f is
{y /in Dom(f) | f[y] = x}.
Let f^{-1}[[x]] denote the preimage of x under f.

Definition. Let f be a zffunction. Let Dom(f) /subset /Ord. f is regressive iff forall alpha /in Dom(f) /setminus <0> f[alpha] /in alpha.


Theorem Fodor. Let kappa /in /BigRegCard. Let f be a zffunction. Let Dom(f) /in stat(kappa). Let f be regressive.
Then exists i /in /Ord f^{-1}[[i]] /in stat(kappa).
Proof by contradiction. Assume the contrary.
Then forall i /in /Ord f^{-1}[[i]] /in NS(kappa).
Proof.
  Let i /in /Ord.
  Then f^{-1}[[i]] is not stationary in kappa.
  f^{-1}[[i]] /subset kappa.
  Then f^{-1}[[i]] /in NS(kappa).
end.
Forall i /in /Ord kappa /setminus f^{-1}[[i]] /in Club(kappa).
Define X[i] = kappa /setminus f^{-1}[[i]] for i in kappa.
X is a zffunction.
Proof.
  Let i /in kappa.
  Then X[i] /subset kappa.
  Then X[i] /in /VV.
end.
kappa /in /Ord.
Forall i /in kappa (X[i] /subset kappa /\ X[i] /in Club(kappa)).
Then X is a sequence of length kappa in Club(kappa) (by sequence).
kappa /in /BigCard.
kappa is regular.
Then /triangle(X,kappa) /in Club(kappa).
Take a zfset C such that C /subset /triangle(X,kappa) /\ C /club kappa.
Let CC = C /setminus <0>.
Then CC /club kappa.
Proof.
  CC /subset kappa.
  CC /cof kappa.
  Proof.
    Let alpha /in kappa.
    Take an zfset beta such that beta /in C /\ alpha /in beta.
    Then beta /in CC.
  end.
  CC /closed kappa.
  Proof.
    Let lambda /in kappa /cap /Lim.
    Let CC /cap lambda /cof lambda.
    Then C /cap lambda /cof lambda.
    Then lambda /in C.
    Then lambda /in CC.
  end.
end.
Then CC /cap Dom(f) /neq /emptyset.
Proof.
  kappa /in /BigCard.
  Dom(f) /subset kappa.
  Dom(f) is stationary in kappa.
  CC /subset kappa.
  CC /club kappa.
  Then CC /cap Dom(f) /neq /emptyset (by stationary).
end.
Take a zfset alpha such that alpha /in CC /cap Dom(f).
Then alpha /in /triangle(X,kappa) /\ alpha /neq 0.
Then forall i /in alpha alpha /in X[i].
Then forall i /in alpha alpha /notin f^{-1}[[i]].
Then forall i /in alpha f[alpha] /neq i.
Then f[alpha] /notin alpha.
f is regressive.
alpha /in Dom(f) /setminus <0>.
Dom(f) /subset /Ord.
Then f[alpha] /in alpha.
Contradiction.
qed.

Corollary Fodor2. Let kappa /in /BigRegCard. Let f be a zffunction. Let Dom(f) /in stat(kappa). Let f be regressive. Then exists T /subset Dom(f) (T /in stat(kappa) /\ (f /upharpoonright T is constant)).
Proof.
Take an ordinal i such that f^{-1}[[i]] /in stat(kappa).
Let T = f^{-1}[[i]].
T /subset Dom(f).
T /in stat(kappa).
f /upharpoonright T is constant.
qed.





Definition. Let kappa /in /BigCard. Let C /in Cl(kappa). The derivation of C in kappa is
{alpha /in kappa /cap /Lim | C /cap alpha /cof alpha}.
Let der(C,k) stand for the derivation of C in k.

Lemma. Let kappa /in /BigCard. Let C /in Cl(kappa). Then der(C,kappa) /subset C.
Proof.
Let alpha /in der(C,kappa).
Then C /cap alpha /cof alpha.
C /subset kappa.
C /closed kappa.
Then alpha /in C.
qed.


Lemma. Let kappa /in /BigCard. Let C /in Cl(kappa). Then der(C,kappa) /in Cl(kappa).
Proof.
der(C,kappa) /subset kappa.
der(C,kappa) /closed kappa.
Proof.
  Let lambda /in kappa /cap /Lim.
  Let der(C,kappa) /cap lambda /cof lambda.
  der(C,kappa) /subset C.
  Then C /cap lambda /cof lambda.
end.
der(C,kappa) /cof kappa.
Proof.
  Let alpha /in kappa.
  C /club kappa.
  Forall a /in kappa exists b /in C a /in b.
  Define sup[a] = (Choose a zfset b such that b /in C /\ a /in b in b) for a in kappa.
  sup : kappa /rightarrow kappa.
  Proof.
    Let i /in kappa.
    Then sup[i] /in C.
    C /subset kappa.
    Then sup[i] /in kappa.
  end.
  Forall beta /in kappa beta /in sup[beta].
  Proof.
    Let beta /in kappa.
    Take ordinals a,b such that a = beta /\ b = sup[beta].
    Then a,b /in /Ord.
    Then a /in b \/ b /in a \/ a = b (by TotalOrder).
    sup[beta] /notin beta + 1.
    Then b /notin a+1.
    Then b /notin a /\ b /neq a.
    Then a /in b.
  end.
  ran(sup) /subset Dom(sup).
  Proof.
    Let a /in ran(sup).
    Take a zfset b such that b /in kappa /\ a = sup[b].
    Then a /in kappa.
    Then a /in Dom(sup).
  end.    

  Define f[n] = (sup ^ (n+1)) [alpha] for n in /NN.

  Forall n /in /NN f[n] /in kappa.
  Proof.
    Let n /in /NN.
    f[n] = (sup ^ (n+1)) [alpha].
    Then f[n] /in ran(sup ^ (n+1)).
    ran(sup ^ (n+1)) /subset Dom(sup).
  end.
  f is a zffunction.
  Proof.
    Let n /in /NN.
    Then f[n] /in kappa.
    Then f[n] /in /VV.
  end.
  f[0] = sup[alpha].
  Forall n /in /NN (n /neq 0 => (n-1 /in /NN /\ f[n] = sup[f[n-1]])).
  Proof by induction.
    Let n /in /NN.
    Case n = 0. end.
    Case n /neq 0.
      Let m = n-1.
      Then m -<- n.
      Then m /neq 0 => (m-1 /in /NN /\ f[m] = sup[f[m-1]]).
      Then m = 0 \/ f[m] = sup[f[m-1]].
    end.
  end.
  Forall a,b /in /NN (a /in b => f[a] /in f[b]).
  Proof.
    Let a /in /NN.
    Forall b /in /NN (a /in b => f[a] /in f[b]).
    Proof by induction.
      Let b /in /NN.
      Case b = 0. end.
      Case b /neq 0.
        Let c = b-1.
        Then c -<- b.
        Then a /notin c \/ f[a] /in f[c].
        Case f[a] /in f[c].
          f[b] = sup[f[c]].
          Then f[c] /in f[b].
          Trans(f[b]).
          Then f[a] /in f[b].
        end.
        Case a /notin c.
          Then a /notin b \/ a = c.
        end.
      end.
    end.
  end.
  Forall a,b /in /NN (a /subset b => f[a] /subset f[b]).
  Proof.
    Let a,b /in /NN. Let a /subset b.
    a,b /in /Ord.
    Then a /in b \/ b /in a \/ a = b (by TotalOrder).
    Then a /in b \/ a = b.
  end.
      
  Let x = /bigcup f^[/NN].
  x /in /Ord.
  Proof.
    f^[/NN] /subset /Ord.
    Then Trans(/bigcup f^[/NN]).
    Then /bigcup f^[/NN] /in /Ord.
  end.
  x /subset kappa.
  Proof.
    Let a /in x.
    Take a zfset b such that b /in f^[/NN] /\ a /in b.
    Take a zfset n such that n /in /NN /\ b = f[n].
    Then b /in kappa.
    Then a /in kappa.
  end.
  Then x /in kappa \/ x = kappa.
  Proof.
    x, kappa /in /Ord.
    x /in kappa \/ kappa /in x \/ x = kappa (by TotalOrder).
    kappa /notin x.
  end.
  x /in kappa.
  Proof by contradiction. Assume the contrary.
    Then x = kappa.
    f^[/NN] /cof kappa.
    Proof.
      Let a /in kappa.
      Then a /in /bigcup f^[/NN].
    end.
    Card(f^[/NN]) /subset /NN.
    Card(f^[/NN]) /in cofset2(kappa).
    Then /bigcap cofset2(kappa) /subset Card(f^[/NN]).
    Then cof(kappa) /subset /NN.
    Contradiction.
  end.
    
  alpha /in x.
  Proof.
    f[0] = sup[alpha].
    Then alpha /in f[0].
    Then alpha /in /bigcup f^[/NN].
  end.
    
  x /in /Lim.
  Proof by contradiction. Assume the contrary.
    alpha /in x.
    Then x /neq 0.
    Then x /in /Succ.
    Take an ordinal a such that x = a+1.
    Then a /in x.
    Take a zfset b such that b /in f^[/NN] /\ a /in b.
    f^[/NN] /subset kappa.
    Then b /in /Ord.
    Then a+1 /subset b.
    Then a+1 = b \/ a+1 /in b.
    Proof.
      a+1,b /in /Ord.
      a+1 /in b \/ b /in a+1 \/ a+1 = b (by TotalOrder).
      b /notin a+1.
    end.
    Take a zfset n such that n /in /NN /\ b = f[n].
    Then b /in f[n+1].
    Then b /in /bigcup f^[/NN].
    Then b /in x.
    Then a+1 /in x.
    Contradiction.
  end.

  x /in der(C,kappa).
  Proof.
    C /cap x /cof x.
    Proof.
      Let j /in x.
      Take a zfset n such that n /in /NN /\ j /in f[n].
      f[n] /in C.
      f[n] /in x.
      Proof.
        f[n] /in f[n+1].
        f[n+1] /in f^[/NN].
        Then f[n] /in /bigcup f^[/NN].
      end.
      f[n] /in C /cap x.
      j /in f[n].
    end.
    x /in kappa /cap /Lim.
  end.
  alpha /in x.
end.
qed.


Definition. Let lambda, kappa /in /BigRegCard. Let lambda /in kappa. The subset of cofinality lambda in kappa is
{alpha /in kappa /cap /Lim | cof(alpha) = lambda}.
Let Estat(k,l) stand for the subset of cofinality l in k.


Lemma. Let lambda, kappa /in /BigRegCard. Let lambda /in kappa. Then Estat(kappa,lambda) is stationary in kappa.
Proof.
Let X = Estat(kappa,lambda).
kappa /in /BigCard.
X /subset kappa.
Forall C /subset kappa (C /club kappa => X /cap C /neq /emptyset).
Proof.
  Let C /subset kappa.
  Let C /club kappa.
  Then C /cof kappa.
  Then kappa /subset otp(C).
  Proof.
    otp(C) /in cofset(kappa).
    cof(kappa) = kappa.
    Then /bigcap cofset(kappa) = kappa.
    /bigcap cofset(kappa) /subset otp(kappa).
  end.
  Then lambda /subset cof(kappa).
  C /subset /Ord.
  C /in /VV.
  Take a zffunction f such that (f is an epshomo) /\ f : otp(C) /leftrightarrow C.
  /bigcup f^[lambda] /in /Lim /\ cof(/bigcup f^[lambda]) = cof(lambda).
  Let alpha = /bigcup f^[lambda].
  Then alpha /in /Lim /\ cof(alpha) = lambda.
  alpha /in kappa.
  Proof.
    lambda /in otp(C).
    alpha /subset f[lambda].
    Proof.
      Let a /in alpha.
      Take a zfset b such that b /in f^[lambda] /\ a /in b.
      Take a zfset c such that c /in lambda /\ b = f[c].
      c,lambda /in Dom(f).
      Then f[c] /in f[lambda] (by eps).
      f[lambda] /in /Ord.
      Then a /in f[lambda].
    end.
    f[lambda] /in kappa.
    alpha, kappa /in /Ord.
    Then alpha /in kappa \/ kappa /in alpha \/ alpha = kappa (by TotalOrder).
    alpha /neq kappa.
    kappa /notin alpha.
    Then alpha /in kappa.
  end.
  Then alpha /in /Lim /cap kappa.
  C /cap alpha /cof alpha.
  Proof.
    Let a /in alpha.
    Take a zfset b such that b /in f^[lambda] /\ a /in b.
    Take a zfset c such that c /in lambda /\ b = f[c].
    c, c+1 /in Dom(f).
    c /in c+1.
    Then f[c] /in f[c+1] (by eps).
    c+1 /in lambda.
    Then f[c+1] /in f^[lambda].
    Then f[c] /in /bigcup f^[lambda].
    Then f[c] /in C /cap alpha.
    a /in f[c].
  end.
  Then alpha /in C.
end.
Then X is stationary in kappa (by stationary2).
qed.

Lemma. Let kappa be a successor cardinal. Then kappa /in /BigCard.
Proof.
cof(kappa) = kappa.
Take an ordinal alpha such that kappa = Alef[alpha + 1].
1 /subset alpha + 1.
Then Alef[1] /subset Alef[alpha + 1].
Then Alef[1] /subset kappa.
qed.

Definition. Let kappa /in /BigCard. Let S be a set. The set of stationary subsets of kappa in S is
{x /in stat(kappa) | x /subset S}.
Let stat(k,S) stand for the set of stationary subsets of k in S.

Definition. Let M be a set. Let lambda /in /Ord. Let f be a sequence of length lambda in M. f is pairwise disjoint on lambda in M iff
forall a,b /in lambda (a /neq b => f[a] /cap f[b] = /emptyset).



Axiom. Let a,b be objects. Let A,B be sets. Let (a,b) /in A /times B. Then a /in A /\ b /in B.
Let obj1,obj2,obj stand for objects.






Lemma. Contradiction.
