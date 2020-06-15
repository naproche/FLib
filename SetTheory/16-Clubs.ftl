# 16-Clubs

# Now we define closed unbounded sets and show that the closed unbounded filter on kappa is cof(kappa)-closed.
# For this we reintroduce the inductive composition of a function.

# Main results:

# - the intersection of less then cof(kappa) many clubs is a club
# - Club(kappa) is cof(kappa)-closed






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
Axiom TotalOrder. Forall alpha, beta (alpha /in beta \/ beta /in alpha \/ alpha = beta).
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

Signature. Alef is a zffunction.
Axiom. Alef : /Ord /rightarrow /Cd.
Axiom. Alef[/emptyset] = /NN.
Axiom. Let alpha /in /Succ. Let beta /in /Ord. Let alpha = beta + 1. Then Alef[beta] /in /Ord /\ Alef[alpha] = Plus[Alef[beta]].
Axiom. Let alpha /in /Lim. Then Alef[alpha] = {zfset x | exists beta /in alpha x /in Alef[beta]}.

Axiom. Let x /in /VV. Let x /subset /Cd. Then Card(/bigcup x) = /bigcup x.
Axiom. Forall alpha, beta (alpha /in beta => Alef[alpha] /in Alef[beta]).
Axiom. Alef is injective.
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
Axiom. Let f be a zffunction. Let forall x,y /in Dom(f) (x /in y => f[x] /in f[y]). Then f is an epshomo.
Axiom. Let x, y be sets. Let x /subset /Ord /\ y /subset /Ord. Let f be a zffunction. 
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

Axiom. Let x /subset /Ord. Let y be a set. Then otp(x) = y iff exists f ((f is an epshomo) /\ f : x /leftrightarrow y).
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
Axiom. Let alpha /in /Lim. Then cof(Alef[alpha]) = cof(alpha).
Axiom. Forall alpha /in /Ord cof(Alef[alpha + 1]) = Alef[alpha + 1].




# Closed unbounded sets


Definition. Let kappa /in /Lim. Let C /subset kappa. C is closed in kappa iff
(forall lambda /in /Lim /cap kappa (C /cap lambda /cof lambda => lambda /in C)).
Let C /closed k stand for C is closed in k.

Definition. Let kappa /in /Lim. Let C /subset kappa. C is closed unbounded in kappa iff
(C /cof kappa /\ (C is closed in kappa)).
Let C /club k stand for C is closed unbounded in k.


Signature. Let kappa /in /Card. Let lambda /in /Ord. A sequence of lambda clubs of kappa is a zffunction.
Axiom clubseq. Let kappa /in /Card. Let lambda /in /Ord. Let C be a zffunction. C is a sequence of lambda clubs of kappa iff Dom(C) = lambda /\ forall i /in lambda (C[i] /subset kappa /\ C[i] /club kappa).
Axiom. Let kappa /in /Card. Let lambda /in cof(kappa). Let C be a sequence of lambda clubs of kappa. Then (C is a zffunction) /\ Dom(C) = lambda /\ forall i /in lambda (C[i] /subset kappa /\ C[i] /club kappa).



# Inductive function composition

Signature. f ^ n is an object.
Axiom. Let f be a zffunction. Let ran(f) /subset Dom(f). Let n /in /NN. Then f ^ n is a function.
Axiom. Let f be a zffunction. Let ran(f) /subset Dom(f). Let n /in /NN. Then Dom(f^n) = Dom(f).
Axiom. Let f be a zffunction. Let ran(f) /subset Dom(f). Let x /in Dom(f). Then (f^0)[x] = x.
Axiom. Let f be a zffunction. Let ran(f) /subset Dom(f). Let x /in Dom(f). Forall n /in /NN ((f^n)[x] /in Dom(f) /\ (f^(n+1))[x] = f[((f^n)[x])]).

Lemma. Let f be a zffunction. Let ran(f) /subset Dom(f). Let n /in /NN. Let n /neq 0. Let x /in Dom(f). Then (f^(n-1))[x] /in Dom(f) /\ (f^(n))[x] = f[((f^(n-1))[x])].
Proof.
Forall m /in /NN ((f^m)[x] /in Dom(f) /\ (f^(m+1))[x] = f[((f^m)[x])]).
Take a natural number m such that m = n-1.
Then (f^(m+1))[x] = f[((f^m)[x])].
qed.

Lemma. Let f be a zffunction. Let ran(f) /subset Dom(f). Then forall n /in /NN (f^n is a zffunction).
Proof by induction.
  Let n /in /NN.
  Case n = 0.
    f ^ 0 is a zffunction.
    Proof.
      Dom(f ^ 0) = Dom(f).
      Let x /in Dom(f).
      Then (f ^ 0)[x] = x.
      Then (f ^ 0)[x] /in /VV.
    end.
  end.
  Case n /neq 0.
    Then n-1 /in n.
    n-1 -<- n.
    Then (f ^ (n-1)) is a zffunction.
    Dom(f ^ n) = Dom(f).
    Let x /in Dom(f).
    Then (f^(n))[x] = f[((f^(n-1))[x])].
    Then (f^(n))[x] /in /VV.
  end.
qed.

Lemma. Let f be a zffunction. Let ran(f) /subset Dom(f). Then forall n /in /NN ((f^n is a zffunction) /\ (ran(f^n) /subset Dom(f))).

Lemma. Let f be a zffunction. Let ran(f) /subset Dom(f). Then forall n /in /NN (f ^ (n+1) = f /circ (f ^ n)).

Lemma. Let f be a zffunction. Let ran(f) /subset Dom(f). Let n /in /NN. Let n /neq 0. Then ran(f^(n-1)) /subset Dom(f) /\ (f ^ (n) = f /circ (f ^ (n-1))).

# end



Lemma clubintersection. Let kappa /in /Card. Let Alef[1] /subset cof(kappa). Let lambda /in cof(kappa). Let lambda /neq /emptyset. Let C be a sequence of lambda clubs of kappa.
Then (C is a zffunction) /\ /bigcap C^[lambda] /subset kappa /\ /bigcap C^[lambda] /club kappa.
Proof.
C is a sequence of lambda clubs of kappa.

Let M = /bigcap C^[lambda].

Then (C is a zffunction) /\ Dom(C) = lambda /\ forall i /in lambda (C[i] /subset kappa /\ C[i] /club kappa).
M /subset kappa.
Proof.
  Let x /in M.
  Take a zfset i such that i /in lambda.
  C[i] /in C^[lambda].
  Then x /in C[i].
  C[i] /subset kappa.
  Then x /in kappa.
end.

M /closed kappa.
Proof.
  Let gamma /in /Lim /cap kappa.
  Let M /cap gamma /cof gamma.
  Then gamma /in M.
  Proof.
    Let y /in C^[lambda].
    Then gamma /in y.
    Proof.
      Take a zfset i such that i /in lambda /\ y = C[i].
      M /subset C[i].
      Then C[i] /cap gamma /cof gamma.
      Then C[i] /club kappa.
      Then gamma /in C[i].
    end.
  end.
end.

M /cof kappa.
Proof.
  Let alpha /in kappa.
  Then exists x /in M (alpha /in x).
  Proof.
    Define supset[beta] = {gamma /in kappa | (forall i /in lambda exists j /in C[i] /cap gamma (beta /in j))} for beta in kappa.
    Forall beta /in kappa forall gamma /in supset[beta] beta /in gamma.
    Proof.
      Let beta /in kappa.
      Let gamma /in supset[beta].
      Take a zfset i such that i /in lambda.
      Forall ii /in lambda exists j /in C[ii] /cap gamma (beta /in j).
      Take a zfset j such that j /in C[i] /cap gamma /\ beta /in j.
      Then j /in gamma.
      Then beta /in gamma.
    end.
    Forall beta /in kappa supset[beta] /neq /emptyset.
    Proof.
      Let beta /in kappa.
      Forall i /in lambda exists j /in C[i] (beta /in j).
      Forall i /in lambda exists j /in /VV (j /in C[i] /setminus (beta + 1)).
      Define f[i] = (Choose a zfset j such that (j /in C[i] /setminus (beta + 1)) in j) for i in lambda.
      f : lambda /rightarrow kappa.
      Proof.
        Let i /in lambda.
        Then f[i] /in C[i].
        Then f[i] /in kappa.
      end.
      Forall i /in lambda beta /in f[i].
      Proof.
        Let i /in lambda.
        f[i] /in C[i] /setminus (beta + 1).
        f[i], beta /in /Ord.
        f[i] /in beta \/ beta /in f[i] \/ f[i] = beta (by TotalOrder).
        f[i] /notin beta /\ f[i] /neq beta.
        Then beta /in f[i].
      end.
      /bigcup f^[lambda] /in kappa.
      Proof by contradiction. Assume the contrary.
        f^[lambda] /subset kappa.
        /bigcup f^[lambda] /in /Ord.
        Proof.
          f^[lambda] /subset /Ord.
          Then Trans(/bigcup f^[lambda]).
        end.
        Then /bigcup f^[lambda] = kappa.
        Proof.
          Take an ordinal a such that a = /bigcup f^[lambda].
          Then a /in kappa \/ kappa /in a \/ a = kappa.
          a /notin kappa.
          kappa /notin a.
        end.
        Then f^[lambda] /cof kappa.
        Proof.
          Let a /in kappa.
          Then a /in /bigcup f^[lambda].
        end.
        Card(f^[lambda]) /subset lambda.
        Card(f^[lambda]) /in cofset2(kappa).
        Then /bigcap cofset2(kappa) /subset Card(f^[lambda]).
        Then cof(kappa) /subset lambda.
        Contradiction.
      end.
      Let gamma = /bigcup f^[lambda] + 1.
      Then gamma /in kappa.
      Forall i /in lambda exists j /in C[i] /cap gamma (beta /in j).
      Proof.
        Let i /in lambda.
        Then f[i] /in C[i].
        f[i] /in gamma.
        Proof.
          f[i] /in f^[lambda].
          Then f[i] /subset /bigcup f^[lambda].
          Then f[i] /in /bigcup f^[lambda] \/ f[i] = /bigcup f^[lambda].
          Proof.
            Take ordinals a,b such that a = f[i] /\ b = /bigcup f^[lambda].
            Then a /in b \/ b /in a \/ a = b.
            a /subset b.
            Then a /in b \/ a = b.
          end.
        end.
        beta /in f[i].
      end.
      Then gamma /in supset[beta].
    end.
    Define sup[beta] = (Choose a zfset gamma such that gamma /in supset[beta] in gamma) for beta in kappa.
    Forall beta /in kappa beta /in sup[beta].
    Forall beta /in kappa sup[beta] /in kappa.
    Forall beta /in kappa forall i /in lambda exists j /in C[i] /cap sup[beta] (beta /in j).
    sup is a zffunction.
    Proof.
      Let a /in kappa.
      Then sup[a] /in kappa.
      Then sup[a] /in /VV.
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
      Then b /in /Ord.
      Then a+1 /subset b.
      Then a+1 = b \/ a+1 /in b.
      Proof.
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
    
    Forall i /in lambda x /in C[i].
    Proof.
      Let i /in lambda.
      Forall n /in /NN exists j /in C[i] (f[n] /in j /\ j /in f[n+1]).
      Proof.
        Let n /in /NN.
        f[n+1] = sup[f[n]].
        Then exists j /in C[i] /cap f[n+1] (f[n] /in j).
      end.
      Define val[n] = (Choose a zfset j such that j /in C[i] /\ (f[n] /in j /\ j /in f[n+1]) in j) for n in /NN.
      val is a zffunction.
      Proof.
        Let n /in /NN.
        Then val[n] /in /VV.
      end.
      /bigcup val^[/NN] /in /Ord.
      Proof.
        val^[/NN] /subset /Ord.
        Then Trans(/bigcup val^[/NN]).
      end.
      /bigcup val^[/NN] /subset x.
      Proof.
        Let a /in /bigcup val^[/NN].
        Take a zfset b such that b /in val^[/NN] /\ a /in b.
        Take a zfset c such that c /in /NN /\ b = val[c].
        val[c] /in f[c+1].
        Then val[c] /in /bigcup f^[/NN].
        Then val[c] /in x.
        Trans(x).
        Then a /in x.
      end.
      x /subset /bigcup val^[/NN].
      Proof.
        Let a /in x.
        Take a zfset b such that b /in f^[/NN] /\ a /in b.
        Take a zfset c such that c /in /NN /\ b = f[c].
        Then b /in val[c].
        val[c] /in val^[/NN].
        Then b /in /bigcup val^[/NN].
        Trans(/bigcup val^[/NN]).
        Then a /in /bigcup val^[/NN].
      end.
      Then x = /bigcup val^[/NN].
      
      x /in /Lim /cap kappa.
      C[i] /cap x /cof x.
      Proof.
        Let a /in x.
        Take a zfset b such that b /in val^[/NN] /\ a /in b.
        Take a zfset c such that c /in /NN /\ b = val[c].
        Then b /in f[c+1].
        Then b /in /bigcup f^[/NN].
        Then b /in x.
        b /in C[i].
        Then b /in C[i] /cap x.
      end.
      Then x /in C[i].
    end.
    Then x /in M.
    Proof.
      Forall a /in C^[lambda] x /in a.
      Then x /in /bigcap C^[lambda].
    end.

  end.

end.
qed.



Lemma. Let kappa /in /Card. Let Alef[1] /subset cof(kappa). Let C,D /subset kappa. Let C,D /club kappa. Then C /cap D /club kappa.
Proof.
Define f[i] =
  Case i = 0 -> C,
  Case i = 1 -> D
for i in 2.
Then f is a zffunction.
Proof.
  Let i /in 2.
  Then f[i] /subset kappa.
  Then f[i] /in /VV.
end.
f is a sequence of 2 clubs of kappa.
Proof.
  kappa /in /Card.
  2 /in /Ord.
  f is a zffunction.
  (f is a sequence of 2 clubs of kappa) iff Dom(f) = 2 /\ forall i /in 2 (f[i] /subset kappa /\ f[i] /club kappa) (by clubseq).
  Dom(f) = 2.
  Forall i /in 2 (f[i] /subset kappa /\ f[i] /club kappa).
end.
Then /bigcap f^[2] /club kappa.
f^[2] = <C,D>.
Then /bigcap f^[2] = C /cap D.
qed.



Definition. Let kappa /in /Card. Let Alef[1] /subset cof(kappa). The closed unbounded filter on kappa is
{X /subset kappa | exists C /subset X (C /club kappa)}.
Let Club(k) stand for the closed unbounded filter on k.

Lemma. Let kappa /in /Card. Let Alef[1] /subset cof(kappa). Then Club(kappa) /in /VV.
Proof.
Club(kappa) /subset /PP kappa.
qed.


Lemma. Let kappa /in /Card. Let Alef[1] /subset cof(kappa). Then Club(kappa) /neq /emptyset /\ Club(kappa) /subset /PP kappa.
Proof.
kappa /club kappa.
qed.

Lemma. Let kappa /in /Card. Let Alef[1] /subset cof(kappa). Then /emptyset /notin Club(kappa).

Lemma. Let kappa /in /Card. Let Alef[1] /subset cof(kappa). Let X /in Club(kappa). Let Y /subset kappa. Let X /subset Y. Then Y /in Club(kappa).
Proof.
Take a zfset C such that C /subset X /\ C /club kappa.
Then C /subset Y /\ C /club kappa.
Then Y /in Club(kappa).
qed.


Lemma. Let kappa /in /Card. Let Alef[1] /subset cof(kappa). Let X,Y /in Club(kappa). Then X /cap Y /in Club(kappa).
Proof.
Take a zfset C such that C /subset X /\ C /club kappa.
Take a zfset D such that D /subset Y /\ D /club kappa.
C,D /subset kappa.
Then C /cap D /club kappa.
C /cap D /subset X /cap Y.
qed.


Signature. Let kappa /in /Card. Let lambda /in /Ord. A sequence of lambda clubfiltersets of kappa is a zffunction.
Axiom clubfilterseq. Let kappa /in /Card. Let Alef[1] /subset cof(kappa). Let lambda /in /Ord. Let C be a zffunction. C is a sequence of lambda clubfiltersets of kappa iff Dom(C) = lambda /\ forall i /in lambda (C[i] /in Club(kappa)).
Axiom. Let kappa /in /Card. Let Alef[1] /subset cof(kappa). Let lambda /in cof(kappa). Let C be a sequence of lambda clubs of kappa. Then (C is a zffunction) /\ Dom(C) = lambda /\ forall i /in lambda (C[i] /in Club(kappa)).

Lemma. Let kappa /in /Card. Let Alef[1] /subset cof(kappa). Let lambda /in cof(kappa). Let lambda /neq /emptyset. Let X be a sequence of lambda clubfiltersets of kappa. Then /bigcap X^[lambda] /in Club(kappa). 
Proof.
Forall i /in lambda exists Ci /subset X[i] (Ci /subset kappa /\ Ci /club kappa).
Proof.
  Let i /in lambda.
  Then X[i] /in Club(kappa).
  Take a zfset Ci such that Ci /subset X[i] /\ Ci /club kappa.
  Then Ci /subset kappa /\ Ci /club kappa.
end.
Define C[i] = (Choose a zfset Ci such that Ci /subset X[i] /\ Ci /subset kappa /\ Ci /club kappa in Ci) for i in lambda.
C is a zffunction.
Proof.
  Let i /in lambda.
  Then C[i] /subset X[i].
  Then C[i] /in /VV.
end.
kappa /in /Card. lambda /in /Ord.
Then C is a sequence of lambda clubs of kappa iff Dom(C) = lambda /\ forall i /in lambda (C[i] /subset kappa /\ C[i] /club kappa) (by clubseq).
Dom(C) = lambda.
Forall i /in lambda (C[i] /subset kappa /\ C[i] /club kappa).
Then C is a sequence of lambda clubs of kappa.
(C is a zffunction) /\ /bigcap C^[lambda] /subset kappa /\ /bigcap C^[lambda] /club kappa (by clubintersection).
/bigcap C^[lambda] /subset /bigcap X^[lambda].
/bigcap X^[lambda] /subset kappa.
Then /bigcap X^[lambda] /in Club(kappa). 
qed.







Lemma. Contradiction.
