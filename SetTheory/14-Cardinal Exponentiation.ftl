# 14-Cardinal Exponentiation

# In the last section we examined the value of the continuum function depending on the Gimel function.
# Now we examine arbitrary cardinal exponentiation and proof a calculation rule.

# Main results:

# - the value of kappa ^ lambda depending on the relation between kappa and lambda



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
Axiom. Let kappa, lambda /in /Cd. Let /NN /subset kappa. Let 2 /subset lambda. Let lambda /subset (2 ^3 kappa).
Then lambda ^3 kappa = 2 ^3 kappa.

Axiom. Let alpha /in /Cd. Let alpha /neq 0. Then 0 ^3 alpha = 0.
Axiom. Forall kappa /in /Cd (kappa ^3 1 = kappa).
Axiom. Let kappa /in /Cd. Then 2 ^3 kappa = Card(/PP kappa).
Axiom. Let x,y /in /VV. Let x /tilde y. Then /PP x /tilde /PP y.
Axiom. Let x /in /VV. Then Card(/PP x) = 2 ^3 Card(x).
Axiom. Let kappa /in /Cd. Then kappa /in 2 ^3 kappa.
Axiom. Let kappa /in /Cd. Then kappa *3 1 = kappa.
Axiom. Let alpha, beta, gamma /in /Cd. Let beta /subset gamma. Let 0 /in alpha \/ 0 /in beta. Then alpha ^3 beta /subset alpha ^3 gamma.
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

Axiom. Forall alpha /in /Ord /NN /subset Beth[alpha].
Axiom. Forall alpha, beta /in /Ord (beta /in alpha => Beth[beta] /in Beth[alpha]).




# Gimels

Signature. Gimel is a zffunction.
Axiom. Gimel : /Card /rightarrow /Card.
Axiom. Let kappa /in /Card. Then kappa ^3 cof(kappa) /in /Card.
Axiom. Forall kappa /in /Card Gimel[kappa] = kappa ^3 cof(kappa).

Signature. Let kappa /in /Cd. Let lambda /in /Card. kappa ^< lambda is a set.
Axiom exp. Let kappa /in /Cd. Let lambda /in /Card. kappa ^< lambda = {zfset x | exists v /in lambda x /in kappa ^3 Card(v)}.

Axiom. Let kappa /in /Cd. Let lambda /in /Card. Then kappa ^< lambda /in /Cd.
Axiom. Let kappa /in /Card. Then 2 ^< kappa /in /Card.
Axiom. Forall kappa /in /Card kappa /in Gimel[kappa].
Axiom. Let kappa /in /Card. Let cof(kappa) = kappa. Then Gimel[kappa] = 2 ^3 kappa.

Axiom. Let kappa /in /Card. Let cof(kappa) /in kappa. Then 2 ^3 kappa /subset (2 ^< kappa) ^3 cof(kappa).
Axiom. Let kappa /in /Card. Let cof(kappa) /in kappa. Let (exists kappap /in /Card /cap kappa forall lambda /in /Card
(kappap /subset lambda /\ lambda /in kappa => 2 ^3 kappap = 2 ^3 lambda)). Then 2 ^3 kappa = 2 ^< kappa.
Axiom. Let kappa /in /Card. Let cof(kappa) /in kappa. Let (forall kappap /in /Cd /cap kappa exists lambda /in /Cd /cap kappa
(kappap /in lambda /\ 2 ^3 kappap /in 2 ^3 lambda)). Then 2 ^3 kappa = Gimel[2 ^< kappa].




# Cardinal Exponentiation


Lemma. Let v /in /VV. Let b /in /Cd. Then Card(^{b}v) = Card(v) ^3 b.
Proof.
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
      Then f[x] /in Dom(bij^{-1}).
      g[x] = (bij^{-1})[f[x]].
      Take a zfset y such that y = (bij^{-1})[f[x]].
      Then bij[y] = f[x].
      Then (bij /circ g)[x] = f[x].
    end.
  end.
  Then phi[g] = f.
  Then f /in ran(phi).
end.
Then ran(phi) = ^{b}Card(v).
phi : ^{b}v /leftrightarrow ^{b}Card(v).
Then Card(^{b}v) = Card(^{b}Card(v)).
Then Card(^{b}v) = Card(v) ^3 b.
qed.




Lemma. Let lambda /in /Card. Then 0 ^3 lambda = 0.
Lemma. Let lambda /in /Card. Then 1 ^3 lambda = 1.
Proof.
^{lambda}1 /neq /emptyset.
Forall f1,f2 /in ^{lambda}1 f1 = f2.
Proof.
  Let f1,f2 /in ^{lambda}1.
  Then f1,f2 are functions.
  Dom(f1) = Dom(f2).
  Forall x /in Dom(f1) (f1[x] = f2[x]).
  Then f1 = f2.
end.
Take a zffunction f such that f /in ^{lambda}1.
Define g[n] = f for n in 1.
Then g : 1 /rightarrow ^{lambda}1.
Proof.
  Let n /in 1.
  Then g[n] /in ^{lambda}1.
end.
g is injective.
ran(g) = ^{lambda}1.
Then g : 1 /leftrightarrow ^{lambda}1.
Then Card(^{lambda}1) = 1.
qed.
Lemma. Let lambda /in /Card. Let kappa /in /Cd. Let 2 /subset kappa /\ kappa /subset lambda. Then kappa ^3 lambda = 2 ^3 lambda.
Proof.
lambda /subset 2 ^3 lambda.
Then kappa /subset 2 ^3 lambda.
qed.


Lemma. Let lambda, kappa /in /Card. Let xi /in /Cd. Let lambda /in kappa. Let xi /in kappa. Let kappa /subset xi ^3 lambda.
Then kappa ^3 lambda = xi ^3 lambda.
Proof.
xi /subset kappa.
Then xi ^3 lambda /subset kappa ^3 lambda.
kappa /subset xi ^3 lambda.
Then kappa ^3 lambda /subset (xi ^3 lambda) ^3 lambda.
(xi ^3 lambda) ^3 lambda = xi ^3 (lambda *3 lambda).
lambda *3 lambda = lambda.
Then (xi ^3 lambda) ^3 lambda = xi ^3 lambda.
Then kappa ^3 lambda /subset xi ^3 lambda.
qed.


Lemma. Let kappa, lambda /in /Card. Let lambda /in kappa. Let forall xi /in /Cd /cap kappa (xi ^3 lambda /in kappa). Let lambda /in cof(kappa).
Then kappa ^3 lambda = kappa.
Proof.
kappa = kappa ^3 1.
1 /subset lambda.
Then kappa ^3 1 /subset kappa ^3 lambda.
Then kappa /subset kappa ^3 lambda.

Forall f /in ^{lambda}kappa /bigcup ran(f) /in kappa.
Proof by contradiction. Assume the contrary.
  Take a zffunction f such that f /in ^{lambda}kappa /\ /bigcup ran(f) /notin kappa.
  Then f : lambda /rightarrow kappa.
  ran(f) /subset kappa.
  /bigcup ran(f) /subset kappa.
  /bigcup ran(f) /in /Ord.
  Proof.
    Trans(/bigcup ran(f)).
    ran(f) = f^[lambda].
    Then ran(f) /in /VV.
    Then /bigcup ran(f) /in /VV.
  end.
  Then /bigcup ran(f) = kappa.
  Proof.
    Take ordinals aa,bb such that aa = /bigcup ran(f) /\ bb = kappa.
    Then aa /in bb \/ bb /in aa \/ aa = bb.
    aa /notin bb.
    aa /subset bb.
    Then aa = bb.
  end.
  Then ran(f) /cof kappa.
    
  ran(f) = f^[lambda].
  Then Card(ran(f)) /subset Card(lambda).
  Card(ran(f)) /in cofset2(kappa).
  Then /bigcap cofset2(kappa) /subset lambda.
  Then cof(kappa) /subset lambda.
  Contradiction.
end.

Define M = {zffunction f | exists v /in kappa (f : lambda /rightarrow v)}.
Then M = ^{lambda}kappa.
Proof.
  M /subset ^{lambda}kappa.
  Proof.
    Let f /in M.
    Take a zfset v such that v /in kappa /\ f : lambda /rightarrow v.
    v /subset kappa.
    Then f : lambda /rightarrow kappa.
    Then f /in ^{lambda}kappa.
  end.
  ^{lambda}kappa /subset M.
  Proof.
    Let f /in ^{lambda}kappa.
    Then /bigcup ran(f) /in kappa.
    Take a zfset v such that v /in kappa /\ v = /bigcup ran(f).
    Then ran(f) /subset v+1.
    Proof.
      Let x /in ran(f).
      Then x /subset v.
      x /in /Ord.
      Then x /in v+1.
    end.
    Then f : lambda /rightarrow v+1.
    kappa /in /Lim.
    Then v+1 /in kappa.
    Then f /in M.      
  end.
end.
Then Card(M) = kappa ^3 lambda.

Define seq[v] = Card(^{lambda}v) for v in kappa.
Then seq is a sequence of cardinals.
Proof.
  Let v /in kappa. Then seq[v] /in /Cd.
end.

Card(M) /subset Card(/sumset seq).
Proof.
  Define bij[v] = (choose a zffunction psi such that psi : ^{lambda}v /leftrightarrow Card(^{lambda}v) in psi)
  for v in kappa.
  Forall v /in kappa forall f (f : lambda /rightarrow v => f /in Dom(bij[v])).
  Define phi[f] = (choose a zfset v such that v /in kappa /\ f : lambda /rightarrow v in ((bij[v])[f],v)) for f in M.
  Then phi : M /rightarrow /sumset seq.
  Proof.
    Let f /in M.
    Take a zfset v such that v /in kappa /\ f : lambda /rightarrow v /\ phi[f] = ((bij[v])[f],v).
    Then (bij[v])[f] /in seq[v].
    Then phi[f] /in /sumset seq.
  end.
  phi is injective.
  Proof.
    Let f1,f2 /in M. Let f1 /neq f2.
    Take a zfset v1 such that v1 /in kappa /\ f1 : lambda /rightarrow v1 /\ phi[f1] = ((bij[v1])[f1],v1).
    Take a zfset v2 such that v2 /in kappa /\ f2 : lambda /rightarrow v2 /\ phi[f2] = ((bij[v2])[f2],v2).
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

/sumset seq /subset kappa /times kappa.
Proof.
  Let pair /in /sumset seq.
  Take zfsets a,b such that b /in kappa /\ a /in seq[b] /\ pair = (a,b).
  seq[b] = Card(^{lambda}b).
  Card(^{lambda}b) = Card(b) ^3 lambda.
  Card(b) /in /Cd /cap kappa.
  Then Card(b) ^3 lambda /in kappa.
  Then seq[b] /in kappa.
  Then a /in kappa.
  Then (a,b) /in kappa /times kappa.
end.
Then Card(/sumset seq) /subset Card(kappa /times kappa).
Card(kappa /times kappa) = kappa *3 kappa.
kappa *3 kappa = kappa.
Then Card(/sumset seq) /subset kappa.

Then Card(M) /subset kappa.
Then kappa ^3 lambda /subset kappa.

qed.


Definition. Let f,g be zffunctions. f and g are diagcomposable iff Dom(f) = Dom(g) /\ forall i /in Dom(f) ((f[i] is a zffunction) /\ g[i] /in Dom(f[i])).

Lemma. Let f,g be zffunction. Let f and g be diagcomposable.
Then exists h (Dom(h) = Dom(f) /\ forall i /in Dom(f) h[i] = (f[i])[g[i]]).
Proof.
Define h[i] = (f[i])[g[i]] for i in Dom(f).
Then h is a zffunction.
Proof.
  Let i /in Dom(f).
  Then h[i] = (f[i])[g[i]].
  f[i] is a zffunction.
  Then (f[i])[g[i]] /in /VV.
end.
qed.

Definition. Let f,g be zffunction. Let f and g be diagcomposable.
The diagcomposition of f and g is a zffunction h such that (Dom(h) = Dom(f) /\ forall i /in Dom(f) h[i] = (f[i])[g[i]]).
Let g /comp f stand for the diagcomposition of f and g.

Lemma. Let kappa, lambda /in /Card. Let lambda /in kappa. Let forall xi /in /Cd /cap kappa (xi ^3 lambda /in kappa). Let cof(kappa) /subset lambda.
Then kappa ^3 lambda = Gimel[kappa].
Proof.
Gimel[kappa] /subset kappa ^3 lambda.
Proof.
  Gimel[kappa] = kappa ^3 cof(kappa).
  kappa ^3 cof(kappa) /subset kappa ^3 lambda.
  Proof.
    Take cardinals a,b,c such that a = kappa /\ b = cof(kappa) /\ c = lambda.
    Then b /subset c.
    0 /in a.
    Forall alpha, beta, gamma /in /Cd (beta /subset gamma /\ 0 /in alpha => alpha ^3 beta /subset alpha ^3 gamma).
    Then a ^3 b /subset a ^3 c.
  end.
end.

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
  Let lam /in kappa.
  alpha /in /Lim.
  Then Alef[alpha] = {zfset xx | exists beta /in alpha xx /in Alef[beta]}.
  Take a zfset beta such that beta /in alpha /\ lam /in Alef[beta].
  Take a zfset b such that b /in xa /\ beta /in b.
  Then Alef[beta] /subset Alef[b].
  Then lam /in Alef[b].
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
Take a zffunction xi such that xi : cof(kappa) /leftrightarrow x /\ (xi is an epshomo).
Forall i1,i2 /in cof(kappa) (i1 /in i2 => xi[i1] /in xi[i2]) (by eps).
Forall i /in cof(kappa) xi[i] /in /Card.
Proof.
  Let i /in cof(kappa).
  Then xi[i] /in x.
  Take a zfset j such that j /in xa /\ xi[i] = Alef[j].
  Alef[j] /in /Cd.
  /NN /subset Alef[j].
  Then Alef[j] /in /Card.
end.
Card(x) = cof(kappa).

Forall a /in /VV exists f (Dom(f) = /VV /\ forall b /in /VV ((b /in a => f[b] = b) /\ (b /notin a => f[b] = 0))).
Proof.
  Let a /in /VV.
  Define f[b] =
    Case b /in a -> b,
    Case b /notin a -> 0
  for b in /VV.
  Then Dom(f) = /VV.
  Forall b /in /VV ((b /in a => f[b] = b) /\ (b /notin a => f[b] = 0)).
end.
Define delta[a] = (Choose a zffunction f such that Dom(f) = /VV /\ forall b /in /VV ((b /in a => f[b] = b) /\ (b /notin a => f[b] = 0)) in f) for a in /VV.
Forall a,b /in /VV (b /in a => (delta[a])[b] = b).
Proof.
  Let a,b /in /VV.
  Let b /in a.
  Take a zffunction f such that Dom(f) = /VV /\ forall bb /in /VV (bb /in a => f[bb] = bb /\ bb /notin a => f[bb] = 0) /\ delta[a] = f.
end.
Forall a,b /in /VV (b /notin a => (delta[a])[b] = 0).
Proof.
  Let a,b /in /VV.
  Let b /notin a.
  Take a zffunction f such that Dom(f) = /VV /\ forall bb /in /VV (bb /in a => f[bb] = bb /\ bb /notin a => f[bb] = 0) /\ delta[a] = f.
end.

Forall pair /in cof(kappa) /times ^{lambda}kappa exists i,f /in /VV (i /in cof(kappa) /\ f /in ^{lambda}kappa /\ pair = (i,f)).
Define F[pair] = (choose zfsets i, f such that (i /in cof(kappa) /\ f /in ^{lambda}kappa /\ pair = (i,f)) in ((delta[xi[i]]) /circ f)) for pair in cof(kappa) /times ^{lambda}kappa.

Forall i /in cof(kappa) forall f /in ^{lambda}kappa (i,f) /in Dom(F).
Forall i /in cof(kappa) forall f /in ^{lambda}kappa F[(i,f)] = (delta[xi[i]]) /circ f.
Proof.
  Let i /in cof(kappa).
  Let f /in ^{lambda}kappa.
  Let pair = (i,f).
  Then F[pair] = F[(i,f)].
  Take zfsets i1,f1 such that i1 /in cof(kappa) /\ f1 /in ^{lambda}kappa /\ pair = (i1,f1).
  Then i = i1 /\ f = f1.
  Then F[pair] = (delta[xi[i]]) /circ f.
end.

Forall f /in ^{lambda}kappa forall i /in cof(kappa) (delta[xi[i]]) /circ f /in /VV.
Forall f /in ^{lambda}kappa exists g (Dom(g) = cof(kappa) /\ forall i /in cof(kappa) g[i] = F[(i,f)]).
Proof.
  Let f /in ^{lambda}kappa.
  Forall i /in cof(kappa) F[(i,f)] = (delta[xi[i]]) /circ f.
  Forall i /in cof(kappa) Dom(delta[xi[i]]) = /VV.
  Then forall i /in cof(kappa) ran(f) /subset Dom(delta[xi[i]]).
  Define g[i] = (delta[xi[i]]) /circ f for i in cof(kappa).
  g is a zffunction.
  Proof.
    Let i /in cof(kappa).
    Take a zfset pair such that pair = (i,f).
    Then pair /in cof(kappa) /times ^{lambda}kappa.
    Take zfsets i1,f1 such that i1 /in cof(kappa) /\ f1 /in ^{lambda}kappa /\
    (i1,f1) = pair /\ F[pair] = (delta[xi[i]]) /circ f.
    Then i1 = i /\ f1 = f.
    F[pair] = (delta[xi[i]]) /circ f.
    Then F[(i,f)] /in /VV.
  end.
  Then forall i /in cof(kappa) g[i] = F[(i,f)].
end.

Define G[f] = (Choose a zffunction g such that (Dom(g) = cof(kappa) /\ forall i /in cof(kappa) g[i] = F[(i,f)]) in g) for f in ^{lambda}kappa.

Forall f /in ^{lambda}kappa forall i /in cof(kappa) F[(i,f)] /in ^{lambda}(xi[i]).
Proof.
  Let f /in ^{lambda}kappa.
  Let i /in cof(kappa).
  Then F[(i,f)] = (delta[xi[i]]) /circ f.
  (delta[xi[i]]) /circ f is a zffunction.
  Dom((delta[xi[i]]) /circ f) = lambda.
  ((delta[xi[i]]) /circ f) : lambda /rightarrow xi[i].
  Proof.
    Let j /in lambda.
    Then ((delta[xi[i]]) /circ f)[j] = (delta[xi[i]])[f[j]].
    Then ((delta[xi[i]]) /circ f)[j] /in xi[i].
    Proof.
      Case f[j] /in xi[i]. Then (delta[xi[i]])[f[j]] = f[j]. end.
      Case f[j] /notin xi[i]. Then (delta[xi[i]])[f[j]] = 0. end.
    end.
  end.
  Then ((delta[xi[i]]) /circ f) /in ^{lambda}(xi[i]).
end.
Then forall f /in ^{lambda}kappa forall i /in cof(kappa) (G[f])[i] /in ^{lambda}(xi[i]).

G is a zffunction.
Proof.
  Dom(G) = ^{lambda}kappa.
  Forall f /in ^{lambda}kappa G[f] /in /VV.
  Proof.
    Let f /in ^{lambda}kappa.
    Take a zffunction g such that g = G[f].
    Dom(g) /in /VV.
    Then g /in /VV.
  end.
end.
G is injective.
Proof.
  Let f1, f2 /in Dom(G). Let f1 /neq f2.
  Then G[f1] /neq G[f2].
  Proof.
    Exists a /in lambda (f1[a] /neq f2[a]).
    Proof by contradiction. Assume the contrary.
      f1,f2 are functions.
      Dom(f1) = Dom(f2).
      Dom(f1) = lambda.
      Forall a /in Dom(f1) f1[a] = f2[a].
      Then f1 = f2.
      Contradiction.
    end.
    Take a zfset a such that a /in lambda /\ f1[a] /neq f2[a].
    f1 : lambda /rightarrow kappa.
    Then f1[a] /in kappa.
    Take a zfset i1 such that i1 /in cof(kappa) /\ f1[a] /in xi[i1].
    f2 : lambda /rightarrow kappa.
    Then f2[a] /in kappa.
    Take a zfset i2 such that i2 /in cof(kappa) /\ f2[a] /in xi[i2].
    Exists i /in cof(kappa) (xi[i1] /subset xi[i] /\ xi[i2] /subset xi[i]).
    Proof.
      i1,i2 /in /Ord.
      Then i1 /in i2 \/ i2 /in i1 \/ i1 = i2.
      Case i1 = i2. end.
      Case i1 /in i2.
        Then xi[i1] /subset xi[i2].
      end.
      Case i2 /in i1.
        Then xi[i2] /subset xi[i1].
      end.
    end.
    Take a zfset i such that i /in cof(kappa) /\ (xi[i1] /subset xi[i] /\ xi[i2] /subset xi[i]).
    Then f1[a] /in xi[i] /\ f2[a] /in xi[i].
    Then (G[f1])[i] /neq (G[f2])[i].
    Proof.
      (G[f1])[i] = F[(i,f1)].
      F[(i,f1)] = (delta[xi[i]]) /circ f1.
      f1[a] /in xi[i].
      Then (delta[xi[i]])[f1[a]] = f1[a].
      Then ((delta[xi[i]]) /circ f1)[a] = f1[a].
      Then (F[(i,f1)])[a] = f1[a].

      (G[f2])[i] = F[(i,f2)].
      F[(i,f2)] = (delta[xi[i]]) /circ f2.
      f2[a] /in xi[i].
      Then (delta[xi[i]])[f2[a]] = f2[a].
      Then ((delta[xi[i]]) /circ f2)[a] = f2[a].
      Then (F[(i,f2)])[a] = f2[a].
      
      Then F[(i,f1)] /neq F[(i,f2)].
      Then (G[f1])[i] /neq (G[f2])[i].
    end.
    Then G[f1] /neq G[f2].
  end.
end.

Forall i /in cof(kappa) Card(^{lambda}(xi[i])) /in kappa.
Proof.
  Let i /in cof(kappa).
  Then xi[i] /in kappa.
  Then xi[i] ^3 lambda /in kappa.
  Card(^{lambda}(xi[i])) = xi[i] ^3 lambda.
end.
Forall i /in cof(kappa) exists f (f : ^{lambda}(xi[i]) /rightarrow kappa /\ (f is injective)).
Proof.
  Let i /in cof(kappa).
  Then Card(^{lambda}(xi[i])) /subset Card(kappa).
end.
Define inj[i] = (Choose a zffunction f such that (f : ^{lambda}(xi[i]) /rightarrow kappa /\ (f is injective)) in f) for i in cof(kappa).
inj is a zffunction.
Proof.
  Let i /in cof(kappa).
  Then inj[i] is a zffunction.
  Dom(inj[i]) /in /VV.
  Then inj[i] /in /VV.
end.

Forall f /in ^{lambda}kappa forall i /in cof(kappa) (G[f])[i] /in Dom(inj[i]).
Proof.
  Let f /in ^{lambda}kappa.
  Forall i /in cof(kappa) (G[f])[i] /in ^{lambda}xi[i].
end.
Forall f /in ^{lambda}kappa exists g (Dom(g) = cof(kappa) /\ (forall i /in cof(kappa) (g[i] = (inj[i])[(G[f])[i]]))).
Proof.
  Let f /in ^{lambda}kappa.
  Then exists g (Dom(g) = cof(kappa) /\ (forall i /in cof(kappa) (g[i] = (inj[i])[(G[f])[i]]))).
  Proof.
    Define g[i] = (inj[i])[(G[f])[i]] for i in cof(kappa).
    g is a zffunction.
    Proof.
      Let i /in cof(kappa).
      Then g[i] = (inj[i])[(G[f])[i]].
      Then g[i] /in ran(inj[i]).
      Then g[i] /in /VV.
    end.
    Dom(g) = cof(kappa) /\ (forall i /in cof(kappa) (g[i] = (inj[i])[(G[f])[i]])).
  end.
end.

Card(G^[^{lambda}kappa]) /subset Card(^{cof(kappa)}kappa).
Proof.
  Let M = G^[^{lambda}kappa].
  Forall g /in M ((g is a zffunction) /\ Dom(g) = cof(kappa) /\ forall i /in cof(kappa) g[i] /in ^{lambda}(xi[i])).
  Proof.
    Let g /in M.
    Then g /in G^[^{lambda}kappa]. 
    Then exists f /in ^{lambda}kappa g = G[f].
    Take a zfset f such that f /in ^{lambda}kappa /\ g = G[f].
    Then Dom(g) = cof(kappa).
    Forall i /in cof(kappa) (G[f])[i] = F[(i,f)].
    Forall i /in cof(kappa) g[i] = F[(i,f)].
    Then forall i /in cof(kappa) g[i] /in ^{lambda}(xi[i]).
  end.
  Forall g /in M (inj, g are zffunctions).
  Forall g /in M (inj and g are diagcomposable).
  Proof.
    Let g /in M.
    g, inj are zffunctions.
    Dom(g) = Dom(inj).
    Forall i /in Dom(inj) ((inj[i] is a zffunction) /\ g[i] /in Dom(inj[i])).
  end.
  Forall g /in M g /comp inj /in ^{cof(kappa)}kappa.
  Proof.
    Let g /in M.
    g /comp inj is a zffunction.
    Dom(g /comp inj) = cof(kappa).
    g /comp inj : cof(kappa) /rightarrow kappa.
    Proof.
      Let i /in cof(kappa).
      Then (g /comp inj)[i] = (inj[i])[g[i]].
      inj[i] : ^{lambda}(xi[i]) /rightarrow kappa.
      Then (inj[i])[g[i]] /in kappa.
      Then (g /comp inj)[i] /in kappa.
    end.
  end.
  Define H[g] = g /comp inj for g in M.
  H : M /rightarrow ^{cof(kappa)}kappa.
  Proof.
    Let N = ^{cof(kappa)}kappa.
    Forall g /in M H[g] /in N.
    Proof.
      Let g /in M.
      Then H[g] = g /comp inj.
      Then H[g] /in ^{cof(kappa)}kappa.
    end.
    Then H : M /rightarrow N.
  end.
  H is injective.
  Proof.
    Let g1,g2 /in M. Let g1 /neq g2.
    Then H[g1] /neq H[g2].
    Proof.
      Exists i /in cof(kappa) (g1[i] /neq g2[i]).
      Proof by contradiction. Assume the contrary.
        g1,g2 are functions.
        Dom(g1) = Dom(g2).
        Dom(g1) = cof(kappa).
        Forall i /in Dom(g1) g1[i] = g2[i].
        Then g1 = g2.
        Contradiction.
      end.
      Take a zfset i such that i /in cof(kappa) /\ g1[i] /neq g2[i].
      (H[g1])[i] = (g1 /comp inj)[i].
      (g1 /comp inj)[i] = (inj[i])[g1[i]].
      (H[g2])[i] = (g2 /comp inj)[i].
      (g2 /comp inj)[i] = (inj[i])[g2[i]].
      inj[i] is injective.
      g1[i] /neq g2[i].
      Then (inj[i])[g1[i]] /neq (inj[i])[g2[i]].
      Then (H[g1])[i] /neq (H[g2])[i].
      Then H[g1] /neq H[g2].
    end.
  end.
  Then Card(M) /subset Card(^{cof(kappa)}kappa).
  Card(M) = Card(G^[^{lambda}kappa]).
end.

Card(G^[^{lambda}kappa]) = Card(^{lambda}kappa).
Proof.
  Let M = ^{lambda}kappa.
  G is a zffunction.
  G is injective.
  Dom(G) = M.
  ran(G) = G^[M].
  Then G : M /leftrightarrow G^[M].
  Then Card(M) = Card(G^[M]).
end.
Then Card(G^[^{lambda}kappa]) /subset Card(^{cof(kappa)}kappa).
Card(^{lambda}kappa) = kappa ^3 lambda.
Card(^{cof(kappa)}kappa) = kappa ^3 cof(kappa).
kappa ^3 cof(kappa) = Gimel[kappa].
Then kappa ^3 lambda /subset Gimel[kappa].

Then kappa ^3 lambda = Gimel[kappa].

qed.











Lemma. Contradiction.

