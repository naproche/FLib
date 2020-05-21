# 11-Cofinality

# Here again we need the function otp which associates to every subset of /Ord its order-type.
# However we now do it in a simpler way by using axioms which gives us the desired properties of otp.
# These properties were proven before but we safe much calculation time by not defining the construction of otp.
# We then define cofinality (as the minimal order-type of a cofinal subset), show that it is the same as the minimal cardinality
# of a cofinal subset and proof some facts about the cofinality of some cardinals.

# Main results:

# - the minimal cardinal of a cofinal subset coincides with the minimal otder-type
# - cof(lambda) is regular
# - cof(Alef[lambda]) = cof(lambda)
# - every infinite successor cardinal is regular






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
# New Axiom
Axiom. Let x be a zfset. Let f be a zffunction. Let x /subset Dom(f). Then Card(f^[x]) /subset Card(x).

Definition. The class of cardinals is
{ordinal alpha | alpha is a cardinal}.
Let /Card stand for the class of cardinals.

Axiom. Forall n /in /NN Card(n) = n.
Axiom. Card(/NN) = /NN.

Axiom. Let x be a zfset. Then x < /PP x.
Axiom. /Ord is a proper class.
Axiom. /Card is a proper class.

Axiom. Let kappa be a cardinal. Let /NN /subset kappa. Then kappa /in /Lim.
Lemma. Let kappa be a cardinal. Let kappa /notin /NN. Then kappa /in /Lim.




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



# Order-Type

# we now define this without the construction of section 7, only with its properties



Signature. An epshomo is a notion.

Axiom. Let f be an epshomo. Then f is a zffunction.
Axiom. Let f be a zffunction. Then f is an epshomo iff
forall x /in Dom(f) (f^[x /cap Dom(f)] /subset f[x]).

Lemma. Let f be an epshomo. Let x,y /in Dom(f). Let x /in y. Then f[x] /in f[y].
Proof.
(f^[y /cap Dom(f)] /subset f[y]).
x /in y /cap Dom(f).
Then f[x] /in f^[y /cap Dom(f)].
end.


Signature. Let x /subset /Ord. The ordertype of x is a notion.
Let otp(x) stand for the ordertype of x.

Axiom. Let x /subset /Ord. Then otp(x) is a set.
Axiom. Let alpha be an ordinal. Let x /subset alpha. Then otp(x) is an ordinal.
Axiom. Let x /subset /Ord. Let forall alpha /in /Ord x /notin /PP alpha. Then otp(x) = /Ord.
Lemma. Let x /subset /Ord. Let x be a proper class. Then otp(x) = /Ord.

Signature. Let x /subset /Ord. otpfunc(x) is a zffunction.

Axiom. Let x /subset /Ord. Then otpfunc(x) : x /leftrightarrow otp(x).
Axiom. Let x /subset /Ord. Then Dom(otpfunc(x)) = x /\ (forall y /in x (otpfunc(x)[y] = otpfunc(x)^[y /cap x])).
Lemma. Let x /subset /Ord. Then otpfunc(x) is an epshomo.
Proof.
Dom(otpfunc(x)) = x.
Let y /in Dom(otpfunc(x)).
Then otpfunc(x)^[y /cap x] /subset otpfunc(x)[y].
qed.

Axiom. Let x /subset /Ord. Let y be a set. Then otp(x) = y iff exists f ((f is an epshomo) /\ f : x /leftrightarrow y).

Axiom. Let x /subset /Ord. Let x be a proper class. Then otp(x) = /Ord.

Axiom. Let x /subset /Ord. Let x be a zfset. Then otp(x) /in /Ord.

Axiom. Let alpha be an ordinal. Let x /subset alpha. Then otp(x) /subset alpha.

Lemma. Let alpha /in /Ord. Then otp(alpha) = alpha.
Proof.
alpha /subset /Ord. alpha is a set.

Id /upharpoonright alpha : alpha /leftrightarrow alpha.
Id /upharpoonright alpha is an epshomo.
Proof.
  Dom(Id /upharpoonright alpha) = alpha.
  Let x /in alpha. 
  Then x /cap alpha = x.
  Then (Id /upharpoonright alpha)^[x /cap alpha] = (Id /upharpoonright alpha)[x].
end.
qed.

Lemma. Let x be a zfset. Let x /subset /Ord. Then Card(x) /subset otp(x).
Proof.
Take a zffunction f such that f : x /leftrightarrow otp(x).
Then f^{-1} : otp(x) /leftrightarrow x.
otp(x) /in /Ord. 
otp(x) /in Cardset(x).
qed.







# Cofinality


Definition. Let lambda /in /Lim. Let x /subset lambda. x is cofinal in lambda iff
forall alpha /in lambda exists y /in x alpha /in y.
Let x /cof y stand for x is cofinal in y.

Lemma. Let lambda /in /Lim. Forall x /subset lambda (x /cof lambda => Card(x) /notin /NN).
Proof by contradiction. Assume the contrary.

Define M = {ordinal n | n /in /NN /\ exists x (x /subset lambda /\ x /cof lambda /\ Card(x) = n)}.
Then M /neq /emptyset.

Let n = /bigcap M.
Then n /in M.
Proof by contradiction. Assume the contrary.
  M /subset /Ord.
  Forall m /in M (n /subset m /\ n /neq m).
  Then forall m /in M n /in m.
  Then n /in /bigcap M.
  Contradiction.
end.

Take a zfset x such that x /subset lambda /\ x /cof lambda /\ Card(x) = n.
Take a zffunction f such that f : n /leftrightarrow x.
Then lambda = /bigcup f^[n].
n-1 /subset Dom(f).
n-1 /in Dom(f).
/bigcup f^[n] = (/bigcup f^[n-1]) /cup f[n-1].
Proof.
  n-1 /subset n.
  /bigcup f^[n] /subset (/bigcup f^[n-1]) /cup f[n-1].
  Proof.
    Let a /in /bigcup f^[n].
    Take a zfset m such that m /in n /\ a /in f[m].
    Then m /in n-1 \/ m = n-1.
    n-1 /subset Dom(f).
    Then a /in (/bigcup f^[n-1]) /cup f[n-1].
  end.
  (/bigcup f^[n-1]) /cup f[n-1] /subset /bigcup f^[n].
  Proof.
    Let a /in (/bigcup f^[n-1]) /cup f[n-1].
    Case a /in f[n-1]. (n-1) /in n. Then a /in /bigcup f^[n]. end.
    Case a /in /bigcup f^[n-1]. Then a /in /bigcup f^[n]. end.
  end.
end.
Then lambda = /bigcup f^[n-1] /cup f[n-1].

/bigcup f^[n-1] /in /Ord.
Proof.
  f^[n-1] /subset /Ord.
  Trans(/bigcup f^[n-1]).
end.
f[n-1] /in x.
Then f[n-1] /in /Ord.

Then lambda = /bigcup f^[n-1] \/ lambda = f[n-1].
Proof.
  Take ordinals alpha, beta such that alpha = /bigcup f^[n-1] /\ beta = f[n-1].
  Then alpha /in beta \/ beta /in alpha \/ alpha = beta.
  Then alpha /cup beta = alpha \/ alpha /cup beta = beta.
end.

Then lambda = /bigcup f^[n-1].

Then f^[n-1] /cof lambda.

Card(f^[n-1]) = Card(n-1).
Proof.
  f /upharpoonright (n-1) : n-1 /leftrightarrow f^[n-1].
  Proof.
    Dom(f /upharpoonright (n-1)) = n-1.
    ran(f /upharpoonright (n-1)) = f^[n-1].
    Proof.
      ran(f /upharpoonright (n-1)) /subset f^[n-1].
      Proof.
        Let a /in ran(f /upharpoonright (n-1)).
        Take a zfset m such that m /in (n-1) /\ a = (f /upharpoonright (n-1))[m].
        Then m /in n.
        Then a = f[m].
        Then a /in f^[n-1].
      end.
      f^[n-1] /subset ran(f /upharpoonright (n-1)).
      Proof.
        Let a /in f^[n-1].
        Forall m /in (n-1) m /in n.
        Take a zfset m such that m /in (n-1) /\ a = f[m].
        Then a = (f /upharpoonright (n-1))[m].
        Then a /in ran(f /upharpoonright (n-1)).
      end.
    end.
    f /upharpoonright (n-1) is injective.
    Proof.
      f is injective.
      Let a1,a2 /in (n-1). Let a1 /neq a2.
      Then a1,a2 /in n.
      Then f[a1] /neq f[a2].
      Then (f /upharpoonright (n-1))[a1] /neq (f /upharpoonright (n-1))[a2].
    end.
  end.
end.

n-1 /in /NN.
Then Card(n-1) = n-1.
Then n-1 /in M.
Proof.
  f^[n-1] /subset lambda.
  f^[n-1] /cof lambda.
  Card(f^[n-1]) = n-1.
end.

Contradiction.

qed.


Signature. Let lambda /in /Lim. The cofinality of lambda is a notion.
Let cof(x) stand for the cofinality of x.

Definition. Let lambda /in /Lim. The cofset of lambda is {otp(x) | x /subset lambda /\ x /cof lambda}.
Let cofset(x) stand for the cofset of x.

Lemma. Let lambda /in /Lim. Then cofset(lambda) /neq /emptyset.
Proof.
lambda /cof lambda.
qed.

Axiom. Let lambda /in /Lim. Then cof(lambda) = /bigcap cofset(lambda).

Lemma. Let lambda /in /Lim. Then cof(lambda) /in /Ord.
Proof.
cofset(lambda) /subset /Ord.
qed.

Lemma. Let lambda /in /Lim. Then cof(lambda) /in cofset(lambda).
Proof by Contradiction. Assume the contrary.
Forall x /in cofset(lambda) cof(lambda) /subset x.
Proof.
  Forall x /in cofset(lambda) /bigcap cofset(lambda) /subset x.
end.
Forall x /in cofset(lambda) cof(lambda) /neq x.
Then forall x /in cofset(lambda) cof(lambda) /in x.
Then cof(lambda) /in /bigcap cofset(lambda).
Then cof(lambda) /in cof(lambda).
Contradiction.
qed.

Lemma. Let lambda /in /Lim. Then cof(lambda) /subset lambda.
Proof.
lambda /in cofset(lambda).
Proof.
  lambda /cof lambda.
  lambda = otp(lambda).
end.
Then /bigcap cofset(lambda) /subset lambda.
qed.

Definition. Let lambda /in /Lim. lambda is regular iff cof(lambda) = lambda.

Definition. Let lambda /in /Lim. The altcofset of lambda is {Card(x) | x /subset lambda /\ x /cof lambda}.
Let cofset2(x) stand for the altcofset of x.



Lemma. Let lambda /in /Lim. Then cof(lambda) = /bigcap cofset2(lambda).
Proof.
/bigcap cofset2(lambda) /subset cof(lambda).
Proof.
  Let y /in /bigcap cofset2(lambda).
  Then forall z /in cofset2(lambda) y /in z.
  Then forall z /in cofset(lambda) y /in z.
  Proof.
    Let z /in cofset(lambda).
    Take a zfset x such that x /subset lambda /\ x /cof lambda /\ z = otp(x).
    x /subset /Ord.
    Then Card(x) /subset otp(x).
    y /in Card(x).
  end.
  Then y /in cof(lambda).
end.

/bigcap cofset2(lambda) /in cofset2(lambda).
Proof by Contradiction. Assume the contrary.
  cofset2(lambda) /subset /Ord.
  Forall x /in cofset2(lambda) /bigcap cofset2(lambda) /subset x.
  Forall x /in cofset2(lambda) /bigcap cofset2(lambda) /neq x.
  Then forall x /in cofset2(lambda) /bigcap cofset2(lambda) /in x.
  Then /bigcap cofset2(lambda) /in /bigcap cofset2(lambda).
  Contradiction.
qed.

cof(lambda) /subset /bigcap cofset2(lambda).
Proof.
  Take a zfset x such that x /subset lambda /\ x /cof lambda /\ Card(x) = /bigcap cofset2(lambda).
  Take a zffunction f such that f : Card(x) /leftrightarrow x.
  Define g[n] = /bigcup f^[n] for n in Card(x).
  Then g : Card(x) /rightarrow lambda.
  Proof.
    Forall n /in Card(x) g[n] /in /Ord.
    Proof.
      Let n /in Card(x). Then f^[n] /subset /Ord.
      Then Trans(/bigcup f^[n]).
    end.
    Forall n /in Card(x) g[n] /in lambda.
    Proof by Contradiction. Assume the contrary.
      Take a zfset n such that n /in Card(x) /\ g[n] /notin lambda.
      g[n] /subset lambda.
      Proof.
        f^[n] /subset lambda.
        Then /bigcup f^[n] /subset lambda.
      end.
      Then g[n] = lambda.
      f^[n] /subset lambda.
      f^[n] /cof lambda.
      Then Card(f^[n]) /in cofset2(lambda).
      Card(f^[n]) = Card(n).
      Proof.
        f /upharpoonright n : n /leftrightarrow f^[n].
        Proof.
          Dom(f /upharpoonright n) = n.
          ran(f /upharpoonright n) = f^[n].
          f /upharpoonright n is injective.
        end.
      end.
      Card(n) /in Card(x).
      Card(n) /in cofset2(lambda).
      Contradiction.
    end.
    g is a zffunction.
  end.

  g^[Card(x)] /cof lambda.
  Proof.
    Let alpha /in lambda.
    Take a zfset y such that y /in x /\ alpha /in y.
    Take a zfset beta such that beta /in Card(x) /\ f[beta] = y.
    Then beta + 1 /in Card(x).
    Proof.
      Card(x) /notin /NN.
      Card(x) /in /Lim.
    end.
    beta /in beta + 1.
    Then y /in f^[beta + 1].
    Then alpha /in g[beta + 1].
  end.
  
  Forall a1,a2 /in Card(x) (a1 /in a2 => g[a1] /subset g[a2]).
  Proof.
    Let a1,a2 /in Card(x). Let a1 /in a2.
    Then f^[a1] /subset f^[a2].
    Then /bigcup f^[a1] /subset /bigcup f^[a2].
  end.

  Define M = {ordinal i | i /in Card(x) /\ forall j /in i (g[j] /in g[i])}.
  Define h[i] = g[i] for i in M.
  
  Then h is an epshomo.
  Proof.
    Let i /in M.
    Then h^[i /cap M] /subset h[i].
    Proof.
      Let a /in h^[i /cap M].
      Take a zfset j such that j /in i /cap M /\ a = h[j].
      Then a = g[j].
      j /in M.
      Then g[j] /in g[i].
      g[i] = h[i].
      Then a /in h[i].
    end.
  end.
  
  h^[M] /subset lambda.
  Proof.
    Let i /in M. Then h[i] = g[i].
    g[i] /in lambda.
  end.  
  h^[M] /cof lambda.
  Proof.
    Let alpha /in lambda.
    Take a zfset y such that y /in Card(x) /\ alpha /in g[y].
    Case y /in M. Then alpha /in h[y]. end.
    Case y /notin M.
      Define N = {ordinal z | z /in y /\ g[z] /notin g[y]}.
      Forall z /in N g[z] = g[y].
      Proof.
        Let z /in N.
        Then z /in y.
        Then g[z] /subset g[y] /\ g[z] /notin g[y].
        g[z], g[y] /in /Ord.
        Proof.
          g : Card(x) /rightarrow lambda.
          Then forall a /in Card(x) g[a] /in /Ord.
        end.
        Take ordinals alpha1, beta1 such that alpha1 = g[z] /\ beta1 = g[y].
        Then alpha1 /in beta1 \/ beta1 /in alpha1 \/ alpha1 = beta1.
        alpha1 /notin beta1 /\ alpha1 /subset beta1.
        Then alpha1 = beta1.
      end.
      Let yy = /bigcap N.
      Then yy /in N.
      Proof by contradiction. Assume the contrary.
        N /subset /Ord.
        Forall xx /in N yy /subset xx.
        Forall xx /in N yy /neq xx.
        Then forall xx /in N yy /in xx.
        Then yy /in yy.
        Contradiction.
      end.
      Then g[yy] = g[y].
      yy /in M.
      Proof.
        Forall j /in yy g[j] /in g[yy].
        Proof.
          Let j /in yy.
          Then g[j] /subset g[yy].
          g[j] /in g[yy] \/ g[j] = g[yy].
          Case g[j] = g[yy]. Then j /in N. Contradiction. end.
          Case g[j] /in g[yy]. end.
        end.
      end.
      Then alpha /in h[yy].
    end.
  end.
  
  h : M /leftrightarrow h^[M].
  Proof.
    h is injective.
    Proof.
      Let a1,a2 /in M. Let a1 /neq a2.
      Then h[a1] /neq h[a2].
      Proof.
        a1 /in a2 \/ a2 /in a1.
        Case a1 /in a2.
          Then g[a1] /in g[a2].
          Then h[a1] /neq h[a2].
        end.
        Case a2 /in a1.
          Then g[a2] /in g[a1].
          Then h[a2] /neq h[a1].
        end.
      end.
    end.
  end.
  h^{-1} : h^[M] /leftrightarrow M.  

  M /subset Card(x).
  Then otp(M) /subset Card(x).
  
  M /subset /Ord.
  otpfunc(M) : M /leftrightarrow otp(M).
  otpfunc(M) is an epshomo.
  
  otpfunc(M) /circ h^{-1} : h^[M] /leftrightarrow otp(M).
  Proof.
    Dom(otpfunc(M) /circ h^{-1}) = h^[M].
    ran(otpfunc(M) /circ h^{-1}) = otp(M).
    otpfunc(M) /circ h^{-1} is injective.
  end.
  
  otpfunc(M) /circ h^{-1} is an epshomo.
  Proof.
    Forall a1,a2 /in h^[M] (a1 /in a2 => h^{-1}[a1] /in h^{-1}[a2]).
    Proof.
      Let a1,a2 /in h^[M]. Let a1 /in a2.
      Take zfsets b1,b2 such that b1,b2 /in M /\ h[b1] = a1 /\ h[b2] = a2.
      Then b1 /in b2.
      Proof.
        Forall aa,bb /in /Ord (aa /in bb \/ bb /in aa \/ aa = bb).
        b1,b2 /in /Ord.
        Then b1 /in b2 \/ b2 /in b1 \/ b1 = b2.
        Case b1 = b2. Then a1 = a2. Contradiction. end.
        Case b2 /in b1. 
          Then a2 /in a1.
          Proof.
            h is an epshomo.
            Then h^[b1 /cap M] /subset h[b1].
            b2 /in b1 /cap M.
            Then h[b2] /in h[b1].
          end.
          Contradiction. 
        end.
        Case b1 /in b2. end.
      end.
    end.
    Forall a1,a2 /in M (a1 /in a2 => otpfunc(M)[a1] /in otpfunc(M)[a2]).
    Proof.
      Let a1,a2 /in M. Let a1 /in a2.
      Then otpfunc(M)[a2] = otpfunc(M)^[a2 /cap M].
      a1 /in a2 /cap M.
      Then otpfunc(M)[a1] /in otpfunc(M)[a2].
    end.
    Let phi = otpfunc(M) /circ h^{-1}.
    Then phi : h^[M] /leftrightarrow otp(M).
    
    Forall a1,a2 /in h^[M] (a1 /in a2 => phi[a1] /in phi[a2]).
    Proof.
      Let a1,a2 /in h^[M]. Let a1 /in a2.
      Then h^{-1}[a1] /in h^{-1}[a2].
      h^{-1}[a1], h^{-1}[a2] /in M.
      Take zfsets b1,b2 such that b1,b2 /in M /\ b1 = h^{-1}[a1] /\ b2 = h^{-1}[a2].
      Then b1 /in b2.
      Then otpfunc(M)[b1] /in otpfunc(M)[b2].
    end.      
    Then phi is an epshomo.
    Proof.      
      Let a /in h^[M]. Then phi^[a /cap h^[M]] /subset phi[a].
    end.    
  end.
  
  Then otp(h^[M]) = otp(M).
  
  Then otp(M) /in cofset(lambda).
  Then /bigcap cofset(lambda) /subset otp(M).
  Then cof(lambda) /subset otp(M).
  otp(M) /subset Card(x).
  Then cof(lambda) /subset Card(x).
  
end.

qed.


Lemma. Forall lambda /in /Lim cof(lambda) /subset Card(lambda).
Proof.
Let lambda /in /Lim.
Card(lambda) /in cofset2(lambda).
Proof.
  lambda /subset lambda. lambda /cof lambda.
end.
Then /bigcap cofset2(lambda) /subset Card(lambda).  
qed.

Lemma. Forall lambda /in /Lim /NN /subset cof(lambda).
Proof.
Let lambda /in /Lim.
Forall x /in cofset2(lambda) /NN /subset x.
Proof.
  Let x /in cofset2(lambda).
  Take a zfset y such that y /subset lambda /\ y /cof lambda /\ Card(y) = x.
  Then Card(y) /notin /NN.
  Card(y) /in /Ord.
  Then Card(y) /in /NN \/ /NN /in Card(y) \/ /NN = Card(y).
  Then /NN /subset Card(y).
end.
Then /NN /subset /bigcap cofset2(lambda).
qed.


Lemma. cof(/NN) = /NN.
Proof.
cof(/NN) /subset /NN.
/NN /subset cof(/NN).
qed.


Lemma. Forall lambda /in /Lim cof(lambda) /in cofset2(lambda).
Proof.
Let lambda /in /Lim.
/bigcap cofset2(lambda) /in cofset2(lambda).
Proof by contradiction. Assume the contrary.
  Then forall x /in cofset2(lambda) /bigcap cofset2(lambda) /in x.
  Proof.
    Let x /in cofset2(lambda).
    Then x /neq /bigcap cofset2(lambda).
    /bigcap cofset2(lambda) /subset x.
    /bigcap cofset2(lambda) /in /Ord.
    Proof.
      Trans(/bigcap cofset2(lambda)).
    end.
    x /in /Ord.
    Then /bigcap cofset2(lambda) /in x.
  end.
  Forall x /in cofset2(lambda) (/bigcap cofset2(lambda) /subset x).
  Forall x /in cofset2(lambda) (/bigcap cofset2(lambda) /neq x).
  cofset2(lambda) /subset /Ord.
  /bigcap cofset2(lambda) /in /Ord.
  Proof.
    Trans(/bigcap cofset2(lambda)).
  end.
end.
qed.


Lemma. Forall lambda /in /Lim cof(lambda) /in /Card.
Proof.
Let lambda /in /Lim.
Then cof(lambda) /in cofset2(lambda).
cofset2(lambda) /subset /Card.
qed.


Lemma. Let lambda /in /Lim. Exists x (x /subset lambda /\ x /cof lambda /\ otp(x) = cof(lambda)).
Lemma. Let lambda /in /Lim. Exists x (x /subset lambda /\ x /cof lambda /\ Card(x) = cof(lambda)).




Lemma. Forall lambda /in /Lim (cof(lambda) is regular).
Proof.
Let lambda /in /Lim.
cof(cof(lambda)) /subset cof(lambda).

cof(lambda) /subset cof(cof(lambda)).
Proof.
  Take an ordinal gamma such that gamma = cof(lambda).
  gamma /in cofset(lambda).
  Take a zfset x such that x /subset lambda /\ x /cof lambda /\ otp(x) = gamma.
  x /subset /Ord.
  Then otpfunc(x) : x /leftrightarrow gamma.
  Let f = (otpfunc(x))^{-1}. Then f : gamma /leftrightarrow x.
  Forall a1,a2 /in gamma (a1 /in a2 => f[a1] /in f[a2]).
  Proof.
    Let a1,a2 /in gamma. Let a1 /in a2.
    Take zfsets b1,b2 such that b1,b2 /in x /\ (otpfunc(x))[b1] = a1 /\ (otpfunc(x))[b2] = a2.
    Then b1 /in b2.
    Proof.
      Forall aa,bb /in /Ord (aa /in bb \/ bb /in aa \/ aa = bb).
      b1,b2 /in /Ord.
      Then b1 /in b2 \/ b2 /in b1 \/ b1 = b2.
      Case b1 = b2. Then a1 = a2. Contradiction. end.
      Case b2 /in b1. 
        Then a2 /in a1.
        Proof.
          (otpfunc(x)) is an epshomo.
          Then (otpfunc(x))^[b1 /cap x] /subset (otpfunc(x))[b1].
          b2 /in b1 /cap x.
          Then (otpfunc(x))[b2] /in (otpfunc(x))^[b1 /cap x].
          Then (otpfunc(x))[b2] /in (otpfunc(x))[b1].
        end.
        Contradiction. 
      end.
      Case b1 /in b2. end.
    end.
  end.
  
  cof(gamma) /in cofset(gamma).
  Take a zfset y such that y /subset gamma /\ y /cof gamma /\ otp(y) = cof(gamma).
  y /subset /Ord.
  Then otpfunc(y) : y /leftrightarrow cof(gamma).
  Let g = (otpfunc(y))^{-1}. Then g : cof(gamma) /leftrightarrow y.
  Forall a1,a2 /in cof(gamma) (a1 /in a2 => g[a1] /in g[a2]).
  Proof.
    Let a1,a2 /in cof(gamma). Let a1 /in a2.
    Take zfsets b1,b2 such that b1,b2 /in y /\ (otpfunc(y))[b1] = a1 /\ (otpfunc(y))[b2] = a2.
    Then b1 /in b2.
    Proof.
      Forall aa,bb /in /Ord (aa /in bb \/ bb /in aa \/ aa = bb).
      b1,b2 /in /Ord.
      Then b1 /in b2 \/ b2 /in b1 \/ b1 = b2.
      Case b1 = b2. Then a1 = a2. Contradiction. end.
      Case b2 /in b1. 
        Then a2 /in a1.
        Proof.
          (otpfunc(y)) is an epshomo.
          Then (otpfunc(y))^[b1 /cap y] /subset (otpfunc(y))[b1].
          b2 /in b1 /cap y.
          Then (otpfunc(y))[b2] /in (otpfunc(y))^[b1 /cap y].
          Then (otpfunc(y))[b2] /in (otpfunc(y))[b1].
        end.
        Contradiction. 
      end.
      Case b1 /in b2. end.
    end.
  end.

  Let h = f /circ g.
  Then h : cof(gamma) /rightarrow x.
  Proof.
    Let a /in cof(gamma). 
    Then g[a] /in y.
    Then f[g[a]] /in x.
    Then h[a] /in x.
  end.
  h : cof(gamma) /leftrightarrow h^[cof(gamma)].
  Proof.
    ran(h) = h^[cof(gamma)].
    h is injective.
    Proof.
      f is injective.
      g is injective.
      Let a1,a2 /in cof(gamma). Let a1 /neq a2.
      Then g[a1] /neq g[a2].
      Take zfsets b1,b2 such that b1,b2 /in y /\ b1 = g[a1] /\ b2 = g[a2].
      Then b1 /neq b2.
      Then f[b1] /neq f[b2].
      Then h[a1] /neq h[a2].
    end.
  end.
  Let z = h^[cof(gamma)].
  Then h^{-1} : z /leftrightarrow cof(gamma).
  Forall a1,a2 /in cof(gamma) (a1 /in a2 => h[a1] /in h[a2]).
  Proof.
    Let a1,a2 /in cof(gamma). Let a1 /in a2.
    Then g[a1] /in g[a2].
    g[a1], g[a2] /in y.
    Take zfsets b1,b2 such that b1,b2 /in y /\ b1 = g[a1] /\ b2 = g[a2].
    Then b1 /in b2.
    Then f[b1] /in f[b2].
  end.
  
  Forall a1,a2 /in z (a1 /in a2 => h^{-1}[a1] /in h^{-1}[a2]).
  Proof.
    Let a1,a2 /in z. Let a1 /in a2.
    Take zfsets b1,b2 such that b1,b2 /in cof(gamma) /\ h[b1] = a1 /\ h[b2] = a2.
    Then b1 /in b2.
    Proof.
      Forall aa,bb /in /Ord (aa /in bb \/ bb /in aa \/ aa = bb).
      b1,b2 /in /Ord.
      Then b1 /in b2 \/ b2 /in b1 \/ b1 = b2.
      Case b1 = b2. Then a1 = a2. Contradiction. end.
      Case b2 /in b1. 
        Then h[b2] /in h[b1].
        Then a2 /in a1.
        Contradiction. 
      end.
      Case b1 /in b2. end.
    end.
  end.    
  Then h^{-1} is an epshomo.
  Proof.  
    Let a /in z. Then (h^{-1})^[a /cap z] /subset (h^{-1})[a].
  end. 

  Then otp(z) = cof(gamma).
  Proof.
    z /subset /Ord.
    h^{-1} is an epshomo.
    h^{-1} : z /leftrightarrow cof(gamma).
  end.

  z /cof lambda.
  Proof. 
    Let alpha /in lambda.
    x /cof lambda.
    Take a zfset xa such that xa /in x /\ alpha /in xa.
    f : gamma /leftrightarrow x.
    Take a zfset beta such that beta /in gamma /\ f[beta] = xa.
    y /cof gamma.
    Take a zfset yb such that yb /in y /\ beta /in yb.
    g : cof(gamma) /leftrightarrow y.
    Take a zfset delta such that delta /in cof(gamma) /\ g[delta] = yb.
    Then h[delta] = f[yb].
    beta /in yb.
    Then f[beta] /in f[yb].
    alpha /in f[beta].
    f[yb] /in /Ord.
    Then alpha /in f[yb].
  end.
  
  Then otp(z) /in cofset(lambda).
  Then /bigcap cofset(lambda) /subset otp(z).
  Then cof(lambda) /subset cof(gamma).
 
end.

qed.


Lemma. Forall alpha /in /Ord Alef[alpha] /in /Lim.


Lemma. Let alpha /in /Lim. Then cof(Alef[alpha]) = cof(alpha).
Proof.

cof(Alef[alpha]) /subset cof(alpha).
Proof.
  Take a zfset x such that x /subset alpha /\ x /cof alpha /\ Card(x) = cof(alpha).
  Let y = Alef^[x].
  Then y /subset Alef[alpha].
  Proof.
    Let a /in y.
    Take a zfset b such that b /in x /\ a = Alef[b].
    Then b /in alpha.
    Then Alef[b] /in Alef[alpha].
  end.
  y /cof Alef[alpha].
  Proof.
    Let a /in Alef[alpha].
    Alef[alpha] = {zfset x | exists beta /in alpha x /in Alef[beta]}.
    Take a zfset beta such that beta /in alpha /\ a /in Alef[beta].
    x /cof alpha.
    Take a zfset z such that z /in x /\ beta /in z.
    Then Alef[z] /in y.
    Alef[beta] /subset Alef[z].
    a /in Alef[z].
  end.
  Card(y) = Card(x).
  Proof.
    Alef /upharpoonright x : x /leftrightarrow y.
    Proof.
      Dom(Alef /upharpoonright x) = x.
      ran(Alef /upharpoonright x) = y.
      Alef /upharpoonright x is injective.
      Proof.
        Let a1,a2 /in x.
        Let a1 /neq a2.
        Then Alef[a1] /neq Alef[a2].
        Proof.
          Forall b1, b2 /in /Ord (b1 /in b2 \/ b2 /in b1 \/ b1 = b2).
          a1,a2 /in /Ord.
          Then a1 /in a2 \/ a2 /in a1 \/ a1 = a2.
          a1 /in a2 \/ a2 /in a1.
          Case a1 /in a2. Then Alef[a1] /in Alef[a2]. end.
          Case a2 /in a1. Then Alef[a2] /in Alef[a1]. end.
        end.
      end.
    end.
  end.
  Then Card(y) /in cofset2(Alef[alpha]).
  Then /bigcap cofset2(Alef[alpha]) /subset Card(y).
end.

cof(alpha) /subset cof(Alef[alpha]).
Proof.
  Take a zfset x such that x /subset Alef[alpha] /\ x /cof Alef[alpha] /\ 
  Card(x) = cof(Alef[alpha]).
  Forall y /in x exists beta /in alpha y /in Alef[beta].
  Define f[n] = (choose zfset beta such that beta /in alpha /\ n /in Alef[beta] in beta) 
  for n in x.
  Let y = f^[x].
  Then y /subset alpha.
  y /cof alpha.
  Proof.
    Let beta /in alpha.
    Then Alef[beta] /in Alef[alpha].
    Take a zfset z such that z /in x /\ Alef[beta] /in z.
    Then f[z] /in y.
    z /in Alef[f[z]].
    Then Alef[beta] /in Alef[f[z]].
    Then beta /in f[z].
    Proof.
      beta, f[z] /in /Ord.
      Then beta /in f[z] \/ f[z] /in beta \/ f[z] = beta.
      Case beta /in f[z]. end.
      Case f[z] /in beta. 
        Then Alef[f[z]] /in Alef[beta].
        Take ordinals a1,a2 such that a1 = Alef[beta] /\ a2 = Alef[f[z]].
        Then a1 /in a2 /\ a2 /in a1.
        Contradiction. 
      end.
      Case f[z] = beta. 
        Then Alef[beta] = Alef[f[z]]. 
        Contradiction. 
      end.
    end.
  end.
  Card(y) /subset Card(x).
  Proof.
    f is a zffunction.
    x /subset Dom(f).
    Then Card(f^[x]) /subset Card(x).
  end.
  Card(y) /in cofset2(alpha).
  Then /bigcap cofset2(alpha) /subset Card(y).
  Then /bigcap cofset2(alpha) /subset Card(x).
end.

qed.


Lemma. cof(Alef[/NN]) = /NN.


# New Lemma
Lemma. Let x be a zfset. Let x /neq /emptyset. Let alpha /in /Ord. Let Card(x) /subset alpha. Then exists f (f : alpha /rightarrow x /\ ran(f) = x).
Proof.
Take a zffunction g such that g : Card(x) /leftrightarrow x.
Take a zfset b such that b /in x.
Define f[n] =
  Case n /in Card(x) -> g[n],
  Case n /notin Card(x) -> b
for n in alpha.
Then f : alpha /rightarrow x.
Proof.
  Dom(f) = alpha.
  Let beta /in alpha. Then f[beta] /in x.
end.
ran(f) = x.
Proof.
  Let y /in x.
  Take a zfset beta such that beta /in Card(x) /\ g[beta] = y.
  Then f[beta] = y.
end.
qed.

Axiom. Forall x,y /in /VV (x /times y /in /VV).
Axiom. Forall alpha /in /Ord (Card(Alef[alpha] /times Alef[alpha]) = Alef[alpha]).


Lemma. Forall alpha /in /Ord cof(Alef[alpha + 1]) = Alef[alpha + 1].
Proof by contradiction. Assume the contrary.
Take an ordinal alpha such that alpha /in /Ord /\ cof(Alef[alpha + 1]) /neq Alef[alpha + 1].
Take a zfset x such that x /subset Alef[alpha + 1] /\ x /cof Alef[alpha + 1] /\ Card(x) = cof(Alef[alpha + 1]).
Then Card(x) /subset Alef[alpha].
Proof.
  Card(x) /subset Alef[alpha + 1].
  Card(x) /neq Alef[alpha + 1].
  /NN /subset Card(x).
  Take an ordinal beta such that Card(x) = Alef[beta].
  Then beta /in alpha + 1.
  Then beta /subset alpha.
  Then Card(x) /subset Alef[alpha].
end.
Forall i /in Alef[alpha + 1] Card(i) /subset Alef[alpha].
Proof.
  Let i /in Alef[alpha + 1].
  Then i /in /Ord.
  i /subset Alef[alpha + 1].
  Card(i) /subset i.
  Then Card(i) /subset Alef[alpha + 1].
  Card(i) /neq Alef[alpha + 1].
  Card(i) /in /NN \/ /NN /subset Card(i).
  Proof.
    Card(i), /NN /in /Ord.
    Then Card(i) /in /NN \/ /NN /in Card(i) \/ /NN = Card(i).
  end.
  Case Card(i) /in /NN. 
    /NN /subset Alef[alpha].
    Card(i) /subset /NN.
    Then Card(i) /subset Alef[alpha].
  end.
  Case /NN /subset Card(i).
    Take an ordinal beta such that Card(i) = Alef[beta].
    Then beta /in alpha + 1.
    Then beta /subset alpha.
    Then Card(i) /subset Alef[alpha].
  end.
end.

Take a zffunction f such that f : Alef[alpha] /rightarrow x /\ ran(f) = x.

Forall i /in Alef[alpha + 1] (exists h (h : Alef[alpha] /rightarrow i+1 /\ ran(h) = i+1)).
Proof.
  Let i /in Alef[alpha + 1].
  Then i+1 /in Alef[alpha + 1].
  Card(i+1) /subset i+1.
  Card(i+1) /in /Ord.
  Then Card(i+1) = i+1 \/ Card(i+1) /in i+1.
  Alef[alpha + 1] /in /Ord.
  Then Card(i+1) /in Alef[alpha + 1].
  i+1 /neq /emptyset.
end.
Define g[i] = (choose a zffunction phi such that (phi : Alef[alpha] /rightarrow (i+1) /\ ran(phi) = (i+1)) in phi)
for i in Alef[alpha + 1].

Forall a /in Alef[alpha] f[a] /in Alef[alpha + 1].
Forall a,b /in Alef[alpha] (f[a] /in Dom(g) /\ b /in Dom(g[f[a]])).
Forall pair /in Alef[alpha] /times Alef[alpha] exists a,b /in Alef[alpha] (pair = (a,b)).

Define h[pair] = (Choose zfsets a,b such that a,b /in Alef[alpha] /\ pair = (a,b) in (g[f[a]])[b]) for pair in Alef[alpha] /times Alef[alpha].

h is a zffunction.
Proof.
  Let pair /in Alef[alpha] /times Alef[alpha].
  Take zfsets a,b such that a /in Alef[alpha] /\ b /in Alef[alpha] /\ pair = (a,b).
  Then f[a] /in x.
  Then g[f[a]] is a zffunction.
  Dom(g[f[a]]) = Alef[alpha].
  Then (g[f[a]])[b] /in /VV.
  (g[f[a]])[b] = h[pair].
  Then h[pair] /in /VV.
end.

Alef[alpha + 1] /subset h^[Alef[alpha] /times Alef[alpha]].
Proof.
  Let a /in Alef[alpha + 1].
  Take a zfset b such that b /in x /\ a /in b.
  Take a zfset c such that c /in Alef[alpha] /\ f[c] = b.
  a /in ran(g[b]).
  Take a zfset d such that d /in Alef[alpha] /\ (g[b])[d] = a.
  Then (g[f[c]])[d] = a.
  Take a zfset pair such that pair = (c,d).
  Then pair /in Alef[alpha] /times Alef[alpha].
  h[pair] = (g[f[c]])[d].
  Then h[pair] = a.
end.

Then Card(Alef[alpha + 1]) /subset Card(h^[Alef[alpha] /times Alef[alpha]]).
Card(h^[Alef[alpha] /times Alef[alpha]]) /subset Card(Alef[alpha] /times Alef[alpha]).
Card(Alef[alpha + 1]) = Alef[alpha + 1].
Card(Alef[alpha] /times Alef[alpha]) = Alef[alpha].
Then Alef[alpha + 1] /subset Alef[alpha].
Proof.
  Take a zfset a such that a = Card(Alef[alpha + 1]).
  Take a zfset b such that b = Card(h^[Alef[alpha] /times Alef[alpha]]).
  Take a zfset c such that c = Card(Alef[alpha] /times Alef[alpha]).
  a /subset b.
  b /subset c.
  Then a /subset c.
  a = Alef[alpha + 1].
  c = Alef[alpha].
end.
Alef[alpha] /in Alef[alpha + 1].

Contradiction.

qed.






Lemma. Contradiction.
