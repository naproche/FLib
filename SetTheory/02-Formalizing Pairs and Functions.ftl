# 2-Formalizing Pairs and Functions

# Here we introduce ordered pairs the set-theoretic way as (a,b) = {{a},{a,b}} and show that this has the properties we want for an ordered pair.
# Relations are defined as a set of ordered paird and functions are introduced as relations with additional properties.
# We defined Id as the set of pairs (x,x) and showed that some basic properties about Id hold.

# In this section we do not distinguish between sets and zfsets. But we will see that even without the axiom of foundation
# we will come to a contradiction.

# Main Results:

# - For any set A there is an injective map F : A /rightarrow /PP A.
# - For any set A there is no injective map G : /PP A /rightarrow A.

# The second lemma leads to a contradiction: Since /VV is considered as a set itself we now have /VV = /PP /VV.
# So Id is in fact an injective map from /PP /VV to /VV.
# So here we see that even without foundation, only with the introduction of the power set we lead to a contradiction.
# So we need to introduce zfset even for basic set theory.




# General Syntax

Let x /in y stand for x is an element of y.
Let x /notin y stand for x is not an element of y.
Let x /neq y stand for x != y.


# Pretyped Variables

Let a,b,c,A,B,C,x,y,z,X,Y,Z stand for sets.


# Introduction of Emptyset, Universe

Definition Emptyset. The empty set is {set x | x /neq x}.
Let /emptyset stand for the empty set.

Definition. Let a be a set. a is empty iff a = /emptyset.
Definition. Let a be a set. a is nonempty iff exists b (b /in a).

Lemma. Let a be a set. Let a be nonempty. Then a /neq /emptyset.

Definition Universe. The universe is {set x | x = x}.
Let /VV stand for the universe.

Axiom Extentionality. Forall a, b ( (forall c (c /in a <=> c /in b)) => a = b).

# Attention, the universe is considered as a set itself, so foundation does not hold.



# Arithmetic

Definition Subset. A subset of A is a set B such that
forall c (c /in B => c /in A).
Let B /subset A stand for B is a subset of A.

Lemma SubsetTest. Let A, B be sets. Let A /subset B and B /subset A. Then A = B.

Definition Pair. The pair of A and B is
{set a | a = A \/ a = B}.

Definition Union. The union of X and Y is 
{set x | x /in X or x /in Y}.
Let X /cup Y stand for the union of X and Y.

Definition Intersection. The intersection of X and Y is 
{set x | x /in X and x /in Y}.
Let X /cap Y stand for the intersection of X and Y.

Definition Difference. The difference of X and Y is 
{set x | x /in X and x /notin Y}.
Let X /setminus Y stand for the difference of X and Y.

Definition BigUnion. The union of X is
{set x | exists y (y /in X /\ x /in y)}.
Let /bigcup X stand for the union of X.

Definition BigIntersection. The intersection of X is
{set x | forall y (y /in X => x /in y)}.
Let /bigcap X stand for the intersection of X.

Definition PowerSet. The power set of X is
{set x | x /subset X}.
Let /PP X stand for the power set of X.

Definition Singleton. The singleton set of X is
{set x | x = X}.
Let <X> stand for the singleton set of X.







# Ordered pairs


Definition OPair. Let x and y be sets. The ordered pair of x and y is 
{set z | z = <x> \/ (forall a (a /in z <=> a = x \/ a = y))}.
Let [x,y] stand for the ordered pair of x and y.

Lemma. Let x,y,X,Y be sets such that [x,y] = [X,Y]. Then x = X /\ y = Y.
Proof. <x> /in [x,y]. Therefore <x> /in [X,Y].
Then <x> = <X> \/ (forall a (a /in <x> <=> a = X \/ a = Y)).
Then x=X.
Take a set z such that z is the pair of x and y. Then z /in [x,y]. Then z /in [X,Y].
Then  z = <X> \/ (forall a (a /in z <=> a = X \/ a = Y)).
Then y = X \/ y = Y.
Take a set zz such that zz is the pair of X and Y. Then zz /in [X,Y]. Then zz /in [x,y].
Then  zz = <x> \/ (forall a (a /in zz <=> a = x \/ a = y)).
Then Y = x \/ y = Y.
Then x=X /\ y=Y.
qed.




Definition CartProd. The cartesian product of A and B is
{set x | exists a exists b (x = [a,b] /\ a /in A /\ b /in B)}. 
Let A /times B stand for the cartesian product of A and B.

Lemma CartTest1. Let x be an element of the cartesian product of A and B and x = [a,b]. Then a /in A /\ b /in B.
Lemma CartTest2. Let A and B be sets. Then A /times B = {[a,b] | a,b /in /VV /\ a /in A /\ b /in B}.
Lemma CartTest3. Let A and B be sets. Let x be a set and x /in A /times B.
Then exists a exists b (x = [a,b] /\ a /in A /\ b /in B).
Lemma CartTest4. Let a,b be sets and a /in A and b /in B. Then [a,b] /in A /times B.
Lemma CartTest5. Let a,b be sets and a /in A and b /in B. Then [a,b] /subset /PP (A /cup B).




# Relations


[synonym relation/-s]
Definition. A relation is a set R such that 
R /subset /VV /times /VV.
Let a - R - b stand for [a,b] /in R.

Let R,S stand for relations.

Definition Domain. The domain of R is
{set x | exists y ([x,y] /in R)}.
Let domain(R) stand for the domain of R.

Definition Range. The range of R is
{set y | exists x ([x,y] /in R)}.
Let ran(R) stand for the range of R.

Definition Field. The field of R is
domain(R) /cup ran(R).
Let field(R) stand for the field of R.

Definition Restriction. The restriction of R to A is
{set z | z /in R /\ exists x exists y (z = [x,y] /\ x /in A)}.
Let R /upharpoonright A stand for the restriction of R to A.

Definition Image. The image of A under R is
{set y | exists z exists x (x /in A /\ z = [x,y] /\ z /in R)}.
Let R[A] stand for the image of A under R.

Definition Composition. The composition of S and R is
{set u | exists x exists y exists z (x - R - y /\ y - S - z /\ u = [x,z])}.
Let S /circ R stand for the composition of S and R.

Definition Inverse. The inverse of R is
{set a | exists x,y /in /VV (a = [y,x] /\ [x,y] /in R)}.
Let R^{-1} stand for the inverse of R.


Lemma RelTest1. domain(/emptyset) = /emptyset.
Lemma RelTest2. Let R be a relation. Let x /in R and x = [a,b]. Then [b,a] /in R^{-1}.
Lemma RelTest3. Let x /in R^{-1} and x = [a,b] and y = [b,a]. Then y /in R.
Lemma RelTest4. Let R be a relation. Then R /subset /VV /times /VV.
Lemma RelTest5. Let R be a relation. Then R^{-1} is a relation.

Lemma RelTest6. Let R be a relation. Then (R^{-1})^{-1} is a relation.
Lemma RelTest7. Let x be a set and x /in R. Then exists y,z /in /VV (x = [y,z]).
Lemma RelTest8. Let R be a relation. Let x /in R^{-1}.
Then exists y exists z ([z,y] /in R /\ x = [y,z]).
Lemma RelTest9. Let R be a relation. Let x /in (R^{-1})^{-1}.
Then exists y exists z ([z,y] /in R^{-1} /\ x = [y,z]).
Lemma RelTest10. Let R be a relation. Let x /in (R^{-1})^{-1}.
Then exists y exists z ([y,z] /in R /\ x = [y,z]).
Proof. x /in (R^{-1})^{-1}. Therefore exists y exists z ([z,y] /in R^{-1} /\ x = [y,z]).
Therefore exists y,z [y,z] /in R.
qed.

Lemma RelTest11. Let R be a relation. Let x /in R. Let x = [y,z]. Then [y,z] /in R.
Lemma RelTest12. Let R be a relation. Let x /in (R^{-1})^{-1}.
Then exists y exists z (x /in R /\ x = [y,z]).
Lemma RelTest13. (R^{-1})^{-1} /subset R.




# Functions

Let F denote a relation.

Definition 109. A map is a relation F such that
forall x,y,z (x - F - y /\ x - F - z => y = z).

Definition 109a. Let F be a map.  The value of F at x is 
{set u | forall y /in /VV (x - F - y => u /in y)}.
Let F(x) denote the value of F at x.

Lemma. Let F be a map. Let x /in domain(F). Then F(x) is a set.

Lemma ValTest1. Let F be a map. Let x /in domain(F). Let y be a set. Let x - F - y. Then y = F(x).
Proof. Forall z (x - F - z => z = y). Then F(x) /subset y.
Then y /subset F(x).
Then F(x) = y.
qed.
Lemma ValTest2. Let F be a map. Let x /in domain(F). Let y = F(x). Then x - F - y.
Proof. Take z such that x - F - z. z = y.
qed.

Definition Map. A map from A to B is a relation F such that
F is a map and domain(F) = A and ran(F) /subset B.
Let F : A /rightarrow B stand for F is a map from A to B.

Definition PMap. A partial map from A to B is a relation F such that
F is a map and domain(F) /subset A and ran(F) /subset B.
Let F : A /harpoonright B stand for F is a partial map from A to B.

Definition. Id = {set x | exists y /in /VV (x = [y,y])}. 

Lemma IdTest1. Id is a relation.
Lemma. Let x, y be sets such that x - Id - y. Then x = y.
Proof. [x,y] /in Id. Take sets a, z such that (a /in Id /\ a = [z,z] /\ a = [x,y]).
Then x = y.
qed.
Lemma IdTest2. Id is a map.
Lemma IdTest3. domain(Id) = /VV.
Lemma IdTest4. ran(Id) = /VV.
Lemma IdTest5. Id(x) = x.

Lemma IdTest6. Id : /VV /rightarrow /VV.

Definition. Assume F : A /rightarrow B. F is surjective from A to B
iff ran(F) = B.

Lemma IdTest7. Id is surjective from /VV to /VV.

Definition Injective. Let F be a map. F is injective iff
forall x,y (x,y /in domain(F) /\ x /neq y => F(x) /neq F(y)).

Lemma IdTest8. Id is injective.
Lemma IdTest9. Id^{-1} = Id.
Proof. Let x /in Id. Then exists a (x = [a,a]).
  Then x /in Id.
  Then Id /subset Id^{-1}.
qed.

Definition Bijective. A bijective map from A to B is a map F such that
F : A /rightarrow B and F is surjective from A to B 
and F is injective.
Let F : A /leftrightarrow B stand for 
F is a bijective map from A to B.

Lemma IdTest10. Id : /VV /leftrightarrow /VV.

Lemma InjTest1. Let F be an injective map. Let domain(F) = A and ran(F) = B.
Then F^{-1} is a map.
Lemma InjTest2. Let F be an injective map. Let domain(F) = A and ran(F) = B.
Then domain(F^{-1}) = B and ran(F^{-1}) = A.

Lemma BijTest1. Let F be a bijective map from A to B. Then F^{-1} is a relation.
Lemma BijTest2. Let F be a bijective map from A to B. Then domain(F^{-1}) = B and ran(F^{-1}) = A.
Lemma BijTest3. Let F be a bijective map from A to B.
Then forall x,y (x,y /in domain(F) /\ F(x) = F(y) => x = y).
Lemma BijTest4. Let F be a bijective map from A to B.
Then forall x,y,z (x,y /in domain(F) /\ x - F - z /\ y - F - z => x = y).
Lemma BijTest5. Let F be a bijective map from A to B. Then F^{-1} is a map from B to A.

Definition 110f. ^{A}B = {set f | f : A /rightarrow B}.

Lemma IdTest11. Id /in ^{/VV}/VV.



# Various results


Theorem 115a. There exists an injective map F such that F : A /rightarrow /PP A.
Proof. Define F = {[u,<u>] | u /in A}. F is a relation. F is a map. domain(F) /subset A. A /subset domain(F).
domain(F) = A.
ran(F) /subset /PP A.
F is injective.
qed.


Theorem 114b. Let A be a set. There is no injective map G such that 
G: /PP A /rightarrow A.
Proof by contradiction.
    Assume the contrary.
    Take an injective map G such that G : /PP A /rightarrow A.
    G^{-1} is a map. Take a map F such that F = G^{-1}. domain(F) = ran (G). 
    ran(F) = /PP A.
    Define C = {set u | u /in A /\ u /notin F(u)}.
    C /subset A. C /in ran(G^{-1}).
    There is a set y such that y - F - C.
    #Then y /in C iff y /notin G^{-1}(y).
    #y /in C iff y /notin C.
    Contradiction.
qed.



Lemma. Contradiction.

# Contradictory Axiom. So no everything can be proven.
# /PP /VV = /VV and Id is an injective function Id : /PP /VV /rightarrow /VV.
# Therefore we need to distinguish between zf-sets and proper classes.


