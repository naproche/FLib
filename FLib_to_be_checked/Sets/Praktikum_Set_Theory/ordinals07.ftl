# Proving Zermelo's Wellordering Theorem in Naproche Set Theory

# We present a standard proof of the Wellordering Theorem, using
# ordinals, recursion and Choice. This requires
# to develop some basic theory. We follow parts of the Set Theory
# course 2018/19 at the University of Bonn.

# Some mathematical principles like Choice, set formation and function
# formation are already implemented in Naproche. Other set theoretical
# axioms have to be required explicitly. There are some marked differences
# with ZF set theory: Naproche has some abstraction term mechanisms that
# allow abstractions with arbitrary formulas. This transcends ZF in the
# direction of Kelley-Morse set theory (KM). KM provides good foundations
# for mathematics. ZF is more popular, perhaps for historic reasons, or
# since it is more amenable to the metamathematical analyses of
# axiomatic set theory.

# The abstraction term and function mechanism of the current version 
# of Naproche are directed towards standard mathematical fields and 
# so abstraction terms are naively identified with "sets" instead of
# "classes". To make Naproche work for unrestricted set theory, we
# use Naproche's sets as KM classes. 

# We mention the numberings of the Set Theory scriptum when possible.
# There has been a difficulty with satisfying the existence task connected
# with the Choice operator "choose" in the proof of the Wellordering Theorem.
# We have therefore deactivated that task in the Naproche source file
# ProofTask.hs:82

# Later, the file will be rewritten as a LaTeX file which, using a LaTeX -> ftl filter
# will check in Naproche.


# Preliminaries

# Notation.
Let a \neq b stand for a != b. 

# Preliminaries on Classes and Sets

# "class" is translated into the inbuilt "set" notion of Naproche.
Let A, B, C, D stand for classes.
Let x \in y stand for x is an element of y. 
Let x \notin y stand for not x \in y. 

Definition 7a. A subclass of B is a class A such that every element of A 
is an element of B. Let x \subseteq y stand for x is a subclass of y.

# "Object" stands for mathematical object. Objects can be
# collected together in classes.
[synonym object/objects]
Signature. An object is a notion. Let o stand for objects.

# Ontological axiom: 
Axiom. Any element of any class is an object. # classes consist of objects

# "Sets", which are the main objects of study in set theory, are
# those classes that are mathematical objects.
[synonym set/sets]
Definition. A set is a class that is an object. Let a,b,c,x,y,z stand for sets.

# The axiom schema of foundation is formalized by embedding the element relation
# into the universal induction relation -<- for which Naproche provides an
# induction scheme.
Axiom Foundation. If o \in x then o -<- x.

Theorem 33. x \notin x.
Proof by induction on x.
qed.


# The following definition includes the set existence axiom.
Definition 4a. The empty set is the set that has no elements.
Let \emptyset stand for the empty set.

# We use a new unordered pair instead of the version available in Naproche.
# Perhaps one could as well use Naproche's pair.
Definition 4c. \{a,b\} = {u | u = a or u = b}.

# The pairing axiom.
Axiom Pairing. \{a,b\} is a set.

Definition 7j. \{a\} = {u | u = a}.

Lemma. \{a\} is a set.

Definition 7e. \bigcup(x) = {u | there is a such that u \in a \in x}.

# The union axiom.
Axiom Union. \bigcup(x) is a set.

Definition 7b. A \cup B = {u | u \in A or u \in B}.

Lemma. a \cup b is a set.
Proof. a \cup b = \bigcup(\{a,b\}).
qed.

Definition 7c. A \cap B = {u | u \in A and u \in B}.

# The separation schema.
Axiom Separation. x \cap A is a set.

Definition 7d. A \setminus B = {u | u \in A and u \notin B}.

Lemma. a \setminus B is a set.
Proof. Define C = { u | u \in a and u \notin B}.
a \setminus B = a \cap C.
qed.

Definition 30. Succ(x) = x \cup \{x\}.

Lemma. Succ(x) is a set.


# Class-sized and set-sized functions

# We use the functions built into Naproche.
Let F,G,f,g stand for functions.

Definition 15e. Let F be a function.
F " A = {F[u]|u \in A and u \in Dom(F)}.

Definition 15b. range(F) = F " Dom(F).

# The replacement schema.
Axiom Replacement. F"x is a set.

Definition 19a.
A function from A to B is a function F such that
Dom(F) = A and range(F) \subseteq B.
Let F : A \rightarrow B stand for F is a function from
A to B.

Definition 19c.
A surjective function from A to B is a 
function F such that Dom(F) = A and
range(F) = B.

Definition 19d. 
An injective function from A to B is a function F
such that F : A \rightarrow B and
forall u,v \in A (u \neq v => F[u] \neq F[v]).

Definition 19e.
A bijective function from A to B is a function F
such that F is a surjective function from A to B and
F is an injective function from A to B.
Let F : A \leftrightarrow B stand for F is a 
bijective function from A to B.

Definition. Let F be a function. Let v be an object.
F * v = {u | u \in Dom(F) and F[u] = v}.

Theorem. Let F be an injective function from A to x.
Then A is a set.
Proof. range(F) \subseteq x.
range(F) is a set. Indeed range(F) = x \cap range(F).
Define G[v] = choose u \in F*v in u for v in range(F).
range(G) = A.
qed.

# 3 Ordinal Numbers

Let 0 stand for \emptyset.
Definition. 1 = {0}.
Definition. 2 = {0,1}.
Definition. 3 = {0,1,2}.

Definition 37a. A is transitive iff 
every element of A is a subclass of A.
Let Trans(x) stand for x is transitive.

[synonym ordinal/ordinals]
Definition 37b. An ordinal is a set x such that
x is transitive and every element of x is transitive.
Let Ord(x) stand for x is an ordinal.
Let alpha, beta, gamma, lambda denote ordinals.

Theorem 38a. 0 is an ordinal.

Theorem 38b. Succ(alpha) is an ordinal.

Theorem 39. Every element of alpha is an ordinal.

Theorem 40a. (alpha \in beta and beta \in gamma) => alpha \in gamma.

Theorem 40b. For all alpha alpha \notin alpha.

Definition 41. alpha < beta iff alpha \in beta.

# The following property can be proved by a double induction.
# For the proof, alpha and beta have to be universally quantified.
Axiom 40c. alpha < beta or alpha = beta or beta < alpha.

Theorem 44. If alpha < beta then alpha -<- beta. 

Theorem 42a. alpha < Succ(alpha).

Theorem 42b. If beta < Succ(alpha) then beta = alpha or beta < alpha.

Definition 43a. A successor ordinal is an ordinal alpha such that
exists beta alpha = Succ(beta).

Definition 43b. A limit ordinal is an ordinal alpha such that
alpha \neq 0 and alpha is not a successor ordinal.

Definition 37c. Ord = {u | u is an ordinal}.

# This is the Burali-Forti paradox.
Theorem Exercise15. Ord is not a set.
Proof.
Assume the contrary.
Ord is transitive and every element of Ord is transitive.
Ord \in Ord.
qed.

# The Zermelo Well-Ordering Theorem.
Theorem 72c. For every set x there exists ordinal alpha, function f 
such that f : alpha \leftrightarrow x.
Proof. Let x be a set.
Define F[alpha] = case x \setminus (F " alpha) = \emptyset -> x,
                  case (x \setminus (F " alpha)) \neq \emptyset -> 
                            choose an element v of x \setminus (F " alpha) in v
for alpha in Ord. 
# due to a difficulty with the verification of the "choose" existence task
# we have temporarily removed this obligation from the code
(1) There exists alpha such that F[alpha] = x.
  Proof. Assume the contrary.
  (1a) For all alpha \in Ord F[alpha] \in x \setminus (F " alpha).
  (1b) F : Ord \rightarrow x.
  (1c) F is an injective function from Ord to x.
    Proof. Let beta,gamma \in Ord. Assume beta \neq gamma.
    Then F[beta] \neq F[gamma].
      Proof. Case beta < gamma. F[gamma] \in x \setminus (F " gamma).  F[beta] \neq F[gamma]. end.
      Case gamma < beta. F[beta] \in x \setminus (F " beta). F[beta] \neq F[gamma]. end.
      end.
    qed.
  qed.
Take an ordinal alpha such that F[alpha] = x and for all beta (beta < alpha => F[beta] \neq x).
Proof. Assume the contrary.
Let us show that for all ordinals alpha F[alpha] \neq x.
Proof by induction. qed. qed.

Define f[beta] = F[beta] for beta in alpha.
(2a) For all beta \in alpha f[beta] \in x \setminus (F " beta).
(2b) f : alpha \rightarrow x.
(2c) f is an injective function from alpha to x.
  Proof. Let beta,gamma \in alpha. Assume beta \neq gamma.
  Then f[beta] \neq f[gamma].
    Proof. Case beta < gamma. f[gamma] \in x \setminus (F " gamma).  f[beta] \neq f[gamma]. end.
    Case gamma < beta. F[beta] \in x \setminus (F " beta). f[beta] \neq f[gamma]. end.
    end. qed.
(2d) f is a surjective function from alpha to x.
Proof. Assume the contrary.
range(f) \neq x.
x \setminus (F " alpha) \neq \emptyset.
F[alpha] \in x.
x \in x.
qed.
qed.

# Similarly one could prove Zorn's Lemma and other Choice principles.
