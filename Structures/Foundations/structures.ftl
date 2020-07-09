#
# Mathematical structures
# (Marcel Schütz, 2020)
#

#[prove off][check off]
[read FLib/Structures/Sets/sets.ftl]
#[prove on][check on]


# 1. Axioms for structures

Signature FoundStr000. A structure is an injective function that is a class.

Axiom FoundStr002. Let X be a structure. The domain of X is a class.

Axiom FoundStr005. Let X be a structure. range(X) = X.

Axiom FoundStr007. Every element of any structure is an element.


Proposition FoundStr009. Let X be a structure and A be a subset of the domain of X. Then X[A] is a
subset of X.

Proof.
  Every value of X is an element. Indeed every value of X lies in X. Hence X[A] is a set (by
  SetSet060). Indeed X is a function. X[A] = {X(a) | a \in A} (by FoundMap188). Indeed X is a map
  and A is a subclass of dom(X). Hence every element of X[A] lies in X.
qed.


Proposition FoundStr010. Let X be a structure. X is a bijection between the domain of X and X.


Proposition FoundStr015. Let X be a structure. X^{-1} is a bijection between X and the domain of X.

Proof.
  X is a bijection between dom(X) and X. Hence X is a bijective map. Thus X is invertible (by
  FoundMap170). Indeed X is bijective. Hence X^{-1} is bijective (by FoundMap175).
qed.


Proposition FoundStr020. Let X be a structure and x be an element of the domain of X. Then X(x) is
an element of X.

Proof.
  X(x) lies in the range of X.
qed.


Proposition FoundStr025. Let X be a structure and y be an element of X. Then there is an element x
of the domain of X such that X(x) = y.

Proof.
  X is a surjective map. y is an element of the codomain of X. Hence we have the thesis (by
  FoundMap100).
qed.


Proposition FoundStr030. Let X be a structure and x,y be elements of the domain of X. x = y iff
X(x) = X(y).

Proof.
  X is an injective map. Hence the thesis (by FoundMap092).
qed.


Proposition FoundStr031. Let X be a structure and A be a class. X[A] = {X(a) | a \in A \cap dom(X)}.

Proof.
  X is a map. Hence we have the thesis (by FoundMap180).
qed.


Proposition FoundStr032. Let X be a structure and x \in X. Then x = X(X^{-1}(x)).

Proof.
  X is a bijection between dom(X) and X. Hence the thesis (by FoundMap179c).
qed.


Proposition FoundStr033. Let X be a structure and x \in dom(X). Then x = X^{-1}(X(x)).

Proof.
  X is a bijection between dom(X) and X. Hence the thesis (by FoundMap179d).
qed.


Proposition FoundStr034. Let X be a structure and x be an entity such that X(x) \in X. Then
X^{-1}(X(x)) \in dom(X).

Proof.
  X(x) lies in the domain of X^{-1}. X^{-1} is a bijection between X and dom(X). Hence dom(X) is the
  codomain of X^{-1}.
qed.


# 2. Small and large structures

Definition FoundStr035. A small structure is a structure that is a set.

Definition FoundStr036. A large structure is a structure that is a proper class.


Proposition FoundStr037. Let X be a small structure. Then the domain of X is a set.

Proof. [prove off] qed.


Proposition FoundStr038. Let X be a small structure and A be a subset of X. Then X^{-1}[A] is a
subset of the domain of X.

Proof. [prove off] qed.


# 3. Substructures

Definition FoundStr040. Let X be a structure. A substructure of X is a structure Y such that the
domain of Y is a subclass of the domain of X.

Definition FoundStr045. Let X be a structure and Y be a substructure of X. The inclusion of Y into X
is the map i from Y to X such that i(y) = X(Y^{-1}(y)) for all y \in Y.


Proposition FoundStr050. Let X be a structure and Y be a substructure of X. The inclusion of Y into
X is an injective map.

Proof. [prove off] qed.


Proposition FoundStr055. Every structure X is a substructure of X.

Proof. [prove off] qed.


Proposition FoundStr060. Let X,Y be structures such that dom(X) = dom(Y). Then Y is a substructure
of X.

Proof. [prove off] qed.


# 3.1 Abuse of notation

Axiom FoundStr070. Let X be a structure and Y be a substructure of X. Let i be the inclusion of Y
into X. Let f be a map such that dom(f) = X. Then f(y) = f(i(y)) for all y \in Y.


# 4. Constructing new structures

Axiom FoundStr100. Let X,Y be structures. Then X \times Y is a structure such that dom(X \times Y) =
dom(X) \times dom(Y).

Proposition FoundStr105. Let X be a structure and Y be a substructure of X. Then Y \times Y is a
substructure of X \times X.

Proof. [prove off] qed.
