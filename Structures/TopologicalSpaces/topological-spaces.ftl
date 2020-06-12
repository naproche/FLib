#
# Topological spaces
# (Marcel Schütz, 2020)
#

[prove off]
[read ForTheLib/Foundations/structures.ftl]
[read ForTheLib/Foundations/types.ftl]
[read ForTheLib/Sets/set-systems.ftl]
[read ForTheLib/Foundations/axioms.ftl]
[prove on]


# 1. Topologies

# 1.1 Topologies of open sets

Signature TopTop000. TopOpen1 is an axiom.

Axiom TopTop005. Let X be a set and U be a subset of the powerset of X. (X,U) satisfies TopOpen1 iff
the empty set and X lie in U.


Signature TopTop010. TopOpen2 is an axiom.

Axiom TopTop015. Let X be a set and U be a subset of the powerset of X. (X,U) satisfies TopOpen2 iff
U is closed under finite intersections.


Signature TopTop020. TopOpen3 is an axiom.

Axiom TopTop025. Let X be a set and U be a subset of the powerset of X. (X,U) satisfies TopOpen3 iff
U is closed under arbitrary unions.


Definition TopTop030. Let X be an object. A topology of open sets on X is a subset U of the powerset
of X such that (X,U) satisfies TopOpen1 and TopOpen2 and TopOpen3.

Let a topology on X stand for a topology of open sets on X.


# 1.2 Topologies of closed sets

Signature TopTop035. TopClosed1 is an axiom.

Axiom TopTop040. Let X be a set and U be a subset of the powerset of X. (X,U) satisfies TopClosed1
iff the empty set and X lie in U.


Signature TopTop045. TopClosed2 is an axiom.

Axiom TopTop050. Let X be a set and U be a subset of the powerset of X. (X,U) satisfies TopClosed2
iff U is closed under finite unions.


Signature TopTop055. TopClosed3 is an axiom.

Axiom TopTop060. Let X be a set and U be a subset of the powerset of X. (X,U) satisfies TopClosed3
iff U is closed under arbitrary intersections.


Definition TopTop065. Let X be an object. A topology of closed sets on X is a subset U of the
powerset of X such that (X,U) satisfies TopClosed1 and TopClosed2 and TopClosed3.


# 1.3 Examples

Definition TopTop070. Let X be a set. The discrete topology on X is a class U such that U =
{A | A is a subset of X}.

Definition TopTop075. Let X be a set. The indiscrete topology on X is a class U such that U =
{\emptyset,X}.


Proposition TopTop080. Let X be a set. The discrete topology on X is a topology on X.

Proof.
  Take a class D that is the discrete topology on X. Then D = {A | A is a subset of X}. D is the
  powerset of X (by SetSet080). Hence D is a subset of the powerset of X.

  The empty set and X belong to D. Thus (X,D) satisfies TopOpen1 (by TopTop005).

  For all A,B \in D we have A \cap B \in D.
  proof.
    Let A,B \in D. Then A,B are subsets of X. Hence A \cap B is a set. Every element of A \cap B
    lies in X. Hence A \cap B is a subset of X.
  end.

  Thus D is closed under finite intersections (by SetSs010). Therefore (X,D) satisfies TopOpen2 (by
  TopTop015).

  For all nonempty subsets U of D we have \bigcup U \in D.
  proof.
    Let U be a nonempty subset of D. Every element of U is a subset of X. Hence \bigcup U is a set.
    Every element of \bigcup U lies in X. Hence \bigcup U is a subset of X.
  end.

  Hence D is closed under arbitrary unions (by SetSs040). Thus (X,D) satisfies TopOpen3 (by
  TopTop025).
qed.


Proposition TopTop085. Let X be a set. The discrete topology on X is a topology of closed sets on X.

Proof.
  Take a class D that is the discrete topology on X. Then D = {A | A is a subset of X}. D is the
  powerset of X (by SetSet080). Hence D is a subset of the powerset of X.

  The empty set and X belong to D. Thus (X,D) satisfies TopClosed1 (by TopTop040).

  For all A,B \in D we have A \cup B \in D.
  proof.
    Let A,B \in D. Then A,B are subsets of X. Hence A \cup B is a set. Every element of A \cup B
    lies in X. Thus A \cup B is a subset of X.
  end.

  Hence D is closed under finite unions (by SetSs020). Thus (X,D) satisfies TopClosed2 (by
  TopTop050).

  For all nonempty subsets U of D we have \bigcap U \in D.
  proof.
    Let U be a nonempty subset of D. Then every element of U is a subset of X. Hence \bigcap U is a
    set. Every element of \bigcap U lies in X. Thus \bigcap U is a subset of X (by SetSet082).
  end.

  Hence D is closed under arbitrary intersections (by SetSs035). Thus (X,D) satisfies TopClosed3 (by
  TopTop060).
qed.


Proposition TopTop090. Let X be a set. The indiscrete topology on X is a topology on X.

Proof.
  Take a class I that is the indiscrete topology on X. I = {\emptyset,X}. Every element of I is a
  subset of X. Hence I is a subset of the powerset of X. I is a system of sets.

  The empty set and X belong to I. Hence (X,I) satisfies TopOpen1 (by TopTop005).

  For all A,B \in I we have A \cap B \in I.
  proof.
    Let A,B \in I.

    Case A,B = \emptyset. Obvious.

    Case A,B = X. Obvious.

    Case A = \emptyset and B = X. Obvious.

    Case A = X and B = \emptyset. Obvious.
  end.

  Hence I is closed under finite intersections (by SetSs010). Thus (X,I) satisfies TopOpen2 (by
  TopTop015).

  For all nonempty subsets U of I we have \bigcup U \in I.
  proof.
    Let U be a nonempty subset of I.

    Case U = {\emptyset}.
      \bigcup U = \emptyset.
    end.

    Case U = {X}.
      \bigcup U = X.
    end.

    Case U = {\emptyset,X}.
      U = `{\emptyset,X}`. Therefore \bigcup U = \emptyset \cup X (by FoundCl090). Indeed \emptyset
      and X are classes.
    end.
  end.

  Hence I is closed under arbitrary unions (by SetSs040). Thus (X,I) satisfies TopOpen3 (by
  TopTop025).
qed.


Proposition TopTop095. Let X be a set. The indiscrete topology on X is a topology of closed sets on
X.

Proof. [prove off] qed.


# 2. Topological spaces

Signature TopTop100. A topological space is a small structure.

Definition TopTop105. Let X be a topological space. The topology of X is a class T such that T =
{A | A is an open subset of X}.

Axiom TopTop115. Let X be a topological space. The topology of X is a topology on X.


# 3. Open and closed sets

# 3.1 Open sets

Proposition TopTop120. Let X be a topological space and U be a set. Assume that every element of U
is an open subset of X. Then \bigcup U is open.

Proof. [prove off] qed.


Proposition TopTop125. Let X be a topological space and A,B be open subsets of X. Then A \cup B is
open.

Proof. [prove off] qed.


Proposition TopTop130. Let X be a topological space and U be a nonempty finite set. Assume that
every element of U is an open subset of X. Then \bigcap U is open.

Proof. [prove off] qed.


Proposition TopTop135. Let X be a topological space and A,B be open subsets of X. Then A \cap B is
open.

Proof. [prove off] qed.


# 3.2 Closed sets

Axiom TopTop140. Let X be a topological space and A be a subset of X. A is closed iff X \setminus A
is open.


Proposition TopTop145. Let X be a topological space and A be a subset of X. A is open iff
X \setminus A is closed.

Proof. [prove off] qed.


Proposition TopTop150. Let X be a topological space and U be a class. Assume that U = {A | A is a
closed subset of X}. U is a topology of closed sets on X.

Proof. [prove off] qed.


Corollary TopTop155. Let X be a topological space and U be a nonempty set. Assume that every element
of U is a closed subset of X. Then \bigcap U is closed.

Proof. [prove off] qed.


Corollary TopTop160. Let X be a topological space and A,B be closed subsets of X. Then A \cap B is
closed.

Proof. [prove off] qed.


Corollary TopTop165. Let X be a topological space and U be a finite set. Assume that every element
of U is a closed subset of X. Then \bigcup U is open.

Proof. [prove off] qed.


Corollary TopTop170. Let X be a topological space and A,B be closed subsets of X. Then A \cup B is
closed.

Proof. [prove off] qed.


# 3. TOP

Signature TopTop175. TOP is a type.

Axiom TopTop180. TOP = {X | X is a topological space}.

# Be aware that the class term notation does not imply that TOP is a class!


# 3.1 Instances of TOP

# 3.1.1 TOP_{open}

Signature TopTop190. TOP_{open} is a function of TOP.

Axiom TopTop195. Let T be a topological space. Let X be the domain of T and U be a class. Assume
that U = {T^{-1}[A] | A is an open subset of T}. TOP_{open}(T) = (X,U).


Proposition TopTop200. Let T be a topological space and U be a class. Assume that U = {T^{-1}[A] | A
is an open subset of T}. Then U is a topology on the domain of T.

Proof. [prove off] qed.


Proposition TopTop205. TOP_{open} is an instantiation of TOP.

Proof. [prove off] qed.


Axiom TopTop210. Let X be a set and U be a topology on X. Then there is a topological space T such
that TOP_{open}(T) = (X,U).

Corollary TopTop215. Let X be a set and U be a topology on X. Then (X,U) is an instance of TOP.

Proof. [prove off] qed.


# 3.1.2 TOP_{closed}

Signature TopTop220. TOP_{closed} is a function of TOP.

Axiom TopTop225. Let T be a topological space. Let X be the domain of T and U be a class. Assume
that U = {T^{-1}[A] | A is a closed subset of T}. TOP_{closed}(T) = (X,U).


Proposition TopTop230. TOP_{closed} is an instantiation of TOP.

Proof. [prove off] qed.


Proposition TopTop233. TOP_{closed} and TOP_{open} are equivalent.

Proof. [prove off] qed.


Proposition TopTop235. Let X be a set and U be a topology of closed sets on X. Then there is a
topological space T such that TOP_{closed}(T) = (X,U).

Proof. [prove off] qed.


Corollary TopTop240. Let X be a set and U be a topology of closed sets on X. Then (X,U) is an
instance of TOP.

Proof. [prove off] qed.


# 3.2 Equality of topological spaces

Proposition TopTop250. Let X,Y be topological spaces. Let T be an instantiation of TOP. If
T(X) = T(Y) then X = Y.

Proof. [prove off] qed.
