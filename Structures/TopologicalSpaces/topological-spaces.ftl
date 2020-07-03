#
# Topological spaces
# (Marcel Schütz, 2020)
#

#[prove off][check off]
[read FLib/Structures/Sets/topologies.ftl]
[read FLib/Structures/Foundations/structures.ftl]
#[prove on][check on]


# 1. Topological spaces

Signature TopTop000. TOP is a class.

Definition TopTop005. A topological space is an element of TOP.


Axiom TopTop010. Every topological spaces is a structure.

Lemma TopTop015. Every topological space is a map.

Lemma TopTop020. Every topological space is a class.


# 2. Constructing topological spaces

Axiom TopTop025. TOP_{1} is a class such that TOP_{1} = {(X,U) | X is a set and U is a topology on X}.

Signature TopTop030. Top_{1} is a bijection between TOP_{1} and TOP.

Axiom TopTop052. Let X be a set and U be a topology on X. (X,U)_{TOP} = Top_{1}(X,U).


Axiom TopTop035. Let X be a set and U be a topology on X. Then dom((X,U)_{TOP}) = X.


Lemma TopTop040. Let X be a set and U be a topology on X. Then (X,U)_{TOP} is a topological space.

Proof.  
  (X,U)_{TOP} = Top_{1}(X,U). (X,U) lies in the domain of Top_{1} (by TopTop025). Indeed
  dom(Top_{1}) = TOP_{1}. The codomain of Top_{1} is TOP. Hence Top_{1}(X,U) lies in TOP. Thus
  Top_{1}(X,U) lies in TOP. Every element of TOP is a topological spaces. Then we have the thesis.
qed.


Lemma TopTop045. Let X be a set and U be a topology on X. Let x be an element of X. Then
(X,U)_{TOP}(x) is an element of (X,U)_{TOP}.

Proof.
  (X,U)_{TOP} = Top_{1}(X,U). Top_{1}(X,U) is a topological space such that X is the domain of
  Top_{1}(X,U). Hence x lies in the domain of Top_{1}(X,U). Top_{1}(X,U) is a structure. Then we
  have the thesis (by FoundStr020).
qed.


Lemma TopTop050. Every topological space is a set.

Proof.
  Let T be a topological space. Then T lies in the codomain of Top_{1}. Top_{1} is a surjective map.
  Hence we can take an element S of TOP_{1} such that Top_{1}(S) = T (by FoundMap100). Indeed
  dom(Top_{1}) = TOP_{1}. Take a set X and a topology U on X such that S = (X,U) (by TopTop025).
qed.


# 3. Open and closed sets

Axiom TopTop055. Let X be a set and U be a topology on X. Then for all subsets B of Top_{1}(X,U) we
have B = Top_{1}(X,U)[A] for some A \in U iff B is open.


Proposition TopTop057. Let X be a set and U be a topology on X. Let A \in U. Then Top_{1}(X,U)[A] is
an open subset of Top_{1}(X,U).

Proof.
  A is a subset of X. Take a topological space T such that T = Top_{1}(X,U). T[A] is a subset of T.
  Indeed T is a structure. Hence T[A] is open (by TopTop055).
qed.


Proposition TopTop058. Let X be a set and U be a topology on X. Let A be an open subset of
Top_{1}(X,U). Then Top_{1}(X,U)^{-1}[A] \in U.

Proof.
  Take a topological space T such that T = Top_{1}(X,U). A is open. Hence we can take a B \in U such
  that A = T[B] (by TopTop055). T^{-1}[T[B]] = B (by FoundMap200). Indeed T is an injective map from
  X to T and B is a subclass of X.
qed.


Lemma TopTop060. Let T be a topological space. Let V be a class such that V = {A | A is an open
subset of T}. Then V is a topology on T.

Proof.
  T lies in the codomain of Top_{1}. Top_{1} is a surjective map. Hence we can take an element S of
  TOP_{1} such that Top_{1}(S) = T (by FoundMap100). Indeed dom(Top_{1}) = TOP_{1}. Take a set X and
  a topology U on X such that S = (X,U) (by TopTop025).

  (1) T is a bijective function of X.

  V = {T[A] | A \in U}. 
  proof.
    Let B be an entity. T = Top_{1}(X,U).

    If B \in V then B = T[A] for some A \in U.
    proof.
      Assume that B \in V. Then B is an open subset of T. Thus B = T[A] for some A \in U (by
      TopTop055).
    end.

    If B = T[A] for some A \in U then B \in V.
    proof.
      Let A \in U. Assume that B = T[A].

      B is a subset of T.
      proof.
        U is a subset of the powerset of X. Hence every element of U is a subset of X. Thus A is a
        subset of X. T[A] = {T(x) | x \in A \cap dom(T)} (by FoundMap180). Indeed T is a map. Hence
        T[A] = {T(x) | x \in A}. Indeed A \cap dom(T) = A. T = {T(x) | x \in dom(T)}. Indeed T is a
        structure.

        Every element of T[A] lies in T.
        proof.
          Let y \in T[A]. Take x \in A such that y = T(x). Then x \in dom(T). Hence y \in T.
        end.

        Thus T[A] is a set. Indeed A is a set. 
      end.

      Then B is open (by TopTop055).
    end.
  end.

  Then V is a topology on T[X] (by SetTop065).
qed.


Axiom TopTop065. Let T be a topological space and A be a subset of T. A is closed iff T \setminus A
is open.


Proposition TopTop070. Let T be a topological space and A be a subset of T. A is open iff
T \setminus A is closed.

Proof.
  If A is open then T \setminus A is closed.
  proof.
    Assume that A is open. A = T \setminus (T \setminus A). Hence the thesis (by TopTop065). Indeed
    T \setminus A is a subset of T.
  end.

  If T \setminus A is closed then A is open.
  proof.
    Assume that T \setminus A is closed. Then T \setminus (T \setminus A) is open (by TopTop065).
    Indeed T \setminus A is a subset of T. T \setminus (T \setminus A) = A.
  end.
qed.


Proposition TopTop075. Let T be a topological space. Let V be a class such that V = {A | A is a
closed subset of T}. Then V is a topology of closed sets on T.

Proof.
  Define U = {A | A is an open subset of T}. U is a topology on T (by TopTop060).

  V = {T \setminus A | A \in U}.
  proof.
    Let B be an entity.

    If B \in V then B = T \setminus A for some A \in U.
    proof.
      Assume B \in V. Then B is a closed subset of T. Hence T \setminus B is an open subset of T.
      Thus T \setminus B \in U. B = T \setminus (T \setminus B).
    end.

    If B = T \setminus A for some A \in U then B \in V.
    proof.
      Let A \in U. Assume that B = T \setminus A. A is an open subset of T. Hence B is closed (by
      TopTop070).
    end.
  end.

  Hence the thesis (by SetTop140). Indeed T is a set.
qed.


# 3.1 Basic properties of open sets

Proposition TopTop080. Every topological space is an open set.

Proof.
  Let X be a topological space. Define V = {A | A is an open subset of X}. V is a topology on X (by
  TopTop060). Hence X lies in V (by SetTop040). Indeed X is a set.
qed.


Proposition TopTop085. The empty set is open subset of every topological space.

Proof.
  Let X be a topological space. Define V = {A | A is an open subset of X}. V is a topology on X (by
  TopTop060). Hence the empty set lies in V (by SetTop035). Indeed X is a set.
qed.


Proposition TopTop090. Let X be a topological space and U be a set. Assume that every element of U
is an open subset of X. Then \bigcup U is open.

Proof.
  Define V = {A | A is an open subset of X}. V is a topology on X (by TopTop060). U is a subset of
  V. Indeed every element of U lies in V. Hence \bigcup U is an element of V (by SetTop055). Indeed
  X is a set.
qed.


Proposition TopTop095. Let X be a topological space and A,B be open subsets of X. Then A \cup B is
open.

Proof.
  Define V = {C | C is an open subset of X}. V is a topology on X (by TopTop060). A,B are elements
  of V. Thus A \cup B lies in V (by SetTop060). Indeed X is a set.
qed.


Proposition TopTop100. Let X be a topological space and U be a nonempty finite set. Assume that
every element of U is an open subset of X. Then \bigcap U is open.

Proof.
  Define V = {A | A is an open subset of X}. V is a topology on X (by TopTop060). U is a finite
  nonempty subset of V. Indeed every element of U lies in V. Hence \bigcap U is an element of V (by
  SetTop045). Indeed X is a set.
qed.


Proposition TopTop105. Let X be a topological space and A,B be open subsets of X. Then A \cap B is
open.

Proof.
  Define V = {C | C is an open subset of X}. V is a topology on X (by TopTop060). A,B are elements
  of V. Thus A \cap B lies in V (by SetTop050). Indeed X is a set.
qed.


# 3.2 Basic properties of closed sets

Proposition TopTop110. Every topological space is closed.

Proof.
  Let X be a topological space. Define V = {A | A is a closed subset of X}. V is a topology of
  closed sets on X (by TopTop075). Hence X lies in V (by SetTop110). Indeed X is a set.
qed.


Proposition TopTop115. The empty set is a closed subset of every topological space.

Proof.
  Let X be a topological space. Define V = {A | A is a closed subset of X}. V is a topology of
  closed sets on X (by TopTop075). Hence the empty set lies in V (by SetTop105). Indeed X is a set.
qed.


Proposition TopTop125. Let X be a topological space and U be a nonempty set. Assume that every
element of U is a closed subset of X. Then \bigcap U is closed.

Proof.
  Define V = {A | A is a closed subset of X}. V is a topology of closed sets on X (by TopTop075).
  U is a nonempty subset of V. Indeed every element of U lies in V. Hence \bigcap U lies in V (by
  SetTop125). Indeed X is a set.
qed.


Proposition TopTop130. Let X be a topological space and A,B be closed subsets of X. Then A \cap B is
closed.

Proof.
  Define V = {C | C is a closed subset of X}. V is a topology of closed sets on X (by TopTop075).
  A,B are elements of V. Hence A \cap B lies in V (by SetTop130). Indeed X is a set.
qed.


Proposition TopTop135. Let X be a topological space and U be a finite set. Assume that every element
of U is a closed subset of X. Then \bigcup U is closed.

Proof.
  Define V = {A | A is a closed subset of X}. V is a topology of closed sets on X (by TopTop075).
  U is a finite subset of V. Indeed every element of U lies in V. Hence \bigcup U lies in V (by
  SetTop115). Indeed X is a set.
qed.


Proposition TopTop140. Let X be a topological space and A,B be closed subsets of X. Then A \cup B is
closed.

Proof.
  Define V = {C | C is a closed subset of X}. V is a topology of closed sets on X (by TopTop075).
  A,B are elements of V. Hence A \cup B lies in V (by SetTop120). Indeed X is a set.
qed.


# 4. Another way of constructing topological spaces

Axiom TopTop145. TOP_{2} is a class such that TOP_{2} = {(X,U) | X is a set and U is a topology of
closed sets on X}.


Signature TopTop150. Top_{2} is a function of Top_{2}.

Axiom TopTop135. Let X be a set and U be a topology of closed sets on X. Let V be a class such that
V = {X \setminus A | A \in U}. Then Top_{2}(X,U) = Top_{1}(X,V).


Proposition TopTop155. Top_{2} is a bijection between Top_{2} and TOP.

Proof. [prove off] qed.


Proposition TopTop160. Let X be a set and U be a topology of closed sets on X. Then
dom(Top_{2}(X,U)) = X.

Proof. [prove off] qed.


Proposition TopTop165. Let X be a set and U be a topology on X. Then Top_{2}(X,U) is a topological
space.

Proof. [prove off] qed.


Proposition TopTop170. Let X be a set and U be a topology on X. Let x be an element of X. Then
Top_{2}(X,U)(x) is an element of Top_{2}(X,U).

Proof. [prove off] qed.


Proposition TopTop175. Let X be a set and U be a topology of closed sets on X. Then for all subsets
B of Top_{2}(X,U) we have B = Top_{2}(X,U)[A] for some A \in U iff B is closed.

Proof. [prove off] qed.


# 5. Neighbourhoods

Axiom TopTop200. Let X be a topological space and x \in X. Let U be an entity. U is a neighbourhood
of x iff U is a subset of X such that there is an open subset of U that contains x.


Proposition TopTop205. Let X be a topological space and x \in X. Every neighbourhood of x contains
x.

Proof.
  Let U be a neighbourhood of x. Take a subset A of U that contains x (by TopTop200).
qed.


Proposition TopTop210. Let X be a topological space and U be a subset of X. U is open iff U is a
neighbourhood of every element of U.

Proof.
  If U is open then U is a neighbourhood of every element of U.
  proof.
    Assume that U is open. Let x be an element of U. U is an open subset of U that contains x. Hence
    U is a neighbourhood of x (by TopTop200). Indeed x is an element of X.
  end.

  If U is a neighbourhood of every element of U then U is open.
  proof.
    Assume that U is a neighbourhood of every element of U. For all x \in U there is an open subset
    of U that contains x (by TopTop200). Indeed every element of U lies in X.

    Define f(x) = choose an open subset A of U that contains x in A for x in U.

    f[U] is a set. Hence \bigcup f[U] and U are sets. f[U] = {f(x) | x \in U \cap dom(f)} (by
    FoundMap180). Indeed f is a map. Hence f[U] = {f(x) | x \in U}. Thus every element of f[U] is an
    open subset of U.

    \bigcup f[U] = U.
    proof.
      Every element of \bigcup f[U] lies in U.
      proof.
        Let y \in \bigcup f[U]. Take an element A of f[U] such that y \in A. A is a subset of U.
      end.

      Every element of U lies in \bigcup f[U].
      proof.
        Let y \in U. Then y \in f(y). Hence y is an element of some element of f[U]. Indeed f(y)
        lies in f[U] (by FoundFun115).
      end.

      Hence the thesis (by SetSet083).
    end.

    Every element of f[U] is an open subset of X.
    proof.
      Let A \in f[U]. A and X are sets. Every element of A lies in X.
    end.

    Thus \bigcup f[U] is open (by TopTop090).
  end.
qed.
