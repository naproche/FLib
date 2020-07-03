#
# Topologies
# (Marcel Schütz, 2020)
#

#[prove off][check off]
[read FLib/Structures/Sets/set-systems.ftl]
#[prove on][check on]


# 1. Topologies

# 1.1 Topologies of open sets

Signature SetTop000. TopOpen1 is an axiom.

Axiom SetTop005. Let X be a set and U be a subset of the powerset of X. (X,U) satisfies
TopOpen1 iff the empty set and X lie in U.


Signature SetTop010. TopOpen2 is an axiom.

Axiom SetTop015. Let X be a set and U be a subset of the powerset of X. (X,U) satisfies
TopOpen2 iff U is closed under finite intersections.


Signature SetTop020. TopOpen3 is an axiom.

Axiom SetTop025. Let X be a set and U be a subset of the powerset of X. (X,U) satisfies
TopOpen3 iff U is closed under arbitrary unions.


Definition SetTop030. Let X be a set. A topology of open sets on X is a subset U of Pow(X) such
that

  (X,U) satisfies TopOpen1 and

  (X,U) satisfies TopOpen2 and

  (X,U) satisfies TopOpen3.


Let a topology on X stand for a topology of open sets on X.


Lemma SetTop033. Let X be a set and U be a topology on X. Then every element of U is a subset of X.


Lemma SetTop035. Let X be a set and U be a topology on X. Then \emptyset \in U.

Proof.
  (X,U) satisfies TopOpen1. Hence the thesis (by SetTop005). Indeed U is a subset of the powerset
  of X.
qed.


Lemma SetTop040. Let X be a set and U be a topology on X. Then X \in U.

Proof.
  (X,U) satisfies TopOpen1. Hence the thesis (by SetTop005). Indeed U is a subset of the powerset
  of X.
qed.


Lemma SetTop045. Let X be a set and U be a topology on X. Let V be a nonempty finite subset of
U. Then \bigcap V \in U.

Proof.
  (X,U) satisfies TopOpen2. Hence U is closed under finite intersections (by SetTop015). Indeed U is
  a subset of the powerset of X. 
qed.


Lemma SetTop050. Let X be a set and U be a topology on X. Let A,B \in U. Then A \cap B \in U.

Proof.
  Define V = {A,B}. Then V = `{A,B}`. V is a nonempty finite set. Moreover V is a subset of U.
  Indeed every element of V lies in U. A \cap B = \bigcap V. Hence we have the thesis (by
  SetTop045).
qed.


Lemma SetTop055. Let X be a set and U be a topology on X. Let V be a subset of U. Then
\bigcup V \in U.

Proof.
  (X,U) satisfies TopOpen3. Hence U is closed under arbitrary unions (by SetTop025). Indeed U is
  a subset of the powerset of X. 
qed.


Lemma SetTop060. Let X be a set and U be a topology on X. Let A,B \in U. Then A \cup B \in U.

Proof.
  Define V = {A,B}. Then V = `{A,B}`. V is a subset of U. Indeed every element of V lies in U.
  A \cup B = \bigcup V. Hence we have the thesis (by SetTop055).
qed.


Proposition SetTop065. Let X be a set and U be a topology on X. Let f be a bijective function of X.
Let V be a class such that V = {f[A] | A \in U}. Then V is a topology on f[X].

Proof.
  Every element of U is a subset of X.

  V is a subset of the powerset of f[X].
  proof.
    Define g(A) = f[A] for A in U. U is a set. Hence g[U] is a set.

    g[U] = V.
    proof.
      g[U] = {g(A) | A \in U \cap dom(g)} (by FoundMap180). Indeed g is a map. Hence g[U] =
      {g(A) | A \in U}. Thus g[U] = {f[A] | A \in U}. Then every element of g[U] lies in V and
      every element of V lies in g[U].
    end.

    f[X] = {f(A) | A \in X \cap dom(f)} (by FoundMap180). Indeed f is a map. (1) Hence f[X] =
    {f(x) | x \in X}.

    Every element of V is a subset of f[X].
    proof.
      Let B \in V. Take A \in U such that B = f[A]. f[A] = {f(x) | x \in A \cap dom(f)} (by
      FoundMap180). Indeed f is a map. (2) Every element of A lies in X. (3) Hence f[A] =
      {f(x) | x \in A}. Thus every element of f[A] lies in f[X] (by 1, 2, 3). A and X are sets.
      Hence f[A] and f[X] are sets. Thus f[A] is a subset of f[X] (by SetSet082).
    end.

    V and the powerset of f[X] are sets. Pow(f[X]) = {B | B is a subclass of f[X]}. Hence Pow(f[X])
    = {B | B is a subset of f[X]}. Thus every element of V lies in the powerset of f[X]. Then V is a
    subset of Pow(f[X]) (by SetSet082).
  end.

  f[X] is a set.

  \emptyset and f[X] are elements of V. Hence (f[X],V) satisfies TopOpen1 (by SetTop005).

  For all A,B \in V we have A \cap B \in V.
  proof.
    Let A,B \in V. Take C,D \in U such that A = f[C] and B = f[D]. Then A \cap B = f[C] \cap f[D] =
    f[C \cap D]. Indeed f is an injective map. C \cap D \in U.
  end.

  Hence V is closed under finite intersections. Thus (f[X],V) satisfies TopOpen2 (by SetTop015).

  V is closed under arbitrary unions.
  proof.
    Let W be a subset of V. Then for all B \in W there is an A \in U such that B = f[A]. Define
    Y = {A in U | f[A] \in W}. Then W = {f[A] | A \in Y}. Hence \bigcup W = f[\bigcup Y] (by
    FoundMap230). Indeed f is a map. Y is a subset of U. Thus \bigcup Y is an element of U.
  end.

  Hence (f[X],V) satisfies TopOpen3 (by SetTop025).
qed.


# 1.2 Topologies of closed sets

Signature SetTop070. TopClosed1 is an axiom.

Axiom SetTop075. Let X be a set and U be a subset of the powerset of X. (X,U) satisfies
TopClosed1 iff the empty set and X lie in U.


Signature SetTop080. TopClosed2 is an axiom.

Axiom SetTop085. Let X be a set and U be a subset of the powerset of X. (X,U) satisfies
TopClosed2 iff U is closed under finite unions.


Signature SetTop090. TopClosed3 is an axiom.

Axiom SetTop095. Let X be a set and U be a subset of the powerset of X. (X,U) satisfies
TopClosed3 iff U is closed under arbitrary intersections.


Definition SetTop100. Let X be a set. A topology of closed sets on X is a subset U of Pow(X)
such that

  (X,U) satisfies TopClosed1 and

  (X,U) satisfies TopClosed2 and

  (X,U) satisfies TopClosed3.


Lemma SetTop105. Let X be a set and U be a topology of closed sets on X. Then \emptyset \in U.

Proof.
  (X,U) satisfies TopClosed1. Hence the thesis (by SetTop075). Indeed U is a subset of the powerset
  of X.
qed.


Lemma SetTop110. Let X be a set and U be a topology of closed sets on X. Then X \in U.

Proof.
  (X,U) satisfies TopClosed1. Hence the thesis (by SetTop075). Indeed U is a subset of the powerset
  of X.
qed.


Lemma SetTop115. Let X be a set and U be a topology of closed sets on X. Let V be a finite
subset of U. Then \bigcup V \in U.

Proof.
  (X,U) satisfies TopClosed2. Hence U is closed under finite unions (by SetTop085). Indeed U is
  a subset of the powerset of X. 
qed.


Lemma SetTop120. Let X be a set and U be a topology of closed sets on X. Let A,B \in U. Then
A \cup B \in U.

Proof.
  Define V = {A,B}. Then V = `{A,B}`. V is a finite set. Moreover V is a subset of U. Indeed every
  element of V lies in U. A \cup B = \bigcup V. Hence we have the thesis (by SetTop115).
qed.


Lemma SetTop125. Let X be a set and U be a topology of closed sets on X. Let V be a nonempty
subset of U. Then \bigcap V \in U.

Proof.
  (X,U) satisfies TopClosed3. Hence U is closed under arbitrary intersections (by SetTop095). Indeed
  U is a subset of the powerset of X. 
qed.


Lemma SetTop130. Let X be a set and U be a topology of closed sets on X. Let A,B \in U. Then
A \cap B \in U.

Proof.
  Define V = {A,B}. Then V = `{A,B}`. V is a nonempty subset of U. Indeed every element of V lies in
  U. A \cap B = \bigcap V. Hence we have the thesis (by SetTop125).
qed.


Proposition SetTop140. Let X be a set and U be a topology of open sets on X. Let V be a class
such that V = {X \setminus A | A \in U}. Then V is a topology of closed sets on X.

Proof.
  V is a subset of the powerset of X.
  proof.
    U is a set. Define f(A) = X \setminus A for A in U. f[U] = {f(A) | A \in U \cap dom(f)} (by
    FoundMap180). Indeed f is a map. {f(A) | A \in U \cap dom(f)} = {X \setminus A| A \in U}. Thus
    f[U] = {X \setminus A | A \in U}.

    Every element of f[U] lies in V.
    proof.
      Let B \in f[U]. Take A \in U such that B = X \setminus A.
    end.

    Every element of V lies in f[U].
    proof.
      Let B \in V. Take A \in U such that B = X \setminus A.
    end.

    Hence f[U] = V. Then V is a set. Furthermore every element of V is a subclass of X. Thus every
    element of V is an element of Pow(X).
  end.

  The empty set and X belong to V. Hence (X,V) satisfies TopClosed1 (by SetTop075).

  For all A,B \in V we have A \cup B \in V.
  proof.
    Let A,B \in V. Take C,D \in U such that A = X \setminus C and B = X \setminus D. Then
    A \cup B = (X \setminus C) \cup (X \setminus D) = X \setminus (C \cap D). C \cap D lies in U.
    Hence X \setminus (C \cap D) lies in V.
  end.

  Thus V is closed under finite unions. Therefore (X,V) satisfies TopClosed2 (by SetTop085).

  V is closed under arbitrary intersections.
  proof.
    Let W be a nonempty subset of V. Every element of W belongs to V. Thus for all B \in W there is
    an A \in U such that B = X \setminus A.

    Define f(B) = choose A \in U such that B = X \setminus A in A for B in W.

    For all B \in W and all A \in U if B = X \setminus A then A = f(B).
    proof.
      Let B \in W and A \in U. Assume that B = X \setminus A. Then X \setminus A = X \setminus f(B).
    end.

    Every element of f[W] lies in U.
    proof.
      Let A \in f[W]. Then A = f(B) for some B \in W.
    end.

    f[W] = {f(B) | B \in W}.
    proof.
      f is a map. Hence f[W] = {f(B) | B \in W \cap dom(f)} (by FoundMap180).
    end.

    Then W = {X \setminus A | A \in f[W]}.
    proof.
      Let B be an entity.

      If B \in W then there is an element A of f[W] such that B = X \setminus A.
      proof.
        Assume that B \in W. Take A \in U such that B = X \setminus A. Then A = f(B).
      end.

      If there is an element A of f[W] such that B = X \setminus A then B \in W.
      proof.
        Let A be an element of f[W] such that B = X \setminus A. Take C \in W such that A = f(C).
      end.
    end.

    \bigcap W = X \setminus \bigcup f[W].
    proof.
      Case f[W] is empty. Obvious.

      Case f[W] is nonempty.
        Every element of \bigcap W lies in X \setminus \bigcup f[W].
        proof.
          Let x \in \bigcap W. Then x is an element of every element of W. Hence x \in X \setminus A
          for all A \in f[W]. x \in X and x \notin A for all A \in f[W].
        end.

        Every element of X \setminus \bigcup f[W] lies in \bigcap W.
        proof.
          Let x \in X \setminus \bigcup f[W]. Then x \in X and x \notin A for every A \in f[W].
        end.
      end.
    end.

    f[W] is a subset of U. Hence \bigcup f[W] is an element of U. Thus \bigcap W is an element of V.
  end.
qed.


Proposition SetTop145. Let X be a set and U be a topology of closed sets on X. Let V be a class
such that V = {X \setminus A | A \in U}. Then V is a topology of open sets on X.

Proof. [prove off] qed.


Proposition SetTop150. Let X be a set and U be a topology of closed sets on X. Let f be a bijective
function of X. Let V be a class such that V = {f[A] | A \in U}. Then V is a topology of closed sets
on f[X].

Proof. [prove off] qed.


# 2. Examples

# 2.1 The discrete topology

Definition SetTop160. Let X be a set. The discrete topology on X is the powerset of X.


Proposition SetTop165. Let X be a set. Then the discrete topology on X is a topology on X.

Proof.
  Take a class D that is equal to the discrete topology on X.
  # NOTE: We cannot write "Take a class D that is the discrete topology on X." since this statement
  #       can either be translated to "aClass(D) and D = theDiscreteTopologyOn(X)" or to "aClass(D)
  #       and aTopologyOn(D,X) and isDiscrete(D)".

  Then D = {A | A is a subset of X}. D is the powerset of X (by SetSet080). Hence D is a subset of
  the powerset of X.

  The empty set and X belong to D. Thus (X,D) satisfies TopOpen1 (by SetTop005).

  For all A,B \in D we have A \cap B \in D.
  proof.
    Let A,B \in D. Then A,B are subsets of X. Hence A \cap B is a set. Every element of A \cap B
    lies in X. Hence A \cap B is a subset of X.
  end.

  Thus D is closed under finite intersections (by SetSs010). Indeed D is a system of sets. Therefore
  (X,D) satisfies TopOpen2 (by SetTop015).

  For all nonempty subsets U of D we have \bigcup U \in D.
  proof.
    Let U be a nonempty subset of D. Every element of U is a subset of X. Hence \bigcup U is a set.
    Every element of \bigcup U lies in X. Hence \bigcup U is a subset of X.
  end.

  Hence D is closed under arbitrary unions (by SetSs040). Indeed D is a system of sets. Thus (X,D)
  satisfies TopOpen3 (by SetTop025).
qed.


Proposition SetTop170. Let X be a set. Then the discrete topology on X is a topology of closed sets
on X.

Proof.
  Take a class D that is equal to the discrete topology on X. Then D = {A | A is a subset of X}. D
  is the powerset of X (by SetSet080). Hence D is a subset of the powerset of X.

  The empty set and X belong to D. Thus (X,D) satisfies TopClosed1 (by SetTop075).

  For all A,B \in D we have A \cup B \in D.
  proof.
    Let A,B \in D. Then A,B are subsets of X. Hence A \cup B is a set. Every element of A \cup B
    lies in X. Thus A \cup B is a subset of X.
  end.

  Hence D is closed under finite unions (by SetSs020). Indeed D is a system of sets. Thus (X,D)
  satisfies TopClosed2 (by SetTop085).

  For all nonempty subsets U of D we have \bigcap U \in D.
 proof.
    Let U be a nonempty subset of D. Then every element of U is a subset of X. Hence \bigcap U is a
    set. Every element of \bigcap U lies in X. Thus \bigcap U is a subset of X (by SetSet082).
  end.

  Hence D is closed under arbitrary intersections (by SetSs035). Indeed D is a system of sets. Thus
  (X,D) satisfies TopClosed3 (by SetTop095).
qed.


# 2.2 The indiscrete topology

Definition SetTop175. Let X be a set. The indiscrete topology on X is a class U such that U =
{\emptyset,X}.


Proposition SetTop180. Let X be a set. The indiscrete topology on X is a topology on X.

Proof.
  Take a class I that is equal to the indiscrete topology on X. I = {\emptyset,X}. I is a set (by
  SetSet072). Indeed \emptyset,X are elements. Every element of I is a subset of X. Hence I is a
  subset of the powerset of X. Indeed every element of I lies in the powerset of X. I is a system of
  sets.

  The empty set and X belong to I. Hence (X,I) satisfies TopOpen1 (by SetTop005).

  For all A,B \in I we have A \cap B \in I.
  proof.
    Let A,B \in I.

    Case A,B = \emptyset. Obvious.

    Case A,B = X. Obvious.

    Case A = \emptyset and B = X. Obvious.

    Case A = X and B = \emptyset. Obvious.
  end.

  Hence I is closed under finite intersections (by SetSs010). Thus (X,I) satisfies TopOpen2 (by
  SetTop015).

  For all nonempty subsets U of I we have \bigcup U \in I.
  proof.
    Let U be a nonempty subset of I. Then U = {\emptyset} or U = {X} or U = {\emptyset,X}.

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
  SetTop025).
qed.


Proposition SetTop185. Let X be a set. The indiscrete topology on X is a topology of closed sets on
X.

Proof. [prove off] qed.


# 2.3 The cofinite topology

Definition SetTop190. Let X be a set. The cofinite topology on X is a class U such that U =
{A | A is a subset of X such that A = \emptyset or X \setminus A is finite}.


Proposition SetTop195. Let X be a set. Then the cofinite topology on X is a topology on X.

Proof. [prove off] qed.


# 2.4 The cocountable topology

Definition SetTop200. Let X be a set. The cocountable topology on X is a class U such that U =
{A | A is a subset of X such that A = \emptyset or X \setminus A is countable}.


Proposition SetTop205. Let X be a set. Then the cocountable topology on X is a topology on X.

Proof. [prove off] qed.


# 3. Induced topologies

# 3.1 The subspace topology

Proposition SetTop300. Let X be a set and U be a topology on X. Let A be a subset of X. Let V be a
class such that V = {A \cap B | B \in U}. Then V is a topology on A.

Proof.
  V is a subset of the powerset of A.
  proof.
    Define f(B) = A \cap B for B in U. U is a set. Hence f[U] is a set. (1) f[U] = {f(B) | B \in U}
    (by FoundMap186). Indeed f is a map. Thus f[U] = {A \cap B | B \in U} (by 1). Therefore
    f[U] = V. Indeed every element of f[U] lies in V and every element of V lies in f[U].

    Every element of V is a subset of A. Pow(A) = {B | B is a subset of A} (by SetSet080). Indeed A
    is a set and Pow(A) is a class. Hence every element of V lies in the powerset of A.
  end.

  A is a set.

  \emptyset and X are elements of U. A \cap \emptyset = \emptyset and A \cap X = A. Hence \emptyset
  and A are elements of V. Thus (A,V) satisfies TopOpen1.

  For all B,C \in V we have B \cap C \in V.
  proof.
    Let B,C \in V. Take D,E \in U such that B = A \cap D and C = A \cap E. Then B \cap C =
    (A \cap D) \cap (A \cap E) = A \cap (D \cap E). D \cap E lies in U (by SetTop050). 
  end.

  Thus V is closed under finite intersections. Then (A,V) satisfies TopOpen2.

  V is closed under arbitrary unions.
  proof.
    Let W be a subset of V. Define Y = {C in U | A \cap C \in W}. For all B \in W there is a C \in U
    such that B = A \cap C. Hence W = {A \cap C | C \in Y}. Thus \bigcup W = {B | B \in A \cap C for
    some C \in Y}. Indeed \bigcup W = {B | B is an element of some element of W}.

    \bigcup W = A \cap \bigcup Y.
    proof.
      Every element of \bigcup W lies in A \cap \bigcup Y.
      proof.
        Let B \in \bigcup W. Then B lies in A. Moreover B lies in some element of Y. Hence B lies in
        \bigcup Y.
      end.

      Every element of A \cap \bigcup Y lies in \bigcup W.
      proof.
        Let B \in A \cap \bigcup Y. Then B \in A and B \in \bigcup Y. Hence B is an element of some
        element of Y.
      end.
    end.
  end.

  Thus (A,V) satisfies TopOpen3.
qed.


# 3.2 The product topology

Proposition SetTop305. Let X,Y be sets. Let U be a topology on X and V be a topology on Y. Let W be
a class such that W = {A \times B | (A,B) \in U \times V}. Then W is a topology on X \times Y.

Proof.
  X \times Y is a set. U \times V = {(A,B) | A \in U and B \in V} (by FoundFam380). Indeed U and V
  are classes. Every element of U is a subset of X. Every element of V is a subset of Y.

  W is a subset of the powerset of X \times Y.
  proof.
    Define f((A,B)) = A \times B for (A,B) in U \times V. U \times V is a set. Hence f[U \times V]
    is a set. (1) f[U \times V] = {f(C) | C \in U \times V} (by FoundMap186). Indeed f is a map.
    (2) Thus f[U \times V] = {A \times B | (A,B) \in U \times V} (by 1). f[U \times V] = W. Indeed
    every element of f[U \times V] lies in W and every element of W lies in f[U \times V] (by 2).
    Hence W is a set.

    Pow(X \times Y) is a set. Pow(X \times Y) = {Z | Z is a subset of X \times Y}.

    Every element of W lies in Pow(X \times Y).
    proof.
      Let C \in W. Take entities A,B such that (A,B) \in U \times V and C = A \times B.

      C is a subset of X \times Y.
      proof.
        A \in U and B \in V (by FoundFam415). Indeed U and V are classes. Hence A is a subset of X
        and B is a subset of Y. A \times B is a set. A \times B = {(x,y) | x \in A and y \in B} (by
        FoundFam380). Indeed A,B are classes.

        Every element of A \times B lies in X \times Y.
        proof.
          Let z \in A \times B. Take x \in A and y \in B such that z = (x,y). Then x \in X and
          y \in Y. Hence (x,y) \in X \times Y (by FoundFam415). Indeed X,Y are classes.
        end.
      end.
    end.
  end.

  \emptyset is an element of U and an element of V. Hence (\emptyset,\emptyset) \in U \times V. Thus
  \emptyset \times \emptyset \in W. \emptyset \times \emptyset = \emptyset. Therefore
  \emptyset \in W.

  X \in U and Y \in V. Hence (X,Y) \in U \times V. Thus X \times Y \in W.

  Then (X \times Y, W) satisfies TopOpen1.

  For all A,B \in W we have A \cap B \in W.
  proof.
    Let A,B \in W. Take C,D \in U and E,F \in V such that A = C \times E and B = D \times F. Then
    A \cap B = (C \times E) \cap (D \times F) = (C \cap D) \times (E \cap F) (by FoundFam435).
    Indeed C,D,E,F are classes. C \cap D \in U and E \cap F \in V (by SetTop050). Hence
    (C \cap D, E \cap F) \in U \times V. 
  end.

  Then W is closed under finite intersections. Thus (X \times Y, W) satisfies TopOpen2.

  W is closed under arbitrary unions.
  proof.
    [prove off]
  end.

  Hence (X \times Y, W) satisfies TopOpen3.
qed.


# 3.3 The disjoint union topology

Proposition SetTop310. Let X,Y be sets. Let U be a topology on X and V be a topology on Y. Let W be
a class such that W = {(A \times `{0}`) \cup (B \times `{1}`) | (A,B) \in U \times V}. Then W is a
topology on X \uplus Y.

Proof. [prove off] qed.
