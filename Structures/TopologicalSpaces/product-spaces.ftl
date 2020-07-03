#
# Product spaces
# (Marcel Schütz, 2020)
#

#[prove off][check off]
[read FLib/Structures/TopologicalSpaces/continuous-maps.ftl]
#[prove on][check on]


# 1. Product spaces

Axiom TopProd000. Let X,Y be sets. Let U be a topology on X and V be a topology on Y. Let W be a
class such that W = {A \times B | (A,B) \in U \times V}. Then

  (X,U)_{TOP} \times (Y,V)_{TOP} = (X \times Y, W)_{TOP}.


Proposition TopProd002. Let X,Y be topological spaces. Then X \times Y is a topological space.

Proof. [prove off] qed.


Proposition TopProd005. Let X,Y be topological spaces and C be a subset of X \times Y. C is open iff
there are open sets A,B such that A is a subset of X and B is a subset of Y and C = A \times B.

Proof. [prove off] qed.


Corollary TopProd010. Let X,Y be topological spaces. Let A,B be entities. A \times B is an open
subset of X \times Y iff A is an open subset of X and B is an open subset of Y.

Proof. [prove off] qed.


# 2. Continuous maps

Proposition TopProd015. Let X,Y be topological spaces and p be the projection of X \times Y. Then
p_{1} is continuous and p_{2} is continuous.

Proof.
  X,Y are classes.

  p_{1} is a map from X \times Y to X. p_{1}(x,y) = x for all x \in X and all y \in Y (by
  FoundFam065).

  p_{2} is a map from X \times Y to Y. p_{2}(x,y) = y for all x \in X and all y \in Y (by
  FoundFam067).

  p_{1}^{-1}[A] is open for all open subsets A of X.
  proof.
    Let A be an open subset of X.

    p_{1}^{-1}[A] = A \times Y.
    proof.
      A is a class. Hence A \times Y is a class. Furthermore p_{1}^{-1}[A] is a class. If every
      element of p_{1}^{-1}[A] lies in A \times Y and every element of A \times Y lies in
      p_{1}^{-1}[A] then p_{1}^{-1}[A] = A \times Y.

      Every element of p_{1}^{-1}[A] lies in A \times Y.
      proof.
        Let z \in p_{1}^{-1}[A]. Then z \in X \times Y. Hence we can take an element x of X and an
        element y of Y such that z = (x,y) (by FoundFam380). p_{1}(x,y) = x. Hence x \in A. Thus
        (x,y) \in A \times Y (by FoundFam380).
      end.

      Every element of A \times Y lies in p_{1}^{-1}[A].
      proof.
        Let z \in A \times Y. Then we can take an element x of A and an element y of Y such that
        z = (x,y) (by FoundFam380). x \in X. Hence p_{1}(x,y) = x. Thus p_{1}(x,y) \in A.
        p_{1}^{-1}[A] = {u in X \times Y | p_{1}(u) \in A}. (x,y) \in X \times Y (by FoundFam380).
      end.
    end.

    A is an open subset of X and Y is an open subset of Y. Hence A \times Y is an open subset of
    X \times Y (by TopProd010).
  end.

  p_{2}^{-1}[A] is open for all open subsets A of Y.
  proof.
    Let A be an open subset of Y.

    p_{2}^{-1}[A] = X \times A.
    proof.
      A is a class. Hence X \times A is a class. Furthermore p_{2}^{-1}[A] is a class. If every
      element of p_{2}^{-1}[A] lies in X \times A and every element of X \times A lies in
      p_{2}^{-1}[A] then p_{2}^{-1}[A] = X \times A.

      Every element of p_{2}^{-1}[A] lies in X \times A.
      proof.
        Let z \in p_{2}^{-1}[A]. Then z \in X \times Y. Hence we can take an element x of X and an
        element y of Y such that z = (x,y) (by FoundFam380). p_{2}(x,y) = y. Hence y \in A. Thus
        (x,y) \in X \times A (by FoundFam380).
      end.

      Every element of X \times A lies in p_{2}^{-1}[A].
      proof.
        Let z \in X \times A. Then we can take an element x of X and an element y of A such that
        z = (x,y) (by FoundFam380). y \in Y. Hence p_{2}(x,y) = y. Thus p_{2}(x,y) \in A.
        p_{2}^{-1}[A] = {u in X \times Y | p_{2}(u) \in A}. (x,y) \in X \times Y (by FoundFam380).
      end.
    end.

    A is an open subset of Y and X is an open subset of X. Hence X \times A is an open subset of
    X \times Y (by TopProd010).
  end.

  Then we have the thesis (by TopCont000). Indeed X \times Y is a topological space.
qed.


Proposition TopProd020. Let X,Y,Z be topological spaces and p be the projection of X \times Y. Let
g be a map from Z to X \times Y. g is continuous iff p_{1} \circ g is continuous and p_{2} \circ g
is continuous.

Proof. [prove off] qed.


Proposition TopProd025. Let X,Y,A,B be topological spaces. Let f be a map from A to X and g be a map
from B to Y. Then f \times g is continuous iff f is continuous and g is continuous.

Proof. [prove off] qed.
