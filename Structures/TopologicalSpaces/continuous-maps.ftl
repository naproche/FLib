#
# Continuous maps
# (Marcel Schütz, 2020)
#

#[prove off][check off]
[read FLib/Structures/TopologicalSpaces/separation.ftl]
#[prove on][check on]


# 1. Continuous maps

Axiom TopCont000. Let X,Y be topological spaces and f be a map from X to Y. f is continuous iff
f^{-1}[A] is open for all open subsets A of Y.


Proposition TopCont005. Let X,Y be topological spaces and f be a map from X to Y. f is continuous
iff f^{-1}[A] is closed for all closed subsets A of Y.

Proof.
  If f is continuous then f^{-1}[A] is closed for all closed subsets A of Y.
  proof.
    Assume that f is continuous. Let A be a closed subset of Y. Y \setminus A is an open subset of
    Y. Hence f^{-1}[Y \setminus A] is open (by TopCont000). f^{-1}[Y \setminus A] =
    X \setminus f^{-1}[A] (by FoundMap256). Indeed A is a subclass of Y. f^{-1}[A] is a subset of X
    (by SetSet121). Indeed X and Y are sets. Thus f^{-1}[A] is closed.
  end.

  If f^{-1}[A] is closed for all closed subsets A of Y then f is continuous.
  proof.
    Assume that f^{-1}[A] is closed for all closed subsets A of Y.

    f^{-1}[A] is open for all open subsets A of Y.
    proof.
      Let A be an open subset of Y. Then Y \setminus A is a closed subset of Y. Hence
      f^{-1}[Y \setminus A] is closed. f^{-1}[Y \setminus A] = X \setminus f^{-1}[A] (by
      FoundMap256). Indeed A is a subclass of Y. f^{-1}[A] is a subset of X (by SetSet121). Indeed X
      and Y are sets. Thus f^{-1}[A] is open.
    end.

    Then we have the thesis (by TopCont000).
  end.
qed.


Proposition TopCont010. Let X be a topological space. Then id_{X} is continuous.

Proof.
  id_{X}^{-1}[A] is open for all open subsets A of X.
  proof.
    Let A be an open subset of X. Then id_{X}^{-1}[A] = A (by FoundMap197). Indeed A is a subclass
    of X.
  end.

  Hence the thesis (by TopCont000). Indeed id_{X} is a map from X to X.
qed.


Proposition TopCont015. Let X,Y,Z be topological spaces. Let f be a continuous map from X to Y and g
be a continuous map from Y to Z. Then g \circ f is continuous.

Proof.
  g \circ f is a map from X to Z (by FoundMap046).

  (g \circ f)^{-1}[A] is open for all open subsets A of Z.
  proof.
    Let A be an open subset of Z. (g \circ f)^{-1}[A] = f^{-1}[g^{-1}[A]] (by FoundMap198). Indeed A
    is a subclass of Z. g^{-1}[A] is an open subset of Y (by TopCont000, SetSet121). Indeed Y and Z
    are sets. Hence f^{-1}[g^{-1}[A]] is open (by TopCont000).
  end.

  Thus g \circ f is continuous (by TopCont000).
qed.


Proposition TopCont020. Let X,Y be topological spaces and f be a constant map from X to Y. Then f is
continuous.

Proof.
  f^{-1}[A] is open for all open subsets A of Y.
  proof.
    Let A be an open subset of Y. (1) f^{-1}[A] is a class such that f^{-1}[A] =
    {x in X | f(x) \in A}.

    Case X is empty. Obvious.

    Case X is nonempty.
      Take an element a of Y such that f(x) = a for all x \in X.

      Case a \notin A.
        Then f^{-1}[A] = \emptyset (by 1).
      end.

      Case a \in A.
        f^{-1}[A] = {x in X | a \in A}. Hence f^{-1}[A] = {x | x \in X}.

        Thus f^{-1}[A] = X.
        proof.
          Take a class B such that B = f^{-1}[A]. If Every element of B lies in X and every element
          of X lies in B then X = B. Hence X = B. 
        end.
      end.
    end.
  end.

  Hence the thesis (by TopCont000).
qed.


# 2. Discrete and indiscrete spaces.

Axiom TopCont030. Let X be a topological space. X is discrete iff every subset of X is open.


Proposition TopCont032. Let X be a set. Then Top_{1}(X,Pow(X)) is a discrete topological space.

Proof.
  Take a topological space T such that T = Top_{1}(X,Pow(X)).

  Every subset of T is open.
  proof.
    Let A be a subset of T. T^{-1}[A] is a subset of X. Hence T^{-1}[A] is an element of Pow(X).
    Then T[T^{-1}[A]] is an open subset of T (by TopTop057). Indeed Pow(X) is a topology on X.
    T[T^{-1}[A]] = A (by FoundMap199). Indeed T is a surjective map from X to T and A is a subclass
    of T.
  end.
qed.


Axiom TopCont035. Let X be a topological space. X is indiscrete iff for all open subsets A of X we
have A = \emptyset or A = X.


Proposition TopCont037. Let X be a set. Top_{2}(X, `{\emptyset, X}`) is an indiscrete topological
space.

Proof. [prove off] qed.


Proposition TopCont040. Let X be a topological space. X is discrete iff for all topological spaces Y
every map from X to Y is continuous.

Proof.
  If X is discrete then for all topological spaces Y every map from X to Y is continuous.
  proof.
    Assume that X is discrete. Let Y be a topological space and f be a map from X to Y.

    f^{-1}[A] is open for all open subsets A of Y.
    proof.
      Let A be an open subset of Y. Then f^{-1}[A] is a subset of X (by SetSet121). Indeed X and Y
      are sets.
    end.

    Hence f is continuous (by TopCont000).
  end.

  If for all topological spaces Y every map from X to Y is continuous then X is discrete.
  proof.
    Assume that for all topological spaces Y every map from X to Y is continuous.

    Every subset of X is open.
    proof.
      Let A be a subset of X. Take a topological space Y such that Y = Top_{1}(X,Pow(X)). Then Y is
      discrete. A is an element of Pow(X). Hence Y[A] is an open subset of Y (by TopTop057). Indeed
      X is a set and Pow(X) is a topology on X.

      Y is a map from X to Y. Hence Y is continuous. Thus Y^{-1}[Y[A]] is open. Y^{-1}[Y[A]] = A (by
      FoundMap200). Indeed Y is injective and A is a subclass of X.
    end.
  end.
qed.


Proposition TopCont045. Let Y be a topological space. Y is indiscrete iff for all topological spaces
X every map from X to Y is continuous.

Proof. [prove off] qed.


# 3. Homeomorphisms

Definition TopCont050. A homeomorphism is a bijective continuous map f such that f^{-1} is
continuous.

Definition TopCont055. Let X,Y be topological spaces. A homeomorphism between X and Y is a
homeomorphism f such that dom(f) = X and codom(f) = Y.


Proposition TopCont060. Let X,Y be topological spaces and f be a map from X to Y. f is a
homeomorphism iff f is continuous and there is a continuous map g from Y to X such that g \circ f =
id_{X} and f \circ g = id_{Y}.

Proof. [prove off] qed.
