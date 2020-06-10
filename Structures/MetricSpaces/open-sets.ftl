#
# Open and closed sets, neighbourhoods
# (Marcel Schütz, 2020)
#

#[prove off]
[read ForTheLib/MetricSpaces/metric-spaces.ftl]
#[prove on]


# 1. Open sets

Axiom MetOs000. Let X be a metric space and x \in X and epsilon be a positive real number.
B(x,epsilon) is a class such that

  B(x,epsilon) = {y in X | dist(x,y) < epsilon}.


Proposition MetOs001. Let X be a metric space and x \in X. Let epsilon be a positive real number.
Then x \in B(x,epsilon).

Proof.
  dist(x,x) < epsilon. Indeed dist(x,x) = 0 (by MetMs031). Hence the thesis (by MetOs000).
qed.


Proposition MetOs002. Let X be a metric space and x \in X. Let epsilon be a positive real number.
Then B(x,epsilon) is a subset of X.

Proof.
  range(X) is a set (by FoundStr045). Indeed X is a small structure. B(x,epsilon) \subseteq range(X)
  (by FoundCl005). Indeed B(x,epsilon) is a class such that every element of B(x,epsilon) is an
  element of range(X). hence B(x,epsilon) is a subclass of range(X). Thus B(x,epsilon) is a set (by
  SetSet155). B(x,epsilon) \subseteq X. Indeed every element of B(x,epsilon) is an element of X.
qed.


Axiom MetOs005. Let X be a metric space and A be a subcollection of X. A is open iff for all x \in A
there exists a positive real number epsilon such that B(x,epsilon) \subseteq A.


Proposition MetOs010. The empty set is an open subset of every metric space.

Proof.
  For all x \in \emptyset there exists a positive real number epsilon such that
  B(x,epsilon) \subseteq \emptyset. Hence the thesis (by MetOs005). Indeed \emptyset is a subset of
  every metric space.
qed.


Proposition MetOs014. Let X be a metric space. X is open.

Proof.
  For all x \in X we have B(x,1) \subseteq X.
  proof.
    Let x \in X. Hence the thesis (by FoundCl005). Indeed B(x,1) is a class such that every element
    of B(x,1) is an element of X.
  end.

  Thus For all x \in X there exists a positive real number epsilon such that
  B(x,epsilon) \subseteq X. Hence the thesis (by MetOs005).
qed.


Proposition MetOs015. Let X be a metric space. The range of X is an open subset of X.

Proof.
  For all x \in range(X) we have B(x,1) \subseteq range(X).
  proof.
    Let x \in range(X). Then x \in X. Hence the thesis (by FoundCl005). Indeed B(x,1) is a class
    such that every element of B(x,1) is an element of range(X).
  end.

  Thus For all x \in range(X) there exists a positive real number epsilon such that
  B(x,epsilon) \subseteq range(X). range(X) is a subset of X (by FoundStr045). Indeed X is a small
  structure. Hence range(X) is open (by MetOs005). Indeed range(X) is a subcollection of X.
qed.


Proposition MetOs020. Let X be a metric space and x \in X. Let epsilon be a positive real number.
Then B(x,epsilon) is an open subset of X.

Proof.
  For all y \in B(x,epsilon) there exists a positive real number delta such that
  B(y,delta) \subseteq B(x,epsilon).
  proof.
    Let y \in B(x,epsilon).

    Case y = x. Obvious.

    Case y \neq x.    
      Take a real number delta such that delta = epsilon - dist(x,y). Indeed epsilon and dist(x,y)
      are real numbers. epsilon and dist(x,y) are real numbers. delta is positive. Indeed
      dist(x,y) < epsilon. Hence 0 < epsilon - dist(x,y) (by AnaRe241). Hence dist(x,y) > 0 (by
      MetMs027). Indeed x,y \in X. Thus delta < epsilon (by AnaRe242). B(y,delta) =
      {u in X | dist(y,u) < delta} (by MetOs000). Hence Every element of B(y,delta) lies in X.

      Every element of B(y,delta) is an element of B(x,epsilon).
      proof.
        Let z \in B(y,delta). z \in X.

        (1) dist(y,z) < delta.

        (2) dist(x,z) \leq dist(x,y) + dist(y,z) (by MetMs028). Indeed x,y,z \in X.

        (3) dist(x,y) + dist(y,z) < dist(x,y) + delta (by AnaRe246). Indeed dist(x,y), dist(y,z),
        delta are real numbers such that dist(y,z) < delta.

        (4) dist(x,y) + delta = dist(x,y) + (epsilon - dist(x,y)) = epsilon (by AnaRe156). Indeed
        dist(x,y) and epsilon are real numbers.

        Hence dist(x,z) < dist(x,y) + delta.
        proof.
          dist(x,z) is a real number.
          dist(x,y) + dist(y,z) is a real number. Indeed dist(x,y) and dist(y,z) are real numbers.
          dist(x,y) + delta is a real number.
          dist(x,z) \leq dist(x,y) + dist(y,z) < dist(x,y) + delta (by 2,3).
          Hence the thesis (by AnaRe247).
        end.

        Thus dist(x,z) < epsilon. B(x,epsilon) = {u in X | dist(x,u) < epsilon} (by MetOs000).
      end.
    end.
  end.

  B(x,epsilon) is a subset of X. Hence the thesis (by MetOs005). Indeed B(x,epsilon) is a
  subcollection of X.
qed.


Proposition MetOs025. Let X be a metric space and U be a class. Assume that every element of U is an
open subcollection of X. Then \bigcup U is an open subset of X.

Proof.
  Every element of \bigcup U is an element of X.
  proof.
    Let x \in \bigcup U. Take an object A that lies in U and contains x. Every element of A is an
    element of X (by FoundCl005). Indeed A is a class such that A \subseteq X.
  end.

  \bigcup U \subseteq range(X) (by FoundCl005). Indeed \bigcup U is a class such that every element
  of \bigcup U lies in the range of X. Hence \bigcup U is a subset of X. Indeed \bigcup U is a set.

  For all x \in \bigcup U there exists a positive real number epsilon such that B(x,epsilon) is a
  subset of \bigcup U.
  proof.
    Let x \in \bigcup U. Take an object A that lies in U and contains x. Then A is an open
    subcollection of X. Take a positive real number epsilon such that B(x,epsilon) \subseteq A.
    Every element of A lies in X. Every element of B(x,epsilon) lies in A. Hence every element of
    B(x,epsilon) is an element of \bigcup U. Thus B(x,epsilon) \subseteq \bigcup U (by FoundCl005).
    Indeed B(x,epsilon) is a class.
  end.

  Thus \bigcup U is open (by MetOs005).
qed.


Corollary MetOs030. Let X be a metric space and A,B be open subsets of X. Then A \cup B is open.

Proof.
  Define U = {A,B}. U = `{A,B}`. Hence \bigcup U = A \cup B. Every element of U is an open subset of
  X. Hence every element of U is a subcollection of X. Thus \bigcup U is an open subset of X (by
  MetOs025). Indeed U is a set.
qed.


Proposition MetOs035. Let X be a metric space and U be a nonempty finite set. Assume that every
element of U is an open subset of X. Then \bigcap U is an open subset of X.

Proof. [prove off] qed.


Corollary MetOs040. Let X be a metric space and A,B be open subsets of X. Then A \cap B is open.

Proof.
  Define U = {A,B}. Then U = `{A,B}`. Hence U is a finite set (by SetCard086). \bigcap U = A \cap B.
  Every element of U is an open subset of X. Thus \bigcap U is an open subset of X (by MetOs035).
qed.


# 2. Closed sets

Axiom MetOs045. Let X be a metric space and A be a subcollection of X. A is closed iff X \setminus A
is open.


Proposition MetOs050. The empty set is a closed subset of every metric space.

Proof.
  Let X be a metric space. X \setminus \emptyset = {x in X | x \notin \emptyset} (by FoundStr050).
  Indeed X is a structure. Every element of X \setminus \emptyset is an element of range(X) and
  every element of range(X) is an element of X \setminus \emptyset. Hence X \setminus \emptyset =
  range(X). Indeed X \setminus \emptyset is a class. range(X) is open (by MetOs015). Hence \emptyset
  is closed (by MetOs045).
qed.


Proposition MetOs054. Let X be a metric space. X is closed.

Proof.
  X \setminus X = \emptyset. Hence the thesis (by MetOs045). Indeed \emptyset is open.
qed.


Proposition MetOs055. Let X be a metric spaces. range(X) is a closed subset of X.

Proof.
  X \setminus range(X) = \emptyset. range(X) is a subcollection of X. Hence range(X) is closed (by
  MetOs045). Indeed \emptyset is open. range(X) is a set (by FoundStr045). Indeed X is a small
  structure.
qed.


Proposition MetOs056. Let X be a metric space and A be an open subcollection of X. Then
X \setminus A is closed.

Proof.
  Every element of A lies in X. Hence X \setminus (X \setminus A) = A (by FoundStr055). Indeed X is
  a structure. range(X) is a set (by FoundStr045). Indeed X is a small structure. Every element of
  X \setminus A lies in range(X). X \setminus A \subseteq range(X) (by FoundCl000). Indeed range(X)
  is a class. Thus X \setminus A is a set (by SetSet155). Indeed X \setminus A is a class.
  X \setminus A \subseteq X. Indeed Every element of X \setminus A lies in X. Hence X \setminus A is
  a subset of X (by FoundCl005). 
qed.


Proposition MetOs060. Let X be a metric space and U be a finite set. Assume that every element of U
is a closed subset of X. Then \bigcup U is a closed subset of X.

Proof.
  Case U is empty. Obvious.

  Case U is nonempty.
    (1) Define V = {X \setminus A | A \in U}.

    Every element of U is a subcollection of X. Indeed every subset of X is a subcollection of X.
    Every element of V is open. V is nonempty.

    Define f(B) = X \setminus B for B in V.

    f(B) lies in U for all B \in V.
    proof.
      Let B \in V. Take an element A of U such that B = X \setminus A (by 1). A is a subset of X.
      f(B) = X \setminus (X \setminus A) = A (by FoundStr055). Indeed X is a structure and A is a
      class such that every element of A lies in X.
    end.

    Hence range(f) \subseteq U (by FoundCl005). Indeed range(f) is a class such that every element
    of range(f) lies in U (by FoundFun005).

    Every element of U lies in the range of f.
    proof.
      Let A \in U. Every element of A lies in X. Indeed A \subseteq X. Take B \in V such that
      B = X \setminus A. f(B) = X \setminus (X \setminus A) = A (by FoundStr055). Indeed X is a
      structure and A is a class. Hence A lies in the range of f. Indeed
      range(f) = {f(x) | x \in dom(f)}.
    end.

    Hence U \subseteq range(f). Therefore range(f) = U.

    For all B,C \in dom(f) if f(B) = f(C) then B = C.
    proof.
      Let B,C \in dom(f). Assume that f(B) = f(C). Take A \in U such that B = X \setminus A (by 1).
      Take D \in U such that C = X \setminus D (by 1). Then f(B) = X \setminus (X \setminus A) and
      f(C) = X \setminus (X \setminus D). Every element of A lies in X. Indeed A \subseteq X. Every
      element of D lies in X. Indeed D \subseteq X. Hence X \setminus (X \setminus A) = A (by
      FoundStr055). Indeed A is a class and X is a structure. X \setminus (X \setminus D) = D (by
      FoundStr055). Indeed D is a class and X is a structure. Thus A = D.
    end.

    Hence f is injective (by FoundFun070). Thus f is a bijection between V and U.

    f^{-1} is a bijection between U and V. Thus f^{-1}[U] = V.

    Every value of f^{-1} is an element.
    proof.
      Let B be a value of f^{-1}. B \in V. Indeed V = range(f^{-1}). Take A \in U such that
      B = X \setminus A (by 1). range(X) is a set (by FoundStr045). Indeed X is a small structure. B
      is a class such that B = {x in X | x \notin A} (by FoundStr050). Indeed X is a structure and A
      is a class. range(X) \setminus A is a class such that range(X) \setminus A =
      {x in range(X) | x \notin A} (by FoundCl065). Indeed range(X) and A are classes. Hence
      B = range(X) \setminus A. Indeed B = {x in range(X) | x \notin A}. Thus B is a set.
    end.

    U \subseteq dom(f^{-1}). Hence f^{-1}[U] is a set (by SetSet060). Therefore V is a nonempty
    finite set. Then \bigcap V is an open subset of X (by MetOs035). Indeed every element of V is an
    open subset of X. \bigcap V is a subcollection of X. Indeed Every element of \bigcap V lies in
    X. Thus X \setminus \bigcap V is closed (by MetOs056).

    X \setminus \bigcap V = \bigcup U.
    proof.
      Every element of X \setminus \bigcap V lies in \bigcup U.
      proof.
        Let x \in X \setminus \bigcap V. Then x \in X and x \notin \bigcap V. Take an element B of V
        such that x \notin B. Take an element A of U such that B = X \setminus A (by 1). Then
        x \in A. Indeed B = {y in X | y \notin A} (by FoundStr050). Indeed X is a structure and A is
        a class.
      end.

      Every element of \bigcup U lies in X \setminus \bigcap V.
      proof.
        Let x \in \bigcup U. Take A \in U such that x \in A (by FoundCl040). Indeed U is a
        class. Then x \notin X \setminus A. x \in X. Indeed A is a subset of X. X \setminus A \in V
        (by 1). Hence x \notin \bigcap V. Thus x \in X \setminus \bigcap V. Indeed
        X \setminus \bigcap V = {y in X | y \notin \bigcap V} (by FoundStr050). Indeed X is a
        structure and \bigcap V is a class.
      end.

      X \setminus \bigcap V and \bigcup U are classes.
    end.

    Every element of \bigcup U lies in X. Hence \bigcup U \subseteq X (by FoundCl005). Indeed
    \bigcup U is a class. Thus \bigcup U is a closed subset of X.
  end.
qed.


Corollary MetOs065. Let X be a metric space and A,B be closed subsets of X. Then A \cup B is closed.

Proof.
  Define U = {A,B}. U = `{A,B}`. Hence A \cup B = \bigcup U. U is a finite set. Hence the thesis (by
  MetOs060).
qed.


Proposition MetOs067. Let X be a metric space and A be a closed subcollection of X. Then
X \setminus A is open.


Proposition MetOs070. Let X be a metric space and U be a nonempty set. Assume that every element of
U is a closed subset of X. Then \bigcap U is a closed subset of X.

Proof.
  (1) Define V = {X \setminus A | A \in U}.

  range(X) is a set (by FoundStr045).
  Indeed X is a small structure. Every element of V is a subclass of range(X). Indeed for all
  B \in V we have B \subseteq range(X). Hence every element of V lies in the powerset of range(X)
  (by FoundCl075). Indeed range(X) is a class such that every element of V is a subclass of range(X).
  Thus V \subseteq Pow(range(X)). Therefore V is a set. Every element of V is open (by MetOs067,1).
  Indeed every element of U is a closed subcollection of X (by SetSet017). Every element of V is a
  subset of X (by FoundStr060). Indeed X is a small structure and every element of U is a class.
  Hence \bigcup V is an open subset of X (by MetOs025). Indeed every element of V is a subcollection
  of X.

  Thus X \setminus \bigcup V is a closed subset of X.

  X \setminus \bigcup V = \bigcap U.
  proof.
    Every element of X \setminus \bigcup V lies in \bigcap U.
    proof.
      Let x \in X \setminus \bigcup V. Then x \in X and x \notin \bigcup V. Hence x lies in no
      element of V. Thus for all A \in U we have x \notin X \setminus A (by 1). Therefore x \in A
      for all A \in U. Indeed X \setminus A = {y in X | y \notin A} for all A \in U (by
      FoundStr050). Indeed every element of U is a class and X is a structure.
    end.

    Every element of \bigcap U lies in X \setminus \bigcup V.
    proof.
      Let x \in \bigcap U. Then x belongs to every element of U. x \in X. Indeed every element of U
      is a subclass of X. Hence x \notin X \setminus A for all A \in U. Thus x belongs to no element
      of V (by 1). Therefore x \notin \bigcup V. Hence x \in X \setminus \bigcup V (by FoundStr050).
      Indeed X is a structure and \bigcup V is a class.
    end.
  end.
qed.


Corollary MetOs075. Let X be a metric space and A,B be closed subsets of X. Then A \cap B is closed.

Proof.
  Define U = {A,B}. U = `{A,B}`. Hence A \cap B = \bigcap U. U is a nonempty set. Hence the thesis
  (by MetOs070).
qed.


Proposition MetOs078. Let X be a metric space and x \in X. `{x}` is closed.
Proof.
  Case range(X) = `{x}` (by MetOs055). Obvious.

  Case range(X) \neq `{x}`.
    X \setminus `{x}` is a subset of X (by FoundStr060). Indeed X is a small structure.

    (1) For all y \in X \setminus `{x}` there exists a positive real number epsilon such that
    B(y,epsilon) \subseteq X \setminus `{x}`.
    proof.
      Let y \in X \setminus `{x}`. `{x}` = {x}. x,y \in X. y \neq x. dist(x,y) > 0 (by MetMs027).
      Thus dist(x,y) is a positive real number. Every element of B(y,dist(x,y)) lies in X (by
      MetOs000).

      No element of B(y,dist(x,y)) lies in `{x}`.
      proof.
        Assume the contrary. Take an element z of B(y,dist(x,y)) that lies in `{x}`. Then z = x.
        Hence dist(z,y) = dist(x,y). dist(z,y) = dist(y,z) (by MetMs030). Hence
        dist(y,z) = dist(x,y). dist(y,z) < dist(x,y) (by MetOs000). Indeed z \in B(y,dist(x,y)).
        Contradiction.
      end.

      X \setminus `{x}` = {y in X | y \notin `{x}`} (by FoundStr050). Indeed X is a structure and
      `{x}` is a class. Hence every element of B(y,dist(x,y)) lies in X \setminus `{x}`. Thus
      B(y,dist(x,y)) \subseteq X \setminus `{x}`.
    end.

    Take an object Y such that Y = X \setminus `{x}`. Y is a subcollection of X. Hence Y is open iff
    for all y \in Y there exists a positive real number epsilon such that B(y,epsilon) \subseteq Y
    (by MetOs005). Hence Y is open. Thus X \setminus `{x}` is open. `{x}` is a set.
    `{x}` \subseteq X. Then we have the thesis (by MetOs045).
  end.
qed.


# 3. Neighbourhoods

#[prove off]
[read ForTheLib/Sets/filters.ftl]
[prove on]

Axiom MetOs080. Let X be a metric space and x \in X. Let U be an object. U is a neighbourhood of
x iff U is a subcollection of X such that B(x,epsilon) \subseteq U for some positive real number
epsilon.


Proposition MetOs085. Let X be a metric space and x \in X. Let epsilon be a positive real number.
Then B(x,epsilon) is a neighbourhood of x.

Proof.
  B(x,epsilon) is a subcollection of X. Thus B(x,delta) \subseteq B(x,epsilon) for some positive
  real number delta. Hence the thesis (by MetOs080).
qed.


Proposition MetOs090. Let X be a metric space and A be a subcollection of X. A is open iff A is a
neighbourhood of every element of A.

Proof.
  If A is open then A is a neighbourhood of every element of A.
  proof.
    Assume that A is open. Let x \in A. Take a positive real number epsilon such that
    B(x,epsilon) \subseteq A (by MetOs005).
  end.

  If A is a neighbourhood of every element of A then A is open.
  proof.
    Assume that A is a neighbourhood of every element of A.

    For all x \in A there is a positive real number epsilon such that B(x,epsilon) \subseteq A.
    proof.
      Let x \in A. A is a neighbourhood of x. x \in X. Indeed A is a subcollection of X. Take a
      positive real number epsilon such that B(x,epsilon) \subseteq A (by MetOs080).
    end.

    Hence the thesis (by MetOs005). Indeed A is a subcollection of X.
  end.
qed.


Proposition MetOs092. Let X be a metric space and x \in X. Let U be a neighbourhood of x. Then
x \in U.

Proof.
  Take a positive real number epsilon such that B(x,epsilon) \subseteq U (by MetOs080).
  x \in B(x,epsilon) (by MetOs001). Every element of B(x,epsilon) is an element of U (by
  FoundCl005). Indeed B(x,epsilon) is a class.
qed.


Proposition MetOs095. Let X be a metric space and U be a class. Let x \in X. Assume that U =
{N | N is a neighbourhood of x}. Then U is a filter on X.

Proof. [prove off] qed.


Proposition MetOs098. Let X be a metric space and x,y \in X. Assume that x \neq y. There are
disjoint subsets U,V of X such that U is a neighbourhood of X and V is a neighbourhood of y.

Proof. [prove off] qed.
