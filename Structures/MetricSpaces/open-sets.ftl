#
# Open and closed sets, neighbourhoods
# (Marcel Schütz, 2020)
#

#[prove off][check off]
[read ForTheLib/MetricSpaces/metric-spaces.ftl]
[read ForTheLib/Sets/topologies.ftl]
#[prove on][check on]


# 1. Open sets

Axiom MetOs000. Let X be a metric space and a \in X and r be a positive real number.
B(a,r) is a set such that

  B(a,r) = {x in X | dist(a,x) < r}.


Proposition MetOs001. Let X be a metric space and x \in X. Let epsilon be a positive real number.
Then x \in B(x,epsilon).

Proof.
  dist(x,x) < epsilon. Indeed dist(x,x) = 0 (by MetMs135). Hence the thesis (by MetOs000).
qed.


Proposition MetOs002. Let X be a metric space and x \in X. Let epsilon be a positive real number.
Then B(x,epsilon) is a subset of X.

Proof.
  B(x,epsilon) is a class such that every element of B(x,epsilon) lies in X. Hence
  B(x,epsilon) \subseteq X (by FoundCl005). Thus B(x,epsilon) is a set (by SetSet155). Indeed X is a
  set.
qed.


Axiom MetOs005. Let X be a metric space and A be a subset of X. A is open iff for all x \in A
there exists a positive real number epsilon such that B(x,epsilon) \subseteq A.


Proposition MetOs010. The empty set is an open subset of every metric space.

Proof.
  For all x \in \emptyset there exists a positive real number epsilon such that
  B(x,epsilon) \subseteq \emptyset. Hence the thesis (by MetOs005). Indeed \emptyset is a subset of
  every metric space.
qed.


Proposition MetOs015. Let X be a metric space. X is an open subset of X.

Proof.
  For all x \in X we have B(x,1) \subseteq X.
  proof.
    Let x \in X. Then x \in X. B(x,1) is a class such that every element of B(x,1) is an element of
    X (by MetOs000). Indeed 1 is a positive real number. Then we have the thesis (by FoundCl005).
  end.

  Thus For all x \in X there exists a positive real number epsilon such that
  B(x,epsilon) \subseteq X. Hence X is open (by MetOs005). Indeed X is a subset of X.
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
      epsilon and dist(x,y) are real numbers. Hence we can take a real number delta such that
      delta = epsilon - dist(x,y). dist(x,y) < epsilon (by MetOs000). delta is positive. 0 is
      a real number. Hence 0 < epsilon - dist(x,y) (by AnaRe241). dist(x,y) > 0 (by MetMs137).
      Indeed x,y \in X. Thus delta < epsilon (by AnaRe242). Indeed dist(x,y) is positive.
      B(y,delta) = {u in X | dist(y,u) < delta} (by MetOs000). Hence Every element of B(y,delta)
      lies in X.

      Every element of B(y,delta) is an element of B(x,epsilon).
      proof.
        Let z \in B(y,delta). x,y,z \in X.

        (1) dist(y,z) < delta.

        (2) dist(x,z) \leq dist(x,y) + dist(y,z) (by MetMs145).

        (3) dist(x,y) + dist(y,z) < dist(x,y) + delta (by AnaRe246). Indeed dist(x,y), dist(y,z),
        delta are real numbers such that dist(y,z) < delta (by MetMs125, 1).

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
  subset of X.
qed.


Proposition MetOs025. Let X be a metric space and U be a class. Assume that every element of U is an
open subset of X. Then \bigcup U is an open subset of X.

Proof.
  Every element of \bigcup U is an element of X.
  proof.
    Let x \in \bigcup U. Take an entity A that lies in U and contains x. Every element of A is an
    element of X (by FoundCl005). Indeed A is a class such that A \subseteq X.
  end.

  \bigcup U \subseteq range(X) (by FoundCl005). Indeed \bigcup U is a class such that every element
  of \bigcup U lies in the range of X. \bigcup U is a set.

  Hence \bigcup U is a subset of X.

  For all x \in \bigcup U there exists a positive real number epsilon such that
  B(x,epsilon) \subseteq \bigcup U.
  proof.
    Let x \in \bigcup U. Take an entity A that lies in U and contains x. Then A is an open subset of
    X. Take a positive real number epsilon such that B(x,epsilon) \subseteq A (by MetOs005). Every
    element of A lies in X. Every element of B(x,epsilon) lies in A. Hence every element of
    B(x,epsilon) is an element of \bigcup U. Thus B(x,epsilon) \subseteq \bigcup U (by FoundCl005).
    Indeed B(x,epsilon) is a class.
  end.

  Thus \bigcup U is open (by MetOs005).
qed.


Proposition MetOs035. Let X be a metric space and U be a nonempty finite set. Assume that every
element of U is an open subset of X. Then \bigcap U is an open subset of X.

Proof. [prove off] qed.


Corollary MetOs040. Let X be a metric space. Let U be a class such that U = {A | A is an open subset
of X}. Then U is a topology on X.

Proof.
  U is a subset of the powerset of X. Indeed Every element of U lies in Pow(X). X is a set.

  We have \emptyset,X \in U. Hence (X,U) satisfies TopOpen1 (by SetTop005).

  U is closed under finite intersections.
  proof.
    Let V be a nonempty finite subset of U. Then every element of V is an open subset of X. Hence
    \bigcap V is an open subset of X (by MetOs035). Indeed V is a set. Thus \bigcap V belongs to U.
  end.

  Hence (X,U) satisfies TopOpen2 (by SetTop015).

  U is closed under arbitrary unions.
  proof.
    Let V be a subset of U. Then every element of V is an open subset of X. Hence \bigcup V is an
    open subset of X (by MetOs025). Indeed V is a class. Thus \bigcup V belongs to U.
  end.

  Hence (X,U) satisfies TopOpen3 (by SetTop025).
qed.


Corollary MetOs045. Let X be a metric space and A,B be open subsets of X. Then A \cup B is open.

Proof.
  Define U = {C | C is an open subset of X}. Then U is a topology on X (by MetOs040). A,B are
  elements of U. Hence A \cup B \in U (by SetTop060). Indeed X is a set.
qed.


Corollary MetOs050. Let X be a metric space and A,B be open subsets of X. Then A \cap B is open.

Proof.
  Define U = {C | C is an open subset of X}. Then U is a topology on X (by MetOs040). A,B are
  elements of U. Hence A \cap B \in U (by SetTop050). Indeed X is a set.
qed.


# 2. Closed sets

Axiom MetOs055. Let X be a metric space and A be a subset of X. A is closed iff X \setminus A
is open.


Proposition MetOs060. Let X be a metric space and A be an open subset of X. Then X \setminus A is a
closed subset of X.

Proof.
  Every element of X \setminus A lies in X. X and X \setminus A are sets. Hence X \setminus A is a
  subset of X (by SetSet082). 
qed.


Proposition MetOs065. Let X be a metric space and A be a closed subset of X. Then X \setminus A is
an open subset of X.

Proof.
  X \setminus A is open. Moreover X \setminus A is a set. Every element of X \setminus A lies in X.
  Hence X \setminus A is a subset of X (by SetSet082). Indeed X is a set.
qed.


Proposition MetOs075. Let X be a metric space and V be a class such that V = {A | A is a closed
subset of X}. Then V is a topology of closed sets on X.

Proof.
  Define U = {A | A is an open subset of X}. Then U is a topology on X (by MetOs040). For all closed
  subsets A of X there is an element B of U such that A = X \setminus B. Indeed X \setminus A is an
  open subset of X for all closed subsets A of X. Hence V = {X \setminus A | A \in U}. Then we have
  the thesis (by SetTop140). Indeed X is a set.
qed.


Corollary MetOs080. The empty set is a closed subset of every metric space.


Corollary MetOs085. Let X be a metric spaces. X is a closed subset of X.


Corollary MetOs090. Let X be a metric space and U be a finite set. Assume that every element of U
is a closed subset of X. Then \bigcup U is a closed subset of X.

Proof.
  Define V = {A | A is a closed subset of X}. V is a topology of closed sets on X (by MetOs075). U
  is a finite subset of V (by SetSet082). Indeed V is a set such that every element of U lies in V.
  Hence \bigcup U is an element of V (by SetTop115). Indeed X is a set. Thus \bigcup U is closed.
qed.


Corollary MetOs095. Let X be a metric space and A,B be closed subsets of X. Then A \cup B is closed.

Proof.
  Define V = {C | C is a closed subset of X}. V is a topology of closed sets on X (by MetOs075). A,B
  are elements of V. Hence A \cup B lies in V (by SetTop120). Indeed X is a set.
qed.


Proposition MetOs100. Let X be a metric space and U be a nonempty set. Assume that every element of
U is a closed subset of X. Then \bigcap U is a closed subset of X.

Proof.
  Define V = {A | A is a closed subset of X}. V is a topology of closed sets on X (by MetOs075). U
  is a nonempty subset of V (by SetSet082). Indeed V is a set such that every element of U lies in
  V. Hence \bigcap U is an element of V (by SetTop125). Indeed X is a set. Thus \bigcap U is closed.
qed.


Corollary MetOs105. Let X be a metric space and A,B be closed subsets of X. Then A \cap B is closed.

Proof.
  Define V = {C | C is a closed subset of X}. V is a topology of closed sets on X (by MetOs075). A,B
  are elements of V. Hence A \cap B lies in V (by SetTop130). Indeed X is a set.
qed.


# 3. Neighbourhoods

#[prove off][check off]
[read ForTheLib/Sets/filters.ftl]
#[prove on][check on]

Axiom MetOs120. Let X be a metric space and x \in X. Let U be an entity. U is a neighbourhood of
x iff U is a subset of X such that B(x,epsilon) \subseteq U for some positive real number
epsilon.


Proposition MetOs125. Let X be a metric space and x \in X. Let epsilon be a positive real number.
Then B(x,epsilon) is a neighbourhood of x.

Proof.
  B(x,epsilon) is a subset of X. Thus B(x,delta) \subseteq B(x,epsilon) for some positive
  real number delta. Hence the thesis (by MetOs120).
qed.


Proposition MetOs130. Let X be a metric space and A be a subset of X. A is open iff A is a
neighbourhood of every point of A.

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
      Let x \in A. A is a neighbourhood of x. x \in X. Indeed A is a subset of X. Take a
      positive real number epsilon such that B(x,epsilon) \subseteq A (by MetOs120).
    end.

    Hence the thesis (by MetOs005). Indeed A is a subset of X.
  end.
qed.


Proposition MetOs135. Let X be a metric space and x \in X. Let U be a neighbourhood of x. Then
x \in U.

Proof.
  Take a positive real number epsilon such that B(x,epsilon) \subseteq U (by MetOs120).
  x \in B(x,epsilon) (by MetOs001). Every element of B(x,epsilon) is an element of U (by
  FoundCl005). Indeed B(x,epsilon) is a class.
qed.


Proposition MetOs140. Let X be a metric space and U be a class. Let x \in X. Assume that U =
{N | N is a neighbourhood of x}. Then U is a filter on X.

Proof. [prove off] qed.


Proposition MetOs142. Let X be a metric space and x,y \in X. Assume that x \neq y. Then there are
positive real numbers epsilon,delta such that B(x,epsilon) and B(y,delta) are disjoint.

Proof. [prove off] qed.
