#
# Metric spaces
# (Marcel Schütz, 2020)
#

#[prove off]
[read ForTheLib/RealNumbers/real-valued-functions.ftl]
[read ForTheLib/Foundations/structures.ftl]
[read ForTheLib/Foundations/types.ftl]
#[prove on]


# 1. Distance functions and metrics

Definition MetMs000. Let X be an object. A distance function on X is a binary function d on X such
that

  d is nonnegative and realvalued and

  d is positive definite on X and

  d is symmetric on X and

  d is subadditive on X.


Definition MetMs001. Let X be a set. A metric on X is a distance function d on X such that
dom(d) = X \times X.


Lemma MetMs002. Let X be a set and d be a metric on X. Let x,y \in X. Then (x,y) \in dom(d).

Proof.
  d is a binary function on X. Hence the thesis (by AnaRvf094).
qed.


# 2. Metric spaces

Signature MetMs010. A metric space is a small structure.


Signature MetMs024. dist is a distance function on every metric space.

Let the distance of x and y stand for dist(x,y).


Lemma MetMs025. Let X be a metric space and x,y \in X. Then (x,y) \in dom(dist).

Proof.
  dist is a binary function on X. Therefore the thesis (by AnaRvf094).
qed.


Proposition MetMs026. Let X be a metric space and x,y \in X. Then dist(x,y) \geq 0.

Proof.
  dist is a realvalued function. Hence dist \geq 0 iff dist(c) \geq 0 for all c \in dom(dist) (by
  AnaRvf088). Indeed 0 is a real number. dist is nonnegative. Thus dist(c) \geq 0 for all
  c \in dom(dist). (x,y) \in dom(dist).
qed.


Proposition MetMs027. Let X be a metric space and x,y \in X. Assume x \neq y. Then dist(x,y) > 0.

Proof.
  dist(x,y) \geq 0. Hence dist(x,y) = 0 or dist(x,y) > 0 (by AnaRe219). Indeed dist(x,y) and 0 are
  real numbers.
qed.


Proposition MetMs028. Let X be a metric space and x,y,z \in X. Then
dist(x,z) \leq dist(x,y) + dist (y,z).

Proof.
  dist is a realvalued function that is subadditive on X. dist is subadditive on X iff
  dist(a,c) \leq dist(a,b) + dist(b,c) for all a,b,c \in X (by AnaRvf100).
qed.


Proposition MetMs029. Let X be a metric space and x,y \in X. Then dist(x,y) is a real number.


Proposition MetMs030. Let X be a metric space and x,y \in X. Then dist(x,y) = dist(y,x).

Proof.
  dist is a realvalued function that is symmetric on X. dist is symmetric on X iff
  dist(a,b) = dist(b,a) for all a,b \in X (by AnaRvf095).
qed.


Proposition MetMs031. Let X be a metric space and x \in X. Then dist(x,x) = 0.

Proof.
  dist is realvalued function that is positive definite on X.
qed.


# 3. MET

Signature MetMs040. MET is a type.

Axiom MetMs045. MET = {X | X is a metric space}.


Signature MetMs050. MET_{metric} is a function of MET.

Axiom MetMs055. Let M be a metric space. Let X be the domain of M. Let d be a function of X \times X
such that d(x,y) = dist(M(x),M(y)) for all x,y \in X. Then MET_{metric}(M) = (X,d).


Proposition MetMs060. MET_{metric} is an instantiation of MET.

Proof. [prove off] qed.


Proposition MetMs065. Let M be a metric space and X be the domain of M. Let d be a function of
X \times X such that d(x,y) = dist(M(x),M(y)) for all x,y \in X. Then d is a metric on X.

Proof. [prove off] qed.


Proposition MetMs065. Let X be a set and d be a metric on X. Then (X,d) is an instance of MET.

Proof. [prove off] qed.


Proposition MetMs070. Let M,N be metric spaces. If

  the domain of M is equal to the domain of N and

  dist(M(x),M(y)) = dist(N(x),N(y)) for all elements x,y of the domain of M

then M = N.

Proof. [prove off] qed.
