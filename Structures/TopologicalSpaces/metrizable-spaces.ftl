#
# Metrizable spaces
# (Marcel Schütz, 2020)
#

#[prove off][check off]
[read ForTheLib/TopologicalSpaces/continuous-maps.ftl]
[read ForTheLib/MetricSpaces/continuous-maps.ftl]
#[prove on][check on]


# 1. The topology of a metric space

Proposition TopMet000. Let M be a metric space. Assume that dist(x,y) = 1 for all x,y \in M such
that x \neq y. Then every subset of M is open.

Proof. [prove off] qed.


Proposition TopMet005. Let M be a metric space. Assume that for all open subsets A of M we have
A = \emptyset or A = M. Then M has at most one element.

Proof. [prove off] qed.


# 2. Interpreting metric spaces as topological spaces

Signature TopMet010. Top_{3} is a function of MET.

Axiom TopMet015. Let M be a metric space. Let U be a class such that U = {A | A is an open subset of
M}. Top_{3}(M) = Top_{1}(M,U).


Proposition TopMet020. Let M be a metric space. Then Top_{3}(M) is a topological space.

Proof.
  Define U = {A | A is an open subset of M}. Then U is a topology on M (by MetOs040). Hence 
  Top_{1}(M,U) is a topological space. Top_{3}(M) = Top_{1}(M,U) (by TopMet015).
qed.


Proposition TopMet022. Let M be a metric space. dom(Top_{3}(M)) = M.

Proof. [prove off] qed.


Proposition TopMet025. Let M be a metric space and A be an entity. A is an open subset of M iff
Top_{3}(M)[A] is an open subset of Top_{3}(M).

Proof. [prove off] qed.


Proposition TopMet030. Let M be a metric space and A be an entity. A is a closed subset of M iff
Top_{3}(M)[A] is a closed subset of Top_{3}(M).

Proof. [prove off] qed.


Proposition TopMet035. Let M,N be metric spaces and f be a function from M to N. f is continuous iff
(Top_{1}^{-1}(N) \circ f) \circ Top_{3}^{-1}(M) is continuous.

Proof. [prove off] qed.


# 2.1 Metrizable spaces

Definition TopMet040. Let X be a topological space. X is metrizable iff there is a metric space M
such that X = Top_{3}(M).


Proposition TopMet045. Let M be a metric space. Top_{3}(M) is Hausdorff.

Proof.
  Take a topological space X such that X = Top_{3}(M). X is a structure such that dom(X) = M.

  For all x,y \in X if x \neq y then there are disjoint sets U,V such that U is a neighbourhood of x
  and V is a neighbourhood of y.
  proof.
    Let x,y \in X. Assume that x \neq y. X is a bijection between M and X (by FoundStr010). Take
    a,b \in M such that a = X^{-1}(x) and b = X^{-1}(y). Indeed X is a surjective map. Then
    a \neq b (by FoundMap179b). Take positive real numbers epsilon,delta such that
    B(a,epsilon) and B(b,delta) are disjoint (by MetOs142). B(a,epsilon) and B(b,delta) are open
    subsets of M (by MetOs020). Hence X[B(a,epsilon)] and X[B(b,delta)] are open subsets of X.
    Moreover X[B(a,epsilon)] and X[B(b,delta)] are disjoint sets. a \in B(a,epsilon) and
    b \in B(b,delta). x = X(a) and y = X(b) (by FoundMap179c). Thus x \in X[B(a,epsilon)] and
    y \in X[B(b,delta)] (by FoundMap188). Indeed X is a map and B(a,epsilon),B(b,delta) are
    subclasses of M. Therefore X[B(a,epsilon)] is a neighbourhood of x and X[B(b,delta)] is a
    neighbourhood of y.
  end.

  Hence X satisfies T2 (by TopSep025). Thus X is Hausdorff.
qed.


Corollary TopMet050. Any metrizable topological space is Hausdorff.

Corollary TopMet055. Let X be a metrizable topological space and x be an element of X. Then `{x}` is
closed.


Corollary TopMet060. Let M be a metric space and x \in M. Then `{x}` is closed.

Proof.
  Take a topological space X such that X = Top_{3}(M). X is metrizable. Hence X is Hausdorff. Thus
  X satisfies T1. X[`{x}`] = `{X(x)}`. X(x) is an element of X. Hence X[`{x}`] is closed (by
  TopSep045). `{X(x)}` and X are a sets such that every element of `{X(x)}` lies in X. Thus `{X(x)}`
  is a subset of X (by SetSet081)Then we have the thesis (by TopMet030).
qed.
