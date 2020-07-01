#
# Metrizable spaces
# (Marcel Schütz, 2020)
#

[prove off][check off]
[read ForTheLib/TopologicalSpaces/continuous-maps.ftl]
[read ForTheLib/MetricSpaces/continuous-maps.ftl]
[prove on][check on]


# 1. The topology of a metric space

Proposition TopMet000. Let M be a metric space. Assume that dist(x,y) = 1 for all x,y \in M such
that x \neq y. Then M is discrete.

Proof. [prove off] qed.


Proposition TopMet005. Let M be a metric space. Assume that M is indiscrete. Then M has at most one
element.

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


# 2.1 Identifying metric spaces with topological spaces

Axiom TopMet038. Every metric space is a topological space.


# 3. Metrizable spaces

Signature. Let d,a,r be entities. B_{d}(a,r) is a set.

Axiom. Let X be a topological space and d be a metric on X. Let a \in X and r be a positive real
number. Then B_{d}(a,r) = {x in X | d(a,x) < r}.

Signature. Let U,d be entities. U is induced by d is a statement.

Axiom TopMetxxx. Let X be a set and U be a topology on X. Let d be a metric on X. U is induced
by d iff for all A \in U and all x \in A there is a positive real number r such that
B_{d}(x,r) \subseteq A.

Signature. Let X be a topological space. X is metrizable is a statement.

Axiom TopMet040. Let X be a topological space and U be a class such that U = {A | A is an open
subset of X}. X is metrizable iff U is induced by some metric on X.


Proposition. Every metric space is metrizable.

Proof. [prove off] qed.


Axiom. Every metrizable topological space is a metric space.


Proposition TopMet045. Every metrizable topological space is Hausdorff.

Proof.
  Let M be a metrizable topological space. Then M is a metric space.

  For all x,y \in M if x \neq y then there are disjoint sets U,V such that U is a neighbourhood of x
  and V is a neighbourhood of y.
  proof.
    Let x,y \in M. Assume that x \neq y.Take positive real numbers epsilon,delta such that
    B(x,epsilon) and B(y,delta) are disjoint (by MetOs142). B(x,epsilon) is a neighbourhood of x and
    B(y,delta) is a neighbourhood of y. B(x,epsilon) and B(y,delta) are sets.
  end.

  M is a topological space. Hence M satisfies T2 (by TopSep025). Thus M is Hausdorff.
qed.


Corollary TopMet050. Any metric space is Hausdorff.

Corollary TopMet055. Let X be a metrizable topological space and x \in X. Then `{x}` is closed.

Corollary TopMet060. Let M be a metric space and x \in M. Then `{x}` is closed.
