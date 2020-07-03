#
# Continuous functions
# (Marcel Schütz, 2020)
#

#[prove off][check off]
[read FLib/Structures/MetricSpaces/open-sets.ftl]
#[prove on][check on]


Axiom MetCont000. Let X,Y be metric spaces and a \in X. Let f be a map from X to Y. f is continuous
at a iff for all positive real numbers epsilon there is a positive real number delta such that for
all x \in X if dist(x,a) < delta then dist(f(x),f(a)) < epsilon.


Axiom MetCont005. Let X,Y be metric spaces and f be a map from X to Y. f is continuous iff f is
continuous at every element of X.


Proposition MetCont010. Let X be a metric space. id_{X} is continuous.

Proof.
  id_{X} is a map from X to X.

  id_{X} is continuous at every element of X.
  proof.
    Let a \in X.

    For all positive real numbers epsilon there is a positive real number delta such that for all
    x \in X if dist(x,a) < delta then dist(id_{X}(x),id_{X}(a)) < epsilon.
    proof.
      Let epsilon be a positive real number. Take a positive real number delta such that delta =
      epsilon.
    end.

    Hence id_{X} is continuous at a (by MetCont000).
  end.

  Then we have the thesis (by MetCont005). 
qed.

Proposition MetCont015. Let X,Y,Z be metric spaces. Let f be a continuous map from X to Y and g be a
continuous map from Y to Z. Then g \circ f is continuous.

Proof. [prove off] qed.


Theorem MetCont020. Let X,Y be metric spaces and f be a map from X to Y. f is continuous iff
f^{-1}[A] is open for all open subsets A of Y.

Proof. [prove off] qed.


Theorem MetCont025. Let X,Y be metric spaces and f be a map from X to Y. f is continuous iff
f^{-1}[A] is closed for all closed subsets A of Y.

Proof. [prove off] qed.


Theorem MetCont030. Let X,Y be metric spaces and f be a map from X to Y. Let x \in X. f is
continuous at x iff f^{-1}[U] is a neighbourhood of x for all neighbourhoods U of f(x).

Proof. [prove off] qed.
