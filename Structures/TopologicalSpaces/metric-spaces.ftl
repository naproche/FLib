#
# The topology of metric spaces
# (Marcel Schütz, 2020)
#

#[prove off][check off]
[read FLib/Structures/TopologicalSpaces/continuous-maps.ftl]
[read FLib/Structures/MetricSpaces/open-sets.ftl]
#[prove on][check on]


# 1. Interpreting metric spaces as topological spaces

Signature TopMet000. Top_{3} is a function of MET.

Axiom TopMet005. Let M be a metric space. Let U be a class such that U = {A | A is an open subset of
M}. Top_{3}(M) = (M,U)_{TOP}.


Axiom TopMet010. Let M be a metric space. M_{TOP} = Top_{3}(M).

Corollary TopMet015. Let M be a metric space. Let U be a class such that U = {A | A is an open
subset of M}. Then M_{TOP} = (M,U)_{TOP}.

Proof.
  We have the thesis (by TopMet005, TopMet010).
qed.


Proposition TopMet020. Let M be a metric space. Then M_{TOP} is a topological space.

Proof.
  Define U = {A | A is an open subset of M}. Then U is a topology on M (by MetOs040). Hence
  (M,U)_{TOP} is a topological space. M_{TOP} = (M,U)_{TOP} (by TopMet015).
qed.


Proposition TopMet022. Let M be a metric space. dom(M_{TOP}) = M.

Proof. [prove off] qed.


Proposition TopMet025. Let M be a metric space and A be an entity. A is an open subset of M iff
M_{TOP}[A] is an open subset of M_{TOP}.

Proof. [prove off] qed.


Proposition TopMet030. Let M be a metric space and A be an entity. A is a closed subset of M iff
M_{TOP}[A] is a closed subset of M_{TOP}.

Proof. [prove off] qed.


# 1.1 Identifying metric spaces with topological spaces

Axiom TopMet038. Every metric space is a topological space.


# 2. Topological properties of metric spaces

Proposition TopMet000. Let M be a metric space. Assume that dist(x,y) = 1 for all x,y \in M such
that x \neq y. Then M is discrete.

Proof.
  Every subset of M is open.
  proof.
    Let A be a subset of M.

    For all a \in A there exists a positive real number r such that B(a,r) \subseteq A.
    proof.
      Let a be an element of A. Then a lies in M. 1/2 is a positive real number such that
      0 < 1/2 < 1 (by AnaRe192). Hence B(a,1/2) = {x in M | dist(a,x) < 1/2} (by MetOs000).

      B(a,1/2) = {a}.
      proof.
        a is an element of B(a,1/2).

        Every element of B(a,1/2) is equal to a.
        proof.
          Let x \in B(a,1/2).

          Case x = a. Obvious.

          Case x \neq a.
            Then dist(a,x) = 1. Hence dist(a,x) > 1/2. Then dist(a,x) is not less than 1/2.
          end.
        end.
      end.

      Hence B(a,1/2) \subseteq A (by FoundCl000). Indeed A is a class.
    end.

    Thus A is open (by MetOs005).
  end.

  Then we have the thesis (by TopCont030). Indeed M is a topological space.
qed.


Proposition TopMet005. Let M be a metric space. M is indiscrete iff M has at most one element.

Proof.
  If M is indiscrete then M has at most one element.
  proof.
    Assume that M is indiscrete. Then for all open subsets A of M we have A = \emptyset or A = M (by
    TopCont035). Indeed M is a topological space. Assume that M does not has at most one element. 
    Then M has an element and there is no a \in M such that M = {a} (by SetCard080). Indeed M is a
    set. Hence we can take elements a,b of M such that a \neq b. Take a real number r such that r =
    dist(a,b) / 2. r is positive and r < dist(a,b) (by AnaRe193). Indeed dist(a,b) is a positive
    real number (by MetMs138).

    B(a,r) = {x in M | dist(a,x) < r} and B(b,r) = {x in M | dist(b,x) < r} (by MetOs000). B(a,r)
    and B(b,r) are open subsets of M. dist(a,b) is not less than r. Moreover dist(b,a) is not less
    than r. Hence a \notin B(b,r) and b \notin B(a,r). Thus B(a,r) \neq B(b,r). Contradiction.
  end.

  If M has at most one element then M is indiscrete.
  proof.
    Assume that M has at most one element. (1) Then M has no element or M = {a} for some a \in M (by
    SetCard080). Indeed M is a set.

    For all open subsets A of M we have A = \emptyset or A = M.
    proof.
      Let A be an open subset of M.

      Case M has no elements. Obvious.

      Case M = {a} for some a \in M. Obvious.

      Hence the thesis (by 1).
    end.
  end.
qed.


Proposition TopMet045. Every metric space is Hausdorff.

Proof.
  Let M be a metric space.

  For all x,y \in M if x \neq y then there are disjoint sets U,V such that U is a neighbourhood of x
  and V is a neighbourhood of y.
  proof.
    Let x,y \in M. Assume that x \neq y.Take positive real numbers epsilon,delta such that
    B(x,epsilon) and B(y,delta) are disjoint (by MetOs142). B(x,epsilon) is a neighbourhood of x and
    B(y,delta) is a neighbourhood of y. B(x,epsilon) and B(y,delta) are sets.
  end.

  M is a topological space. Hence M satisfies T2 (by TopSep025). Thus M is Hausdorff.
qed.


Corollary TopMet060. Let M be a metric space and x \in M. Then `{x}` is closed.

Proof.
  M is Hausdorff. Hence M satisfies T1.
qed.
