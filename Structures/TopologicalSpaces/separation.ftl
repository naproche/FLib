#
# Separation axioms
# (Marcel Schütz, 2020)
#

#[prove off][check off]
[read FLib/Structures/TopologicalSpaces/topological-spaces.ftl]
#[prove on][check on]


# 1. Separation axioms

Signature TopSep000. T0 is an axiom.

Axiom TopSep005. Let X be a topological space. X satisfies T0 iff for all x,y \in X if x \neq y
then there is a neighbourhood of x that not contains y or there is a neighbourhood of y that does
not contain x.


Signature TopSep010. T1 is an axiom.

Axiom TopSep015. Let X be a topological space. X satisfies T1 iff for all x,y \in X if x \neq y
then there is a neighbourhood of x that does not contain y and there is a neighbourhood of y that
does not contain x.


Signature TopSep020. T2 is an axiom.

Axiom TopSep025. Let X be a topological space. X satisfies T2 iff for all x,y \in X if x \neq y
then there are disjoint sets U,V such that U is a neighbourhood of x and V is a neighbourhood of y.


Definition TopSep030. A Hausdorff space is a topological space that satisfies T2.

Let X is Hausdorff stand for X is a Hausdorff space.


# 2. Consequences

Proposition TopSep035. Let X be a topological space. If X satisfies T1 then X satisfies T0.

Proof.
  Assume that X satisfies T1. For all x,y \in X if x \neq y then there is a neighbourhood of x
  that does not contain y (by TopSep015). Hence the thesis (by TopSep005).
qed.


Proposition TopSep040. Let X be a topological space. If X is Hausdorff then X satisfies T1.

Proof.
  Assume that X is Hausdorff. Then X satisfies T2.

  For all x,y \in X if x \neq y then there is a neighbourhood of x that does not contain y and there
  is a neighbourhood of y that does not contain x.
  proof.
    Let x,y \in X. Assume that x \neq y. Take disjoint sets U,V such that U is a neighbourhood of x
    and V is a neighbourhood of y (by TopSep025).
  end.

  Hence X satisfies T1 (by TopSep015).
qed.


Proposition TopSep045. Let X be a topological space. X satisfies T1 iff `{x}` is closed for all
elements x of X.

Proof.
  If X satisfies T1 then `{x}` is closed for all x \in X.
  proof.
    Assume that X satisfies T1. Let x \in X. `{x}` = {x}.

    For all elements y of X that are not equal to x there is an open subset A of X such that y \in A
    and x \notin A.
    proof.
      Let y \in X. Assume that y \neq x. Take a neighbourhood U of y that does not contain x (by
      TopSep015). Take an open subset A of U that contains y (by TopTop200). U is a subset of X (by
      TopTop200). Thus A,U and X are sets. Every element of A lies in U (by SetSet081). Hence x does
      not lie in A. Every element of A lies in X. Indeed every element of U lies in X.
    end.

    X \setminus `{x}` = {y in X | y \neq x}.

    Define f(y) = choose an open subset A of X such that y \in A and x \notin A in A for y in
    X \setminus `{x}`.

    \bigcup range(f) = X \setminus `{x}`.
    proof.
      Every element of \bigcup range(f) lies in X \setminus `{x}`.
      proof.
        Let y \in \bigcup range(f). Then y \in f(y). f(y) is a subset of X such that x \notin f(y).
        Hence y \in X. Indeed f(y) and X are sets. Furthermore y \neq x.
      end.

      Every element of X \setminus `{x}` lies in \bigcup range(f).
      proof.
        Let y \in X \setminus `{x}`. Then y \in X and y \neq x. y is an element of the domain of f.
        Hence y \in f(y). Thus y is an element of some element of range(f). Indeed range(f) =
        {f(u) | u \in dom(f)}.
      end.
    end.

    Every element of range(f) is an open subset of X. range(f) is a set (by SetSet084). Indeed
    X \setminus `{x}` is a set. Hence \bigcup range(f) is open (by TopTop090). `{x}` is a subset of
    X. Indeed `{x}` is a set and every element of `{x}` lies in X. Thus `{x}` is closed (by
    TopTop065).
  end.

  If `{x}` is closed for all x \in X then X satisfies T1.
  proof.
    Assume that `{x}` is closed for all x \in X.

    For all u,v \in X if u \neq v then there is a neighbourhood of u that does not contain v and
    there is a neighbourhood of v that does not contain u.
    proof.
      Let u,v \in X. Assume that u \neq v. `{u}` is a set and every element of `{u}` lies in X.
      `{v}` is a set and every element of `{v}` lies in X. Moreover X is a set.

      X \setminus `{u}` does not contain u. `{u}` is a subset of X. Hence X \setminus `{u}` is an
      open subset of X (by TopTop065). Indeed X \setminus `{u}` is a subset of X. Thus
      X \setminus `{u}` is an open subset of X \setminus `{u}` that contains v. Hence
      X \setminus `{u}` is a neighbourhood of v (by TopTop200).

      X \setminus `{v}` does not contain v. `{v}` is a subset of X (by SetSet081). Hence
      X \setminus `{v}` is an open subset of X (by TopTop065). Indeed X \setminus `{v}` is a subset
      of X. Thus X \setminus `{v}` is an open subset of X \setminus `{v}` that contains u. Hence
      X \setminus `{v}` is a neighbourhood of u (by TopTop200).
    end.

    Then we have the thesis (by TopSep015).
  end.
qed.
