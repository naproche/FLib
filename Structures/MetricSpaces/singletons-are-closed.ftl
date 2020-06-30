#
# Signletonsets are closed in metric spaces (proof 2)
# (Marcel Schütz, 2020)
#

#[prove off][check off]
[read ForTheLib/MetricSpaces/open-sets.ftl]
#[prove on][check on]


Proposition MetOs110. Let X be a metric space and x \in X. `{x}` is closed.
Proof.
  Case X = `{x}`. Obvious.

  Case X \neq `{x}`.
    X \setminus `{x}` is a subset of X.
    proof.
      X \setminus `{x}` is a class and X is a set. Every element of X \setminus `{x}` lies in X.
      Hence X \setminus `{x}` \subseteq X (by FoundCl005). Then we have the thesis (by SetSet155).
    end.

    (1) For all y \in X \setminus `{x}` there exists a positive real number epsilon such that
    B(y,epsilon) \subseteq X \setminus `{x}`.
    proof.
      Let y \in X \setminus `{x}`. `{x}` = {x}. x,y \in X. y \neq x. Hence dist(x,y) > 0 (by
      MetMs137). Thus dist(x,y) is a positive real number. Every element of B(y,dist(x,y)) lies in X
      (by MetOs000).

      No element of B(y,dist(x,y)) lies in `{x}`.
      proof.
        Assume the contrary. Take an element z of B(y,dist(x,y)) that lies in `{x}`. Then z = x.
        Hence dist(z,y) = dist(x,y). dist(z,y) = dist(y,z) (by MetMs140). Hence
        dist(y,z) = dist(x,y). But dist(y,z) < dist(x,y) (by MetOs000). Indeed z \in B(y,dist(x,y)).
        Contradiction.
      end.

      X \setminus `{x}` = {y in X | y \notin `{x}`} (by FoundStr050). Indeed X is a structure and
      `{x}` is a class. Hence every element of B(y,dist(x,y)) lies in X \setminus `{x}`. Thus
      B(y,dist(x,y)) \subseteq X \setminus `{x}` (by FoundCl005). Indeed B(y,dist(x,y)) is a class.
    end.

    Take an entity Y such that Y = X \setminus `{x}`. Y is a subset of X. Hence Y is open iff for
    all y \in Y there exists a positive real number epsilon such that B(y,epsilon) \subseteq Y (by
    MetOs005). Hence Y is open. Thus X \setminus `{x}` is open.

    [ontored on]
    `{x}` is a subset of X (by SetSet082). Indeed `{x}` and X are sets such that every element of
    `{x}` lies in X.
    [ontored off]

    Hence the thesis (by MetOs055).
  end.
qed.
