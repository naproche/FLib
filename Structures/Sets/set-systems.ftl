#
# Set systems
# (Marcel Schütz, 2020)
#

#[prove off][check off]
[read FLib/Structures/Sets/cardinality.ftl]
#[prove on][check on]


# 1. Definition

Definition SetSs000. A system of sets is a set X such that every element of X is a set.


# 2. Closed under finite unions/intersections

Definition SetSs005. Let X be a system of sets. X is closed under finite intersections iff
\bigcap F \in X for all finite nonempty subsets F of X.


Proposition SetSs010. Let X be a system of sets. X is closed under finite intersections iff
x \cap y \in X for all x,y \in X.

Proof.
  If X is closed under finite intersections then x \cap y \in X for all x,y \in X.
  proof.
    Assume that X is closed under finite intersections. Let x,y \in X. Define F = {u | u = x or u =
    y}. F = `{x,y}`. \bigcap F = x \cap y. F is a set. Indeed x,y are sets.

    Case x = y.
      Then F = `{x}`. Hence F \sim `{0}`.
    end.

    Case x \neq y.
      Then F = `{x,y}`. Hence F \sim `{0,1}`. Thus F is finite. F is a subset of X. Indeed every
      element of F is an element of X.
    end.
  end.

  If x \cap y \in X for all x,y \in X then X is closed under finite intersections.
  proof. [prove off] end.
qed.


Definition SetSs015. Let X be a system of sets. X is closed under finite unions iff
\bigcup F \in X for all finite nonempty subsets F of X.


Proposition SetSs020. Let X be a system of sets. X is closed under finite unions iff x \cup y \in X
for all x,y \in X.

Proof. [prove off] end.


# 3. Closed under countable unions/intersections

Definition SetSs025. Let X be a system of sets. X is closed under countable intersections iff
\bigcap C \in X for all countable nonempty subsets C of X.

Definition SetSs030. Let X be a system of sets. X is closed under countable unions iff
\bigcup C \in X for all countable nonempty subsets C of X.


# 4. Closed under arbitrary unions/intersections

Definition SetSs035. Let X be a system of sets. X is closed under arbitrary intersections iff
\bigcap V \in X for all nonempty subsets V of X.

Definition SetSs040. Let X be a systems of sets. X is closed under arbitrary unions iff
\bigcup V \in X for all nonempty subsets V of X.


# 5. Misc

Proposition SetSs045. Let x be an entity. Every subset of the powerset of x is a systems of sets.

Proof.
  Let y be a subset of Pow(x). Then y is a set and every element of y is a set.
qed.
