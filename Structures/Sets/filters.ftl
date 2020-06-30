#
# Filters
# (Marcel Schütz, 2020)
#

#[prove off][check off]
[read ForTheLib/Sets/set-systems.ftl]
#[prove on][check on]


Definition SetFil000. Let X be a set. A filter on X is a system of sets F such that

  \emptyset \notin F and X \in X and

  F is closed under finite intersections and

  for all sets A,B if A \in F and B \supseteq A then B \in F.


Definition SetFil005. Let X be an entity. An ultrafilter on X is a filter U on X such that for all
subsets A of X we have A \in U or X \setminus A \in U.
