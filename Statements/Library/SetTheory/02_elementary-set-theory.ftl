# 2 Elementary set theory

[read FLib/Statements/Library/statements.ftl]
[read FLib/Statements/Library/SetTheory/01_collections.ftl]


Signature. A zet is a collection. Let x,y,z denote zets.

Definition. A subset of x is a zet y such that y \subseteq x.


# 1.1. Extensionality

Proposition. If x \subseteq y and y \subseteq x then x = y.


# 1.2. The empty set

Definition. x is empty iff x has no elements.

Axiom. There is an empty zet.


Lemma. If x and y are empty then x = y.

Proof.
  Assume that x and y are empty. Then every element of x is an element of y and
  every element of y is an element of x. Hence x \subseteq y and y \subseteq x.
  Thus x = y.
qed.


Definition. \emptyset is the empty zet.


# 1.3. Separation

Let P denote a statement.

Axiom. Assume that P is nullary or P is unary. Then there is a zet y such that
for all objects u we have u \in y iff u \in x and P(u).


Corollary foo. Assume that P is nullary or P is unary. Then there is a zet y
such that y = {u in x | P(u)}.


Lemma. Assume that P is nullary or P is unary. Let x,y be zets. Assume
x = {u | P(u)} and y = {u | P(u)}. Then x = y.


# 1.4 Intersections and complements

Proposition. There is a zet z such that z = {u | u \in x and u \in y}.

Proof.
  [prove off]
  # P(u) iff u \in y.
  Define P = {u | u \in y}.
  P is unary.
  [prove on]

  Take a zet z such that z = {u in x | P(u)} (by foo). Then z = {u | u \in x and
  u \in y}.
qed.


Axiom. x \cap y is the zet z such that z = {u | u \in x and u \in y}.


Lemma. There is a zet z such that z = {u | u \in x and u \notin y}.

Proof.
  [prove off]
  # P(u) iff u \notin y.
  Define P = {u | u \notin y}.
  P is unary.
  [prove off]

  Take a zet z such that z = {u in x | P(u)} (by foo). Then z = {u | u \in x and
  u \notin y}.
qed.


Axiom. x \setminus y is the zet z such that z = {u | u \in x and u \notin y}.


# 1.5 Unions

Axiom. There is a zet z such that z = {u | u \in x or u \in y}.

Axiom. x \cup y is the zet z such that z = {u | u \in x or u \in y}.
