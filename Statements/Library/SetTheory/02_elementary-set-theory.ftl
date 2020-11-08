# 2 Elementary set theory

[read FLib/Statements/Library/statements.ftl]
[read FLib/Statements/Library/SetTheory/01_collections.ftl]


Signature 0201. A zet is a collection. Let x,y,z denote zets.

Definition 0202. Let C be a collection. A subset of C is a zet x such that
x \subseteq C.

Definition 0203. Let C be a collection. A superset of C is a zet x such that
x \supseteq C.


Definition 0204. An element is an object a such that a is an urelement or a is a
zet.


# 2.2 Extensionality

Proposition 0205. If x \subseteq y and y \subseteq x then x = y.

Corollary 0206. If y = {u | u \in x} then x = y.

Proof.
  Assume y = {u | u \in x}. Then every element of y is an element of x and every
  element of x is an element of y. Hence y \subseteq y and x \subseteq y. Thus
  x = y.
qed.


# 2.2 Separation

Let P denote a statement.

Axiom 0207. Assume that P is nullary or P is unary. Then there is a zet y such
that for all objects u we have u \in y iff u \in x and P(u).


Corollary 0208. Assume that P is nullary or P is unary. Then there is a zet y
such that y = {u in x | P(u)}.


Lemma 0209. Assume that P is nullary or P is unary. Let x,y be zets. Assume
x = {u | P(u)} and y = {u | P(u)}. Then x = y.


# 2.3 Set existence and the empty set

Definition 0210. x is empty iff x has no elements.

Axiom 0211. There is a zet.


Lemma 0212. There is an empty zet.

Proof.
  Take a zet x.

  [prove off]
  Define P = {u | FALSE}. P is a proposition.
  [prove on]

  Take a zet y such that y = {u in x | P(u)}. Then y is empty.
qed.


Lemma 0213. If x and y are empty then x = y.

Proof.
  Assume that x and y are empty. Then every element of x is an element of y and
  every element of y is an element of x. Hence x \subseteq y and y \subseteq x.
  Thus x = y.
qed.


Definition 0214. \emptyset is the empty zet.


# 2.4 Intersections and complements

Lemma 0215. There is a zet z such that z = {u | u \in x and u \in y}.

Proof.
  [prove off]
  Define P = {u | u \in y}. P is unary.
  [prove on]

  Take a zet z such that z = {u in x | P(u)} (by 0208). Then z = {u | u \in x
  and u \in y}.
qed.


Definition 0216. x \cap y is the zet z such that z = {u | u \in x and u \in y}.


Lemma 0217. There is a zet z such that z = {u | u \in x and u \notin y}.

Proof.
  [prove off]
  Define P = {u | u \notin y}. P is unary.
  [prove on]

  Take a zet z such that z = {u in x | P(u)} (by 0208). Then z = {u | u \in x
  and u \notin y}.
qed.


Definition 0218. x \setminus y is the zet z such that z = {u | u \in x and
u \notin y}.


# 2.5 Unions

Axiom 0219. There is a zet z such that z = {u | u \in x or u \in y}.

Definition 0220. x \cup y is the zet z such that z = {u | u \in x or u \in y}.


# 2.6 Pairs and singleton sets

Let a,b denote elements.

Axiom 0221. There is a zet x such that x = {u | u = a or u = b}.

Definition 0222. `{a,b}` is the zet x such that x = {u | u = a or u = b}. Let
the unordered pair of a and b stand for `{a,b}`.


Lemma 0223. There is a zet x such that x = {u | u = a}.

Proof.
  `{a,a}` is a zet and `{a,a}` = {u | u = a}.
qed.


Definition 0224. Let a be an element. `{a}` is the zet x such that `{a}` =
{u | u = a}. Let the singleton set of a stand for `{a}`.
