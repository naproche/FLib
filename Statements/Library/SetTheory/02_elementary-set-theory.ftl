# 2 Elementary set theory

[read FLib/Statements/Library/statements.ftl]
[read FLib/Statements/Library/SetTheory/01_collections.ftl]


Signature 0201. A zet is a collection. Let x,y,z denote zets.

Definition 0202. Let C be a collection. A subset of C is a zet x such that
x /subseteq C.

Definition 0203. Let C be a collection. A superset of C is a zet x such that
x /supseteq C.


Definition 0204. An element is an object a such that a is an urelement or a is a
zet.


# 2.1 Separation

Let P denote a statement.

Axiom 0205. Assume that P has at most one free variable. Then there is a zet y
such that y = {u in x | P(u)}.


Lemma 0206. Assume that P has at most one free variable. Let x,y be zets. Assume
x = {u | P(u)} and y = {u | P(u)}. Then x = y.


# 2.2 Set existence and the empty set

Axiom 0208. There is a zet.


Lemma 0209. There is an empty zet.

Proof.
  Take a zet x.

  [prove off]
  Define P = {u | FALSE}. P is a statement.
  [/prove]

  Take a zet y such that y = {u in x | P(u)}. Then y is empty.
qed.


Lemma 0210. If x and y are empty then x = y.

Proof.
  Assume that x and y are empty. Then every element of x is an element of y and
  every element of y is an element of x. Hence x /subseteq y and y /subseteq x.
  Thus x = y.
qed.


Definition 0211. /emptyset is the empty zet.


# 2.3 Intersections and complements

Lemma 0212. There is a zet z such that z = {u | u /in x and u /in y}.

Proof.
  [prove off]
  Define P = {u | u /in y}. P has at most one free variable.
  [/prove]

  Take a zet z such that z = {u in x | P(u)} (by 0205). Then z = {u | u /in x
  and u /in y}.
qed.


Definition 0213. x /cap y is the zet z such that z = {u | u /in x and u /in y}.


Lemma 0214. There is a zet z such that z = {u | u /in x and u /notin y}.

Proof.
  [prove off]
  Define P = {u | u /notin y}. P has at most one free variable.
  [/prove]

  Take a zet z such that z = {u in x | P(u)} (by 0205). Then z = {u | u /in x
  and u /notin y}.
qed.


Definition 0215. x /setminus y is the zet z such that z = {u | u /in x and
u /notin y}.


# 2.4 Unions

Axiom 0216. There is a zet z such that z = {u | u /in x or u /in y}.

Definition 0217. x /cup y is the zet z such that z = {u | u /in x or u /in y}.


# 2.5 Pairs and singleton sets

Let a,b denote elements.

Axiom 0218. There is a zet x such that x = {u | u = a or u = b}.

Definition 0229. `{a,b}` is the zet x such that x = {u | u = a or u = b}. Let
the unordered pair of a and b stand for `{a,b}`.


Lemma 0220. There is a zet x such that x = {u | u = a}.

Proof.
  `{a,a}` is a zet and `{a,a}` = {u | u = a}.
qed.


Definition 0221. Let a be an element. `{a}` is the zet x such that `{a}` =
{u | u = a}. Let the singleton set of a stand for `{a}`.
