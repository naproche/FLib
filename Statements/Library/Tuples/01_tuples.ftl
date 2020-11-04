# 1 Tuples

[read FLib/Statements/Library/Arithmetic/05_ordering.ftl]


Let m,n denote natural numbers.


Definition TU0101. \{m, \ldots, n\} = {k | k is a natural number and
m \leq k \leq n}.

Definition TU0102. Let n be a natural number. A tuple of length n is a function
t such that Dom(t) = \{1, \ldots, n\}.

Definition TU0103. A tuple is a tuple of length (some natural number).

Definition TU0104. Let t be a tuple. An entry of t is an object y such that
y = t[x] for some element x of Dom(t).


Let the first   component of t stand for t[1].
Let the second  component of t stand for t[2].
Let the third   component of t stand for t[3].
Let the fourth  component of t stand for t[4].
Let the fifth   component of t stand for t[5].
Let the sixth   component of t stand for t[6].
Let the seventh component of t stand for t[7].
Let the eigth   component of t stand for t[8].
Let the ninth   component of t stand for t[9].

Let the first   entry of t stand for t[1].
Let the second  entry of t stand for t[2].
Let the third   entry of t stand for t[3].
Let the fourth  entry of t stand for t[4].
Let the fifth   entry of t stand for t[5].
Let the sixth   entry of t stand for t[6].
Let the seventh entry of t stand for t[7].
Let the eigth   entry of t stand for t[8].
Let the ninth   entry of t stand for t[9].


Lemma TU0105. Let n be a natural number. Let s,t be tuples of length n. If
s[k] = t[k] for all elements k of \{1, \ldots, n\} then s = t.


# Powers of sets

Let X denote a set.


Definition TU0106. \emptyset is the set that has no elements.


Axiom TU0107. X^{n} is a set.

Axiom TU0108. X^{0} = {\emptyset}.

Axiom TU0109. X^{1} = X.

Axiom TU0110. Assume n > 1. Then X^{n} = {t | t is a tuple of length n such that
every entry of t is an element of X}.
