# 1 Collections

[read FLib/Statements/Library/synonyms.ftl]

[prover eprover-2.5]


Let a collection stand for a set. Let x,y denote collections.

Let x \in y stand for x is an element of y. Let x \notin y stand for x is not an
element of y.


Definition 0101. x \subseteq y iff every element of x is an element of y. Let
x \supseteq y stand for y \subseteq x. Let x \subsetneq y stand for
x \subseteq y and x \neq y. Let x \supsetneq y stand for y \subsetneq x.


Lemma 0102. If y = {u | u \in x} then x = y.

Corollary 0103. If x \subseteq y and y \subseteq x then x = y.


Definition 0104. An urelement is an object that is not a collection.
