# 5 Classes

[read FLib/Statements/Library/SetTheory/02_elementary-set-theory.ftl]


Signature 0501. A class is a collection. Let X,Y,Z denote classes.

Axiom 0502. X is a zet iff X is an element of some class.

Definition 0503. A proper class is a class that is not a zet.


# Sub- and superclasses

Definition 0504. Let C be a collection. A subclass of C is a class X such that
X /subseteq C.

Definition 0505. Let C be a collection. A superclass of C is a class X such that
X /supseteq C.


# Comprehension

Axiom 0506. Let P be a statement. Assume that P has at most one free variable.
There exists a class X such that X = {u | u is an element and P(u)}.


Definition 0507. /mathbb{V} is the set of zets.


Proposition 0508. /mathbb{V} is a class.

Proof.
  [prove off]
  Define P = {u | u is a zet}. P has one free variable.
  [/prove]

  Take a class V such that V = {u | u is an element and P(u)}. Then V = {u | u
  is a zet}. Hence V = /mathbb{V}.
qed.
