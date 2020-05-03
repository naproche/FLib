# Kelley Morse Theory of Sets and Classes

# We formalize the 

# Appendix: ELEMENTARY SET THEORY 

# of John L. Kelley 
# GENERAL TOPOLOGY 
# D. Van Nostrand Company Inc. 1955
#
# The appendix develops what is known as Kelley-Morse
# class theory (KM). 
# Kelley writes: "The system of axioms adopted is a variant
# of systems of Skolem and of A.P.Morse and owes much to
# the Hilbert-Bernays-von Neumann system as formulated
# by Gödel."

# This file covers the first 56 top level sections of the appendix
# in an alternative ontoloy.
# We use SADs inbuilt class notion and mechanisms to model the
# classes of Kelley. Classes consist of objects, and
# sets are classes that are objects themselves.
# Ordered pairs of objects constitute an elementary notion and are
# objects themselves that satisfy the universal property of
# ordered pairs.
# This leads to a conservative variant of Kelley Morse class theory 
# without difficulties about the exact construction of
# ordered pairs and notions derived from ordered pairs like
# relations and functions.


# This file checks in ~XXXX min on my laptop.

# The Classification Axiom Scheme

[prove off]

Let a \neq b stand for a != b.

Let x, y, z, r, s, t stand for classes.

[synonym object/-s]
Signature. An object is a notion.
Let a, b, c, d, e stand for objects.

Let a \in x stand for a is an element of x.

# Ontological axiom:
Axiom. Every element of x is an object.

# Axiom I. Axiom of extent.
Axiom I. For each x for each y x = y iff for each object a a \in x iff a \in y.

[synonym set/-s]
Definition 1. A set is a class that is an object.

# Axiom II, the classification axiom-scheme is built into
# the class mechanisms of SAD.

# Elementary Algebra of Classes

Definition 2. x \cup y = { object a | a \in x or a \in y }.

Definition 3. x \cap y = { object a | a \in x and a \in y }.

Let the union of x and y stand for x \cup y.
Let the intersection of x and y stand for x \cap y.

Theorem 4. (a \in x \cup y iff a \in x or a \in y)
and (a \in x \cap y iff a \in x and a \in y).

Theorem 5. x \cup x = x and x \cap x = x.

Theorem 6. x \cup y = y \cup x and x \cap y = y \cap x.

Theorem 7. (x \cup y) \cup z = x \cup (y \cup z) 
and (x \cap y) \cap z = x \cap (y \cap z).

Theorem 8. x \cap (y \cup z) = (x \cap y) \cup (x \cap z)
and x \cup (y \cap z) = (x \cup y) \cap (x \cup z).

# 9 Definition, as a parser directive.
Let a \notin b stand for a is not an element of b.

Definition 10. ~ x = { object a | a \notin x}.
Let the complement of x stand for ~ x.

Theorem 11. ~ (~ x) = x.

Theorem 12. ~ (x \cup y) = (~ x) \cap (~ y) 
and ~ (x \cap y) = (~ x) \cup (~ y).

Definition 13. x ~ y = x \cap (~ y).

Theorem 14. x \cap (y ~ z) = (x \cap y) ~ z.

Definition 15. 0 = { object a | a \neq a}.
Let the void class stand for 0.
Let zero stand for 0.

Theorem 16. a \notin 0.

Theorem 17. 0 \cup x = x and 0 \cap x = 0.

Definition 18. UU = { object a | a = a}.
Let the universe stand for UU.

Theorem 19. x \in UU iff x is a set.

Theorem 20. x \cup UU = UU and x \cap UU = x.

Theorem 21. ~ 0 = UU and ~ UU = 0.

Definition 22. \bigcap x = { object a | for each y if y \in x then a \in y}.

Definition 23. \bigcup x = { object a | for some y (a \in y and y \in x)}.

Let the intersection of x stand for \bigcap x.
Let the union of x stand for \bigcup x.

Theorem 24. \bigcap 0 = UU and \bigcup 0 = 0.

Definition 25. A subclass of y is a class x such that each element of x is an
element of y. Let x \subset y stand for x is a subclass of y.
Let x is contained in y stand for x \subset y.

Lemma. 0 \subset 0 and 0 \notin 0.

Theorem 26. 0 \subset x and x \subset UU.

Theorem 27. x = y iff x \subset y and y \subset x.

Theorem 28. If x \subset y and y \subset z then x \subset z.

Theorem 29. x \subset y iff x \cup y = y.

Theorem 30. x \subset y iff x \cap y = x.

Theorem 31. If x \subset y then \bigcup x \subset \bigcup y
and \bigcap y \subset \bigcap x.

Theorem 32. If x \in y then x \subset \bigcup y 
and \bigcap y \subset x.

# Existence of sets

# Axiom of subsets.
Axiom III. If x is a set then there is a set y such that for each
z if z \subset x then z \in y.

# This axiom is a kind of powerclass axiom, where the powerclass
# also has all subCLASSES as elements.

# This is Zermelo's axiom of separation:

Theorem 33. If x is a set and z \subset x then z is a set.

# In the original ontology, Theorem 34 was provable, because
# all elements were sets. Since now we also allow objects we have to
# pull some set existence properties forward as axioms.

Axiom. 0 is a set.

Theorem 34a. 0 = \bigcap UU.

# The other part of Theorem 34 will be done after the introduction
# of singletons.

Theorem 35. If x has an element that is a set then \bigcap x is a set.

Definition 36. 2^x = {set y | y \subset x}.

# The following theorem had to be adjusted to the new ontology.
Theorem 37. 2^UU = {set y | y = y }.

Theorem 38. If x is a set then 2^x is a set and for
each y  y \subset x iff y \in 2^x.
Proof. Let x be a set.
Take a set y such that for each z 
if z \subset x then z \in y (by III).
2^x \subset y.
qed.

# The Russell paradox.

Definition. RR = {set x | x \notin x}.

Theorem. RR is not a set.

Theorem 39. UU is not a set.

Definition 40. {a} = { object b | b = a}.
Let the singleton of a stand for {a}.

Theorem 41. b \in {a} iff b = a.

Axiom 42. {a} is a set.

Theorem 34b. UU = \bigcup UU.

Theorem 44. If x is a set then \bigcap {x} = x 
and \bigcup {x} = x.

Axiom IV. If x is a set and y is a set then x \cup y is a set.

Definition 45. {a,b} = {a} \cup {b}.
Let the unordered pair of x and y stand for {x,y}.

Theorem 46. {a,b} is a set and (c \in {a,b} iff c=a or c=b). 

Theorem 47. If x,y are sets then \bigcap {x,y} = x \cap y
and \bigcup {x,y} = x \cup y.
Proof. Let x,y be sets.
\bigcup {x,y} \subset x \cup y.
x \cup y \subset \bigcup {x,y}.
qed.

# Ordered Pairs; Relationsx

Signature 48. (a,b) is an object.
Let the ordered pair of a and b stand for (a,b).

[/prove]

Axiom 55. If (a,b) = (c,d) then
a = c and b = d.

[synonym relation/-s]
Definition 56. A relation is a class r such that for each element c of r
there exist a and b such that c = (a,b).

Let r,s,t stand for relations.

Definition 57. r \circ s =
{ (a,c) | a,c are objects and there exists b such that 
(a,b) \in s and (b,c) \in r}.

Theorem 58. (r \circ s) \circ t \subset r \circ (s \circ t).
Proof. Let a,d be objects such that (a,d) \in (r \circ s) \circ t.
Take c such that (a,c) \in r \circ s and (c,d) \in t.
Take b such that (a,b) \in r and (b,c) \in s. 
r \circ (s \circ t) \subset (r \circ s) \circ t.
qed.

Theorem 58. (r \circ s) \circ t = r \circ (s \circ t).
Proof. (r \circ s) \circ t \subset r \circ (s \circ t).
r \circ (s \circ t) \subset (r \circ s) \circ t.
qed.


Theorem 59a. r \circ (s \cup t) = (r \circ s) \cup (r \circ t).
Proof. r \circ (s \cup t) \subset (r \circ s) \cup (r \circ t).
(r \circ s) \cup (r \circ t) \subset r \circ (s \cup t).
qed.

Theorem 59b. r \circ (s \cap t) \subset (r \circ s) \cap (r \circ t).


Definition 60. r^{-1} = {(b,a) | a,b are objects and (a,b) \in r}.
Let the relation inverse to r stand for r^{-1}.

Lemma. r^{-1} is a relation.

#Theorem 61. (r^{-1})^{-1} = r.
#Proof.
#r \subset (r^{-1})^{-1}.
#(r^{-1})^{-1} \subset r.
#qed.

#Lemma 62a. Assume r \subset s. Then r^{-1} \subset s^{-1}.

# [/prove]

#Lemma 62b. (r \circ s)^{-1} \subset (s^{-1}) \circ (r^{-1}).
#Proof. Let u \in (r \circ s)^{-1}. 
#Take c and a such that u = [c,a].
#Take an object b such that ([a,b] \in s and [b,c] \in r).
#Indeed [a,c] \in r \circ s. 
#[b,a] \in s^{-1} and [c,b] \in r^{-1}.
#Then [c,a] \in (s^{-1}) \circ (r^{-1}).
#qed.

#Lemma. (s^{-1}) \circ (r^{-1}) \subset (r \circ s)^{-1}.
#Proof.
#((s^{-1}) \circ (r^{-1}))^{-1} \subset 
#((r^{-1})^{-1}) \circ ((s^{-1})^{-1}) (by 62b) .
#((s^{-1}) \circ (r^{-1}))^{-1} \subset 
#r \circ s (by 61) .
#(((s^{-1}) \circ (r^{-1}))^{-1})^{-1} \subset 
#(r \circ s)^{-1} (by 62a).
#(s^{-1}) \circ (r^{-1}) \subset (r \circ s)^{-1} (by 61).
#qed.

#Theorem 62. (r \circ s)^{-1} = (s^{-1}) \circ (r^{-1}).
#Proof. (r \circ s)^{-1} \subset (s^{-1}) \circ (r^{-1}).
#(s^{-1}) \circ (r^{-1}) \subset (r \circ s)^{-1}.
#qed.


