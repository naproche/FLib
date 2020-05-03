# Kelley Morse Theory of Classes

# We follow the appendix of John L. Kelley 
# General Topology D. Van Nostrand Company Inc. 1955
# The appendix develops what is known as Kelley-Morse
# class theory (KM). 
# Kelley writes: "The system of axioms adopted is a variant
# of systems of Skolem and of A.P.Morse and owes much to
# the Hilber-Bernays-von Neumann system as formulated
# by Gödel.

# This file covers the first 56 top level sections of the appendix.
# It uses SADs inbuilt set notion and mechanisms to model the
# classes of Kelley.

# This file checks in 3 min on my laptop.

# Elementary Set Theory

# The Classification Axiom Scheme

# We formalize "classes" of KM by 
# the imbuilt "sets" in SAD3.

# Axioms I and II are built into SAD3.

Let x, y, z, r, s, t, a, b, c, d, e stand for sets.

Let a \in b stand for a is an element of b.

# Axiom I. Axiom of extent.
Axiom I. For each x for each y x = y iff for each set z z \in x iff z \in y.

# We formalize "sets" of KM by defining
# a notion of "sset" (for "small set")

[sset/-s]
Definition 1. A sset is a set that is an element of some set.

# Elementary Algebra of Classes

Definition 2. x \cup y = { sset u | u \in x or u \in y }.

Definition 3. x \cap y = { sset u | u \in x and u \in y }.

Let the union of x and y stand for x \cup y.
Let the intersection of x and y stand for x \cap y.

Theorem 4a. z \in x \cup y iff z \in x or z \in y.
Theorem 4b. z \in x \cap y iff z \in x and z \in y.

Theorem 5a. x \cup x = x.
Theorem 5b. x \cap x = x.

Theorem 6a. x \cup y = y \cup x.
Theorem 6b. x \cap y = y \cap x.

Theorem 7a. (x \cup y) \cup z = x \cup (y \cup z).
Theorem 7b. (x \cap y) \cap z = x \cap (y \cap z).

Theorem 8a. x \cap (y \cup z) = (x \cap y) \cup (x \cap z).
Theorem 8b. x \cup (y \cap z) = (x \cup y) \cap (x \cup z).

# Definition 9.
Let a \notin b stand for a is not an element of b.

Definition 10. ~ x = {sset u | u \notin x}.
Let the complement of x stand for ~ x.

Theorem 11. ~ (~ x) = x.

Theorem 12a. ~ (x \cup y) = (~ x) \cap (~ y).
Theorem 12b. ~ (x \cap y) = (~ x) \cup (~ y).

Definition 13. x ~ y = x \cap (~ y).

Theorem 14. x \cap (y ~ z) = (x \cap y) ~ z.

Let a \noteq b stand for a != b.
Definition 15. 0 = {sset u | u \noteq u}.
Let the void class stand for 0.
Let zero stand for 0.

Theorem 16. x \notin 0.

Theorem 17a. 0 \cup x = x.
Theorem 17b. 0 \cap x = 0.

Definition 18. UU = {sset u | u = u}.
Let the universe stand for UU.

Theorem 19. x \in UU iff x is a sset.

Theorem 20a. x \cup UU = UU.
Theorem 20b. x \cap UU = x.

Theorem 21a. ~ 0 = UU.
Theorem 21b. ~ UU = 0.

Definition 22. \bigcap x = {sset u | for each y if y \in x then u \in y}.

Definition 23. \bigcup x = {sset u | for some y (y \in x and u \in y)}.

Let the intersection of x stand for \bigcap x.
Let the union of x stand for \bigcup x.

Theorem 24a. \bigcap 0 = UU.
Theorem 24b. \bigcup 0 = 0.

Definition 25. A subclass of y is a set x such that each element of x is an
element of y. Let x \subset y stand for x is a subclass of y.
Let x is contained in y stand for x \subset y.

Lemma. 0 \subset 0 and 0 \notin 0.

Theorem 26a. 0 \subset x.
Theorem 26b. x \subset UU.

Theorem 27. x = y iff x \subset y and y \subset x.

Theorem 28. If x \subset y and y \subset z then x \subset z.

Theorem 29. x \subset y iff x \cup y = y.

Theorem 30. x \subset y iff x \cap y = x.

Theorem 31a. If x \subset y then \bigcup x \subset \bigcup y.
Theorem 31a. If x \subset y then \bigcap y \subset \bigcap x.

Theorem 32a. If x \in y then x \subset \bigcup y.
Theorem 32b. If x \in y then \bigcap y \subset x.

# Existence of Sets

# Axiom of subsets.
Axiom III. If x is a sset then there is a sset y such that for each
z if z \subset x then z \in y.

# This axiom is a kind of powerset axiom, where the powerset
# also has all subCLASSES as elements.

Theorem 33. If x is a sset and z \subset x then z is a sset.

Theorem 34a. 0 = \bigcap UU.
Theorem 34b. UU = \bigcup UU.



Theorem 35. If x \noteq 0 then \bigcap x is a sset.

Definition 36. 2^x = {sset y | y \subset x}.

Theorem 37. UU = 2^UU.

Theorem 38a. If x is a sset then 2^x is a sset.
Proof. Let x be a sset.
Take a sset y such that for each z 
if z \subset x then z \in y (by III).
2^x \subset y.
qed.

Theorem 38b. If x is a sset then y \subset x iff y \in 2^x.

Definition. RR = {sset x | x \notin x}.

Theorem. RR is not a sset.
# Proof. Let RR be a sset.
# RR \in RR <=> RR \notin RR.
# Contradiction.
# qed.

Theorem 39. UU is not a sset.

Definition 40. <x> = {sset z | if x \in UU then z = x}.
Let the singleton of x stand for <x>.

Theorem 41. If x is a sset then for each y y \in <x> iff y = x.

Theorem 42. If x is a sset then <x> is a sset.
Proof. Let x be a sset. Then <x> \subset 2^x. 2^x is a set.
qed.

Theorem 43. <x> = UU iff x is not a sset.

Theorem 44a. If x is a sset then \bigcap <x> = x.
Theorem 44b. If x is a sset then \bigcup <x> = x.
Theorem 44c. If x is not a sset then \bigcap <x> = 0.
Theorem 44d. If x is not a sset then \bigcup <x> = UU.

Axiom IV. If x is a sset and y is a sset then x \cup y is a sset.

Definition 45. <x,y> = <x> \cup <y>.
Let the unordered pair of x and y stand for <x,y>.

Theorem 46a. If x is a sset and y is a sset then <x,y> is a sset.
Theorem 46b. If x is a sset and y is a sset then
z \in <x,y> iff z=x or z=y.
Theorem 46c. <x,y> = UU iff x is not a sset or y is not a sset.

Theorem 47a. If x,y are ssets then \bigcap <x,y> = x \cap y.

Theorem 47b. If x,y are ssets then \bigcup <x,y> = x \cup y.
Proof. Let x,y be ssets.
\bigcup <x,y> \subset x \cup y.
x \cup y \subset \bigcup <x,y>.
qed.

Theorem 47c. If x is not a sset or y is not a sset then
\bigcap <x,y> = 0.
Theorem 47d. If x is not a sset or y is not a sset then
\bigcup <x,y> = UU.

# Ordered Pairs; Relations

Definition 48. [x,y] = <<x>,<x,y>>.
Let the ordered pair of x and y stand for [x,y].

Theorem 49a. [x,y] is a sset iff x is a sset and y is a sset.
Theorem 49b. If [x,y] is not a sset then [x,y] = UU.



Theorem 50a. If x and y are ssets then 
  \bigcup [x,y] = <x,y> and
  \bigcap [x,y] = <x> and
  \bigcup \bigcap [x,y] = x and
  \bigcap \bigcap [x,y] = x and
  \bigcup \bigcup [x,y] = x \cup y and
  \bigcap \bigcup [x,y] = x \cap y.

Theorem. If x is not a sset or y is not a sset then
  \bigcup \bigcap [x,y] = 0 and
  \bigcap \bigcap [x,y] = UU and
  \bigcup \bigcup [x,y] = UU and
  \bigcap \bigcup [x,y] = 0.

Definition 51. 1st z = \bigcap \bigcap z.

Definition 52. 2nd z = (\bigcap \bigcup z) \cup 
((\bigcup \bigcup z) ~ \bigcup \bigcap z). 
Let the first coordinate of z stand for 1st z.
Let the second coordinate of z stand for 2nd z.

Theorem 53. 2nd UU = UU.

Theorem 54a. If x and y are ssets then 1st [x,y] = x.
Theorem 54b. If x and y are ssets then 2nd [x,y] = y.
Proof. Let x and y be ssets.
2nd [x,y] = (\bigcap \bigcup [x,y]) \cup 
((\bigcup \bigcup [x,y]) ~ \bigcup \bigcap [x,y])
= (x \cap y) \cup ((x \cup y) ~ x)
= y.
qed.

Theorem 54c. If x is not a sset or y is not a sset then
1st [x,y] = UU and 2nd [x,y] = UU.

Theorem 55. If x and y are ssets and [x,y] = [r,s] then
x = r and y = s.

# We can now extend the signature (our language)
# by [ , ], satisfying axioms ... .
# Ideally, we would like [ , ] an "object" and
# not a set. This requires sets to be objects.
# For the moment, we can however agree [ , ] to
# be a set or UU (= undefined).

Definition 56. A relation is a set r such that for each element z of r
there exist x and y such that z = [x,y].

