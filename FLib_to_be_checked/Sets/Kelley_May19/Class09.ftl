#### Warning: This file runs with a modified Alice:
# "set" is replaced by "class"
# "object" is replaced by "xobject" (which is not used in the text)

# Kelley Morse Theory of Classes

# [prove off]

# We follow the appendix of John L. Kelley 
# General Topology D. Van Nostrand Company Inc. 1955
# The appendix develops what is known as Kelley-Morse
# class theory (KM). 
# Kelley writes: "The system of axioms adopted is a variant
# of systems of Skolem and of A.P.Morse and owes much to
# the Hilber-Bernays-von Neumann system as formulated
# by Gödel.
# 
# We change the ontology by distinguishing classes and objects.
# A class that is an object is a set.
# We restrict definitions of operations like 
# singletons and pairs to objects, when it is not necessary to
# apply them to classes. 
# This file uses SADs inbuilt set notion and mechanisms to model the
# classes of Kelley. However we have replaced the keyword "set"
# by "class"

# This file checks in 2m10s on my laptop.

# Elementary set Theory

# The Classification Axiom Scheme

Let a \noteq b stand for a != b.

Let x, y, z, r, s, t stand for classes.

[object/-s]
Signature. An object is a notion.
Let a, b, c, d, e stand for objects.

Let a \in x stand for a is an element of x.

# Ontological axiom:
Axiom. Every element of x is an object.

# Axiom I. Axiom of extent.
Axiom I. For each x for each y x = y iff for each object z z \in x iff z \in y.

# These are the classes of KM
[set/-s]
Definition 1. A set is a class that is an object.

# Axiom II, the classification axiom-scheme is built into
# the class mechanisms of SAD.

# Elementary Algebra of Classes

Definition 2. x \cup y = { object u | u \in x or u \in y }.

Definition 3. x \cap y = { object u | u \in x and u \in y }.

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

Definition 10. ~ x = {object u | u \notin x}.
Let the complement of x stand for ~ x.

Theorem 11. ~ (~ x) = x.

Theorem 12a. ~ (x \cup y) = (~ x) \cap (~ y).
Theorem 12b. ~ (x \cap y) = (~ x) \cup (~ y).

Definition 13. x ~ y = x \cap (~ y).

Theorem 14. x \cap (y ~ z) = (x \cap y) ~ z.

Definition 15. 0 = {object u | u \noteq u}.
Let the void class stand for 0.
Let zero stand for 0.

Theorem 16. x \notin 0.

Theorem 17a. 0 \cup x = x.
Theorem 17b. 0 \cap x = 0.

Definition 18. UU = {object u | u = u}.
Let the universe stand for UU.

Theorem 19. x \in UU iff x is an object.

Theorem 20a. x \cup UU = UU.
Theorem 20b. x \cap UU = x.

Theorem 21a. ~ 0 = UU.
Theorem 21b. ~ UU = 0.

Definition 22. \bigcap x = {object u | for each set y if y \in x then u \in y}.

Definition 23. \bigcup x = {object u | for some set y (y \in x and u \in y)}.

Let the intersection of x stand for \bigcap x.
Let the union of x stand for \bigcup x.

Theorem 24a. \bigcap 0 = UU.
Theorem 24b. \bigcup 0 = 0.

Definition 25. A subclass of y is a class x such that each element of x is an element of y. 
Let x \subset y stand for x is a subclass of y.
Let x is contained in y stand for x \subset y.

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

# Existence of classes

# Axiom of subclasses.
Axiom III. If x is a set then there is a set y such that for each
z if z \subset x then z \in y.

# This axiom is a kind of powerset axiom, where the powerset
# also has all subCLASSES as elements. Since elements are sets
# these subclasses will be sets. So the separation scheme follows.

Theorem 33. If x is a set and z \subset x then z is a set.

# Theorem 34a. 0 = \bigcap UU.
# Theorem 34b. UU = \bigcup UU.


Theorem 35. If x has an element that is a set 
then \bigcap x is a set.

Definition 36. 2^x = {set y | y \subset x}.

# Theorem 37. UU = 2^UU.

Theorem 38a. If x is a set then 2^x is a set.
Proof. Let x be a set.
Take a set y such that for each z 
if z \subset x then z \in y (by III).
2^x \subset y.
qed.

Theorem 38b. If x is a set then y \subset x iff y \in 2^x.

Definition. RR = {set x | x \notin x}.

Theorem. RR is not a set.

Theorem 39. UU is not a set.

Definition 40. <x> = {object z | if x \in UU then z = x}.
Let the singleton of x stand for <x>.

Theorem 41. If x is an object then for each y y \in <x> iff y = x.

Theorem 42. If x is an object then <x> is a set.
Proof. Let x be an object. Then <x> \subset 2^x. 2^x is a class.
qed.

# Here we could fall back on the singleton and unordered pair of
# SAD
Theorem 43. <x> = UU iff x is not an object.

Theorem 44a. If x is an object then \bigcap <x> = x.
Theorem 44b. If x is an object then \bigcup <x> = x.
# Theorem 44c. If x is not an object then \bigcap <x> = 0.
# Theorem 44d. If x is not an object then \bigcup <x> = UU.

# [/prove]

Axiom IV. If x is a set and y is a set then x \cup y is a set.

Definition 45. Let x,y be objects. <x,y> = <x> \cup <y>.
Let the unordered pair of x and y stand for <x,y>.

Theorem 46a. If x is an object and y is an object then <x,y> is a set.
Theorem 46b. If x is an object and y is an object then
z \in <x,y> iff z=x or z=y.
# Theorem 46c. <x,y> = UU iff x is not an object or y is not an object.

Theorem 47a. If x,y are sets then \bigcap <x,y> = x \cap y.

Theorem 47b. If x,y are sets then \bigcup <x,y> = x \cup y.
Proof. Let x,y be sets.
\bigcup <x,y> \subset x \cup y.
x \cup y \subset \bigcup <x,y>.
qed.

# Theorem 47c. If x is not an object or y is not an object then
# \bigcap <x,y> = 0.
# Theorem 47d. If x is not an object or y is not an object then
# \bigcup <x,y> = UU.


# Ordered Pairs; Relations

Definition 48. Let x,y be objects. [x,y] = <<x>,<x,y>>.
# Let the ordered pair of x and y stand for [x,y].

Theorem 49a. If x,y are objects then [x,y] is a set.
# Theorem 49b. If [x,y] is not an object then [x,y] = UU.

# Signature 48. [a,b] is an object.

# Definition. An ordered pair is an object c such that there exist
# objects a and b such that c = [a,b].

Theorem 50a. If x and y are objects then 
 \bigcup [x,y] = <x,y> and
 \bigcap [x,y] = <x> and
 \bigcup \bigcap [x,y] = x and
 \bigcap \bigcap [x,y] = x and
 \bigcup \bigcup [x,y] = x \cup y and
 \bigcap \bigcup [x,y] = x \cap y.

# Theorem. If x is not an object or y is not an object then
#   \bigcup \bigcap [x,y] = 0 and
#   \bigcap \bigcap [x,y] = UU and
#   \bigcup \bigcup [x,y] = UU and
#  \bigcap \bigcup [x,y] = 0.

Definition 51. Let z be a set. 1st z = \bigcap \bigcap z.

Definition 52. Let z be a set. 2nd z = 
(\bigcap \bigcup z) \cup ((\bigcup \bigcup z) ~ \bigcup \bigcap z). 
Let the first coordinate of z stand for 1st z.
Let the second coordinate of z stand for 2nd z.

# Theorem 53. 2nd UU = UU.

Theorem 54a. If x and y are objects then 1st [x,y] = x.
Theorem 54b. If x and y are objects then 2nd [x,y] = y.
Proof. Let x and y be objects.
2nd [x,y] = (\bigcap \bigcup [x,y]) \cup 
((\bigcup \bigcup [x,y]) ~ \bigcup \bigcap [x,y])
= (x \cap y) \cup ((x \cup y) ~ x)
= y.
qed.

# Theorem 54c. If x is not an object or y is not an object then
# 1st [x,y] = UU and 2nd [x,y] = UU.

Theorem 55. If x,y,r,s are objects and [x,y] = [r,s] then
x = r and y = s.

# Axiom 55. If [a,b] = [c,d] then
# a = c and b = d.


