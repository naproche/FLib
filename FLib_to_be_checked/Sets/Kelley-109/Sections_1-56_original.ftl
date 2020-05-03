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

# This file covers the first 56 top level sections of the appendix.
# It uses SADs inbuilt class notion and mechanisms to model the
# classes of Kelley. We have built the class notion into 
# Naproche-SAD by replacing "set" by "class"

# This file checks in ~1:30 min on my laptop.

# The Classification Axiom Scheme

# [prove off]

Let x, y, z, r, s, t, a, b, c, d, e stand for sets.

Lemma. x=x.

Let a \neq b stand for a != b.
Let a \in b stand for a is an element of b.

# Axiom I. Axiom of extent.
Axiom I. For each x for each y 
x = y iff for each z z \in x iff z \in y.

# II Classification axiom-scheme corresponds to the way
# "classifications", i.e., abstraction terms are handled
# in Naproche-SAD

[synonym set/-s]
Definition 1. A set is a class that is an element of some class.

# Elementary Algebra of Classes

Definition 2. x \cup y = { set u | u \in x or u \in y }.

Definition 3. x \cap y = { set u | u \in x and u \in y }.

Let the union of x and y stand for x \cup y.
Let the intersection of x and y stand for x \cap y.

Theorem 4. (z \in x \cup y iff z \in x or z \in y)
and (z \in x \cap y iff z \in x and z \in y).

Theorem 5. x \cup x = x and x \cap x = x.

Theorem 6. x \cup y = y \cup x and x \cap y = y \cap x.

Theorem 7. (x \cup y) \cup z = x \cup (y \cup z) 
and (x \cap y) \cap z = x \cap (y \cap z).

Theorem 8. x \cap (y \cup z) = (x \cap y) \cup (x \cap z)
and x \cup (y \cap z) = (x \cup y) \cap (x \cup z).

# 9 Definition, as a parser directive.
Let a \notin b stand for a is not an element of b.

Definition 10. ~ x = {set y | y \notin x}.
Let the complement of x stand for ~ x.

Theorem 11. ~ (~ x) = x.

Theorem 12. ~ (x \cup y) = (~ x) \cap (~ y) 
and ~ (x \cap y) = (~ x) \cup (~ y).

Definition 13. x ~ y = x \cap (~ y).

Theorem 14. x \cap (y ~ z) = (x \cap y) ~ z.

Definition 15. 0 = {set x | x \neq x}.
Let the void class stand for 0.
Let zero stand for 0.

Theorem 16. x \notin 0.

Theorem 17. 0 \cup x = x and 0 \cap x = 0.

Definition 18. UU = {set x | x = x}.
Let the universe stand for UU.

Theorem 19. x \in UU iff x is a set.

Theorem 20. x \cup UU = UU and x \cap UU = x.

Theorem 21. ~ 0 = UU and ~ UU = 0.

Definition 22. \bigcap x = {set z | for each y if y \in x then z \in y}.

Definition 23. \bigcup x = {set z | for some y (z \in y and y \in x)}.

Let the intersection of x stand for \bigcap x.
Let the union of x stand for \bigcup x.

Theorem 24. \bigcap 0 = UU and \bigcup 0 = 0.

Definition 25. A subclass of y is a class x such that each element of x is an
element of y. Let x \subclass y stand for x is a subclass of y.
Let x is contained in y stand for x \subclass y.

Lemma. 0 \subclass 0 and 0 \notin 0.

Theorem 26. 0 \subclass x and x \subclass UU.

Theorem 27. x = y iff x \subclass y and y \subclass x.

Theorem 28. If x \subclass y and y \subclass z then x \subclass z.

Theorem 29. x \subclass y iff x \cup y = y.

Theorem 30. x \subclass y iff x \cap y = x.

Theorem 31. If x \subclass y then \bigcup x \subclass \bigcup y
and \bigcap y \subclass \bigcap x.

Theorem 32. If x \in y then x \subclass \bigcup y 
and \bigcap y \subclass x.

# Existence of sets

# Axiom of subsets.
Axiom III. If x is a set then there is a set y such that for each
z if z \subclass x then z \in y.

# This axiom is a kind of powerclass axiom, where the powerclass
# also has all subCLASSES as elements.

Theorem 33. If x is a set and z \subclass x then z is a set.

Theorem 34. 0 = \bigcap UU and UU = \bigcup UU.

Theorem 35. If x \neq 0 then \bigcap x is a set.

Definition 36. 2^x = {set y | y \subclass x}.

Theorem 37. UU = 2^UU.

Theorem 38. If x is a set then 2^x is a set and for
each y  y \subclass x iff y \in 2^x.
Proof. Let x be a set.
Take a set y such that for each z 
if z \subclass x then z \in y (by III).
2^x \subclass y.
qed.

# The Russell paradox.

Definition. RR = {set x | x \notin x}.

Theorem. RR is not a set.

Theorem 39. UU is not a set.

Definition 40. {x} = {set z | if x \in UU then z = x}.
Let the singleton of x stand for {x}.

# Before We used <x> instead of {x} since {x} was an inbuilt 
# set notation

Theorem 41. If x is a set then for each y y \in {x} iff y = x.

Theorem 42. If x is a set then {x} is a set.
Proof. Let x be a set. Then {x} \subclass 2^x 
and 2^x is a set.
qed.

Theorem 43. {x} = UU iff x is not a set.

Theorem 44a. If x is a set then \bigcap {x} = x 
and \bigcup {x} = x.
Theorem 44b. If x is not a set then \bigcap {x} = 0
and \bigcup {x} = UU.

Axiom IV. If x is a set and y is a set then x \cup y is a set.

Definition 45. {x,y} = {x} \cup {y}.
Let the unordered pair of x and y stand for {x,y}.

# The following has been a problem before:
# We use <x,y> instead of {x y} because Naproche-SAD requires
# some symbolic or textual material between the variables
# x and y. We use {x;y} instead of {x,y} because the latter
# notion is an inbuilt set notation of Naproche-SAD.

Theorem 46a. If x is a set and y is a set 
then {x,y} is a set and (z \in {x,y} iff z=x or z=y). 

Theorem 46b. {x,y} = UU iff x is not a set or y is not a set.

Theorem 47a. If x,y are sets then \bigcap {x,y} = x \cap y
and \bigcup {x,y} = x \cup y.
Proof. Let x,y be sets.
\bigcup {x,y} \subclass x \cup y.
x \cup y \subclass \bigcup {x,y}.
qed.

Theorem 47b. If x is not a set or y is not a set then
\bigcap {x,y} = 0 and \bigcup {x,y} = UU.

# Ordered Pairs; Relations

Definition 48. (x,y) = {{x},{x,y}}.
Let the ordered pair of x and y stand for (x,y).

Theorem 49a. (x,y) is a set iff x is a set and y is a set.
Theorem 49b. If (x,y) is not a set then (x,y) = UU.

# [/prove]

Theorem 50a. If x and y are sets then 
  \bigcup (x,y) = {x,y} and
  \bigcap (x,y) = {x} and
  \bigcup \bigcap (x,y) = x and
  \bigcap \bigcap (x,y) = x and
  \bigcup \bigcup (x,y) = x \cup y and
  \bigcap \bigcup (x,y) = x \cap y.

Theorem 50b. If x is not a set or y is not a set then
  \bigcup \bigcap (x,y) = 0 and
  \bigcap \bigcap (x,y) = UU and
  \bigcup \bigcup (x,y) = UU and
  \bigcap \bigcup (x,y) = 0.

Definition 51. 1st z = \bigcap \bigcap z.

Definition 52. 2nd z = (\bigcap \bigcup z) \cup 
((\bigcup \bigcup z) ~ \bigcup \bigcap z). 
Let the first coordinate of z stand for 1st z.
Let the second coordinate of z stand for 2nd z.

Theorem 53. 2nd UU = UU.

Theorem 54a. If x and y are sets 
then 1st (x,y) = x and 2nd (x,y) = y.
Proof. Let x and y be sets.
2nd (x,y) = (\bigcap \bigcup (x,y)) \cup 
((\bigcup \bigcup (x,y)) ~ \bigcup \bigcap (x,y))
= (x \cap y) \cup ((x \cup y) ~ x)
= y.
qed.

Theorem 54b. If x is not a set or y is not a set then
1st (x,y) = UU and 2nd (x,y) = UU.

Theorem 55. If x and y are sets and (x,y) = (r,s) then
x = r and y = s.

# We can interpret UU to mean undefined.
# Then ( , ) produces a a set or undefined.
# We can instead extend the signature (our language)
# by an elementary symbol ( , ), satisfying standard axioms ... .
# Ideally, we would like ( , ) to an "object" and
# not a set. Sets will also be objects.

Definition 56. A relation is a class r such that for each element z of r
there exist x and y such that z = (x,y).


