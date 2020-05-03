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
# This leads to a conservative variant of Kelley Morse class theory 
# without difficulties about the exact construction of
# ordered pairs and notions derived from ordered pairs like
# relations and functions.
# The new ontology leads to restructurings of the text.
# We shall, e.g., omit Theorems that are concerned with using
# UU as an indicator of "undefined".

# This file checks in ~1:10 min on my laptop.

# The Classification Axiom Scheme

# [prove off]

Let a \neq b stand for a != b.

Let x, y, z, r, s, t stand for classes.
Let a, b, c, d, e stand for objects.

Let a \in x stand for a is an element of x.

# Ontological axiom:
Axiom. Every element of x is an object.

# Axiom I. Axiom of extent.
Axiom I. For each x for each y we have 
x = y iff for each object a a \in x iff a \in y.

[synonym set/-s]
Definition 1. A set is a class that is an object.

# Axiom II, the classification axiom-scheme is built into
# the class mechanisms of SAD.

# Elementary Algebra of Classes

Definition 2. x \cup y = { object a | a \in x or a \in y }.

Definition 3. x \cap y = { object a | a \in x and a \in y }.

Let the union of x and y stand for x \cup y.
Let the intersection of x and y stand for x \cap y.

Theorem 4. If z \in x \cup y then z is a class.

Theorem 4a. (a \in x \cap y iff a \in x and a \in y).

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

# This is Zermelo's axiom of separation:

Theorem 33. If x is a set and z \subclass x then z is a set.

# In the original ontology, Theorem 34 was provable, because
# all elements were sets. Since now we also allow objects we have to
# pull some set existence properties forward as axioms.

Axiom. 0 is a set.

Theorem 34a. 0 = \bigcap UU.

# The other part of Theorem 34 will be done after the introduction
# of singletons.

Theorem 35. If x has an element that is a set then \bigcap x is a set.

Definition 36. 2^x = {set y | y \subclass x}.

# The following theorem had to be adjusted to the new ontology.
Theorem 37. 2^UU = {set y | y = y }.

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
\bigcup {x,y} \subclass x \cup y.
x \cup y \subclass \bigcup {x,y}.
qed.

# Ordered Pairs; Relations

Definition 48. (a,b) = {{a},{a,b}}.
Let the ordered pair of x and y stand for (x,y).

Theorem 49. (a,b) is a set.

# [/prove]

Theorem 55. If (a,b) = (c,d) then
a = c and b = d.

# We can now extend the signature (our language)
# by an elementary symbol ( , ), satisfying standard axioms ... .
# where ordered pairs are objects.

Definition 56. A relation is a class r such that for each element c of r
there exist a and b such that c = (a,b).