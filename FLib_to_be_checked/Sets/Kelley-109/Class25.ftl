#### Warning: This file runs with a modified Alice:
# "set" is replaced by "class"
# "object" is replaced by "xobject" (which is not used in the text)
# "aSet" in the output to the external prover is replaced by
# "aClass".

# This file checks until Lemma 62a. Then eprover is overwhelmed
# by the length of the article and fails.
#
# In shorter version of the file we observed erratic behavior 
# due to premise selection:
# In a certain version,
# when Definition 3 is commented out, file checks.
# When Definition 3 is in, file does not check, namely 
# Theorem 62b is not accepted, although there is no immediate conflict
# with Def 3 (\cap).
#
# Probably this behavior cannot be reproduced, since the file has
# changed since then.

# Obviously the REASONER should be very selective which premises
# to give to the prover.

# We shell now try thinned out versions to check the relation and
# the functions separately. 

# Kelley Morse Theory of Classes

# [prove off][check off]

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

# This file checks in 3 min on my laptop.

# Elementary set Theory

# The Classification Axiom Scheme

Let a \neq b stand for a != b.

Let x, y, z, r, s, t stand for classes.

[synonym object/-s]
Signature. An object is a notion.
Let a, b, c, d, e stand for objects.

Let a \in x stand for a is an element of x.

# Ontological axiom:
Axiom. Every element of x is an object.

# Axiom I. Axiom of extent.
Axiom I. For each x for each y x = y iff for each object z z \in x iff z \in y.

# These are the classes of KM
[synonym set/-s]
Definition 1. A set is a class that is an object.

Definition 2. x \cup y = { object u | u \in x or u \in y }.
Definition 3. x \cap y = { object u | u \in x and u \in y }.



# Axiom II, the classification axiom-scheme is built into
# the class mechanisms of SAD.

# Elementary Algebra of Classes


# Definition 9.
Let a \notin b stand for a is not an element of b.

Definition 10. ~ x = {object u | u \notin x}.
Let the complement of x stand for ~ x.

Definition 13. x ~ y = x \cap (~ y).

Definition 15. 0 = {object u | u \neq u}.
Let the void class stand for 0.
Let zero stand for 0.



Definition 15a. x is nonvoid iff x \neq 0.

# Definition 18. UU = {object u | u = u}.
# Let the universe stand for UU.

# Theorem 19. x \in UU iff x is an object.

Definition 22. \bigcap x = {object u | for each set y if y \in x then u \in y}.

Definition 23. \bigcup x = {object u | for some set y (y \in x and u \in y)}.

Definition 25. A subclass of y is a class x such that each element of x is an element of y. 
Let x \subset y stand for x is a subclass of y.
Let x is contained in y stand for x \subset y.

Theorem 27. x = y iff x \subset y and y \subset x.

Theorem 28. If x \subset y and y \subset z then x \subset z.


# Axiom of subclasses.
Axiom III. If x is a set then there is a set y such that for each
z if z \subset x then z \in y.

# This axiom is a kind of powerset axiom, where the powerset
# also has all subCLASSES as elements. Since elements are sets
# these subclasses will be sets. So the separation scheme follows.

Theorem 33. If x is a set and z \subset x then z is a set.

Definition 36. 2^x = {set y | y \subset x}.

# Theorem 37. UU = 2^UU.

Theorem 38a. If x is a set then 2^x is a set.

# Definition. RR = {set x | x \notin x}.

# Theorem. RR is not a set.

# Theorem 39. UU is not a set.

# Definition 40. <a> = {a}.
# Let the singleton of x stand for <x>.

# Definition 45. <a,b> = {a,b}.
# Let the unordered pair of x and y stand for <x,y>.

# Theorem 46a. If x is an object and y is an object then <x,y> is a set.
# Theorem 46b. If x is an object and y is an object then
# z \in <x,y> iff z=x or z=y.
# Theorem 46c. <x,y> = UU iff x is not an object or y is not an object.

# Ordered Pairs; Relations

# Definition 48. Let x,y be objects. [x,y] = <<x>,<x,y>>.
# Let the ordered pair of x and y stand for [x,y].

# Theorem 49a. If x,y are objects then [x,y] is a set.
# Theorem 49b. If [x,y] is not an object then [x,y] = UU.

Signature 48. [a,b] is an object.

Definition. An ordered pair is an object c such that there exist
objects a and b such that c = [a,b].


# Theorem 50a. If x and y are objects then 
#  \bigcup [x,y] = <x,y> and
#  \bigcap [x,y] = <x> and
#  \bigcup \bigcap [x,y] = x and
#  \bigcap \bigcap [x,y] = x and
#  \bigcup \bigcup [x,y] = x \cup y and
#  \bigcap \bigcup [x,y] = x \cap y.

# Theorem. If x is not an object or y is not an object then
#   \bigcup \bigcap [x,y] = 0 and
#   \bigcap \bigcap [x,y] = UU and
#   \bigcup \bigcup [x,y] = UU and
#  \bigcap \bigcup [x,y] = 0.

# Definition 51. Let z be a set. 1st z = \bigcap \bigcap z.

#Definition 52. Let z be a set. 2nd z = (\bigcap \bigcup z) \cup 
#((\bigcup \bigcup z) ~ \bigcup \bigcap z). 
#Let the first coordinate of z stand for 1st z.
#Let the second coordinate of z stand for 2nd z.

# Theorem 53. 2nd UU = UU.

#Theorem 54a. If x and y are objects then 1st [x,y] = x.
#Theorem 54b. If x and y are objects then 2nd [x,y] = y.
#Proof. Let x and y be objects.
#2nd [x,y] = (\bigcap \bigcup [x,y]) \cup 
#((\bigcup \bigcup [x,y]) ~ \bigcup \bigcap [x,y])
#= (x \cap y) \cup ((x \cup y) ~ x)
#= y.
#qed.

# Theorem 54c. If x is not an object or y is not an object then
# 1st [x,y] = UU and 2nd [x,y] = UU.

# Theorem 55. If x,y,r,s are objects and [x,y] = [r,s] then
# x = r and y = s.

Axiom 55. If [a,b] = [c,d] then
a = c and b = d.

# We can now extend the signature (our language)
# by [ , ], satisfying axioms ... .
# Ideally, we would like [ , ] an "object" and
# not a class. This requires classes to be objects.
# For the moment, we can however agree [ , ] to
# be a class or UU (= undefined).

# [/prove]

[synonym relation/-s]
Definition 56. A relation is a class r such that
every element of r is an ordered pair.

Let r,s,t stand for relations.

Definition 57. r \circ s =
{[x,z] | x,z are objects and there exists an object b such that 
[x,b] \in s and [b,z] \in r}.

Lemma. r \circ s is a relation.
# Proof. Let x,z be objects such that [x,z] \in r \circ s.
# Take an object b such that [x,b] \in s and [b,z] \in r.
# qed.

Definition. id = {[x,x] | x is an object}.

Lemma. id is a relation.

Lemma. (id \circ id) \circ id = id.

Theorem 58. (r \circ s) \circ t \subset r \circ (s \circ t).
Proof. Let a,d be objects such that [a,d] \in (r \circ s) \circ t.
Take an object c such that [a,c] \in r \circ s and [c,d] \in t.
qed.

# Theorem 59a. r \circ (s \cup t) = (r \circ s) \cup (r \circ t).
# Proof. r \circ (s \cup t) \subset (r \circ s) \cup (r \circ t).
# (r \circ s) \cup (r \circ t) \subset r \circ (s \cup t).
# qed.

Theorem 59b. r \circ (s \cap t) \subset (r \circ s) \cap (r \circ t).

Lemma.  r \circ (s \cap t) is a relation.

Definition 60. r^{-1} = {[b,a] | a,b are objects and [a,b] \in r}.
Let the relation inverse to r stand for r^{-1}.

Lemma. [a,b] \in r iff [b,a] \in r^{-1}.

Lemma. r^{-1} is a relation.
Proof. Let z \in r^{-1}.
Take a,b such that z = [a,b].
z is an ordered pair.
qed.

# Theorem 61. (r^{-1})^{-1} = r.
# Proof.
# r \subset (r^{-1})^{-1}.
# (r^{-1})^{-1} \subset r.
# qed.

Lemma 62a. Assume r \subset s. Then r^{-1} \subset s^{-1}.

# [/prove]

Lemma 62b. (r \circ s)^{-1} \subset (s^{-1}) \circ (r^{-1}).
Proof. Let u \in (r \circ s)^{-1}. 
Take c and a such that u = [c,a].
Take an object b such that ([a,b] \in s and [b,c] \in r).
Indeed [a,c] \in r \circ s. 
[b,a] \in s^{-1} and [c,b] \in r^{-1}.
Then [c,a] \in (s^{-1}) \circ (r^{-1}).
qed.

Lemma. (s^{-1}) \circ (r^{-1}) \subset (r \circ s)^{-1}.
Proof.
((s^{-1}) \circ (r^{-1}))^{-1} \subset 
((r^{-1})^{-1}) \circ ((s^{-1})^{-1}) (by 62b) .
((s^{-1}) \circ (r^{-1}))^{-1} \subset 
r \circ s (by 61) .
(((s^{-1}) \circ (r^{-1}))^{-1})^{-1} \subset 
(r \circ s)^{-1} (by 62a).
(s^{-1}) \circ (r^{-1}) \subset (r \circ s)^{-1} (by 61).
qed.

Theorem 62. (r \circ s)^{-1} = (s^{-1}) \circ (r^{-1}).
Proof. (r \circ s)^{-1} \subset (s^{-1}) \circ (r^{-1}).
(s^{-1}) \circ (r^{-1}) \subset (r \circ s)^{-1}.
qed.

# Functions

# Since "function" is predefined in SAD3, we use the word "map"
# instead.

# [/prove]

[synonym map/-s]
Definition 63. A map is a relation f such that for each
a,b,c if [a,b] \in f and [a,c] \in f then b = c.

Let f,g stand for maps.

Theorem 64. If f, g are maps then f \circ g is a map.

Definition 65. \domain x = {object u | there exists an object v 
such that [u,v] \in x}.

Definition 66. \range x = {object v | there exists an object u 
such that [u,v] \in x}.

Signature 68. Let f be a map. Let u \in \domain f.
The value of f at u is an object v such that [u,v] \in f.
Let f[u] stand for the value of f at u.

Theorem 70. Let f be a map. Then f = {[u,f(u)] | u \in \domain f}.

Theorem 71. Assume \domain f = \domain g and 
for all u \in \domain f f(u) = g(u). Then f = g.
Proof. Let us show that f \subset g.
Let w \in f. 
# Take objects u, v such that w=[u,v].
#  u \in \domain f and v = f(u).
# Then u \in \domain g and v = g(u).
Then w \in g. end.
Let us show that g \subset f.
Let w \in g.  
Take objects u, v such that w=[u,v].
u \in \domain g and v = g(u).
Then u \in \domain f and v = f(u).
Then w \in f. end.
qed.

# Axiom of substitution.
Axiom V. If f is a map and \domain f is a set then \range f is a set.

# Axiom of amalgamation.
Axiom VI. If x is a set then \bigcup x is a set.

Definition 72. x \times y = {[u,v] | u \in x and v \in y}.

