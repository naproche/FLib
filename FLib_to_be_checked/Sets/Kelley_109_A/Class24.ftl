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

[prove off][check off]

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

Definition 40. <a> = {a}.
Let the singleton of x stand for <x>.

Definition 45. <a,b> = {a,b}.
Let the unordered pair of x and y stand for <x,y>.

Theorem 46a. If x is an object and y is an object then <x,y> is a set.
Theorem 46b. If x is an object and y is an object then
z \in <x,y> iff z=x or z=y.
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

[relation/-s]
Definition 56. A relation is a class r such that
every element of r is an ordered pair.

Let r,s,t stand for relations.

Definition 57. r \circ s =
{[x,z] | x,z are objects and there exists an object b such that 
[x,b] \in s and [b,z] \in r}.

Theorem 58. (r \circ s) \circ t = r \circ (s \circ t).
Proof. (r \circ s) \circ t \subset r \circ (s \circ t) and
r \circ (s \circ t) \subset (r \circ s) \circ t.
qed.

Theorem 59a. r \circ (s \cup t) = (r \circ s) \cup (r \circ t).
Proof. r \circ (s \cup t) \subset (r \circ s) \cup (r \circ t).
(r \circ s) \cup (r \circ t) \subset r \circ (s \cup t).
qed.

# Theorem 59b. r \circ (s \cap t) \subset (r \circ s) \cap (r \circ t).


Definition 60. r^{-1} = {[b,a] | a,b are objects and [a,b] \in r}.
Let the relation inverse to r stand for r^{-1}.

Lemma. r^{-1} is a relation.

Theorem 61. (r^{-1})^{-1} = r.
Proof.
r \subset (r^{-1})^{-1}.
(r^{-1})^{-1} \subset r.
qed.

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

[map/-s]
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
Let f(u) stand for the value of f at u.

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

Theorem 73. Let u be an object. Let y be a set. Then <u> \times y is a set.
Proof. Define
f = {[w,v] | w \in y and v = [u,w]}.
f is a map. 
\domain f = y.
\range f = <u> \times y.
qed.

# [/prove]

Theorem 74. Let x,y be sets. Then x \times y is a set.
Proof. Define
f = {[u,w] | u \in x and w = <u> \times y}.
f is a map.
\domain f = x.
\range f is a set.
\range f = {set z | there exists u \in x such that z = <u> \times y}.
\bigcup (\range f) is a set.
\bigcup (\range f) \subset x \times y.
Let us show that x \times y \subset \bigcup (\range f).
Let w \in x \times y. Take u \in x and v \in y such that w = [u,v].
w \in <u> \times y \in \range f.
w \in \bigcup \range f.
end.
qed.

Theorem 75. Let f be a map. Let \domain f be a set.
Then f is a set.
Proof. f \subset \domain f \times \range f. qed.

Definition 76.
y \tothe x = {map f | \domain f = x and \range f \subset y}.

Theorem 77. Let x,y be sets. Then y \tothe x is a set.
Proof. y \tothe x \subset 2^(x \times y).
qed.

Definition 78. f is on x iff x = \domain f.

Definition 79. f is to y iff \range f \subset y.

Definition 80. f is onto y iff \range f = y.

# Well Ordering



# Definition 81. x r y if and only if (x,y) \in r.
Let x (r) y stand for (x,y) \in r.

Definition 82. r connects x iff for all elements u,v of x
u (r) v or v (r) u or v = u.

Definition 83. r is transitive in x iff 
for all elements u,v,w of x if u (r) v and v (r) w then u (r) w.

Definition 84. r is asymmetric in x iff for all elements u,v of x
if u (r) v then not v (r) u.

# Definition 85. x \neq y if and only if it is false that x = y.

Definition 86. a minimizes x in r iff a \in x and 
for each y \in x not y (r) a.

[wellorder/-s]
Definition 87. r wellorders x iff r connects x and for each
subclass y of x such that y \neq 0 
there exists an object z such that 
z minimizes y in r.

Theorem 88a. If r wellorders x then r is
asymmetric in x.
Proof. Assume r wellorders x.
Let u \in x and v \in x.
Assume u (r) v and v (r) u.
Then <u,v> \subset x.
Take an object z such that z minimizes <u,v> in r.
z = u or z = v.
Then not v (r) u or not u (r) v.
Contradiction. 
Then r is asymmetric in x.
qed.

Theorem 88b. If r wellorders x then r is
transitive in x.
Proof. Assume r wellorders x.
Assume that r is not transitive in x.
Take elements u,v,w of x such that 
u (r) v and v (r) w and not u (r) w.
u \neq w. Indeed r is asymmetric in x.
w (r) u.
There is no object a such that a minimizes (<u> \cup <v>) \cup <w> in r.
(<u> \cup <v>) \cup <w> \subset x.
Take an object b such that b minimizes (<u> \cup <v>) \cup <w> in r.
Contradiction.
qed.



[section/-s]
Definition 89. A section of x in r is a class y such that
y \subset x and r wellorders x and for each objects u,v such that
u \in x and v \in y and u (r) v we have u \in y.

Theorem 90. If z \neq 0 and every element of z is a section
of x in r then \bigcup z and \bigcap z are sections of x in r.

Theorem 91. If y is a section of x in r and y \neq x then
y = {u | u \in x and u (r) v} for some element v of x.
Proof. Let y be a section of x in r and y \neq x.
Take an object v such that v minimizes x ~ y in r.
# The rest of the proof is found automatically!!
qed.

Theorem 92. If x and y are sections of z in r then
x \subset y or y \subset x.

# [/prove][/check]

[orderpreserve/-s]
Definition 93. f orderpreserves r and s iff r wellorders \domain f
and s wellorders \range f and f(u) (s) f(v) for all elements
u, v of \domain f such that u (r) v.
# Not allowed to write "u and v" instead of "u, v"!

Theorem 94. If x is a section of y in r and f orderpreserves
r and r and f is on x and f is to y then for each element u of x
it is wrong that f(u) (r) u.
Proof. 
Assume x is a section of y in r and f orderpreserves
r and r and f is on x and f is to y. 
Define A = {u | u \in x and f(u) (r) u}.
Let us show that A = 0.
Assume the contrary.
Take an object v such that v minimizes A in r.
Then f(v) (r) v.
For all elements u of x such that u (r) v 
we have u (r) f(u) or u = f(u).
f(v) (r) f(f(v)) or f(v) = f(f(v)).
f(f(v)) (r) f(v). Indeed f orderpreserves r and r.
Contradiction.
end.
qed.

Definition 95. A oneonefunction is a map f
such that f^{-1} is a map.

Lemma. f is a oneonefunction iff for all elements
x,y of \domain f such that x \neq y we have f(x) \neq f(y).



Theorem 96a. If f orderpreserves r and s then f is a oneonefunction.
Proof. Assume that f orderpreserves r and s.
Let u,v be elements of \domain f.
Assume f(u) = f(v). Then it is wrong that u (r) v or v (r) u.
Indeed u (r) v => f(u) (s) f(v) and
v (r) u => f(v) (s) f(u).
Hence u = v. Indeed r connects \domain f.
qed.

[/prove][/check]

# Theorem 96b. If f orderpreserves r and s then 
# f^{-1} orderpreserves s and r.
# Proof.
# Assume that f orderpreserves r and s.
# \domain f^{-1} = \range f.
# s wellorders \domain f^{-1}.
# \range f^{-1} = \domain f.
# r wellorders \range f^{-1}.
# Let us show that f^{-1}(u) (r) f^{-1}(v) for all elements
# u, v of \domain f^{-1} such that u (s) v.
# Let a, b be elements of \domain f^{-1} such that a (s) b.
# Take an element u of \domain f such that a = f(u).
# Indeed a \in \range f.
# Take elements u, v of \domain f such that a = f(u) and b = f(v).
# f^{-1}(a) = u and f^{-1}(b) = v.
# f(u) (s) f(v).
# Not u = v.
# Not v (r) u.
# u (r) v.
# f^{-1}(a) (r) f^{-1}(b).
# end.
# qed.

Theorem 97. If f and g orderpreserve r and s
and \domain f, \domain g are sections of x in r
and \range f, \range g are sections of y in s
then f \subset g or g \subset f.
Proof. 
Assume that f and g orderpreserve r and s
and \domain f, \domain g are sections of x in r
and \range f, \range g are sections of y in s.
Then \domain f \subset \domain g or 
\domain g \subset \domain f.
Let us show that f(u) = g(u) for all elements u of
\domain f \cap \domain g.
Define A = {object z | z \in (\domain f) \cap (\domain g) 
                       and g(z) \neq f(z)}.
Let us show that A = 0.
Assume the contrary.
Take an object u such that u minimizes A in r.
Then f(u) \neq g(u).
Case f(u) (s) g(u).
f(u) \in \range g. Indeed g(u) \in \range g.
Take an object a such that a \in \domain g and g(a) = f(u).
end.


end.
end.
qed.

# For all elements u of x such that u (r) v 
# we have u (r) f(u) or u = f(u).
# f(v) (r) f(f(v)) or f(v) = f(f(v)).
# f(f(v)) (r) f(v). Indeed f orderpreserves r and r.
# Contradiction.


#FOAM #FOAMT #FAMT






# Axiom of regularity

# [/prove][/check]

Axiom VII. If x \neq 0 then there is an element y of x
such that if y is a class then x \cap y = 0.

Theorem 101. x \notin x.
Proof. Assume x \in x. Define r = {x}. Take an element y of r
such that if y is a class then r \cap y = 0. 
y = x. Then y \in r \cap y. Contradiction.
qed.

Theorem 102. Not (x \in y and y \in x).
Proof. Assume x \in y and y \in x. Define r = {object z | z=x or z=y}.
Take an element z of r such that if z is a class then r \cap z = 0.
Case z = x. Then y \in r \cap z. Contradiction. end.
Case z = y. Then x \in r \cap z. Contradiction. end.
qed.

Definition 103. EE = {[x,y] | x,y are sets and x \in y}.

Lemma. EE is a relation.

# Theorem 104. EE is not a set.
# The proof in Kelley is based on the Kuratowski pair and Foundation. 
# We have to give a proof based on replacement.

Definition 105. x is full iff each element of x is a subclass of x.

Definition 106. An ordinal is a class x such that EE connects
x and x is full.

Theorem 107. If x is an ordinal then EE wellorders x.
Proof. Let x be an ordinal.
Let y be a nonvoid subclass of x.
Take an element u of y such that if u is a class
then y \cap u = 0.
Then no element of y is an element of u and
u minimizes y in EE.
qed.



Axiom 108. If x is an ordinal and y \subset x and y \neq x
and y is full then y \in x.

Theorem 109. If x is an ordinal and y is an ordinal then
x \subset y or y \subset x.
Proof. 
Let us prove that x \cap y is full.
Let z \in x \cap y. 
Then z \in x and z \subset x. end.
x \cap y = x or x \cap y \in x.
qed.
