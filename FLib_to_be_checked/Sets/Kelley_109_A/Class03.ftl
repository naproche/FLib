# [prove off]
[printgoal on]
[printreason on]

Let X,Y,Z stand for classes.
Let a \in b stand for a is an element of b.

# We deal with mathematical objects.
[object/-s]
Signature. An object is a notion.
Let a,b,c,d stand for objects. 

[set/-s]
Signature. A set is a class that is an object.

Let x,y,z,w denote sets.

Definition 2. X \cup Y = {object u | u \in X or u \in Y }.

Definition 3. X \cap Y = {object u | u \in X and u \in Y }.

Let the union of x and y stand for x \cup y.
Let the intersection of x and y stand for x \cap y.

Definition 25. A subclass of Y is a set X such that each element of X is an element of Y. 
Let x \subset y stand for x is a subclass of y.


Signature 48. [a,b] is an object.

Axiom 55. If [a,b] = [c,d] then a=c and b=d.

[relation/-s]
Definition 56. A relation is a class X such that for each element c of X there exist a and b such that c = [a,b].

Let r,s,t stand for relations.

Definition 57. r \circ s =
{[a,c] | a,c are objects and there exists b such that 
[a,b] \in s and [b,c] \in r}.

Lemma. r \cup s is a relation.

# Theorem 58. (r \circ s) \circ t = r \circ (s \circ t).
# Proof. (r \circ s) \circ t \subset r \circ (s \circ t) and
# r \circ (s \circ t) \subset (r \circ s) \circ t.
# qed.

# Theorem 59a. r \circ (s \cup t) = (r \circ s) \cup (r \circ t).
# Proof. r \circ (s \cup t) \subset (r \circ s) \cup (r \circ t).
# (r \circ s) \cup (r \circ t) \subset r \circ (s \cup t).
# qed.

Definition 60. r^{-1} = {[b,a] | a,b are objects and [a,b] \in r}.
Let the relation inverse to r stand for r^{-1}.

Lemma. r^{-1} is a relation.

Theorem 61. (r^{-1})^{-1} = r.
Proof.
r \subset (r^{-1})^{-1}.
(r^{-1})^{-1} \subset r.
qed.

Lemma 62a. Assume r \subset s. Then r^{-1} \subset s^{-1}.

Lemma 62b. (r \circ s)^{-1} \subset (s^{-1}) \circ (r^{-1}).

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

# [/prove]

# Functions

[map/-s]
Definition 63. A map is a relation f such that for each
a,b,c if [a,b] \in f and [a,c] \in f then b = c.

Let f,g stand for maps.

Theorem 64. If f, g are maps then f \circ g is a map.

Definition 65. \domain x = {object u | there exists an object v 
such that [u,v] \in x}.

Definition 66. \range x = {object v | there exists an object u 
such that [u,v] \in x}.


