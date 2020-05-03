#### Example file for a problem with "take"

## Ontology

Let x, y, z, r, s, t stand for classes.

[object/-s]
Signature. An object is a notion.
Let a, b, c, d, e stand for objects.

Let a \in x stand for a is an element of x.

# Ontological axiom:
Axiom. Every element of x is an object.

# Axiom I. Axiom of extent.
Axiom I. For each x for each y x = y iff for each object z z \in x iff z \in y.

[set/-s]
Definition 1. A set is a class that is an object.

Definition 25. A subclass of y is a class x such that each element of x is an element of y. 
Let x \subset y stand for x is a subclass of y.
Let x is contained in y stand for x \subset y.

Theorem 27. x = y iff x \subset y and y \subset x.

## Ordered pairs

Signature 48. [a,b] is an object.

Definition. An ordered pair is an object c such that there exist
objects a and b such that c = [a,b].


Axiom 55. If [a,b] = [c,d] then
a = c and b = d.

## Relations

[relation/-s]
Definition 56. A relation is a class r such that
every element of r is an ordered pair.

Let r,s,t stand for relations.

Definition 57. r \circ s =
{[x,z] | x,z are objects and there exists an object b such that 
[x,b] \in s and [b,z] \in r}.
Let the composition of r and s stand for r \circ s.

# Theorem 58 checks automatically, so we don't need to unravel
# the definition of \circ by hand.

Theorem 58. (r \circ s) \circ t = r \circ (s \circ t).
Proof. (r \circ s) \circ t \subset r \circ (s \circ t) and
r \circ (s \circ t) \subset (r \circ s) \circ t.
qed.

Definition 60. r^{-1} = {[b,a] | a,b are objects and [a,b] \in r}.
Let the relation inverse to r stand for r^{-1}.

# The *proof* of Lemma 62b fails at "Take an object b ..."

Lemma. r^{-1} is a relation.

Lemma 62b. (r \circ s)^{-1} \subset (s^{-1}) \circ (r^{-1}).
Proof. Let u \in (r \circ s)^{-1}. 
Take c and a such that u = [c,a].
Then [a,c] \in r \circ s. 
Take an object b such that ([a,b] \in s and [b,c] \in r).
[b,a] \in s^{-1} and [c,b] \in r^{-1}.
Then [c,a] \in (s^{-1}) \circ (r^{-1}).
qed.


