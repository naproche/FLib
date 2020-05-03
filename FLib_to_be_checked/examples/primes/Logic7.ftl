[object/-s] [set/sets/class/classes] [smallset/smallsets] [element/-s]

Signature Objects. An object is a notion. # mathematical objects
Let a,b,c,d denote objects.

Signature Sets.  A set is a notion. # classes of objects
Let A,B,C,D denote sets.

Signature Element.  An element of A is an object.
Let x << A stand for x is an element of A.

Signature Smallset1. A smallset is a set.
Signature Smallset2.  A smallset is an object.
Let u,v,w,x,y denote smallsets.

Definition Universe. Uni = {object a | a = a }.

Definition SetUniverse. SUni = {smallset u | u = u }.

Definition Empty. Emp = {object a | a != a }.

Axiom. A << Uni => A << SUni. # sets which are objects are small

Definition Subset. A subclass of B is a class A such that
every element of A is an element of B.

Let A [[ B stand for A is a subclass of B.

Lemma. Emp [[ A [[ Uni.


[number/-s]

Signature. A natural number is an object.
Signature. Nat is the set of natural numbers.
Let m,n denote natural numbers.
Signature. X0 is a natural number.
Signature. X1 is a natural number.
Signature. The successor of m is a natural number.
Let succ(m) stand for the successor of m.

Lemma. m << A [[ Nat => succ(m) << Nat.

Axiom. succ(m) != X0.
Axiom. succ(m) = succ(n) => m=n.
## Axiom. (x [[ Nat /\ X0 << x /\ (succ(m) << x for all m << x)) => x = Nat.






