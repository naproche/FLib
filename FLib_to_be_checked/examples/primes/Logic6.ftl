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

Definition Russell. RR = {smallsets x | not x << x }.

Lemma. not RR << SUni.

Lemma. not RR << Uni.

Axiom Extensionality. (A [[ B and B [[ A) => A=B.

Definition Intersection. A //\\ B = {x << A | x << B}.

Lemma. A //\\ Uni = A.
Indeed A //\\ Uni [[ A and A [[ A //\\ Uni.

Axiom Subsets. A //\\ x << SUni.

Lemma. Let A [[ x . Then A << SUni.
Indeed A = A //\\ x.

# Lemma. not SS << SS.

# Lemma. not SS << UU.

Lemma. not Uni << Uni.

Axiom Emptyset. Emp << SUni.

Lemma. Emp != SUni.

Definition UPair. The unordered pair of a and b is {c | c=a or c=b}.
Let [a,b] stand for the unordered pair of a and b.

Definition. [a] = [a,a].

Lemma. c << [a,b] iff c=a or c=b .

Axiom Pairset. [a,b] << SUni.

Lemma. [a,b] << Uni.

Definition Pair. The ordered pair of a and b is [[a],[a,b]].
Let <a,b> stand for the ordered pair of a and b.

Lemma. <a,b> << SUni.

Lemma. Let <a,b> = <c,d>. Then a=c and b=d.

Definition Product. The cartesian product of A and B is {<u,v> | u << A and v << B }.
Let A >< B stand for the cartesian product of A and B.

Lemma. Let z << A >< B. Then there are a,b such that (a<<A and b<<B and z=<a,b>).

Lemma. Let A [[ B and C [[ D. Then A >< C [[ B >< D.

Definition Union. The union of A is 
{objects a| a << y for some y << A //\\ SUni}.
Let Union(A) stand for the union of A.

Lemma. Union(Emp) = Emp.

Lemma. Union(SUni) = Uni.

Lemma. A [[ B => Union(A) [[ Union (B).

Axiom Unionset. Union(x) << SUni.

Definition Powerset. The powerset of A is {smallsets x | x [[ A }.
Let Pow(A) stand for the powerset of A.

Lemma. Emp << Pow(A).
Lemma. x << Pow(x).

Axiom Power. Pow(x) << SUni.

Lemma. Let a << x and b << y. Then <a,b> << Pow(Pow(Union([x,y]))).

Lemma. x >< y [[ Pow(Pow(Union([x,y]))).
Proof. Let z << x >< y. Take a,b such that (a<<x and b<<y and z=<a,b>).
Then <a,b> << Pow(Pow(Union([x,y]))).
qed

Lemma. x >< y << SUni.
Indeed Pow(Pow(Union([x,y]))) << SUni.

Definition Relation. A relation is a class R such that R [[ Uni >< Uni.

Definition Function. A function is a relation F such that
for all objects a,b,c (<a,b> << F and <a,c> << F) => b=c.

Definition Identity. ID = { <a,a> | a << Uni }.

Lemma. ID is a function.

Definition Image. Let F be a function. 
F"A={objects b | <a,b> << F for some a << A}.

Lemma. Let F be a function. Then F"Emp = Emp.

Axiom Replacement. Let F be a function and x << SUni. Then F"x << SUni.

[number/-s]

Signature. A natural number is an object.
Signature. Nat is the set of natural numbers.
Let m,n denote natural numbers.
Signature. X0 is a natural number.
Signature. X1 is a natural number.
Signature. The successor of m is a natural number.
Let succ(m) stand for the successor of m.

Axiom. succ(m) != X0.
Axiom. succ(m) = succ(n) => m=n.
Axiom. (A [[ Nat /\ X0 << A /\ (succ(m) << A for all m << A //\\ Nat)) => A = Nat.






