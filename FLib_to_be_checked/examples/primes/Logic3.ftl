[set/sets/class/classes] [smallset/smallsets] [element/-s]

Signature SetSort.  A set is a notion. # class
Signature ElmSort.  A smallset is a set. # set

Let A,B,C,D denote classes.
Let u,v,w,x,y denote smallsets.

Signature EOfElem.  An element of A is a smallset.
Let x << A stand for x is an element of A.

Definition. VV = {smallset x | x = x }.

Definition. NN = {smallset x | x != x }.

Definition. A subclass of B is a class A such that
every element of A is an element of B.

Let A [[ B stand for A is a subclass of B.

Lemma. NN [[ A [[ VV.

Definition. RR = {x << VV | not x << x }.

Lemma. not RR << VV.

Axiom Extensionality. (A [[ B and B [[ A) => A=B.

Definition. A //\\ B = {x << A | x << B}.

Lemma. A //\\ VV = A.
Indeed A //\\ VV [[ A and A [[ A //\\ VV.

Axiom Subsets. A //\\ x << VV.

Lemma. Let A [[ x . Then A << VV.
Indeed A = A //\\ x.

Lemma. not VV << VV.

Axiom. NN << VV.

Lemma. NN != VV.

Definition. The unordered pair of u and v is {w | w=u or w=v}.
Let [u,v] stand for the unordered pair of u and v.

Definition. [u] = [u,u].

Lemma. w << [u,v] iff w=u or w=v .

Axiom. [u,v] << VV.

Definition. The ordered pair of u and v is [[u],[u,v]].
Let <u,v> stand for the ordered pair of u and v.

Lemma. <u,v> << VV.

Lemma. Let <u,v> = <x,y>. Then u=x and v=y.

Definition. The cartesian product of A and B is {<u,v> | u << A and v << B }.
Let A >< B stand for the cartesian product of A and B.

Lemma. Let z << A >< B. Then there are u,v such that (u<<A and v<<B and z=<u,v>).

Lemma. Let A [[ B and C [[ D. Then A >< C [[ B >< D.

Definition. The union of A is {smallsets x| x << y for some y << A}.
Let Un(A) stand for the union of A.

Lemma. Un(NN) = NN.

Lemma. Un(VV) = VV.

Lemma. A [[ B => Un(A) [[ Un (B).

Axiom. Un(x) << VV.

Definition. The powerset of A is {smallsets x | x [[ A }.
Let Pow(A) stand for the powerset of A.

Lemma. NN << Pow(A).
Lemma. x << Pow(x).

Axiom. Pow(x) << VV.

Lemma. Let u << x and v << y. Then <u,v> << Pow(Pow(Un([x,y]))).

Lemma. x >< y [[ Pow(Pow(Un([x,y]))).
Proof. Let z << x >< y. Take u,v such that (u<<x and v<<y and z=<u,v>).
Then <u,v> << Pow(Pow(Un([x,y]))).
qed

Lemma. x >< y << VV.
Indeed Pow(Pow(Un([x,y]))) << VV.

Definition. A relation is a class R such that R [[ VV >< VV.

Definition. A function is a relation F such that
for all smallsets x,y,z (<x,y> << F and <x,z> << F) => y=z.

Definition. ID = { <x,x> | x << VV }.

Lemma. ID is a function.

Definition. Let F be a function. 
F"A={smallsets y | <x,y> << F for some x << A}.

Lemma. Let F be a function. Then F"NN = NN.

Axiom. Let F be a function and x << VV. Then F"x << VV.


