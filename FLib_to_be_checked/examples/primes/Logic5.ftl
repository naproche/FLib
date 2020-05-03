[set/-s] [class/-es] [smallset/-s] [element/-s]

Signature SetSort.  A set is a notion. # class
Signature ElmSort.  A smallset is a set. # set

Let A,B denote sets.
Let u,v,w,x,y denote smallsets.

Signature EOfElem.  An element of A is a smallset.
Let x << A stand for x is an element of A.

Definition. VV is the set of smallsets.

Definition. VV = {smallset x | x = x }.

Definition. NN = {smallset x | x != x }.

Definition. A subset of B is a set A such that
every element of A is an element of B.

Let A [[ B stand for A is a subset of B.

Lemma. u [[ VV.

Lemma. NN [[ A [[ VV.

Definition. RR = {x << VV | not x << x }.

Lemma. not RR << VV.

Axiom Extensionality. (A [[ B and B [[ A) => A=B.

Lemma. Let x << VV. Contradiction.




