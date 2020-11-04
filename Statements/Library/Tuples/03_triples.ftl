# 3 Triples

[read FLib/Statements/Library/Tuples/01_tuples.ftl]


Let a triple  stand for a tuple of length 3.
Let a treble  stand for a tuple of length 3.
Let a triplet stand for a tuple of length 3.
Let a triad   stand for a tuple of length 3.


Signature TU0301. Let x1,x2,x3 be objects. (x1,x2,x3) is a triple.


Axiom TU0302. Let x1,x2,x3 be objects. x1 is the first entry of (x1,x2,x3).

Axiom TU0303. Let x1,x2,x3 be objects. x2 is the second entry of (x1,x2,x3).

Axiom TU0304. Let x1,x2,x3 be objects. x3 is the third entry of (x1,x2,x3).


# 3.1 Basic properties

Lemma TU0305. Let t be a triple. Then t = (x1,x2,x3) for some objects x1,x2,x3.

Proof.
  
qed.


Lemma TU0306. Let x1,x2,x3,y1,y2,y3 be objects. If (x1,x2,x3) = (y1,y2,y3) then
x1 = y1 and x2 = y2 and x3 = y3.


Lemma TU0307. Let x1,x2,x3 be objects. {x | x is an entry of (x1,x2,x3)} =
{x1,x2,x3}.

Proof.

qed.


# 3.2 The 3rd power of sets

Proposition TU0308. Let X be a set. X^{3} = {(x1,x2,x3) | x1,x2,x3 are elements
of X}.

Proof.

qed.