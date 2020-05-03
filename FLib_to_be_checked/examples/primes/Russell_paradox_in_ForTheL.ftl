# Russell's Paradox

[set/-s] [element/-s]
Signature SetSort.  An element is a notion.
Signature ElmSort.  A set is an element.
Let A,B denote sets.

Signature EOfElem.  An element of A is an element.
Let x << A stand for x is an element of A.

Theorem. Contradiction.
Proof. Let RR = {set A | not A << A }. 
Then RR << RR iff not RR << RR .
qed

