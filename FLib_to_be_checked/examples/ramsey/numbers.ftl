[read ramsey/sets.ftl]

Let A,B,C,D,P,Q,R,S,T denote sets.
Let x,y,z denote elements.

[number/-s]

Signature NATSet.   NAT is a countable set.

Let a natural number stand for an element of NAT.
Let i,j,k,l,m,n denote natural numbers.

Signature ZeroNum.  0 is a natural number.

Let n is nonzero stand for n != 0.

Signature SuccNum.  succ n is a nonzero natural number.

Axiom SuccEquSucc.  succ n = succ m  =>  n = m.
Axiom NatExtra.     n = 0 or n = succ m for some m.
Axiom NatNSucc.     n != succ n.

Signature LessRel.  n <= m is an atom.

Axiom ZeroLess.     0 <= n.
Axiom NoScLessZr.   For no n (succ n <= 0).
Axiom SuccLess.     n <= m  <=>  succ n <= succ m.
Axiom LessSucc.     n <= succ n.

Axiom LessRefl.     i <= i.
Axiom LessASymm.    i <= j <= i  =>  i = j.
Axiom LessTrans.    i <= j <= k  =>  i <= k.
Axiom LessTotal.    i <= j \/ succ j <= i.

#
# Proof by induction in ForTheL are based on a predefined binary
# predicate symbol (-<-) considered to be a well-founded ordering.
# We give concrete axioms for (-<-) to simulate natural induction.
#

Signature IHSort.   n -<- m is an atom.
Axiom IH.           n -<- succ n.

