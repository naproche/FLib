[read Forster/Reals.ftl]

Signature NaturalNum.
A natural number is a real number.

Definition NatSet.
NAT is the set of natural numbers.

Axiom ZeroNat.
0 is a natural number.

Axiom OneNat.
1 is a natural number.

Let m,n denote natural numbers.

Axiom AddClosedNat.
m + n is a natural number.

Axiom MultClosedNat.
m * n is a natural number.

Axiom MinClosed.
Assume m =< n. n - m is a natural number.


Axiom PosNaturals.
Let n be a natural number. (not n = 0 => pos(n)).


Let 2 denote 1 + 1.


Lemma PosTwo.
pos(2).

Lemma TwoNotZero.
not 2 = 0.

###Archimedes

Axiom ArchimedeanAxiom.
Let x,y be real numbers. If (pos(x) /\ pos(y)) then there exists a natural number
n such that y < n * x.





###Some Operations.


Lemma maxtype.
Let n,m be natural numbers. Then max(n,m) is a natural number.
Proof.
Case n =< m. Obvious.
Case m =< n. Obvious.
qed.

[group NatGr NaturalNum ZeroNat OneNat AddClosedNat MultClosedNat MinClosed PosNaturals PosTwo TwoNotZero ArchimedeanAxiom maxtype NatSet]
[exit]
