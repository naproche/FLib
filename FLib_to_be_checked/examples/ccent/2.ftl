# We need a number ontology (ordered field, etc.) out of which
# we would select e.g. integers as natural numbers.


[number/-s]

Signature NatSort.  A number is a notion.

Let i,j,k,l,m,n,p,q,r denote numbers.

Signature SortsC.  0 is a number.

Let x is nonzero stand for x != 0.

Signature SortsC.  1 is a nonzero number.

Let x is trivial stand for x = 0 \/ x = 1.
Let x is nontrivial stand for x != 0 and x != 1.

Signature SortsB.  m + n is a number.
Signature SortsB.  m * n is a number.

Axiom AddComm.   m + n = n + m.
Axiom AddAsso.  (m + n) + l = m + (n + l).
Axiom _AddZero.  m + 0 = m = 0 + m.

Axiom MulComm.   m * n = n * m.
Axiom MulAsso.  (m * n) * l = m * (n * l).
Axiom _MulUnit.  m * 1 = m = 1 * m.
Axiom _MulZero.  m * 0 = 0 = 0 * m.

Axiom AMDistr.  m * (n + l) = (m * n) + (m * l) and
                (n + l) * m = (n * m) + (l * m).

Axiom AddCanc.  If (l + m = l + n \/ m + l = n + l) then m = n.

Axiom MulCanc.  Assume that l is nonzero.
                If (l * m = l * n \/ m * l = n * l) then m = n.

Axiom ZeroAdd.  If m + n = 0 then m = 0 /\ n = 0.
Lemma ZeroMul.  If m * n = 0 then m = 0 \/ n = 0.

Definition DefLE.   m <= n <=> exists l : m + l = n.

Definition DefDiff.  Assume that n <= m.
  m - n is a number l such that n + l = m.

Lemma LERefl.   m <= m.

Lemma LEAsym.   m <= n <= m  =>  m = n.

Lemma LETran.   m <= n <= l  =>  m <= l.

Let m < n stand for m != n and m <= n.

Axiom LETotal.  m <= n \/ n < m.

Lemma MonAdd.   Assume that l < n.
  Then m + l < m + n and l + m < n + m.

Lemma MonMul.   Assume that m is nonzero and l < n.
  Then m * l < m * n and l * m < n * m.

Axiom LENTr.    n = 0 \/ n = 1 \/ 1 < n.

Lemma MonMul2.  m != 0 => n <= n * m.
Indeed m != 0 => 1 <= m.

Signature IH.   n -<- m is an atom.
Axiom IH.       n < m => n -<- m.


# 2. DIVISIBILITY

[divide/-s] [divisor/-s]

Definition divisibility.
  n divides m iff for some l (m = n * l).

Let x | y denote x divides y.
Let a divisor of x denote a number that divides x.

Definition DefQuot. Assume that m is nonzero and m | n.
  n / m is a number l such that n = m * l.

Lemma DivTrans. l | m | n => l | n.

Lemma DivSum.   Let l | m and l | n. Then l | m + n.
Indeed if l is nonzero then m + n = l * ((m / l) + (n / l)).

Lemma DivMin.   Let l | m and l | m + n. Then l | n.
Proof.
  Assume that l,n are nonzero.
  Take p such that m = l * p. Take q such that m + n = l * q .
  Let us show that p <= q.
  Assume the contrary. Then q < p.
  m+n = l * q < l * p = m. m <= m+n.
  m = m+n. n=0.
  Contradiction. qed. 
  Take r = q - p.
  We have (l * p) + (l * r) = (l * p) + n.
  Hence n = l * r.
qed.

Lemma DivLE.    Let m | n != 0. Then m <= n.

Lemma DivAsso.  Let l be nonzero and divide m.
                Then n * (m / l) = (n * m) / l.
Indeed (l * n) * (m / l) = l * ((n * m) / l).

[prime/-s] [compound/-s] [primenumber/-s]

Definition DefPrime.
  n is prime iff n is nontrivial and
    for every divisor m of n (m = 1 \/ m = n).

Let x is compound stand for x is not prime.


Lemma PrimDiv. Every nontrivial k has a prime divisor.
Proof by induction.
  Let k be nontrivial.
  Case k is prime. Obvious.
  Case k is compound. Obvious.
qed.


