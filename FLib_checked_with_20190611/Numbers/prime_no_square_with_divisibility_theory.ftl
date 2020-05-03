[synonym number/-s]
Signature NatSort.  A natural number is a notion.

Let i,j,k,l,m,n denote natural numbers.

Signature SortsC.  0 is a natural number.

Let x is nonzero stand for x != 0.

Signature SortsC.  1 is a nonzero natural number.

Let x is trivial stand for x = 0 \/ x = 1.
Let x is nontrivial stand for x != 0 and x != 1.

Signature SortsB.  m + n is a natural number.
Signature SortsB.  m * n is a natural number.

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
  m - n is a natural number l such that n + l = m.

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

# Signature IH.   n -<- m is an atom.
Axiom IH.       n < m => n -<- m.


[synonym divide/-s] [synonym divisor/-s]

Definition DefDiv.
  n divides m iff for some l (m = n * l).

Let x | y denote x divides y.
Let a divisor of x denote a natural number that divides x.

Definition DefQuot. Assume that m is nonzero and m | n.
  n / m is a natural number l such that n = m * l.

Lemma DivTrans. l | m | n => l | n.

Lemma DivSum.   Let l | m and l | n. Then l | m + n.
Indeed if l is nonzero then m + n = l * ((m / l) + (n / l)).

Lemma DivMin.   Let l | m and l | m + n. Then l | n.
Proof.
  Assume that l is nonzero.
  Take p = m / l. Take q = (m + n) / l.
  Let us show that p <= q. Indeed m <= m + n.
  Take r = q - p.

  We have (l * p) + (l * r) = (l * p) + n.
  Hence n = l * r.
qed.

Lemma DivLE.    Let m | n != 0. Then m <= n.

Lemma DivAsso.  Let l be nonzero and divide m.
                Then n * (m / l) = (n * m) / l.
Indeed (l * n) * (m / l) = l * ((n * m) / l).

[synonym prime/-s] [synonym compound/-s]

Definition DefPrime.
  n is prime iff n is nontrivial and
    for every divisor m of n (m = 1 \/ m = n).

Let x is compound stand for x is not prime.

Lemma PrimDiv. Every nontrivial k has a prime divisor.
Proof by induction on k.
   Let k be a nontrivial natural number.
   Case k is prime. Obvious.
   Case k is compound. Obvious.
 qed.

Lemma PDP.  For all natural numbers n,m,p
  if p is prime and p | n * m then p | n or p | m.
Proof by induction on ((n + m) + p).
  Let n,m,p be natural numbers.
  Assume that p is prime and p divides n * m.

  Case p <= n.
    Take r = n - p. We have r < n.
    Let us show that p divides r * m.
      n = p + r.
      n * m = (p * m) + (r * m).
      r * m = (n * m) - (p * m).
      p | n * m and p | p * m.
      p | (n * m) - (p * m).
    end.
    Then p divides r or p divides m (by IH).
    Indeed (r + m) + p < (n + m) + p (by MonAdd).
  end.

  Case p <= m.
    Take r = m - p. We have r < m.
    Let us show that p divides n * r.
      m = p + r.
      n * m = (p * n) + (n * r).
      n * r = (n * m) - (p * n).
      p | n * m and p | p * n.
      p | (n * m) - (p * n).
    end.
    Then p divides n or p divides r (by IH).
    Indeed (n + r) + p < (n + m) + p (by MonAdd).
  end.

  Case n < p and m < p.
    Take k = (n * m) / p.

    Case k is trivial. Obvious.

    Case k is nontrivial.
      Take a prime divisor r of k.
      r <= k and r | n * m.
      Let us show that k < p.
        Assume that p <= k.
        Then n * m < p * m < p * k.
        We have a contradiction.
      end.

      Then r divides n or r divides m (by IH).
      Indeed (n + m) + r < (n + m) + p.

      Case r divides n.
        We have (n / r) < n.
        Let us prove that p divides (n / r) * m.
            ((n / r) * m) * r = n * m = ((p * k) / r) * r.
            Then p * (k / r) = (n / r) * m (by DivAsso,MulCanc).
        end.
        Then p divides (n / r) or p divides m (by IH).
        Indeed ((n / r) + m) + p < (n + m) + p (by MonAdd).
      end.

      Case r divides m.
        We have (m / r) < m.
        Let us prove that p divides n * (m / r).
            (n * (m / r)) * r = m * n = ((p * k) / r) * r.
            Then p * (k / r) = n * (m / r) (by DivAsso,MulCanc).
        end.
        Then p divides n or p divides (m / r) (by IH).
        Indeed (n + (m / r)) + p < (n + m) + p (by MonAdd).
      end.
    end.
  end.
qed.


Theorem Main.
  For all nonzero natural numbers n,m,p
    if p * (m * m) = (n * n) then p is compound.
Proof by induction.
  Let n,m,p be nonzero natural numbers.
  Assume that p * (m * m) = (n * n).
  Assume that p is prime.
  Hence p divides n * n and p divides n.
  Take q = n / p. Then m * m = p * (q * q).
  Indeed p * (m * m) = p * (p * (q * q)).
  m < n. Indeed n <= m => n * n <= m * m.
  Hence p is compound.
qed.

