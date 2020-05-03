[synonym number/-s]

Signature NatSort.  A natural number is a notion.

Let i,j,k,l,m,n,p,q,r denote natural numbers.

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
  Take p such that m = l * p. Take q such that m + n = l * q .
  Let us show that p <= q.
  Assume the contrary. Then q < p.
  m+n = l * q < l * p = m.
  Contradiction. qed. 
  Take r = q - p.
  We have (l * p) + (l * r) = (l * p) + n.
  Hence n = l * r.
qed.

Lemma DivLE.    Let m | n != 0. Then m <= n.

Lemma DivAsso.  Let l be nonzero and divide m.
                Then n * (m / l) = (n * m) / l.
Indeed (l * n) * (m / l) = l * ((n * m) / l).

[synonym prime/-s] [synonym compound/-s] [synonym primenumber/-s]

Definition DefPrime.
  n is prime iff n is nontrivial and
    for every divisor m of n (m = 1 \/ m = n).

Let x is compound stand for x is not prime.
Let primenumber stand for prime natural number.

Lemma PrimDiv. Every nontrivial k has a prime divisor.
Proof by induction.
qed.

[synonym set/-s] [synonym element/-s] 
[synonym belong/-s] [synonym subset/-s]

Signature ElmSort.  An element is a notion.

Let A,B,C,D,P,Q,R,S,T denote sets.
Let x,y,z denote elements.

Axiom. Let a be an element of S. Then a is an element.

Let x belongs to S stand for x is an element of S.
Let x is in S stand for x belongs to S.
Let x << S stand for x is in S.

Definition DefEmp.  {} is a set that has no elements.

Let S is empty stand for S = {}.
Let S is nonempty stand for S != {}.

Definition DefSub.  A subset of S is a set T such that
                    every element of T belongs to S.

Let A [= B stand for A is a subset of B.

Lemma SubRefl.      A [= A.
Axiom SubASymm.     A [= B [= A  =>  A = B.
Lemma SubTrans.     A [= B [= C  =>  A [= C.

Definition Nat. Nat is the set of natural numbers.

[synonym function/-s]

Let F,G,P denote functions.

Signature DomSet.   Dom F is a set.
Signature ImgElm.   Let x << Dom F. F(x) is an element.
Definition DefPtt.  F<y> = { x << Dom F | F(x) = y }.

Lemma PttSet.       F<y> [= Dom F.

Definition DefSImg. Let X [= Dom F. F{X} = { F(x) | x << X }.

Let Ran F stand for F{Dom F}.

Let a function from D stand for a function F
                    such that Dom F = D.

Let a function from D to R stand for a function F
                    such that Dom F = D and Ran F [= R.

Let F : D stand for F is a function from D.
Let F : D -> R stand for F is a function from D to R.

Lemma ImgRng.       Let x << Dom F. F(x) belongs to Ran F.

Definition DefRst.  Let S [= Dom F. F!S is a function G from S
                    such that for every (x << S) G(x) = F(x).

Let the domain of F stand for Dom F.
Let the range of F stand for Ran F.

Definition. Seq(m,n) = { i<<Nat | m <= i <= n }.

Definition. Let F be a function such that Seq(m,n) [= Dom F . 
Set(F,m,n) = { F(i) | i<<Nat /\ m <= i <= n }.

Signature.  Let F be a function such that Seq(m,n) [= Dom F .
Prod(F,m,n) is a natural number.

Axiom MultTriv. Let F be a function such that Seq(m,n) [= Dom F .
1 <= Prod(F,m,n).  

Axiom MultProd. Let m <= i <= n. Let F be a function such that 
Seq(m,n) [= Dom F /\ Ran F [= Nat .
F(i) divides Prod(F,m,n).

Definition. F lists A in n steps iff 
(Seq(1,n) = Dom F and A = Set(F,1,n)).

Definition. A is finite iff there is a function
F such that there is a natural number n such that 
F lists A in n steps.

Definition. A is infinite iff A is not finite.

Lemma. Let PP be the set of prime natural numbers. PP is infinite.

Proof. Let A be a finite set of prime natural numbers.
Take a function P and a natural number r such that P lists A in r steps.
Take n=Prod(P,1,r)+1.
Take a prime divisor p of n.
Let us show that p is not an element of A.
Assume the contrary.
Take i such that (1 <= i <= r and p=P(i)).
Seq(1,r) [= Dom P and Ran P [= Nat.
P(i) divides Prod(P,1,r) (by MultProd).
Then p divides 1 (by DivMin). 
Contradiction. qed.
Hence A is not the set of prime natural numbers.
qed.





