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



[set/-s] [element/-s] [belong/-s] [subset/-s]

Signature SetSort.  A set is a notion.
Signature ElmSort.  An element is a notion.

Let A,B,C,D,P,Q,R,S,T denote sets.
Let x,y,z denote elements.

Signature EOfElem.  An element of S is an element.

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



Definition Nat. Nat is the set of numbers.

[function/-s]

Signature FunSort.  A function is a notion.

Let F,G,P denote functions.

Signature DomSet.   Dom F is a set.
Signature ImgElm.   Let x << Dom F. F(x) is an element.
Definition DefPtt.  F[y] = { x << Dom F | F(x) = y }.

Lemma PttSet.       F[y] [= Dom F.

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

Definition. F lists A in n steps iff 
(Seq(1,n) = Dom F and A = Set(F,1,n)).
Definition. A is finite iff there is a function
F and a number n such that F lists A in n steps.

Definition. A is infinite iff A is not finite.


