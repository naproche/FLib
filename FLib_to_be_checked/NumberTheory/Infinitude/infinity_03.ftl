\newtheorem{signature}{Signature} 
\newtheorem{axiom}{Axiom} 
\newcommand{\power}{{\cal P}} 
\newcommand{\preimg}[2]{{#1}^{-1}[#2]} 
\newcommand{\Seq}[2]{\{#1,\dots,#2\}}
\newcommand{\Set}[3]{\{#1_{#2},\dots,#1_{#3}\}}
\newcommand{\Product}[3]{\prod_{i=#2}^{#3}{#1}_i}
\newcommand{\subs}[2]{{#1}_{#2}}
\newcommand{\CC}{{\Bbb C}}
\newcommand{\RR}{{\Bbb R}}
\newcommand{\QQ}{{\Bbb Q}}
\newcommand{\ZZ}{{\Bbb Z}} 
\newcommand{\NN}{{\Bbb N}}

#[prove off]

\section{There are infinitely many primes}
%#
%# Version 17 March 2012
%#
\section{I. Foundations}


\subsection{1. Sets}

[set/-s] [element/-s] [belong/-s] [subset/-s]

Signature SetSort.  A set is a notion.
Signature ElmSort.  An element is a notion.

Let A,X,Y,Z denote sets.
Let x,y,z denote elements.

Signature EOfElem.  An element of X is an element.

Let x belongs to X stand for x is an element of X.
Let x is in X stand for x belongs to X.
Let x << X stand for x is in X.

Definition DefEmp.  {} is a set that has no elements.

Let S is empty stand for S = {}.
Let S is nonempty stand for S != {}.

Definition DefSub.  A subset of Y is a set X such that
                    every element of X belongs to Y.

Let X [= Y stand for X is a subset of Y.

Lemma SubRefl.      X [= X.
Axiom SubASymm.     X [= Y [= X  =>  X = Y.
Lemma SubTrans.     X [= Y [= Z  =>  X [= Y.

[function/-s]

Signature FunSort.  A function is a notion.

Let f,g,p denote functions.

Signature DomSet.   Dom f is a set.
Let the domain of f stand for Dom f.

Signature ImgElm.   Let x << Dom f. f(x) is an element.
Let \subfunc{f}{x} stand for f(x).

Definition DefSImg. Let X [= Dom f. f[X] = { f(x) | x << X }.

Let Ran f stand for f[Dom f].
Let the range of f stand for Ran f.

Lemma ImgRng.       Let x << Dom f. f(x) belongs to Ran f.

Let a function from X stand for a function f
                    such that Dom f = X.

Let a function from X to Y stand for a function f
                    such that Dom f = X and Ran f [= Y.

Let f : X stand for f is a function from X.
Let f : X -> Y stand for f is a function from X to Y.

Definition DefRst.  Let X [= Dom f. f!X is a function g from X
                    such that for every (x << X) g(x) = f(x).


[number/-s]


Signature NatSort.  A number is a notion.
Definition Nat. Nat is the set of numbers.

Let i,j,k,l,m,n,q,r denote numbers.

Signature SortsC.  0 is a number.

Let x is nonzero stand for x != 0.

Signature SortsC.  1 is a nonzero number.

Signature SortsB.  m + n is a number.
Signature SortsB.  m * n is a number.

Axiom AddAsso.  (m + n) + l = m + (n + l).
Axiom AddZero.  m + 0 = m = 0 + m.
Axiom AddComm.   m + n = n + m.

Axiom MulAsso.  (m * n) * l = m * (n * l).
Axiom MulUnit.  m * 1 = m = 1 * m.
Axiom MulZero.  m * 0 = 0 = 0 * m.
Axiom MulComm.   m * n = n * m.

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

#[/prove]

Lemma MonMul2.  m != 0 => n <= n * m.
Proof.
Let m!=0.
1 <= m.
qed.

Signature IH.   m -<- n is an atom.
Axiom IH.       m < n => m -<- n.


Definition. Seq(m,n) = { i<<Nat | m <= i <= n }.

Definition. Let f be a function such that Seq(m,n) [= Dom f . 
Set(f,m,n) = { f(i) | i<<Nat /\ m <= i <= n }.

Definition. f lists X in n steps iff 
(Seq(1,n) = Dom f and X = Set(f,1,n)).
Definition. X is finite iff there is a function
f and a number n such that f lists X in n steps.

Definition. X is infinite iff X is not finite.

[divide/-s] [divisor/-s]

Definition DefDiv.
  m divides n iff for some l (n = m * l).

Let m | n denote m divides n.
Let a divisor of n denote a number that divides n.

Definition DefQuot. Assume that m is nonzero and m | n.
  n / m is a number l such that n = m * l.

Lemma DivTrans. l | m | n => l | n.

Lemma DivSum.   Let l | m and l | n. Then l | m + n.
Indeed if l is nonzero then m + n = l * ((m / l) + (n / l)).

Lemma DivMin.   Let l | m and l | m + n. Then l | n.
Proof.
  Assume that l,n are nonzero.
  Take i such that m = l * i. Take j such that m + n = l * j .
  Let us show that i <= j.
  Assume the contrary. Then j < i.
  m+n = l * j < l * i = m. m <= m+n.
  m = m+n. n=0.
  Contradiction. qed. 
  Take k = j - i.
  We have (l * i) + (l * k) = (l * i) + n.
  Hence n = l * k.
qed.

Lemma DivLE.    Let m | n != 0. Then m <= n.

Lemma DivAsso.  Let l be nonzero and divide m.
                Then n * (m / l) = (n * m) / l.
Indeed (l * n) * (m / l) = l * ((n * m) / l).

Signature.  Let f be a function such that Seq(m,n) [= Dom f .
Prod(f,m,n) is a number.

Axiom MultTriv. Let f be a function such that Seq(m,n) [= Dom f .
1 <= Prod(f,m,n).

Axiom MultProd. Let m <= i <= n. Let f be a function such that 
Seq(m,n) [= Dom f /\ Ran f [= Nat .
f(i) divides Prod(f,m,n).
  
[prime/-s] [compound/-s] [primenumber/-s]

Let m is trivial stand for m = 0 \/ m = 1.
Let m is nontrivial stand for m != 0 and m != 1.

Definition DefPrime.
  q is prime iff q is nontrivial and
    for every divisor m of q (m = 1 \/ m = q).

Let m is compound stand for m is not prime.

Lemma PrimDiv. Every nontrivial k has a prime divisor.
Proof by induction.
  Let k be nontrivial.
  Case k is prime. Obvious.
  Case k is compound. 
  Take a divisor m of k such that m!=1 /\ m!=k.
  m!=0.
  Take a prime divisor n of m.
  n is a prime divisor of k.
  end.
qed.

Lemma. The set of prime numbers is infinite.

Proof. Let A be a finite set of prime numbers.
Take a function p and a number r such that p lists A in r steps.
Take n=Prod(p,1,r)+1.
Take a prime divisor q of n.
Let us show that q is not an element of A.
Assume the contrary.
Take i such that (1 <= i <= r and q=p(i)).
p(i) divides Prod(p,1,r) (by MultProd).
Indeed Seq(1,r) [= Dom p and Ran p [= Nat.
Then q divides 1 (by DivMin). 
Contradiction. qed.
Hence A is not the set of prime numbers.
qed.





