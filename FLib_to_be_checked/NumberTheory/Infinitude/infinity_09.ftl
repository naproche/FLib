#\newtheorem{signature}{Signature}
#\newtheorem{axiom}{Axiom}
#\newtheorem{signaturep}{Signature}
#\newtheorem{axiomp}{Axiom}
#\newtheorem{definitionp}{Definition}
#\newtheorem{theoremp}{Theorem}
#\newtheorem{lemmap}{Lemma}
 
#\newcommand{\power}{{\cal P}} 
#\newcommand{\preimg}[2]{{#1}^{-1}[#2]} 
#\newcommand{\Seq}[2]{{#1,\dots,#2}}
#\newcommand{\Set}[3]{{#1_{#2},\dots,#1_{#3}}}
#\newcommand{\Product}[3]{\prod_{i=#2}^{#3}{#1}_i}
#\newcommand{\subfunc}[2]{{#1}_{#2}}
#\newcommand{\CC}{{\Bbb C}}
#\newcommand{\RR}{{\Bbb R}}
#\newcommand{\QQ}{{\Bbb Q}}
#\newcommand{\ZZ}{{\Bbb Z}} 
#\newcommand{\NN}{{\Bbb N}}
#\newcommand{\NNplus}{{\Bbb N}^+}

#\title{There are infinitely many primes}
#\maketitle
#
# Version 18 March 2012
#
#\section{I. Foundations}

#\subsection{1. Sets}

[set/-s] [element/-s] [belong/-s] [subset/-s]

Signature. A set is a notion.
Let A,X,Y,Z denote sets.

Work with elements.
Let x,y,z denote elements.


Signature EOfElem.  
An element of X is an element.
Let x belongs to X stand for x is an element of X.
Let x is in X stand for x belongs to X.
Let x \in X stand for x is in X.


Definition DefEmp.
\emptyset is a set that has no elements.
Let X is empty stand for X = \emptyset.
Let X is nonempty stand for X != \emptyset.


Definition DefSub.  
A subset of Y is a set X such that
every element of X belongs to Y.
Let X \subseteq Y stand for X is a subset of Y.


Lemma SubRefl.
X \subseteq X.


Lemma SubTrans.
X \subseteq Y \subseteq Z  =>  X \subseteq Z.


Axiom SubASymm.
X \subseteq Y \subseteq X  =>  X = Y.



#\subsection{2. Functions}

[function/-s]

Work with functions.
Let f,g,p denote functions.


Signature DomSet.
dom f is a set.
Let the domain of f stand for dom f.


Signature ImgElm.
Let x \in dom f. f(x) is an element.
Let \subfunc{f}{x} stand for f(x).


Definition DefSImg. 
Let X \subseteq dom f. f[X] = { f(x) | x \in X }.
Let ran f stand for f[dom f].
Let the range of f stand for ran f.

Let a function from X stand for a function f
such that dom f = X.
Let a function from X to Y stand 
for a function f such that dom f = X
and ran f \subseteq Y.

Let f : X stand for f is a function from X.
Let f : X -> Y stand for f is a function from X to Y.


Lemma ImgRng.
Let x \in dom f. f(x) belongs to ran f.


Definition DefRst.
Let X \subseteq dom f. 
f \upharpoonright X is a function g from X
such that for every x \in X g(x) = f(x).


#\subsection{3. Numbers}

[number/-s]

Work with numbers.
Let i,j,k,l,m,n,q,r denote numbers.


Definition Nat.
\NN is the set of numbers.


Signature SortsC.  
0 is a number.
Let x is nonzero stand for x != 0.


Signature SortsC.
1 is a nonzero number.


Signature SortsB.
m + n is a number.


Signature SortsB.
m \cdot n is a number.


Axiom AddAsso. (m + n) + l = m + (n + l).
Axiom AddZero.  m + 0 = m = 0 + m. 
Axiom AddComm.   m + n = n + m. 

Axiom MulAsso.  
(m \cdot n) \cdot l = m \cdot (n \cdot l).

Axiom MulUnit.  m \cdot 1 = m = 1 \cdot m.
Axiom MulZero.  m \cdot 0 = 0 = 0 \cdot m.
Axiom MulComm.  m \cdot n = n \cdot m.

Axiom AMDistr.  
m \cdot (n + l) = (m \cdot n) + (m \cdot l) and
(n + l) \cdot m = (n \cdot m) + (l \cdot m).

Axiom AddCanc.  
If l + m = l + n or m + l = n + l then m = n.

Axiom MulCanc.
Assume that l is nonzero. If 
l \cdot m = l \cdot n or m \cdot l = n \cdot l 
then m = n.

Axiom ZeroAdd.
If m + n = 0 then m = 0 and n = 0.

Lemma ZeroMul.
If m \cdot n = 0 then m = 0 or n = 0.


Definition DefLE.
m \leq n iff there exists l such that m + l = n.


Definition DefDiff.  Assume that m \leq n.
n - m is a number l such that m + l = n.


Lemma LERefl. m \leq m. 
Lemma LETran. m \leq n \leq l  =>  m \leq l.

Lemma LEAsym. m \leq n \leq m  =>  m = n. 


Let m < n stand for m != n and m \leq n.

Axiom LETotal. m \leq n or n < m. 

Lemma MonAdd. Assume that l < n.
Then m + l < m + n and l + m < n + m.


Lemma MonMul. Assume that m is nonzero and l < n.
Then m \cdot l < m \cdot n and l \cdot m < n \cdot m.


Axiom LENTr. 
n = 0 or n = 1 or 1 < n.


Lemma MonMul2. m != 0 => n \leq n \cdot m.

Proof.
Let m != 0. Then 1 \leq m.
qed.

Signature InbuiltForthelInductionRelation. m -<- n is an atom.


Axiom EmbeddingLessIntoInductionRelation. m < n => m -<- n. 

#\subsection{4. Finite Sets and Sequences}

Definition. 
\Seq{m}{n} = { i \in \NN | m \leq i \leq n }.


Definition. 
Let f be a function such that 
\Seq{m}{n} \subseteq dom f. 
\Set{f}{m}{n} = { f(i) | i \in \NN /\ m \leq i \leq n }.


Definition. f lists X in n steps iff 
dom f = \Seq{1}{n} and X = \Set{f}{1}{n}.


Definition. X is finite iff there is a function
f and a number n such that f lists X in n steps.


Definition. X is infinite iff X is not finite.


#\section{II. Prime Numbers}

#\subsection{1. Divisibility}

[divide/-s] [divisor/-s]

Definition DefDiv.
m divides n iff for some l n = m \cdot l.
Let m | n denote m divides n.
Let a divisor of n denote a number that divides n.


Definition DefQuot.
Assume that m is nonzero and m | n.
\frac{n}{m} is a number l such that n = m \cdot l.


Lemma DivTrans. l | m | n => l | n.


Lemma DivSum.
Let l | m and l | n. Then l | m + n.
Indeed if l is nonzero then 
m + n = l \cdot (\frac{m}{l} + \frac{n}{l}).


Lemma DivMin.
Let l | m and l | m + n. Then l | n.

Proof.
Assume that l,n are nonzero.
Take i such that m = l \cdot i. 
Take j such that m + n = l \cdot j.

Let us show that i \leq j.
Assume the contrary. Then j < i.
m+n = l \cdot j < l \cdot i = m. 
m \leq m+n.
m = m+n. n=0.
Contradiction. end.
 
Take k = j - i.
We have (l \cdot i) + (l \cdot k) = (l \cdot i) + n.
Hence n = l \cdot k.
qed.

Lemma DivLE.
Let m | n != 0. Then m \leq n.


Lemma DivAsso.
Let l be nonzero and divide m.
Then n \cdot \frac{m}{l} = \frac{n \cdot m}{l}.
Proof.
(l \cdot n) \cdot \frac{m}{l} = l \cdot \frac{n \cdot m}{l}.
qed.

Definition.
\NNplus = {n \in \NN | n != 0 }.


Signature.  
Let f : \Seq{m}{n} -> \NNplus.
\Product{f}{m}{n} is an element of \NNplus.


Axiom MultProd.
Let f : \Seq{m}{n} -> \NNplus.
Let m \leq j \leq n.
\subfunc{f}{j} divides \Product{f}{m}{n}.


#\subsection{2. Primes} 

[prime/-s] [compound/-s] [primenumber/-s]

Let m is trivial stand for m = 0 or m = 1.
Let m is nontrivial stand for m != 0 and m != 1.

Definition DefPrime.
q is prime iff q is nontrivial and
for every divisor m of q m = 1 or m = q.


Let m is compound stand for m is not prime.

Lemma PrimDiv.
Every nontrivial k has a prime divisor.

Proof by induction on k.
Let k be nontrivial.
Case k is prime. Obvious.
Case k is compound. 
Take a divisor m of k such that m != 1 and m != k.
#m != 0.
m is nontrivial and m -<- k.
Take a prime divisor n of m.
n is a prime divisor of k.
end.
qed.


Theorem.
The set of prime numbers is infinite.

Proof.
Let A be a finite set of prime numbers.
Take a function p and a number r such that 
p lists A in r steps.
ran p \subseteq \NNplus.
\Product{p}{1}{r} != 0.
Take n=\Product{p}{1}{r}+1.
n is nontrivial.
Take a prime divisor q of n (by PrimDiv).

Let us show that q is not an element of A.
Assume the contrary.
Take i such that (1 \leq i \leq r and q=\subfunc{p}{i}).
\subfunc{p}{i} divides \Product{p}{1}{r} (by MultProd).
Then q divides 1 (by DivMin). 
Contradiction. qed.

Hence A is not the set of prime numbers.
qed.




