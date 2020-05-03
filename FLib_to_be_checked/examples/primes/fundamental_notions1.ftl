\title{An Introduction to Number Theory}

## fundamental_notions.ftl, Version 15.3.2012

#  I. Foundations

#  1. Sets

[set/-s] [element/-s] [belong/-s] [subset/-s]

Signature Set.   A set is a notion.

Let X,Y,Z stand for sets.

Signature Element. An element is a notion.

Let x,y,z stand for elements.

Signature Element_of. An element of X is a notion.
Let x belongs to X stand for x is an element of X.
Let x << X stand for x is an element of X.

Definition Subset.  A subset of Y is a set X such that
every element of X belongs to Y.

Let X [= Y stand for X is a subset of Y.

Lemma Subset_is_reflexive. X [= X.

Lemma Subset_is_transitive. X [= Y [= Z  =>  X [= Z.

Definition Emptyset.  {} is a set that has no elements.
Let S is empty stand for S = {}.
Let S is nonempty stand for S != {}.

Axiom Extensionality.     X [= Y [= X  =>  X = Y.

Lemma. If X has no elements then X={}.

Axiom Pairing. {x,y} is a set such that for all z
(z<<{x,y} iff z=x or z=y).

## Pairing, Union, Powerset, ...
## One could remark that certain operations have good algebraic properties:
## Union is associative, commutative, idempotent. 


#  2. Functions

[function/-s]

#  Being a {\em function} is a basic notion.

Signature FunSort.  A function is a notion.

Let F,G,P stand for functions. Let x,y,z stand for elements.

## For functions, we should proceed similar to sets. Functions can extend each other,
## Functions that mutually extend each other are equal. Functions can be defined
## as part of the logic. There should be a logic construct like
## Define a function $f:A \rightarrow B$ by
## $f(a)$ is equal to the *unique* "Notion" b such that $\phi(a,b)$. The presuppositions
## are that $A$ must be a set and that one has uniqueness.

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

## Permutations want notions like injective, surjective, bijective in
## the part about functions.


#  3. Numbers

## Ganesalingam makes the point, that mathematics should
## have numbers as something inbuilt, given, and not constructed
## set theoretically.

## We want to formalize a domain CC of complex numbers, and the sets of natural, 
## integer, 
## rational and real numbers are subsets of CC. This means that some algebraic laws
## only have to be stated once and we have less difficulties with typing
## issues. We have operations like addition and multiplication.

## So we go a special way from larger to smaller number systems. Along the way we
## loose some closure properties, but we gain some other structure. The reals
## are an ordered field, the rationals consist of quotients of integers, the integers
## consist of positive and negative naturals, the naturals satisfy induction.

## It should be possible to carry this out in some detail in SAD, and
## this is a kind of test of concept. To obtain
## natural ways of notation in SAD, one has to apply some tricks, like first defining a
## noun notion "number", then allowing the words "complex", "real", etc. and so on.
## Such tricks could become "natural" in an appropriate further development of
## Naproche and SAD.

[number/-s]

#  CC is a set.

Signature Complex.  A number is a notion.

Signature Zero. 0 is a number.

Let x is nonzero stand for x != 0.

Signature SortsC.  1 is a nonzero number.

Let x is trivial stand for x = 0 \/ x = 1.
Let x is nontrivial stand for x != 0 and x != 1.

Let i,j,k,l,m,n,p,q,r,x denote numbers.

Definition. Let CC be the set of numbers.

## Note that this contains the axiom that CC is not a proper class. Think of 
## Russell's paradox.

Signature Natural. NN is a set.
Let n is natural stand for n<<NN.
Signature Integers. ZZ is a set.
Let n is integer stand for n<<ZZ.
Signature Rationals. QQ is a set.
Let n is rational stand for n<<QQ.
Signature Reals. RR is a set.
Let n is real stand for n<<RR.

Axiom. NN [= ZZ [= QQ [= RR.

## We postulate addition and multiplication of numbers. 
#  There is a basic operation $+$ which assigns to numbers $m$ and $n$ a number $m+n$.
#  There is a basic operation $*$ which assigns to numbers $m$ and $n$ a number $m*n$.

# 3.1 Complex Numbers

Signature SortsB.  m + n is a number.
Signature SortsB.  m * n is a number.

## They following axioms are satisfied. 
## We have 
## an associative situation and we should again implement some internal representation,
## where only the sequence of summands or factors is important, but bracketing does not
## occur. Also we can let * have higher precedence than +.

Axiom AddAsso.  (m + n) + l = m + (n + l).
Axiom _AddZero.  m + 0 = m = 0 + m.
Axiom AddComm. m+n=n+m.

Axiom MulAsso.  (m * n) * l = m * (n * l).
Axiom _MulUnit.  m * 1 = m = 1 * m.
Axiom _MulZero.  m * 0 = 0 = 0 * m.
Axiom MultComm. m*n=n*m.

Axiom AMDistr.  m * (n + l) = (m * n) + (m * l).

## Other distributivity missing.

## On the complex numbers, further axioms are satisfied.

Axiom. a+b is complex. 
Axiom. a*b is complex.

Axiom. a+b=b+a.
Axiom. a*b=b*a.
Axiom. (a+b)*c=(a*c)+(b*c).

## And the further field axioms, etc. We could single out the imaginary unit, ...

## We now go to the smaller number systems.

# 3.2 Real numbers

Signature. m is real is an atom.

Definition. Let R be the set of real numbers.

Axiom Subs. Any real number is complex.

Lemma. R [= C (by Subs).
Proof. Let a<<R. 
Then a is a real number. 
a is complex. 
a<<C. 
Qed.

## Do something about the linear orders <= and <.

# 3.3 Rational numbers

## Do something about representing rationals as quotients.

# 3.4 Integer numbers 

## Do something about representing integers as differences of naturals.

## Rhese might actually be interesting for some number theory
## because divisibility is better developed in the integers
## than in the naturals, because there is the difficulty with
## differences becoming negative.

[divide/-s] [divisor/-s]

Definition DefDiv.
  n divides m iff for some l (m = n * l).

Let x | y denote x divides y.
Let a divisor of x denote a number that divides x.

Definition DefQuot. Assume that m is nonzero and m | n.
  n / m is a number l such that n = m * l.

Lemma DivTrans. l | m | n => l | n.

[prove off]
Lemma DivSum.   Let l | m and l | n. Then l | m + n.
Indeed if l is nonzero then m + n = l * ((m / l) + (n / l)).
[/prove]
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

# 3.5. Natural numbers

## Here is something about induction, using the inbuilt induction of SAD.
## But this should be formulated more explicitely.

Signature IH.   n -<- m is an atom.
Axiom IH.       n < m => n -<- m.


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

#Lemma MonMul2.  m != 0 => n <= n * m.
#Indeed m != 0 => 1 <= m.

[prove off]
Lemma DivLE.    Let m | n != 0. Then m <= n.
[/prove]

Lemma DivAsso.  Let l be nonzero and divide m.
                Then n * (m / l) = (n * m) / l.
Indeed (l * n) * (m / l) = l * ((n * m) / l).

# 4. Finite sets and sequences.

## 

Definition. Seq(m,n) = { i<<Nat | m <= i <= n }.

Definition. Let F be a function such that Seq(m,n) [= Dom F . 
Set(F,m,n) = { F(i) | i<<Nat /\ m <= i <= n }.

Axiom MultProd. Let m <= i <= n. Let F be a function such that 
Seq(m,n) [= Dom F /\ Ran F [= Nat .
F(i) divides Prod(F,m,n).

Definition. F lists A in n steps iff 
(Seq(1,n) = Dom F and A = Set(F,1,n)).
Definition. A is finite iff there is a function
F and a number n such that F lists A in n steps.

Definition. A is infinite iff A is not finite.

## More on finite and also infinite things. Like permutations (we later
## want the prime factorization to be unique up to permutation). Maybe
## that permutations want notions like injective, surjective, bijective in
## the part about functions.

# 5. Elementary number theory

# 5.1 Divisibility and prime numbers

## More on divisibility

[prime/-s] [compound/-s] [primenumber/-s]

## Divisibility for "Big Products" etc.

Signature.  Let F be a function such that Seq(m,n) [= Dom F .
Prod(F,m,n) is a number.

Axiom MultTriv. Let F be a function such that Seq(m,n) [= Dom F .
1 <= Prod(F,m,n).  


Definition DefPrime.
  n is prime iff n is nontrivial and
    for every divisor m of n (m = 1 \/ m = n).

Let x is compound stand for x is not prime.

## Fundamental theorem of 

Lemma PrimDiv. Every nontrivial k has a prime divisor.
Proof by induction.
  Let k be nontrivial.
  Case k is prime. Obvious.
  Case k is compound. Obvious.
qed.

Lemma. The set of prime numbers is infinite.

Proof. Let A be a finite set of prime numbers.
Take a function P and a number r such that P lists A in r steps.
Take n=Prod(P,1,r)+1.
Take a prime divisor p of n.
Let us show that p is not an element of A.
Assume the contrary.
Take i such that (1 <= i <= r and p=P(i)).
P(i) divides Prod(P,1,r) (by MultProd).
Indeed Seq(1,r) [= Dom P and Ran P [= Nat.
Then p divides 1 (by DivMin). 
Contradiction. qed.
Hence A is not the set of prime numbers.
qed.

## .............. etc.



