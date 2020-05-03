## fundamental_notions.ftl, Version 14.3.2012

## This is a *very* rough sketch for setting up standard mathematical foundations and
## proceeding in the direction of elementary number theory like Merlin is considering.
## The text was pasted together from existing SAD examples + something on
## finite sequences in order to get a
## smooth proof of the infinity of primes, very similar to our old example from
## Proofs from THE BOOK.

## This text does no longer really run in the SAD system. Some issues have to
## be excepted from the proving process. Also in the later part of the paper,
## the word "number" should be substituted by "natural number".

## The elementary number theory should be extended along the lines that Merlin is 
## pursuing.
## We omit - like most reasonable texts on these matters - the foundational questions 
## where to get the mathematical objects from.

## I suppose that as a study of feasability, a lot of this could be carried out in SAD,
## sometimes with unpleasant tweeking and stretching the SAD system.

## I propose this sketch as a discussion paper for the Naproche week at Cambridge.
## At the moment the paper omits all linguistic and formal semantics issues.
## Ideally one should be able to do a "sum" of features in Naproche and SAD plus
## some new features described in the sequel or coming up whilst carrying out the
## programme.

#  Foundations

## We proceed axiomatically. The mathematical universe consists of undefined basic notions 
## whose properties are described by axioms.

## Along with the foundational setup, natural notions should be provided:
## 1. The system should be integrated, like Naproche, with LaTeX or TeXmacs
## 2. The usual freedoms should be available: many possible variables, like
## greek letters, decorated letters, subscripts.
## 3. Use the standard special symbols like {\Bbb R} for the set of reals
## 4. Provide grammar for the symbolic formulas dependent on the properties of
## symbols. This is standard for infix relations. But we could also do this
## for associative or even commutative operations. Internally,
## (d+(b+a))+d should just be represented as sum(a,b,d,d), without brackets,
## and in lexicographical order. (as a "bag" or "multiset").
## 5. Introduce special macros for finite sets and sequences, i.e. use the
## macros below and make them at the same time into LaTeX layout macros.
## 6. Similarly for "Big Operators" like \sum or \prod.
## 7. At the moment only variables are allowed in quantifications and
## set formations. It would be nice to allow writing complex terms in these
## constructions:
## "There is a finite set {x_1,..,x_n} of prime numbers such that \phi" is 
## shorthand for
## "There is a number n and there is a function f such that 
## f has domain {1,...,n} and every thing in the range is a prime number and
## the range of f satisfies \phi". 
## 8. In the context of functions we should have some inbuilt definition mechanism
## similar to the inbuilt mechanisms for sets:
## "Define a function f:A->B by ..."
## This should act like a Signature or Definition command.
## A could be a set, or some "setlike" type, B should be some set or type. Then we
## do not get the Russell paradox. The Definition would come with several 
## presuppositions that have to dealt with automatically. One has to think, whether
## to allow partial or only total functions.

#  1. Sets

#  Being a "set" is a basic notion.
## Some properties of sets are built into the logic of Naproche. Others have to be 
## postulated axiomatically.

[set/-s] [element/-s] [belong/-s] [subset/-s]

Signature Sets.   A set is a notion.

#  We use variables $X,Y$ to denote {\em sets}.

Let A,B,C,R,S,T,X,Y,Z stand for sets.

#  Being an element of a set $X$ is a basic notion.
#  We also say "$x$ {\em belongs to} $X$" or "$x\in X$"
#  for $x$ is an element of $X$.

Signature Ele. An element is a notion.
Signature Elements. An element of S is a notion.

Let x belongs to S stand for x is an element of S.
Let x << S stand for x is an element of S.

#  1.1. Definition. A set $X$ is a {\em subset} of a set $Y$, or
#  $X\subseteq Y$, if
#  every element of $X$ belongs to $Y$.

Definition Subset.  A subset of S is a set T such that
                        every element of T belongs to S.

Let S [= T stand for S is a subset of T.

## One can show that $\subseteq$ is reflexive and transitive.
#  1.2. Lemma. $A \subseteq A$.

Lemma SubRefl.      A [= A.

#  1.3. Lemma. If $X \subseteq Y \subseteq Z$ then $X \subseteq Z$.

Lemma SubTrans.     A [= B [= C  =>  A [= C.

## This may have an influence on the grammatical properties of the symbol
## $\subseteq$. In particular one can form $\subseteq$-chains.

#  Let $\emptyset$ denote a set that has no elements. We say
#  $X$ is {\em empty} for $X=\emptyset$. $X$ is {\em nonempty}
#  if $X \neq \emptyset$.

Definition DefEmp.  {} is a set that has no elements.

Let S is empty stand for S = {}.
Let S is nonempty stand for S != {}.

## The axiom of extensionality expresses that sets are only determined
## by their elements:
#  1.4. Axiom of Extensionality. If $X\subseteq Y \subseteq Z$ then
# $X=Y$.

Axiom SubASymm.     A [= B [= A  =>  A = B.

## The axiom of extensionality implies that the empty set is uniquely determined.
#  1.5. Lemma. Let $X$ be a set that has no elements. Then $X=\emptyset$.

Lemma. If S has no elements then S={}.

## The further axioms of set theory imply that the universe of sets is closed
## under many important operations.

## Pairing, Union, Powerset, ...
## One could remark that certain operations have good algebraic properties:
## Union is associative, commutative, idempotent. Maybe one should introduce 
## a general internal normal form for terms formed with unions, so that
## many obvious equivalences are internally identical. It suffices e.g. to
## list all summands of the union without repetition in ascending order. Since
## the empty set is neutral for unions, empty summands can internally be left away.
## Similar mechanism could be discussed later for sums, products, etc.
## Also the set formation term {x,y,z} is associative, commutative and idempotent.
## One could say a bit about preferences, for example that
## intersection binds more than union.


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



