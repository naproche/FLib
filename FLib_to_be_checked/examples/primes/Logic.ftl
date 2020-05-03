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

Signature Ele. An element is a set.
Signature Elements. An element of S is a notion.

Let x belongs to S stand for x is an element of S.
Let x << S stand for x is an element of S.
Let x </< S stand for x is not an element of S.

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

Let a surjection from D onto R stand for a function F
                     such that D is the domain of F and R is the range of F.

## Permutations want notions like injective, surjective, bijective in
## the part about functions.

Signature Symbol. A symbol is a notion.
Signature. equiv is a symbol.
Signature. neg is a symbol.

Lemma. equiv != neg.
