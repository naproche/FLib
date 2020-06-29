[read Forthel-Dateien/SetTheory/Library/L04-Arithmetic.ftl]

[prove off]

## Pretyped Variables

Let w,x,y,z,W,X,Y,Z stand for zfsets.
Let a,b,c,d,A,B,C,D,M stand for sets.
Let o,o1,o2 stand for objects.
Let alpha, beta, gamma, delta stand for ordinals.
Let k,l,m,n stand for natural numbers.
Let f,g,h,F,G,H stand for zffunction.
Let kappa, lambda stand for cardinals.



## Ordered pairs

Axiom. Let a,b /in /VV. Then (a,b) is a zfset.
Axiom. Let x,y,X,Y be objects. (x,y) = (X,Y) => x = X /\ y = Y.

Definition. The cartesian product of A and B is
{(a,b) | a /in A /\ b /in B}.
Let A /times B stand for the cartesian product of A and B.

Lemma. Let A,B be sets. Let (a,b) /in A /times B. Then a /in A /\ b /in B.


## Relations

[synonym relation/-s]

Definition. A relation is a set R such that 
R /subset /VV /times /VV.
Let a - R - b stand for (a,b) /in R.

Lemma. Let R be a relation. x /in R => exists a,b /in /VV (x = (a,b)).

Definition. Let R be a relation. The reldomain of R is
{zfset a | exists z (a - R - z)}.
Let reldomain(R) stand for the reldomain of R.

Definition. Let R be a relation. The relrange of R is
{zfset a | exists z (z - R - a)}.
Let relrange(R) stand for the relrange of R.

Definition. Let R be a relation. The relfield of R is
relrange(R) /cup reldomain(R).
Let relfield(R) stand for the relfield of R.

Definition. Let R be a relation. Let x /in /VV. The smallerset of R relative to x is
{zfset y | y - R - x}.
Let sset(R,x) stand for the smallerset of R relative to x.

Lemma. Let R be a relation. Let x /in /VV. Then sset(R,x) /subset reldomain(R).

Definition. Let R be a relation. Let A be a set. The relrestriction of R to A is a relation RR such that
forall x,y /in /VV (x - RR - y iff (x - R - y /\ x,y /in A)).
Let R /restrict A stand for the relrestriction of R to A.

Lemma. Let R be a relation. Let A be a set. Then relfield(R /restrict A) /subset A.



## Attributes of relations

Definition. Let R be a relation. R is reflexive iff forall x /in relfield(R) (x - R - x).
Let ref(R) stand for R is reflexive.

Definition. Let R be a relation. R is irreflexive iff forall x /in relfield(R) (not (x - R - x)).
Let irref(R) stand for R is irreflexive.

Definition. Let R be a relation. R is symmetric iff forall x,y (x - R - y => y - R - x).
Let sym(R) stand for R is symmetric.

Definition. Let R be a relation. R is antisymmetric iff forall x,y (x - R - y /\ y - R - x => x = y).
Let antisym(R) stand for R is antisymmetric.

Definition. Let R be a relation. R is reltransitive iff forall x,y,z (x - R - y /\ y - R - z => x - R - z).
Let reltrans(R) stand for R is reltransitive.

Definition. Let R be a relation. R is connex iff forall x,y /in relfield(R) (x - R - y \/ y - R - x \/ x = y).
Let con(R) stand for R is connex.


## Kinds of relations

Signature. An equivalence relation is a notion.
Axiom. Let R be an equivalence relation. Then R is a relation.
Axiom. Let R be a relation. R is an equivalence relation iff ref(R) /\ sym(R) /\ reltrans(R).
Let eqrel(R) stand for R is an equivalence relation.

Definition. Let R be an equivalence relation. The equivalence class of x modulo R is {zfset y | y - R - x}.
Let [x]-R stand for the equivalence class of R modulo x.

Signature. A partial order is a notion.
Axiom. Let R be a partial order. Then R is a relation.
Axiom. Let R be a relation. Then R is a partial order iff ref(R) /\ reltrans(R) /\ antisym(R).

Signature. A linear order is a notion.
Axiom. Let R be a linear order. Then R is a relation.
Axiom. Let R be a relation. Then R is a linear order iff con(R) /\ (R is a partial order).

Signature. A partial order on A is a notion.
Axiom. Let A be a set. Let R be a partial order on A. Then R is a partial order.
Axiom. Let R be a relation. Let A be a set. Then R is a partial order on A iff (R is a partial order) /\ relfield(R) = A.

Signature. A strict partial order is a notion.
Axiom. Let R be a strict partial order. Then R is a relation.
Axiom. Let R be a relation. Then R is a strict partial order iff reltrans(R) /\ irref(R).

Lemma. Let R be a strict partial order. Let relfield(R) /neq /emptyset. Then R is not a partial order.

Signature. A strict linear order is a notion.
Axiom. Let R be a strict linear order. Then R is a relation.
Axiom. Let R be a relation. Then R is a strict linear order iff con(R) /\ (R is a strict partial order).




## Wellfounded Relations


Definition wf. Let R be a relation.  R is wellfounded iff
(forall A ((A /neq /emptyset /\ A /subset reldomain(R)) => (exists x /in A (forall y /in A (not (y - R - x)))))).

Lemma wellfounded. Let R be a wellfounded relation. Let M be a set. Let M /neq /emptyset. Let M /subset reldomain(R). Then exists x /in M (forall y /in M (not (y - R - x))).

Definition. Let R be a relation. R is strongly wellfounded iff
(R is wellfounded) /\ (forall x /in relfield(R) sset(R,x) /in /VV).

Signature. A wellorder is a notion.

Axiom. Let R be a wellorder. Then R is a relation.

Axiom. Let R be a relation. Then R is a wellorder iff (R is wellfounded) and (R is a strict linear order).

Signature. A strong wellorder is a notion.

Axiom. Let R be a strong wellorder. Then R is a relation.

Axiom. Let R be a relation. Then R is a strong wellorder iff (R is strongly wellfounded) and (R is a wellorder).

Definition. Let R be a strongly wellfounded relation. R is extensional iff forall x,y /in reldomain(R) (sset(R,x) = sset(R,y) => x = y).
Let ext(R) stand for R is extensional.

Lemma. Let R be a strong wellorder. Then R is extensional.



## Relation-reality-check


Lemma. Let R be a relation. Let forall x,y /in /VV (x - R - y iff x /in y). Then antisym(R).

Lemma. Let R be a relation. Let relfield(R) = /Ord. Let forall alpha, beta (alpha - R - beta iff alpha /in beta).
Then R is a strict linear order.

Lemma. Let R be a relation. Let forall x,y /in /VV (x - R - y iff x /in y). Then R is strongly wellfounded.



## Mostowski Collapse


Let SWR stand for a strongly wellfounded relation.
Signature. TCol SWR is a function.

Axiom. Let R be a strongly wellfounded relation. Dom(TCol R) = reldomain(R).

Axiom. Let R be a strongly wellfounded relation. Then forall x /in (reldomain(R))  (((TCol R) [x]) = ((TCol R) /caret [sset(R,x)])).

Lemma. Let R be a strongly wellfounded relation. Then (TCol R) is a zffunction.

Lemma. Let R be a strongly wellfounded relation. Then forall x /in (reldomain(R))  ((TCol R) [x] = (TCol R)^[sset(R,x)]).

Signature. eps is an object.

Axiom. eps is a relation.

Axiom. Forall x,y /in /VV (x - eps - y iff x /in y).

Lemma. reldomain(eps) = /VV.

Lemma. eps is strongly wellfounded.

Lemma. Forall x /in /VV sset(eps,x) = x.

Lemma. eps is extensional.

Lemma. Let A /subset /Ord. (eps /restrict A) is a strong wellorder.

Definition. Let x be a zfset. Let x /subset /Ord. The epsrestriction of x is
eps /restrict (x /cup (<(/bigcup x) + 1>)).
Let epsrest(x) stand for the epsrestriction of x.

Lemma. Let x be a zfset. Let x /subset /Ord. Then reldomain(epsrest(x)) = x.

Lemma. Let x /subset /Ord. Let x be a proper class. Then reldomain(eps /restrict x) = x.

Lemma. Let x be a zfset. Let x /subset /Ord. Then x /cup <(/bigcup x)+1> /subset /Ord.

Lemma. Let x be a zfset. Let x /subset /Ord. Then epsrest(x) is a strong wellorder.

Lemma. Forall x /in /VV (TCol eps)[x] = x.

Lemma. Let R be a strongly wellfounded relation. Let R be extensional. Then Trans(ran(TCol R)).

Lemma. Let R be a strongly wellfounded relation. Let R be extensional. Then (TCol R) is injective.

Lemma. Let R be a strongly wellfounded relation. Let R be extensional. Then forall x,y /in reldomain(R) ((TCol R)[x],(TCol R)[y] /in /VV /\ (x - R - y iff (TCol R)[x] /in (TCol R)[y])).

Lemma. Let R be a strong wellorder. Let reldomain(R) /in /VV. Then ran(TCol R) /in /Ord.

Lemma. Let R be a strong wellorder. Let reldomain(R) be a proper class. Then ran(TCol R) = /Ord.



## Order-type


Definition. Let R be a strong wellorder. The relordertype of R is ran(TCol R).
Let relotp(R) stand for the relordertype of R.

Lemma. Let R be a strong wellorder. Then relotp(R) /in /Ord \/ relotp(R) = /Ord.

Signature. Let x be a set. The ordertype of x is a set.
Let otp(x) stand for the ordertype of x.

Axiom. Let x be a zfset. Let x /subset /Ord. Then otp(x) = ran(TCol epsrest(x)).

Axiom. Let x /subset /Ord. Let x be a proper class. Then otp(x) = ran(TCol (eps /restrict /Ord)).

Lemma. Let x /subset /Ord. Let x be a proper class. Then otp(x) = /Ord.

Lemma. Let x be a zfset. Let x /subset /Ord. Then otp(x) /in /Ord.

Lemma. Let alpha be an ordinal. Let x /subset alpha. Then otp(x) /subset alpha.



## epshomo and epsiso

[synonym epshomo/-s]
[synonym epsiso/-s]

Signature. An epshomo is a notion.

Axiom. Let f be an epshomo. Then f is a zffunction.

Axiom. Let f be a zffunction. Then f is an epshomo iff forall x /in Dom(f) (f^[x /cap Dom(f)] /subset f[x]).

Lemma. Let f be a zffunction. f is an epshomo iff forall x,y /in Dom(f) (x /in y => f[x] /in f[y]).

Signature. An epsiso is a notion.

Axiom. Let f be an epsiso. Then f is a zffunction.

Axiom epsiso. Let f be a zffunction. Then f is an epsiso iff f is injective and forall x,y /in Dom(f) (x /in y iff f[x] /in f[y]).

Lemma. Let f be an epsiso. Then forall x /in Dom(f) (f^[x /cap Dom(f)] = f[x] /cap ran(f)).

Lemma. Let f be a zffunction. Then f is an epsiso iff f is injective and forall x /in Dom(f) (f^[x /cap Dom(f)] = f[x] /cap ran(f)).

Lemma. Let f be an epsiso. Then f^{-1} is an epsiso.

Lemma. Let f,g be epsisos. Let ran(f) /subset Dom(g). Then g /circ f is an epsiso.

Lemma. Let f be an epsiso. Let Dom(f), ran(f) be transitive. Then Dom(f) = ran(f) and forall x /in Dom(f) f[x] = x.



## Simplifying otp


Lemma. Let x /subset /Ord. Let forall alpha /in /Ord x /notin /PP alpha. Then otp(x) = /Ord.

Signature. Let x /subset /Ord. otpfunc(x) is a zffunction.

Axiom. Let x /subset /Ord. Let x /in /VV. Then otpfunc(x) = TCol epsrest(x).

Axiom. Let x /subset /Ord. Let x be a proper class. Then otpfunc(x) = TCol (eps /restrict x).

Lemma. Let x /subset /Ord. Then otpfunc(x) : x /leftrightarrow otp(x).

Lemma. Let x /subset /Ord. Then Dom(otpfunc(x)) = x /\ forall y /in x otpfunc(x)[y] = otpfunc(x)^[y /cap x].

Lemma. Let x /subset /Ord. Then otpfunc(x) is an epsiso.

Lemma. Let x /subset /Ord. Let y /in /Ord \/ y = /Ord. Then otp(x) = y iff exists f ((f is an epsiso) /\ f : x /leftrightarrow y).

Lemma. Let alpha /in /Ord. Then otp(alpha) = alpha.

Lemma. Let x be a zfset. Let x /subset /Ord. Then Card(x) /subset otp(x).

Lemma. Let x /subset /Ord. Let y /in /Ord \/ y = /Ord. Then otp(x) = y iff exists f ((f is an epsiso) /\ f : y /leftrightarrow x).




[prove on]
