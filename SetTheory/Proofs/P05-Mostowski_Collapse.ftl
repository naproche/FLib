[read Forthel-Dateien/SetTheory/Library/L04-Arithmetic.ftl]

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

Lemma. Let A,B be sets. Let a,b be objects. Let (a,b) /in A /times B. Then a /in A /\ b /in B.

Lemma. Forall x,y /in /VV (x /times y /in /VV).
Proof.
  Let x,y /in /VV.
  Define f[i] = {(i,j) | j /in y} for i in x.
  Forall z /in x f[z] /in /VV.
  Proof.
    Let z /in x.
    Define g[i] = (z,i) for i in y.
    Then g is a zffunction.
    Proof.
      Let i /in y.
      Then g[i] /in /VV.
    end.
    f[z] /subset g^[y].
    g^[y] /subset f[z].
    Then f[z] /in /VV.
  end.
  Then x /times y /subset /bigcup f^[x].
  Proof.
    Let pair /in x /times y. 
    Take zfsets a,b such that a /in x /\ b /in y /\ pair = (a,b).
    Then pair /in f[a].
  end.
  Then f^[x] /in /VV.
qed.


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

Definition. Let R be a relation. R is symmetric iff forall x,y /in relfield(R) (x - R - y => y - R - x).
Let sym(R) stand for R is symmetric.

Definition. Let R be a relation. R is antisymmetric iff forall x,y /in relfield(R) (x - R - y /\ y - R - x => x = y).
Let antisym(R) stand for R is antisymmetric.

Definition. Let R be a relation. R is reltransitive iff forall x,y,z /in relfield(R) (x - R - y /\ y - R - z => x - R - z).
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
Proof.
  M is a set. M /neq /emptyset /\ M /subset reldomain(R).
  Then exists x /in M (forall y /in M (not (y - R - x))) (by wf).
qed.

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
Proof.
  R is connex.
  Then (forall x,y /in relfield(R) (x - R - y \/ y - R - x \/ x = y)).
  Let x, y /in reldomain(R). Then x,y /in relfield(R). Then (x - R - y \/ y - R - x \/ x = y).
qed.


# Relation-reality-check

Lemma. Let R be a relation. Let forall x,y /in /VV (x - R - y iff x /in y). Then antisym(R).
Proof by contradiction. Assume the contrary. 
  Take x,y such that (x,y /in /VV /\ x - R - y /\ y - R - x /\ x /neq y).
  Define A = {zfset z | z = x \/ z = y}.
  Contradiction.
qed.

Lemma. Let R be a relation. Let relfield(R) = /Ord. Let forall alpha, beta (alpha - R - beta iff alpha /in beta).
Then R is a strict linear order.
Proof. reltrans(R).
  irref(R).
  (R is a strict partial order).
  Forall alpha, beta /in /Ord (alpha /in beta \/ beta /in alpha \/ alpha = beta).
  con(R).
qed.

Lemma. Let R be a relation. Let forall x,y /in /VV (x - R - y iff x /in y). Then R is strongly wellfounded.
Proof. 
  reldomain(R) = /VV.
  R is wellfounded.
  Proof.
    Let A be a set. Let A /neq /emptyset /\ A /subset /VV. Take a set b such that (b /in A /\ forall c /in b c /notin A).
    Then forall y /in A (not (y - R - b)).
  end.
  Let x /in /VV. Then sset(R,x) = x.
qed.



## Mostowski Collapse


Let SWR stand for a strongly wellfounded relation.
Signature. TCol SWR is a function.

Axiom. Let R be a strongly wellfounded relation. Dom(TCol R) = reldomain(R).
Axiom. Let R be a strongly wellfounded relation. Then forall x /in (reldomain(R))  (((TCol R) [x]) = ((TCol R) /caret [sset(R,x)])).


Lemma. Let R be a strongly wellfounded relation. Then (TCol R) is a zffunction.
Proof.
  Define phi[n] =
    Case (TCol R) [n] /in /VV -> 0,
    Case (TCol R) [n] /notin /VV -> 1
  for n in reldomain(R).

  Forall x /in reldomain(R) (forall y /in sset(R,x) phi[y] = 0 => phi[x] = 0).
  Proof.
    Let x /in reldomain(R). Let forall y /in sset(R,x) phi[y] = 0.
    Define f[n] = (TCol R) [n] for n in sset(R,x).
    Then (f is a zffunction).
    Proof.
      Let n /in Dom(f). Then f[n] /in /VV.
    end.
    (TCol R) /caret [sset(R,x)] = f^[sset(R,x)].
    (TCol R) [x] = (TCol R) /caret [sset(R,x)].
    Then (TCol R) [x] /in /VV.
  end.

  Define M = {zfset x | x /in reldomain(R) /\ phi[x] = 0}.
  Let N = reldomain(R) /setminus M.
  Case N = /emptyset. 
    Then M = reldomain(R). 
    Then forall x /in reldomain(R) phi[x] = 0.
    Dom(TCol R) = reldomain(R).
    Then forall x /in Dom(TCol R) (TCol R)[x] /in /VV.
  end.
  Case N /neq /emptyset.
    R is wellfounded.
    Exists x /in N (forall y /in N (not (y - R - x))) (by wellfounded).
    Take a zfset x such that (x /in N /\ (forall y /in N (not (y - R - x)))).
    Then forall y /in sset(R,x) y /notin N.
    Then forall y /in sset(R,x) phi[y] = 0.
    Then phi[x] = 0.
    Contradiction.
  end.
qed.


Lemma. Let R be a strongly wellfounded relation. Then forall x /in (reldomain(R))  ((TCol R) [x] = (TCol R)^[sset(R,x)]).
Proof.
  TCol R is a zffunction.
  Let x /in reldomain(R).
  Then (TCol R) /caret [sset(R,x)] = (TCol R)^[sset(R,x)].
qed.


Signature. eps is an object.
Axiom. eps is a relation.
Axiom. Forall x,y /in /VV (x - eps - y iff x /in y).
Lemma. reldomain(eps) = /VV.
Lemma. eps is strongly wellfounded.
Lemma. Forall x /in /VV sset(eps,x) = x.
Lemma. eps is extensional.

Lemma. Let A /subset /Ord. (eps /restrict A) is a strong wellorder.
Proof.
  relfield(eps /restrict A) /subset A.
  reldomain(eps /restrict A) /subset /Ord.
  (eps /restrict A) is wellfounded.
  Proof.
    Let B /subset reldomain(eps /restrict A). Let B /neq /emptyset. Then B /subset /Ord.
    Take a set x such that x /in B /\ forall y /in x (y /notin B).
    Then forall y ((y - eps - x) => (y /notin B)).
    Then forall y ((y - (eps /restrict A) - x) => (y /notin B)).
  end.
  (eps /restrict A) is strongly wellfounded.
  Proof.
    Let x /in relfield(eps /restrict A). Then sset((eps /restrict A),x) /subset x.
    Then sset((eps /restrict A),x) /in /VV.
  end.
  (eps /restrict A) is a strict linear order.
  Proof.
    (eps /restrict A) is connex.
    Proof.
      Let x,y /in relfield(eps /restrict A). Then x,y /in A.
      Then x,y /in /Ord. Forall alpha, beta /in /Ord (alpha /in beta \/ beta /in alpha \/ alpha = beta).
      Then x /in y \/ y /in x \/ x = y.
    end.
    (eps /restrict A) is irreflexive.
    (eps /restrict A) is reltransitive.
    Proof.
      Let x, y, z /in /VV. Let x - (eps /restrict A) - y /\ y - (eps /restrict A) - z.
      Then x,y,z /in /Ord /\ x /in y /\ y /in z.
      Then x /in z.
      Then x - (eps /restrict A) - z.
    end.
  end.
qed.


# This is just a shortcut for the restirction of the relation eps such that the domain is x.
Definition. Let x be a zfset. Let x /subset /Ord. The epsrestriction of x is
eps /restrict (x /cup (<(/bigcup x) + 1>)).
Let epsrest(x) stand for the epsrestriction of x.

Lemma. Let x be a zfset. Let x /subset /Ord. Then reldomain(epsrest(x)) = x.
Proof.
  ((/bigcup x)+1) /in x /cup (<(/bigcup x) + 1>).
  Let y /in x.
  Then y /in ((/bigcup x) + 1).
  Proof.
    y, /bigcup x /in /Ord.
    Let a = /bigcup x.
    a,y /in /Ord.
    Then a /in y \/ y /in a \/ a = y (by TotalOrder).
    Then y /in /bigcup x \/ /bigcup x /in y \/ y = /bigcup x.
    Then y /in (/bigcup x) ++.
  end.
  Then y - (epsrest(x)) - ((/bigcup x) + 1).
  Then y /in reldomain(epsrest(x)).
  Let z /in reldomain(epsrest(x)). 
  Take a zfset a such that z - (epsrest(x)) - a.
  Then z /in a /\ z,a /in (x /cup </bigcup x + 1>). 
  Then z /in x.
qed.


Lemma. Let x /subset /Ord. Let x be a proper class. Then reldomain(eps /restrict x) = x.
Proof.
  reldomain(eps /restrict x) /subset x.
  x /subset reldomain(eps /restrict x).
  Proof.
    Let y /in x.
    Then exists z /in x (y /in z).
    Proof by contradiction. Assume the contrary.
      Then forall z /in x (z /subset y).
      Then forall z /in x (z /in y \/ z = y).
      Then x /subset y+1.
      Then x /in /VV.
      Contradiction.
    end.
    Take a zfset z such that z /in x /\ y /in z.
    Then y - eps - z.
    Then y /in reldomain (eps /restrict x).
  end.
qed.

Lemma. Let x be a zfset. Let x /subset /Ord. Then x /cup <(/bigcup x)+1> /subset /Ord.

Lemma. Let x be a zfset. Let x /subset /Ord. Then epsrest(x) is a strong wellorder.


Lemma. Forall x /in /VV (TCol eps)[x] = x.
Proof by induction.
  Let x /in /VV.
  sset(eps,x) = x.
  (TCol eps)[x] = (TCol eps)^[x].
  Forall y /in x (TCol eps)[y] = y.
  Then (TCol eps)^[x] = x.
qed.


Lemma. Let R be a strongly wellfounded relation. Let R be extensional. Then Trans(ran(TCol R)).
Proof.
  Let x /in ran(TCol R). Take a zfset a such that a /in reldomain(R) /\ x = (TCol R)[a].
  Let y /in x. Then y /in (TCol R)^[sset(R,a)].
  Take a zfset b such that b /in sset(R,a) /\ y = (TCol R)[b].
  Then y /in ran(TCol R).
qed.


Lemma. Let R be a strongly wellfounded relation. Let R be extensional. Then (TCol R) is injective.
Proof.
  Define A = {zfset x | x /in ran(TCol R) /\ exists y,z (y /neq z /\ y,z /in reldomain(R) /\ (TCol R)[y] = x /\ (TCol R)[z] = x)}.
  Then A is a set.
  Case A = /emptyset. 
    Then forall y,z /in reldomain(R) (y /neq z => (TCol R)[y] /neq (TCol R)[z]).
    Proof by contradiction. Assume the contrary.
      Take y,z /in reldomain(R) such that y /neq z /\ (TCol R)[y] = (TCol R)[z].
      Then (TCol R)[y] /in A.
      Contradiction.
    end.
    Then (TCol R) is injective. 
  end.

  Case A /neq /emptyset. A /subset ran(TCol R). Take a zfset x such that x /in A /\ forall y /in x y /notin A.
    Take zfsets y1, y2 such that (y1 /neq y2 /\ y1,y2 /in reldomain(R) /\ (TCol R)[y1] = x /\ (TCol R)[y2] = x).
    sset(R,y1) /subset sset(R,y2).
    Proof.
      Let u1 /in sset(R,y1). 
      (TCol R)[y1] = (TCol R)^[sset(R,y1)]. 
      (TCol R)[y1] = x.
      (TCol R)[u1] /in (TCol R)^[sset(R,y1)].
      Then (TCol R)[u1] /in x. 
      Then (TCol R)[u1] /in (TCol R)^[sset(R,y2)].
      Take a zfset u2  such that u2 /in sset(R,y2) /\ (TCol R)[u1] = (TCol R)[u2].
      Then (TCol R)[u1] /notin A.
      Then u1 = u2.
      Proof by contradiction. Assume the contrary. 
        Then u1 /neq u2.
        Let w = (TCol R)[u1]. 
        w /notin A.
        w is a zfset.
        u1,u2 /in reldomain(R).
        u1 /neq u2.
        Then (TCol R)[u1] = w /\ (TCol R)[u2] = w => w /in A.
        Then w /in A. 
        Contradiction.
      end.
    end.
    sset(R,y2) /subset sset(R,y1).
    Proof.
      Let u1 /in sset(R,y2). 
      (TCol R)[y2] = (TCol R)^[sset(R,y2)].
      (TCol R)[y2] = x.
      (TCol R)[u1] /in (TCol R)^[sset(R,y2)].
      Then (TCol R)[u1] /in x.
      Then (TCol R)[u1] /in (TCol R)^[sset(R,y1)].
      Take a zfset u2  such that u2 /in sset(R,y1) /\ (TCol R)[u1] = (TCol R)[u2].
      Then (TCol R)[u1] /notin A.
      Then u1 = u2.
      Proof by contradiction. Assume the contrary. 
        Then u1 /neq u2.
        Let w = (TCol R)[u1]. 
        w /notin A. 
        w is a zfset.
        u1,u2 /in reldomain(R).
        u1 /neq u2.
        Then (TCol R)[u1] = w /\ (TCol R)[u2] = w => w /in A.
        Then w /in A. 
        Contradiction.
      end.
    end.
    sset(R,y1) = sset(R,y2). 
    Then y1 = y2. 
    Contradiction.
  end.
qed.


Lemma. Let R be a strongly wellfounded relation. Let R be extensional. Then forall x,y /in reldomain(R) ((TCol R)[x],(TCol R)[y] /in /VV /\ (x - R - y iff (TCol R)[x] /in (TCol R)[y])).
Proof.
  Let x,y /in reldomain(R). 
  Then (TCol R)[x],(TCol R)[y] /in /VV.
  x - R - y => (TCol R)[x] /in (TCol R)[y].
  Proof.
    Let x - R - y. (TCol R)[y] = (TCol R)^[sset(R,y)].
  end.
  (TCol R)[x] /in (TCol R)[y] => x - R - y.
  Proof.
    Let (TCol R)[x] /in (TCol R)[y]. (TCol R)[y] = (TCol R)^[sset(R,y)].
    Take a set z such that z /in sset(R,y) /\ (TCol R)[x] = (TCol R)[z].
    (TCol R) is injective. 
    Then forall a,b /in reldomain(R) ((TCol R)[a] = (TCol R)[b] => a = b).
    x,z /in reldomain(R).
    Then (TCol R)[x] = (TCol R)[z] => x = z.
    (TCol R)[x] = (TCol R)[z].
    TCol R is injective.
    Then x = z.
    Then x - R - y.
  end.
qed.


Lemma. Let R be a strong wellorder. Let reldomain(R) /in /VV. Then ran(TCol R) /in /Ord.
Proof.
  Trans(ran(TCol R)).
  ran(TCol R) /in /VV.
  Proof.
    ran(TCol R) = (TCol R)^[reldomain(R)].
  end.
  Forall x /in ran(TCol R) Trans(x).
  Proof.
    Let x /in ran(TCol R). 
    Take a zfset y such that y /in reldomain(R)  /\ x = (TCol R)[y].
    Let x1 /in x. 
    Then x1 /in (TCol R)^[sset(R,y)]. 
    Take a zfset y1 such that y1 /in sset(R,y) /\ x1 = (TCol R)[y1].
    Let x2 /in x1.
    Then x2 /in (TCol R)^[sset(R,y1)]. 
    Take a zfset y2 such that y2 /in sset(R,y1) /\ x2 = (TCol R)[y2].
    Then y2 /in sset(R,y).
    Proof.
      y2 - R - y1.
      y1 - R - y.
      reltrans(R).
      Then y2 - R - y.
    end.
    x = (TCol R)^[sset(R,y)].
    (TCol R)[y2] /in (TCol R)^[sset(R,y)].
    Then (TCol R)[y2] /in x.
    Then x2 /in x.
  end.
qed.


Lemma. Let R be a strong wellorder. Let reldomain(R) be a proper class. Then ran(TCol R) = /Ord.
Proof.
  Trans(ran(TCol R)).
  Forall x /in ran(TCol R) Trans(x).
  Proof.
    Let x /in ran(TCol R). Take a zfset y such that y /in reldomain(R)  /\ x = (TCol R)[y].
    Let x1 /in x. 
    Then x1 /in (TCol R)^[sset(R,y)]. 
    Take a set y1 such that y1 /in sset(R,y) /\ x1 = (TCol R)[y1].
    Let x2 /in x1. 
    Then x2 /in (TCol R)^[sset(R,y1)]. 
    Take a set y2 such that y2 /in sset(R,y1) /\ x2 = (TCol R)[y2].
    Then y2 /in sset(R,y).
    Proof.
      y2 - R - y1.
      y1 - R - y.
      reltrans(R).
      Then y2 - R - y.
    end.
    x = (TCol R)^[sset(R,y)].
    (TCol R)[y2] /in (TCol R)^[sset(R,y)].
    Then (TCol R)[y2] /in x.
    Then x2 /in x.
  end.
  Then ran(TCol R) /subset /Ord.
  Let alpha /in /Ord. 
  Then alpha /in ran(TCol R).
  Proof by contradiction. Assume the contrary. 
    Then alpha /notin ran(TCol R).
    Then forall beta /in /Ord (alpha /in beta => beta /notin ran(TCol R)).
    Forall a,b /in /Ord (a /in b \/ b /in a \/ a = b).
    Forall a /in /Ord (a /in ran(TCol R) => alpha /notin a /\ alpha /neq a).
    Then ran(TCol R) /subset alpha.
    Then ran(TCol R) /in /VV.
    (TCol R) is injective.
    Then (TCol R) : reldomain(R) /leftrightarrow ran(TCol R).
    Then (TCol R)^{-1} : ran(TCol R) /leftrightarrow reldomain(R).
    Then reldomain(R) = ((TCol R)^{-1})^[ran(TCol R)].
    Then reldomain(R) /in /VV.
    Contradiction.
  end.
qed.



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
Proof.
  otp(x) = ran(TCol epsrest(x)).
qed.


Lemma. Let alpha be an ordinal. Let x /subset alpha. Then otp(x) /subset alpha.
Proof.
  x /subset /Ord.
  Forall y /in x (TCol epsrest(x))[y] /subset y.
  Proof by induction.
    Let y /in x.
    Then (TCol epsrest(x))[y] /subset y.
    Proof.
      (TCol epsrest(x))[y] = (TCol epsrest(x))^[sset(epsrest(x),y)].
      Let z /in (TCol epsrest(x))[y].  
      Take a zfset a such that a /in sset(epsrest(x),y) /\ z = (TCol epsrest(x))[a].
      Then a /in y.
      Then (TCol epsrest(x))[a] /subset a.
      Then z /subset a.
      a /in /Ord.
      (TCol epsrest(x))[a] /in /Ord.
      z /in /Ord.
      a /notin z.
      Then z /in a \/ z = a (by TotalOrder).
      Then z /in y.
    end.
  end.
  Then ran(TCol epsrest(x)) /subset alpha.
  Proof.
    Let y /in ran(TCol epsrest(x)). 
    Take a zfset z such that z /in x /\ y = (TCol epsrest(x))[z].
    Then y /subset z.
    z /in alpha.
    y, alpha /in /Ord.
    Then y /in alpha \/ alpha /in y \/ alpha = y.
    Then y /in alpha.
    Proof.
      Case y /in alpha. end.
      Case alpha = y. Then alpha /subset z /\ z /in alpha. Contradiction. end.
      Case alpha /in y. Then alpha /in z. z /in alpha. Contradiction. end.
    end.
  end.
qed.



## epshomo and epsiso

[synonym epshomo/-s]
[synonym epsiso/-s]

Signature. An epshomo is a notion.

Axiom. Let f be an epshomo. Then f is a zffunction.
Axiom. Let f be a zffunction. Then f is an epshomo iff
forall x /in Dom(f) (f^[x /cap Dom(f)] /subset f[x]).

Lemma. Let f be a zffunction. f is an epshomo iff forall x,y /in Dom(f) (x /in y => f[x] /in f[y]).
Proof.
  (f is an epshomo) => forall x,y /in Dom(f) (x /in y => f[x] /in f[y]).
  Proof.
    Let f be an epshomo.
    Let x,y /in Dom(f).
    Let x /in y.
    (f^[y /cap Dom(f)] /subset f[y]).
    x /in y /cap Dom(f).
    Then f[x] /in f^[y /cap Dom(f)].
  end.
  (Forall x,y /in Dom(f) (x /in y => f[x] /in f[y])) => (f is an epshomo).
  Proof.
    Let forall x,y /in Dom(f) (x /in y => f[x] /in f[y]).
    Let x /in Dom(f).
    Then f^[x /cap Dom(f)] /subset f[x].
    Proof.
      Let z /in f^[x /cap Dom(f)].
      Take a zfset y such that y /in x /cap Dom(f) /\ f[y] = z.
      Then f[y] /in f[x].
      Then z /in f[x].
    end.
  end.
end.


Signature. An epsiso is a notion.

Axiom. Let f be an epsiso. Then f is a zffunction.
Axiom epsiso. Let f be a zffunction. Then f is an epsiso iff f is injective and forall x,y /in Dom(f) (x /in y iff f[x] /in f[y]).

Lemma. Let f be an epsiso. Then forall x /in Dom(f) (f^[x /cap Dom(f)] = f[x] /cap ran(f)).
Proof.
  Let x /in Dom(f).
  f^[x /cap Dom(f)] /subset f[x] /cap ran(f).
  Proof.
    Let y /in f^[x /cap Dom(f)].
    Take a zfset z such that z /in x /cap Dom(f) /\ f[z] = y.
    z,x /in Dom(f).
    f is a zffunction.
    Then z /in x iff f[z] /in f[x] (by epsiso).
    Then y /in f[x].
    y /in ran(f).
  end.
  f[x] /cap ran(f) /subset f^[x /cap Dom(f)].
  Proof.
    Let y /in f[x] /cap ran(f).
    Take a zfset z such that z /in Dom(f) /\ f[z] = y.
    f[z] /in f[x].
    z,x /in Dom(f).
    f is a zffunction.
    Then z /in x (by epsiso).
    Then y /in f^[x /cap Dom(f)].
  end.
qed.


Lemma. Let f be a zffunction. Then f is an epsiso iff f is injective and forall x /in Dom(f) (f^[x /cap Dom(f)] = f[x] /cap ran(f)).
Proof.
  (f is an epsiso) => (f is injective and forall x /in Dom(f) (f^[x /cap Dom(f)] = f[x] /cap ran(f))).
  (f is injective and forall x /in Dom(f) (f^[x /cap Dom(f)] = f[x] /cap ran(f))) => (f is an epsiso).
  Proof.
    Let f be injective.
    Let forall x /in Dom(f) (f^[x /cap Dom(f)] = f[x] /cap ran(f)).
    Then f is an epsiso.
    Proof.
      Let x,y /in Dom(f).
      Then x /in y iff f[x] /in f[y].
      Proof.
        x /in y => f[x] /in f[y].
        Proof.
          Let x /in y.
          f^[y /cap Dom(f)] = f[y] /cap ran(f).
          f[x] /in f^[y /cap Dom(f)].
          Then f[x] /in f[y].
        end.
        f[x] /in f[y] => x /in y.
        Proof.
          Let f[x] /in f[y].
          f^[y /cap Dom(f)] = f[y] /cap ran(f).
          f[x] /in f[y] /cap ran(f).
          Then f[x] /in f^[y /cap Dom(f)].
          Take a zfset z such that z /in y /cap Dom(f) /\ f[x] = f[z].
          Then x = z.
        end.
      end.
    end.
  end.
qed.


Lemma. Let f be an epsiso. Then f^{-1} is an epsiso.
Proof.
  f^{-1} is injective.
  Proof by contradiction. Assume the contrary.
    Dom(f^{-1}) = ran(f).
    Take zfsets x,y such that x,y /in Dom(f^{-1}) /\ x /neq y /\ f^{-1}[x] = f^{-1}[y].
    Take a zfset z such that z /in Dom(f) /\ f[z] = x.
    Then f[z] = y.
    Then x = y.
    Contradiction.
  end.
  Let x,y /in Dom(f^{-1}).
  Then x,y /in ran(f).
  Take zfsets a,b such that a,b /in Dom(f) /\ f[a] = x /\ f[b] = y.
  f^{-1}[x] = a.
  f^{-1}[y] = b.
  f is a zffunction.
  a /in b iff f[a] /in f[b] (by epsiso).
  Then x /in y iff f^{-1}[x] /in f^{-1}[y].
qed.


Lemma. Let f,g be epsisos. Let ran(f) /subset Dom(g). Then g /circ f is an epsiso.
Proof.
  g /circ f is injective.
  Let x,y /in Dom(g /circ f).
  Then x,y /in Dom(f).
  f is a zffunction.
  Then x /in y iff f[x] /in f[y] (by epsiso).
  f[x], f[y] /in Dom(g).
  g is a zffunction.
  Then f[x] /in f[y] iff g[f[x]] /in g[f[y]] (by epsiso).
  g[f[x]] = (g /circ f)[x].
  g[f[y]] = (g /circ f)[y].
  Then x /in y iff (g /circ f)[x] /in (g /circ f)[y].
qed.


Lemma. Let f be an epsiso. Let Dom(f), ran(f) be transitive. Then Dom(f) = ran(f) and forall x /in Dom(f) f[x] = x.
Proof.
  f is a zffunction.
  Let A = Dom(f).
  Let B = ran(f).
  Forall x /in A f[x] = x.
  Proof by induction.
    Let x /in A.
    x /subset f[x].
    Proof.
      Let y /in x.
      f is a zffunction.
      x,y /in Dom(f).
      Then f[y] /in f[x] (by epsiso).
      f[y] = y.
      Then y /in f[x].
    end.
    f[x] /subset x.
    Proof.
      Let y /in f[x].
      Then y /in B.
      Forall a,b /in B (a /in b => f^{-1}[a] /in f^{-1}[b]).
      Proof.
        Let a,b /in B.
        Let a /in b.
        Take zfsets aa,bb such that aa,bb /in A /\ f[aa] = a /\ f[bb] = b.
        aa /in bb iff f[aa] /in f[bb].
        Then f[aa] /in f[bb].
        Then aa /in bb.
      end.
      Then f^{-1}[y] /in f^{-1}[f[x]].
      f^{-1}[f[x]] = x.    
      Then f^{-1}[y] /in x.
      f[f^{-1}[y]] = y.
      Then f^{-1}[y] = y.
      Then y /in x.
    end.
  end.
  A /subset B.
  B /subset A.
  Proof.
    Let x /in B. Take y such that y /in A /\ f[y] = x. Then x = y. Then x /in A.
  end.
  A = B.
qed.


## Simplifying otp

Lemma. Forall x /subset /Ord (x /in /VV => otp(x) /in /Ord).

Lemma. Forall x /subset /Ord (x /notin /VV => otp(x) = /Ord).

Lemma. Let x /subset /Ord. Let forall alpha /in /Ord x /notin /PP alpha. Then otp(x) = /Ord.
Proof.
  x is a proper class.
  Proof by contradiction. Assume the contrary.
    Then x /in /VV.
    Then /bigcup x /in /Ord.
    Forall alpha /in /Ord exists i /in x (i /notin alpha).
    Forall alpha /in /Ord exists i /in x (alpha /in i).
    Proof.
      Let alpha /in /Ord.
      Take a zfset i such that i /in x /\ i /notin alpha + 1.
      Then alpha + 1 /subset i.
      Then alpha /in i.
    end.
    Then /Ord /subset /bigcup x.
    Contradiction.
  end.
qed.


Signature. Let x /subset /Ord. otpfunc(x) is a zffunction.

Axiom. Let x /subset /Ord. Let x /in /VV. Then otpfunc(x) = TCol epsrest(x).
Axiom. Let x /subset /Ord. Let x be a proper class. Then otpfunc(x) = TCol (eps /restrict x).


Lemma. Let x /subset /Ord. Then otpfunc(x) : x /leftrightarrow otp(x).
Proof.
  Case x /in /VV.
    TCol epsrest(x) : x /leftrightarrow otp(x).
  end.
  Case x /notin /VV.
    reldomain(eps /restrict x) is a proper class.
    Then ran(TCol (eps /restrict x)) = /Ord.
    TCol (eps /restrict x) is injective.
    Dom(TCol (eps /restrict x)) = x.
    Then TCol (eps /restrict x) : x /leftrightarrow /Ord.
  end.
qed.


Lemma. Let x /subset /Ord. Then Dom(otpfunc(x)) = x /\ forall y /in x otpfunc(x)[y] = otpfunc(x)^[y /cap x].
Proof.
  otpfunc(x) : x /leftrightarrow otp(x).
  Then Dom(otpfunc(x)) = x.
  Forall y /in x otpfunc(x)[y] = otpfunc(x)^[y /cap x].
  Proof.
    Let y /in x.
    Case x /in /VV.
      (TCol epsrest(x))[y] = (TCol epsrest(x))^[sset(epsrest(x),y)].
      sset(epsrest(x),y) = y /cap x.
      Proof.
        y /cap x /subset sset(epsrest(x),y).
        Proof.
          Let z /in y /cap x.
          Then z - eps - y.
          z,y /in x.
          Then z - epsrest(x) - y.
          Then z /in sset(epsrest(x),y).
        end.
        sset(epsrest(x),y) /subset y /cap x.
      end.
    end.
    Case x /notin /VV.
      (TCol (eps /restrict x))[y] = (TCol (eps /restrict x))^[sset((eps /restrict x),y)].
      sset((eps /restrict x),y) /subset y /cap x.
      y /cap x /subset sset((eps /restrict x),y).
    end.
  end.
qed.


Lemma. Let x /subset /Ord. Then otpfunc(x) is an epsiso.
Proof.
  otpfunc(x) is injective.
  Dom(otpfunc(x)) = x.
  Let y,z /in x.
  Then y /in z iff otpfunc(x)[y] /in otpfunc(x)[z].
  Proof.
    y /in z => otpfunc(x)[y] /in otpfunc(x)[z].
    Proof.
      Let y /in z.
      Then otpfunc(x)[y] /in otpfunc(x)[z].
      Proof.
        Forall a /in x otpfunc(x)[a] = otpfunc(x)^[a /cap x].
        y /in z /cap x.
      end.
    end.
    otpfunc(x)[y] /in otpfunc(x)[z] => y /in z.
    Proof.
      Let otpfunc(x)[y] /in otpfunc(x)[z].
      otpfunc(x)[z] = otpfunc(x)^[z /cap x].
      Then otpfunc(x)[y] /in otpfunc(x)^[z /cap x].
      Take a zfset a such that a /in z /cap x /\ otpfunc(x)[a] = otpfunc(x)[y].
      Then a = y.
      Proof by contradiction. Assume the contrary.
        Then a /neq y.
        a,y /in Dom(otpfunc(x)).
        otpfunc(x) is injective.
        Then otpfunc(x)[a] /neq otpfunc(x)[y].
        Contradiction.
      end.
    end.
  end.
qed.


Lemma. Let x /subset /Ord. Let y /in /Ord \/ y = /Ord. Then otp(x) = y iff exists f ((f is an epsiso) /\ f : x /leftrightarrow y).
Proof.
  otp(x) = y => exists f ((f is an epsiso) /\ f : x /leftrightarrow y).
  Proof.
    Let otp(x) = y.
    Then otpfunc(x) : x /leftrightarrow y and otpfunc(x) is an epsiso.
  end.
  Exists f ((f is an epsiso) /\ f : x /leftrightarrow y) => otp(x) = y.
  Proof.
    Let exists f ((f is an epsiso) /\ f : x /leftrightarrow y).
    Take an epsiso f such that f : x /leftrightarrow y.
    Let z = otp(x).
    Then otpfunc(x) : x /leftrightarrow z.
    otpfunc(x) is an epsiso.
    Let g = otpfunc(x)^{-1}.
    Then g is an epsiso.
    Dom(g) = z.
    ran(g) = x.
    Proof.
      Let a /in ran(g).
      Take a zfset b such that b /in Dom(g) /\ g[b] = a.
      b /in ran(otpfunc(x)).
      Take a zfset c such that c /in Dom(otpfunc(x)) /\ otpfunc(x)[c] = b.
      Then a = c.
    end.
    g : z /leftrightarrow x.
    ran(g) /subset Dom(f).
    Then f /circ g is an epsiso.
    f /circ g : z /leftrightarrow y.
    Proof.
      ran(f /circ g) = y.
      Proof.
        Let a /in y.
        Take a zfset b such that b /in Dom(f) /\ f[b] = a.
        Then b /in x.
        Then b /in ran(g).
        Take a zfset c such that c /in Dom(g) /\ g[c] = b.
        Then f[g[c]] = a.
        Then a /in ran(f /circ g).
      end.
    end.
    Trans(y) /\ Trans(z).
    Then y = z.
  end.
qed.


Lemma. Let alpha /in /Ord. Then otp(alpha) = alpha.
Proof.
  alpha /subset /Ord. alpha is a zfset.
  Id /upharpoonright alpha : alpha /leftrightarrow alpha.
  Id /upharpoonright alpha is an epsiso.
qed.

Lemma. Let x be a zfset. Let x /subset /Ord. Then Card(x) /subset otp(x).
Proof.
  Take a zffunction f such that f : x /leftrightarrow otp(x).
  Then f^{-1} : otp(x) /leftrightarrow x.
  otp(x) /in /Ord. 
  otp(x) /in Cardset(x).
qed.


Lemma. Let x /subset /Ord. Let y /in /Ord \/ y = /Ord. Then otp(x) = y iff exists f ((f is an epsiso) /\ f : y /leftrightarrow x).
Proof.
  otp(x) = y => exists f ((f is an epsiso) /\ f : y /leftrightarrow x).
  Proof.
    Let otp(x) = y.
    Then otpfunc(x) : x /leftrightarrow y and otpfunc(x) is an epsiso.
    otpfunc(x)^{-1} : y /leftrightarrow x and otpfunc(x)^{-1} is an epsiso.
  end.
  Exists f ((f is an epsiso) /\ f : y /leftrightarrow x) => otp(x) = y.
  Proof.
    Let exists f ((f is an epsiso) /\ f : y /leftrightarrow x).
    Take an epsiso f such that f : y /leftrightarrow x.
    Then f^{-1} is an epsiso.
    f^{-1} : x /leftrightarrow y.
  end.
qed.



