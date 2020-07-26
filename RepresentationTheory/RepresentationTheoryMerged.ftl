[synonym member/-s]
[synonym map/-s]
[synonym space/-s]
[synonym homomorphism/-s]
[synonym algebra/-s]
[synonym algebrahom/-s]
[synonym module/-s]
[synonym modulehom/-s]
[synonym category/categories]
[synonym functor/-s]
[synonym vertex/vertices]
[synonym arrow/-s]

Signature. Let A,a be objects. A\{a} is an object.
Signature. Let A be an object. A member of A is a notion.   # "element" is already used for sets
Let x << A stand for x is a member of A.

Signature. Let f,x be objects. f(x) is an object.
Signature. Let f be an object. Dmn(f) is an object.   # Dom(f) would lead to ambiguity errors.
Signature. Let A be an object. id{A} is an object.
Signature. Let f,g be objects. f*g is an object.
Signature. Let f be an object. f^(-1) is an object.

Signature. Let S be an object.   |S| is an object.
Signature. Let S be an object.   0{S} is an object.
Signature. Let S be an object.   1{S} is an object.
Signature. Let a,b,S be objects. a +{S} b is an object.
Signature. Let a,b,S be objects. a *{S} b is an object.
Signature. Let a,S be objects.   ~{S} a is an object.
Signature. Let a,S be objects.   inv{S} a is an object.
Signature. Let a,b,S be objects. a @{S} b is an object.
Signature. Let a,b,S be objects. a @@{S} b is an object.
Let a < S stand for a << |S|.
Let a < S* stand for a << |S|\{0{S}}.
Let a -{S} b stand for a +{S} (~{S} b).
Let a /{S} b stand for a *{S} (inv{S} b).

Signature. Let K,V,W be objects. Hom(K,V,W) is an object.
Signature. Let f,x,y be objects. f(x,y) is an object.
Signature. Let K,V be objects.   dual(K,V) is an object.
Signature. Let K,V be objects.   V2ddV(K,V) is an object.
Signature. Let R be an object.   Un(R) is an object.
Signature. Let K,V be objects.   Endo(K,V) is an object.   #"End" can cause problems in proofs.
Signature. Let K,V be objects.   Aut(K,V) is an object.
Signature. Let f be an object.   Ker(f) is an object.

Signature. Let p,K,A,V be objects. rep2mod(p,K,A,V) is an object.
Signature. Let K,A,V be objects.   mod2rep(K,A,V) is an object.
Signature. Let K,A,M,N be objects. Hom(K,A,M,N) is an object.
Signature. Let X,C be objects.     1{X,C} is an object.
Signature. Let K,A be objects.     Mod(K,A) is an object.
Signature. Let K,A,x be objects.   Hom(K,A,x,-) is an object.
Signature. Let K,A,x be objects.   Hom(K,A,-,x) is an object.
Signature. id is an object.

Signature. 0 is an object.
Signature. 1 is an object.
Signature. Let Q be an object. Q(st) is an object.
Signature. Let Q be an object. Q(tl) is an object.


Axiom. Let A be a set. Let x be an object. x << A iff x is an element of A.

Definition Subset. Let B be an object. A subset of B is a set A such that
 for all x << A : x << B.

Axiom SetExt. Let A,B be sets. Assume A is subset of B. Assume B is subset of A. Then A = B.

Axiom. Let A be a set. Let a << A. A\{a} is a set.
Axiom. Let A be a set. Let a << A. A\{a} = {x | x << A and x != a}.

##########

Definition. Let f,A,B be objects.
 f is from A to B iff Dmn(f) = A and for all x << A : f(x) << B.

Definition. Let f be an object.
 f is injective iff (for all x,y << Dmn(f) : (f(x) = f(y) => x = y)).

Definition. Let f,B be objects.
 f is surjective onto B iff for all y << B there is an x << Dmn(f) such that f(x) = y.

Definition. Let f,A,B be objects.
 f is bijective from A to B iff (f is from A to B and f is injective and f is surjective onto B).

Signature. A map is a notion.

Let f:A->B stand for (f is a map from A to B).

Axiom MapExt. Let f,g be maps.
 If Dmn(f) = Dmn(g) and (for all x <<  Dmn(f) : f(x) = g(x)) then f = g.

##########

Axiom MapId. Let A be a set.
 id{A} is a map h such that Dmn(h) = A and for all a << A : h(a) = a.

Axiom. Let f,g be maps. f*g is a map.
Axiom. Let f,g be maps. Dmn(f*g) = Dmn(g).
Axiom. Let f,g be maps. Let x be an object. (f*g)(x) = f(g(x)).

Definition. Let f,g be objects.
 f and g are composable iff for all x << Dmn(g) we have g(x) << Dmn(f).

Theorem. Let f be a map. Let A be a set. Let id{A} and f be composable. Then id{A}*f = f.
Proof.
 For all x << Dmn(f) : (id{A}*f)(x) = f(x).
Qed.

Theorem. Let f be a map. Let A be a set. Let Dmn(f) = A. Then f*id{A} = f.
Proof.
 For all x << A : (f*id{A})(x) = f(x).
Qed.

Theorem CompFromTo. Let A,B,C be objects. Let g:A->B. Let f:B->C. Then f*g : A -> C.
Proof.
 For all x << A : (f*g)(x) << C.
Qed.

Theorem. Let A,B,C,D be objects. Let h:A->B. Let g:B->C. Let f:C->D. Then (f*g)*h : A -> D.
Proof.
 (f*g) : B -> D.
Qed.

Theorem. Let A,B,C,D be objects. Let h:A->B. Let g:B->C. Let f:C->D. Then f*(g*h) : A->D.

Theorem ThreeComp. Let A,B,C,D be objects. Let h:A->B. Let g:B->C. Let f:C->D. Then (f*g)*h = f*(g*h).
Proof.
 Dmn((f*g)*h) = A.
 Dmn(f*(g*h)) = A.
 For all x << A : ((f*g)*h)(x) = f(g(h(x))) = (f*(g*h))(x).
Qed.

Axiom. Let f be a map. f^(-1) is a map.
Axiom InverseMap. Let f be a map. Let A,B be sets. Let f be bijective from A to B. Then f^(-1) is a map
 from B to A and (for all x << A : f^(-1)(f(x)) = x) and (for all y << B : f(f^(-1)(y)) = y).

##########

Let K denote a field.

Axiom. Let a,b < K. a @{K} b = a *{K} b.

Theorem. K is a vector space over K.
Proof.
 K is an abelian group.
 For all a < K and all v < K : a @{K} v < K.
 For all v < K                 :       1{K} @{K} v = v.
 For all a,b < K for all v < K : (a *{K} b) @{K} v = a @{K} (b @{K} v).
 For all a,b < K for all v < K : (a +{K} b) @{K} v = (a @{K} v) +{K} (b @{K} v).
 For all a < K for all v,w < K : a @{K} (v +{K} w) = (a @{K} v) +{K} (a @{K} w).
Qed.

##########

Definition AbelianGroup. An abelian group is an object G such that
     (|G| is a set)
 and (0{G} < G)
 and (for all a,b < G   : a +{G} b < G)
 and (for all a < G     :   ~{G} a < G)
 and (for all a < G     :       a +{G} 0{G} = a)
 and (for all a < G     :          a -{G} a = 0{G})
 and (for all a,b,c < G : a +{G} (b +{G} c) = (a +{G} b) +{G} c)
 and (for all a,b < G   :          a +{G} b = b +{G} a).

Theorem NegZero. Let G be an abelian group.
 Then ~{G} 0{G} = 0{G}.

Theorem ZeroAdd. Let G be an abelian group. Let a < G.
 Then 0{G} +{G} a = a.

Theorem NegAdd. Let G be an abelian group. Let a,b < G.
 Then ~{G} (a +{G} b) = (~{G} a) -{G} b.
Proof.
 ~{G} (a +{G} b) = (~{G} (a +{G} b)) +{G} ((a -{G} a) +{G} (b -{G} b)).
 (~{G} (a +{G} b)) +{G} ((a -{G} a) +{G} (b -{G} b))
 = ((~{G} (a +{G} b)) +{G} (a +{G} b)) +{G} ((~{G} a) -{G} b).
 ((~{G} (a +{G} b)) +{G} (a +{G} b)) +{G} ((~{G} a) -{G} b) = (~{G} a) -{G} b.
Qed.

##########

Definition Field. A field is an object K such that
     (K is an abelian group)
 and (1{K} < K)
 and (1{K} != 0{K})
 and (for all a,b < K   : a *{K} b < K)
 and (for all a < K*    : inv{K} a < K)
 and (for all a < K     :       a *{K} 1{K} = a)
 and (for all a < K*    :          a /{K} a = 1{K})
 and (for all a,b,c < K : a *{K} (b *{K} c) = (a *{K} b) *{K} c)
 and (for all a,b < K   :          a *{K} b = b *{K} a)
 and (for all a,b,c < K : a *{K} (b +{K} c) = (a *{K} b) +{K} (a *{K} c)).

##########

Let K denote a field.

Definition VectorSpace. A vector space over K is an object V such that
     (V is an abelian group)
 and (for all a < K and all v < V   : a @{V} v < V)
 and (for all v < V                 :       1{K} @{V} v = v)
 and (for all a,b < K for all v < V : (a *{K} b) @{V} v = a @{V} (b @{V} v))
 and (for all a,b < K for all v < V : (a +{K} b) @{V} v = (a @{V} v) +{V} (b @{V} v))
 and (for all a < K for all v,w < V : a @{V} (v +{V} w) = (a @{V} v) +{V} (a @{V} w)).

Theorem ZeroSmul. Let V be a vector space over K. Let v < V.
 Then 0{K} @{V} v = 0{V}.
Proof.
 0{K} @{V} v
 = ((0{K} @{V} v) +{V} (1{K} @{V} v)) +{V} (~{V} v)
 = ((0{K} +{K} 1{K}) @{V} v) +{V} (~{V} v)
 = (1{K} @{V} v) +{V} (~{V} v)
 = v +{V} (~{V} v)
 = 0{V}.
Qed.

Theorem SmulZero. Let V be a vector space over K. Let a < K.
 Then a @{V} 0{V} = 0{V}.

Theorem NegSmul. Let V be a vector space over K. Let a < K. Let v < V.
 Then (~{K} a) @{V} v = ~{V} (a @{V} v).
Proof.
 (~{K} a) @{V} v
 = (((~{K} a) @{V} v) +{V} (a @{V} v)) +{V} (~{V} (a @{V} v))
 = ~{V} (a @{V} v).
Qed.

Theorem NegOneSmul. Let V be a vector space over K. Let v < V.
 Then (~{K} 1{K}) @{V} v = ~{V} v.

Theorem SmulNeg. Let V be a vector space over K. Let a < K. Let v < V.
 Then a @{V} (~{V} v) = ~{V} (a @{V} v).
Proof.
 a @{V} (~{V} v)
 = (a @{V} (~{V} v)) +{V} ((a @{V} v) -{V} (a @{V} v))
 = ((a @{V} (~{V} v)) +{V} (a @{V} v)) -{V} (a @{V} v)
 = ~{V} (a @{V} v).
Qed.

##########

Let K denote a field.

Definition Homomorphism. Let V and W be objects. A homomorphism over K from V to W is a map f such that
     (V and W are vector spaces over K)
 and (f is from |V| to |W|)
 and (for all u,v < V             : f(u +{V} v) = f(u) +{W} f(v))
 and (for all a < K for all v < V : f(a @{V} v) = a @{W} f(v)).

Let f is linear over K from V to W stand for f is a homomorphism over K from V to W.

Axiom HomSet. Let V and W be vector spaces over K.
 |Hom(K,V,W)| is the set of maps f such that f is linear over K from V to W.

Axiom MapZero. Let V and W be vector spaces over K.
 0{Hom(K,V,W)} is a map h such that Dmn(h) = |V| and for all v < V : h(v) = 0{W}.

Axiom MapAdd. Let V and W be vector spaces over K. Let f,g < Hom(K,V,W).
 f +{Hom(K,V,W)} g is a map h such that Dmn(h) = |V| and
 for all v < V : h(v) = f(v) +{W} g(v).

Axiom MapNeg. Let V and W be vector spaces over K. Let f < Hom(K,V,W).
 ~{Hom(K,V,W)} f is a map h such that Dmn(h) = |V| and
 for all v < V : h(v) = ~{W} f(v).

Axiom MapSmul. Let V and W be vector spaces over K. Let a < K and f < Hom(K,V,W).
 a @{Hom(K,V,W)} f is a map h such that Dmn(h) = |V| and
 for all v < V : h(v) = a @{W} f(v).

Lemma ZeroLinear. Let V and W be vector spaces over K.
 0{Hom(K,V,W)} is linear over K from V to W.
Proof.
 Take a map h such that h = 0{Hom(K,V,W)}.
 Let us show that h is linear over K from V to W.
  h is from |V| to |W|.
  For all u,v < V             : h(u +{V} v) = h(u) +{W} h(v).
  For all a < K for all v < V : h(a @{V} v) = a @{W} h(v).
 qed.
Qed.

Lemma AddLinear. Let V and W be vector spaces over K. Let f,g < Hom(K,V,W).
 Then f +{Hom(K,V,W)} g is linear over K from V to W.
Proof.
 Take a map h such that h = f +{Hom(K,V,W)} g.
 Let us show that h is linear over K from V to W.
  Let us show that h is from |V| to |W|.
   Dmn(h) = |V| (by MapAdd).
   For all v < V : h(v) = f(v) +{W} g(v) < W.
  qed.
  Let us show that for all u,v < V : h(u +{V} v) = h(u) +{W} h(v).
   Let u,v < V.
   h(u +{V} v) = f(u +{V} v) +{W} g(u +{V} v).
   Let us show that f(u +{V} v) +{W} g(u +{V} v) = (f(u) +{W} f(v)) +{W} (g(u) +{W} g(v)).
    f is linear over K from V to W.
    g is linear over K from V to W.
    u,v < V.
    f(u +{V} v) = f(u) +{W} f(v) (by Homomorphism).
    g(u +{V} v) = g(u) +{W} g(v) (by Homomorphism).
   qed.
   Let us show that (f(u) +{W} f(v)) +{W} (g(u) +{W} g(v)) = (f(u) +{W} g(u)) +{W} (f(v) +{W} g(v)).
    f(u),f(v),g(u),g(v) < W.
    W is an abelian group.
    Therefore the thesis (by AbelianGroup).
   qed.
  qed.
  Let us show that for all a < K for all v < V : h(a @{V} v) = a @{W} h(v).
   Let a < K and v < V.
   h(a @{V} v) = f(a @{V} v) +{W} g(a @{V} v).
   Let us show that f(a @{V} v) +{W} g(a @{V} v) = (a @{W} f(v)) +{W} (a @{W} g(v)).
    f,g are linear over K from V to W.
   qed.
   (a @{W} f(v)) +{W} (a @{W} g(v)) = a @{W} (f(v) +{W} g(v)).
   a @{W} (f(v) +{W} g(v)) = a @{W} h(v).
  qed.
 qed.
Qed.

Lemma NegLinear. Let V and W be vector spaces over K. Let f < Hom(K,V,W).
 Then ~{Hom(K,V,W)} f is linear over K from V to W.
Proof.
 Take a map h such that h = ~{Hom(K,V,W)} f.
 Let us show that h is linear over K from V to W.
  Let us show that h is from |V| to |W|.
   Dmn(h) = |V| (by MapNeg).
   For all v < V : h(v) = ~{W} f(v) < W.
  qed.
  Let us show that for all u,v < V : h(u +{V} v) = h(u) +{W} h(v).
   Let u,v < V.
   h(u +{V} v) = ~{W} f(u +{V} v).
   Let us show that ~{W} f(u +{V} v) = ~{W} (f(u) +{W} f(v)).
    f is linear over K from V to W.
   qed.
   ~{W} (f(u) +{W} f(v)) = (~{W} f(u)) +{W} (~{W} f(v)).
   (~{W} f(u)) +{W} (~{W} f(v)) = h(u) +{W} h(v).
  qed.
  Let us show that for all a < K for all v < V : h(a @{V} v) = a @{W} h(v).
   Let a < K and v < V.
   h(a @{V} v) = ~{W} f(a @{V} v).
   Let us show that ~{W} f(a @{V} v) = ~{W} (a @{W} f(v)).
    f is linear over K from V to W.
   qed.
   ~{W} (a @{W} f(v)) = a @{W} (~{W} f(v)).
   a @{W} (~{W} f(v)) = a @{W} h(v).
  qed.
 qed.
Qed.

Lemma SmulLinear. Let V and W be vector spaces over K. Let a < K and f < Hom(K,V,W).
 Then a @{Hom(K,V,W)} f is linear over K from V to W.
Proof.
 Take a map h such that h = a @{Hom(K,V,W)} f.
 Let us show that h is linear over K from V to W.
  h is from |V| to |W|.
  Let us show that for all u,v < V : h(u +{V} v) = h(u) +{W} h(v).
   Let u,v < V.
   h(u +{V} v) = a @{W} f(u +{V} v).
   f is linear over K from V to W.
   f(u +{V} v) = (f(u) +{W} f(v)) (by Homomorphism).
   a @{W} f(u +{V} v) = a @{W} (f(u) +{W} f(v)).
   a @{W} (f(u) +{W} f(v)) = (a @{W} f(u)) +{W} (a @{W} f(v)).
   (a @{W} f(u)) +{W} (a @{W} f(v)) = h(u) +{W} h(v).
  qed.
  Let us show that for all b < K for all v < V : h(b @{V} v) = b @{W} h(v).
   Let b < K and v < V.
   h(b @{V} v) = a @{W} f(b @{V} v) (by MapSmul).
   f is linear over K from V to W.
   a @{W} f(b @{V} v) = a @{W} (b @{W} f(v)) (by Homomorphism).
   a @{W} (b @{W} f(v)) = b @{W} (a @{W} f(v)) = b @{W} h(v).
  qed.
 qed.
Qed.

Theorem HomSpace. Let V and W be vector spaces over K. Then Hom(K,V,W) is a vector space over K.
Proof.
 Take an object H such that H = Hom(K,V,W).
 Let us show that H is an abelian group.
  0{H} < H.
  For all f,g < H : f +{H} g < H.
  For all f < H   :   ~{H} f < H.
  Let us show that for all f < H : f +{H} 0{H} = f.
   Let f < H.
   Let us show that for all v < V : (f +{H} 0{H})(v) = f(v).
    Let v < V.
    (f +{H} 0{H})(v) = f(v) +{W} (0{H}(v)) = f(v).
   qed.
  qed.
  Let us show that for all f < H : f -{H} f = 0{H}.
   Let f < H.
   Let us show that for all v < V : (f -{H} f)(v) = 0{H}(v).
    Let v < V.
    (f -{H} f)(v) = f(v) +{W} (~{H}f)(v) = f(v) -{W} f(v) = 0{W} = 0{H}(v).
   qed.
  qed.
  Let us show that for all f,g,h < H : f +{H} (g +{H} h) = (f +{H} g) +{H} h.
   Let f,g,h < H.
   Let us show that for all v < V : (f +{H} (g +{H} h))(v) = ((f +{H} g) +{H} h)(v).
    Let v < V.
    (f +{H} (g +{H} h))(v)
    = f(v) +{W} (g(v) +{W} h(v))
    = (f(v) +{W} g(v)) +{W} h(v)
    = ((f +{H} g) +{H} h)(v).
   qed.
  qed.
  Let us show that for all f,g < H : f +{H} g = g +{H} f.
   Let f,g < H.
   Let us show that for all v < V : (f +{H} g)(v) = (g +{H} f)(v).
    Let v < V.
    (f +{H} g)(v) = f(v) +{W} g(v) = g(v) +{W} f(v) = (g +{H} f)(v).
   qed.
  qed.
 qed.
 Let us show that H is a vector space over K.  
  H is an abelian group.
  For all a < K and all f < H : a @{H} f < H.
  Let us show that for all f < H : 1{K} @{H} f = f.
   Let f < H.
   For all v < V : (1{K} @{H} f)(v) = f(v).
  qed.
  Let us show that for all a,b < K and all f < H : (a *{K} b) @{H} f = a @{H} (b @{H} f).
   Let a,b < K and f < H.
   Let us show that for all v < V : ((a *{K} b) @{H} f)(v) = (a @{H} (b @{H} f))(v).
    Let v < V.
    ((a *{K} b) @{H} f)(v)
    = (a *{K} b) @{W} f(v)
    = a @{W} (b @{W} f(v))
    = a @{W} (b @{H} f)(v)
    = (a @{H} (b @{H} f))(v).
   qed.
   Dmn(((a *{K} b) @{H} f)) = |V|.
   Dmn((a @{H} (b @{H} f))) = |V|.
   Thus (a *{K} b) @{H} f = a @{H} (b @{H} f).
  qed.
  Let us show that for all a,b < K and all f < H : (a +{K} b) @{H} f = (a @{H} f) +{H} (b @{H} f).
   Let a,b < K and f < H.
   Let us show that for all v < V : ((a +{K} b) @{H} f)(v) = ((a @{H} f) +{H} (b @{H} f))(v).
    Let v < V.
    ((a +{K} b) @{H} f)(v)
    = (a +{K} b) @{W} f(v)
    = (a @{W} f(v)) +{W} (b @{W} f(v))
    = (a @{H} f)(v) +{W} (b @{H} f)(v)
    = ((a @{H} f) +{H} (b @{H} f))(v).
   qed.
   Thus (a +{K} b) @{H} f = (a @{H} f) +{H} (b @{H} f).
  qed.
  Let us show that for all a < K and all f,g < H : a @{H} (f +{H} g) = (a @{H} f) +{H} (a @{H} g).
   Let a < K and f,g < H.
   Let us show that for all v < V : (a @{H} (f +{H} g))(v) = ((a @{H} f) +{H} (a @{H} g))(v).
    Let v < V.
    (a @{H} (f +{H} g))(v)
    = a @{W} (f +{H} g)(v)
    = a @{W} (f(v) +{W} g(v))
    = (a @{W} f(v)) +{W} (a @{W} g(v))
    = (a @{H} f)(v) +{W} (a @{H} g)(v)
    = ((a @{H} f) +{H} (a @{H} g))(v).
   qed.
   Thus a @{H} (f +{H} g) = (a @{H} f) +{H} (a @{H} g).
  qed.
 qed.
Qed.

##########

Let K denote a field.

Axiom ConsequenceOfAC. Let V be a vector space over K. Let v,w < V. Assume that v != w.
 There exists a map g such that g is linear over K from V to K and g(v) != g(w).

Axiom. Let V be a vector space over K. dual(K,V) = Hom(K,V,K).

Definition. Let V be a vector space over K. Let v < V. eval(dual(K,V), v) is a map f such that
 Dmn(f) = |dual(K,V)| and (for all h < dual(K,V) : f(h) = h(v)).

Axiom. Let V be a vector space over K. V2ddV(K,V) is a map f such that
 Dmn(f) = |V| and (for all v < V : f(v) = eval(dual(K,V),v)).

Theorem. Let V be a vector space over K.
 V2ddV(K,V) is injective and linear over K from V to dual(K,dual(K,V)).
Proof.
 Take i = V2ddV(K,V).
 Take ddV = dual(K,dual(K,V)).

 Let us show that i is injective.
  Let us show that for all v,w < V : (v != w => i(v) != i(w)).
   Let v,w < V. Assume v != w.
   Take a map g such that g is linear over K from V to K and g(v) != g(w)
   (by ConsequenceOfAC).
   Thus i(v)(g) != i(w)(g).
  qed.
 qed.

 Let us show that i is linear over K from V to ddV.
  Let us show that i is from |V| to |ddV|.
   Let us show that for all v < V : (i(v) is linear over K from dual(K,V) to K).
    Let v < V.
    Let us show that i(v) is from |dual(K,V)| to |K|.
     Let us show that for all f < dual(K,V) : i(v)(f) < K.
      Let f < dual(K,V).
      i(v)(f) = f(v).
     qed.
    qed.
    Let us show that for all f,g < dual(K,V) : i(v)(f +{dual(K,V)} g) = i(v)(f) +{K} i(v)(g).
     Let f,g < dual(K,V).
     f,g < Hom(K,V,K).
     v < V.
     f +{Hom(K,V,K)} g < Hom(K,V,K).
     i(v)(f +{Hom(K,V,K)} g) = (f +{Hom(K,V,K)} g)(v).
     (f +{Hom(K,V,K)} g)(v) = f(v) +{K} g(v).
     f(v) +{K} g(v) = i(v)(f) +{K} i(v)(g).
    qed.
    Let us show that for all a < K and all f < dual(K,V) : i(v)(a @{dual(K,V)} f) = a @{K} i(v)(f).
     Let a < K and f < dual(K,V).
     a @{dual(K,V)} f < dual(K,V).
     i(v)(a @{dual(K,V)} f) = (a @{dual(K,V)} f)(v) = a @{K} f(v) = a @{K} i(v)(f).
    qed.
   qed.
  qed.

  Let us show that for all u,v < V : i(u +{V} v) = i(u) +{ddV} i(v).
   Let u,v < V.
   Let us show that for all f < dual(K,V) : i(u +{V} v)(f) = (i(u) +{ddV} i(v))(f).
    Let f < dual(K,V).
    i(u +{V} v)(f) = f(u +{V} v).
    Let us show that f(u +{V} v) = f(u) +{K} f(v).
     f is linear over K from V to K.
    qed.
    f(u) +{K} f(v) = i(u)(f) +{K} i(v)(f).
    Let us show that (i(u) +{ddV} i(v))(f) = i(u)(f) +{K} i(v)(f).
     i(u) +{ddV} i(v) = i(u) +{Hom(K,dual(K,V),K)} i(v).
     dual(K,V) is a vector space over K.
    qed.
   qed.
   Dmn(i(u +{V} v)) = |dual(K,V)|.
   Dmn(i(u) +{ddV} i(v)) = |dual(K,V)|.
   Thus i(u +{V} v) = i(u) +{ddV} i(v).
  qed.

  Let us show that for all a < K and all v < V : i(a @{V} v) = a @{ddV} i(v).
   Let a < K and v < V.
   Let us show that for all f < dual(K,V) : i(a @{V} v)(f) = (a @{ddV} i(v))(f).
    Let f < dual(K,V).
    i(a @{V} v)(f) = f(a @{V} v).
    Let us show that f(a @{V} v) = a @{K} f(v).
     f is linear over K from V to K.
    qed.
    a @{K} f(v) = a @{K} i(v)(f).
    Let us show that (a @{ddV} i(v))(f)  = a @{K} i(v)(f).
     a @{ddV} i(v) = a @{Hom(K,dual(K,V),K)} i(v).
     dual(K,V) is a vector space over K.
     f < dual(K,V).
    qed.
   qed.
   Thus i(a @{V} v) = a @{ddV} i(v).
  qed.
 qed.
Qed.

##########

Let K denote a field.

Definition. Let V be an object. A subspace of V over K is an object U such that
     (V is a vector space over K)
 and (|U| is subset of |V|)
 and (0{V} < U)
 and (for all u,v < U             : u +{V} v < U)
 and (for all a < K and all u < U : a @{V} u < U).

Let sub(K,V,U) stand for (V is a vector space over K and U is a subspace of V over K).

Axiom SubZero. Let sub(K,V,U). 0{U} = 0{V}.
Axiom SubAdd.  Let sub(K,V,U). Let u,v < (U).       u +{U} v = u +{V} v.
Axiom SubNeg.  Let sub(K,V,U). Let u < U.             ~{U} u = ~{V} u.
Axiom SubSmul. Let sub(K,V,U). Let a < K and u < U. a @{U} u = a @{V} u.

# Especially, every structure with the same carrier as V is forced to inherit its vector space
# structure. This follows from the next theorem and becomes useful later on.

Theorem. Let V be a vector space over K. Let W be an object. Assume |V|=|W|.
 Then W is a subspace of V over K.
Proof.
 0{V} < W.
 For all u,v < W             : u +{V} v < W.
 For all a < K for all u < W : a @{V} u < W.
Qed.

Theorem. Let sub(K,V,U). Then U is a vector space over K.
Proof.
 Let us show that U is an abelian group.
  |U| is a set.
  0{U} < U.
  For all u,v < U : u +{U} v < U.
  Let us show that for all u < U : ~{U} u < U.
   Let u < U.
   ~{U} u = (~{K} 1{K}) @{V} u.
   ~{K} 1{K} < K.
   (~{K} 1{K}) @{V} u < U.
  qed.
  For all u < U : u +{U} 0{U} = u.
  For all u < U : u -{U} u = 0{U}.
  Let us show that for all u,v,w < U : u +{U} (v +{U} w) = (u +{U} v) +{U} w.
   Let u,v,w < U.
   u +{U} (v +{U} w) = u +{V} (v +{V} w) = (u +{V} v) +{V} w = (u +{U} v) +{U} w.
  qed.
  Let us show that for all u,v < U : u +{U} v = v +{U} u.  
   Let u,v < U.
   u +{U} v = u +{V} v = v +{V} u = v +{U} u.
  qed.
 qed.

 Let us show that U is a vector space over K.
  For all a < K and all u < U  : a @{U} u < U.
  For all u < U : 1{K} @{U} u = u.

  Let us show that for all a,b < K and all u < U : (a *{K} b) @{U} u = a @{U} (b @{U} u).
   Let a,b < K and u < U.
   a *{K} b < K.
   (a *{K} b) @{U} u = (a *{K} b) @{V} u.
   Let us show that (a *{K} b) @{V} u = a @{V} (b @{V} u).
    V is a vector space over K. 
    a,b < K. u < V.
    Therefore the thesis (by VectorSpace).
   qed.
   a @{V} (b @{V} u) = a @{U} (b @{U} u).
  qed.

  Let us show that for all a,b < K for all u < U : (a +{K} b) @{U} u = (a @{U} u) +{U} (b @{U} u).
   Let a,b < K and u < U.
   a +{K} b < K.
   (a +{K} b) @{U} u = (a +{K} b) @{V} u.
   Let us show that (a +{K} b) @{V} u = (a @{V} u) +{V} (b @{V} u).
    V is a vector space over K.
    a,b < K. u < V.
    Therefore the thesis (by VectorSpace).
   qed.
   (a @{V} u) +{V} (b @{V} u) = (a @{U} u) +{U} (b @{U} u).
  qed.

  Let us show that for all a < K for all u,v < U : a @{U} (u +{U} v) = (a @{U} u) +{U} (a @{U} v).
   Let a < K and u,v < U.
   a @{U} (u +{U} v) = a @{V} (u +{V} v) =  (a @{V} u) +{V} (a @{V} v) = (a @{U} u) +{U} (a @{U} v).
  qed.
 qed.
 Therefore the thesis (by VectorSpace).
Qed.

##########

Let K denote a field.

Axiom Kernel. Let V,W be vector spaces over K. Let f < Hom(K,V,W).
 |Ker(f)| is a set and |Ker(f)| = {v | v < V and f(v) = 0{W}}.

Theorem KernelThm1. Let V,W be vector spaces over K. Let f < Hom(K,V,W).
 Let v,w < V. Let f(v) = f(w). Then v -{V} w < Ker(f).
Proof.
 f is linear over K from V to W.
 ~{V} w < V.
 v -{V} w < V.
 f(v -{V} w) = f(v) +{W} f(~{V} w) (by Homomorphism).
 f(~{V} w) = f((~{K} 1{K}) @{V} w) = (~{K} 1{K}) @{W} f(w) = ~{W} f(w) (by NegOneSmul).
 f(v) -{W} f(w) = f(v) -{W} f(w) = 0{W}.
 Therefore f(v -{V} w) = 0{W}.
 |Ker(f)| is a set and |Ker(f)| = {v | v < V and f(v) = 0{W}} (by Kernel).
Qed.

Theorem KernelThm2. Let V,W be vector spaces over K. Let f < Hom(K,V,W).
 Assume |Ker(f)| is a set and |Ker(f)| = {0{V}}. Then f is injective.
Proof.
 f is linear over K from V to W.
 Dmn(f) = |V|.
 Let us show that for all v,w < V : f(v) = f(w) => v = w.
  Let v,w < V. Assume f(v) = f(w).
  v -{V} w < Ker(f) (by KernelThm1).
  v -{V} w = 0{V}.
  w = w +{V} 0{V} = w +{V} (v -{V} w).
  ~{V} w < V.
  w +{V} (v -{V} w) = v +{V} (w -{V} w) (by VectorSpace).
  v +{V} (w -{V} w) = v +{V} 0{V} = v.
 qed.
Qed.

Theorem KernelSubspace. Let V,W be vector spaces over K. Let f < Hom(K,V,W). Then Ker(f) is a subspace of V over K.
Proof.
 |Ker(f)| is a set and |Ker(f)| = {v | v < V and f(v) = 0{W}} (by Kernel).
 |Ker(f)| is subset of |V|.
 Let us show that 0{V} < Ker(f).
  f is linear over K from V to W.
  f(0{V}) = f(0{K} @{V} 0{V}) = 0{K} @{W} f(0{V}) = 0{W} (by ZeroSmul).  
 qed.
 Let us show that for all u,v < Ker(f) : u +{V} v < Ker(f).
  Let u,v < Ker(f).
  f(u) = 0{W}.
  f(v) = 0{W}.
  f is linear over K from V to W.
  f(u +{V} v) = f(u) +{W} f(v) (by Homomorphism).
  f(u) +{W} f(v) = 0{W} +{W} 0{W} = 0{W}.
 qed.
 Let us show that for all a < K and all u < Ker(f) : a @{V} u < Ker(f).
  Let a < K and u < Ker(f).
  f(u) = 0{W}.
  Let us show that f(a @{V} u) = a @{W} f(u).
   f is linear over K from V to W.
   a < K.
   u < V.
  qed.
  a @{W} f(u) = a @{W} 0{W}.
  a @{W} 0{W} = 0{W} (by SmulZero).
 qed.
Qed.

##########

Definition. A group is an object G such that
     (|G| is a set)
 and (1{G} < G)
 and (for all a,b < G   : a *{G} b < G)
 and (for all a < G     : inv{G} a < G)
 and (for all a < G     :       a *{G} 1{G} = a)
 and (for all a < G     :          a /{G} a = 1{G})
 and (for all a,b,c < G : a *{G} (b *{G} c) = (a *{G} b) *{G} c).

##########

Definition. A ring is an object R such that
     (R is an abelian group)
 and (1{R} < R)
 and (for all a,b < R   : a *{R} b < R)
 and (for all a < R     :       a *{R} 1{R} = a)
 and (for all a < R     :       1{R} *{R} a = a)
 and (for all a,b,c < R : a *{R} (b *{R} c) = (a *{R} b) *{R} c)
 and (for all a,b,c < R : a *{R} (b +{R} c) = (a *{R} b) +{R} (a *{R} c))
 and (for all a,b,c < R : (a +{R} b) *{R} c = (a *{R} c) +{R} (b *{R} c)).

##########

Let R denote a Ring.

Axiom. |Un(R)| is a set.
Axiom. |Un(R)| = {r | r < R and there is s < R such that (r *{R} s = 1{R} and s *{R} r = 1{R})}.

Theorem. Let r,s,t < Un(R).
 Assume r *{R} s = 1{R} and s *{R} r = 1{R}. Assume r *{R} t = 1{R} and t *{R} r = 1{R}.
 Then s = t.

# The theorem above allows the following definition.

Axiom. Let r < Un(R). inv{R} r < R.
Axiom. Let r < Un(R). r *{R} (inv{R} r) = 1{R}.
Axiom. Let r < Un(R). (inv{R} r) *{R} r = 1{R}.

Axiom. 1{Un(R)} = 1{R}.
Axiom. Let a,b < Un(R). a *{Un(R)} b = a *{R} b.
Axiom. Let a < Un(R).   inv{Un(R)} a = inv{R} a.

Theorem. Un(R) is a group.
Proof.
 1{Un(R)} < Un(R).
 Let us show that for all a,b < Un(R): a *{Un(R)} b < Un(R).
  Let a,b < Un(R).
  Take s < R such that (a *{R} s = 1{R} and s *{R} a = 1{R}).
  Take t < R such that (b *{R} t = 1{R} and t *{R} b = 1{R}).
  t *{R} s < R.
  (a *{Un(R)} b) *{R} (t *{R} s) = (a *{R} (b *{R} t)) *{R} s = (a *{R} 1{R}) *{R} s
  = a *{R} s = 1{R}.
  (t *{R} s) *{R} (a *{Un(R)} b) = (t *{R} (s *{R} a)) *{R} b = (t *{R} 1{R}) *{R} b
  = t *{R} b = 1{R}.
 qed.
 For all a < Un(R)     : inv{Un(R)} a < Un(R).
 For all a < Un(R)     :       a *{Un(R)} 1{Un(R)} = a.
 For all a < Un(R)     :              a /{Un(R)} a = 1{Un(R)}.
 For all a,b,c < Un(R) : a *{Un(R)} (b *{Un(R)} c) = (a *{Un(R)} b) *{Un(R)} c.
Qed.

##########

Let K denote a field.

Axiom. Let V be a vector space over K. Endo(K,V) = Hom(K,V,V).

Axiom MapOne. Let V be a vector space over K. 1{Endo(K,V)} = id{|V|}.
Axiom MapMul. Let V be a vector space over K. Let f,g < Endo(K,V). f *{Endo(K,V)} g  = f*g.

Theorem. Let V be a vector space over K. Then id{|V|} is linear over K from V to V.
Proof.
 id{|V|} is a map from |V| to |V|.
Qed.

Theorem. Let U,V,W be vector spaces over K. Let f,g be maps.
 Let g be linear over K from U to V. Let f be linear over K from V to W.
 Then f*g is linear over K from U to W.
Proof.
 f*g is a map from |U| to |W|.
Qed.

Theorem. Let V be a vector space over K. Endo(K,V) is a ring.
Proof.
 Take R = Endo(K,V).
 Let us show that R is a ring.
  R is an abelian group.
  1{R} < R.
  Let us show that for all f,g < R : f *{R} g < R.
   Let f,g < R.
   f,g are linear over K from V to V.
   f*g is linear over K from V to V.
  qed.
  For all f < R : f *{R} 1{R} = f.
  For all f < R : 1{R} *{R} f = f.
  Let us show that for all f,g,h < R : f *{R} (g *{R} h) = (f *{R} g) *{R} h.
   Let f,g,h < R.
   f *{R} (g *{R} h) = f*(g*h).
   (f *{R} g) *{R} h = (f*g)*h.
   f,g,h are maps from |V| to |V|.
   f*(g*h) = (f*g)*h.
  qed.
  Let us show that for all f,g,h < R : f *{R} (g +{R} h) = (f *{R} g) +{R} (f *{R} h).
   Let f,g,h < R.
   Let us show that for all v < V : (f *{R} (g +{R} h))(v) = ((f *{R} g) +{R} (f *{R} h))(v).
    Let v < V.
    (f *{R} (g +{R} h))(v)
    = (f*(g +{R} h))(v)
    = f((g +{R} h)(v))
    = f(g(v) +{V} h(v))
    = f(g(v)) +{V} f(h(v))
    = (f*g)(v) +{V} (f*h)(v)
    = (f *{R} g)(v) +{V} (f *{R} h)(v)
    = ((f *{R} g) +{R} (f *{R} h))(v).
   qed.
   Dmn(f *{R} (g +{R} h)) = |V| = Dmn((f *{R} g) +{R} (f *{R} h)).
  qed.
  Let us show that for all f,g,h < R : (f +{R} g) *{R} h = (f *{R} h) +{R} (g *{R} h).
   Let f,g,h < R.
   Let us show that for all v < V : ((f +{R} g) *{R} h)(v) = ((f *{R} h) +{R} (g *{R} h))(v).
    Let v < V.
    ((f +{R} g) *{R} h)(v)
    = (f +{R} g)(h(v))
    = f(h(v)) +{V} g(h(v))
    = (f *{R} h)(v) +{V} (g *{R} h)(v)
    = ((f *{R} h) +{R} (g *{R} h))(v).
   qed.
  qed.
 qed.
Qed.

##########

Let K denote a field.

Axiom. Let V be a vector space over K. Aut(K,V) = Un(Endo(K,V)).

Definition. Let V,W be vector spaces over K. Let f be a map.
 f is isomorphism over K from V to W iff (f < Hom(K,V,W) and f is bijective from |V| to |W|).

Theorem. Let V,W be vector spaces over K. Let f be a map.
 Let f be isomorphism over K from V to W. Then f^(-1) < Hom(K,W,V).
Proof.
 f is bijective from |V| to |W|.
 f^(-1) is a map from |W| to |V|.
 Let us show that f^(-1) is linear over K from W to V.
  Let us show that for all v,w < W : f^(-1)(v +{W} w) = f^(-1)(v) +{V} f^(-1)(w).
   Let v,w < W.
   f(f^(-1)(v +{W} w)) = v +{W} w.
   f^(-1)(v), f^(-1)(w) < V.
   f is linear over K from V to W.
   f(f^(-1)(v) +{V} f^(-1)(w)) = f(f^(-1)(v)) +{W} f(f^(-1)(w)).
   f(f^(-1)(v)) +{W} f(f^(-1)(w)) = v +{W} w.
   f is injective.
   Thus f^(-1)(v +{W} w) = f^(-1)(v) +{V} f^(-1)(w).
  qed.
  Let us show that for all a < K and all w < W : f^(-1)(a @{W} w) = a @{V} f^(-1)(w).
   Let a < K and w < W.
   f(f^(-1)(a @{W} w)) = a @{W} w.
   f^(-1)(w) < V.
   f is linear over K from V to W.
   f(a @{V} f^(-1)(w)) = a @{W} f(f^(-1)(w)) = a @{W} w.
   f is injective.
   Thus f^(-1)(a @{W} w) = a @{V} f^(-1)(w).
  qed.
 qed.
Qed.

Theorem. Let V be a vector space over K. Let f be a map.
 f < Aut(K,V) iff f is isomorphism over K from V to V.
Proof.
 Let us show that f < Aut(K,V) => (f is isomorphism over K from V to V).
  Let f < Aut(K,V).
  Take g < Endo(K,V) such that (g *{Endo(K,V)} f = 1{Endo(K,V)} and f *{Endo(K,V)} g = 1{Endo(K,V)}).
  g*f = id{|V|}.
  f*g = id{|V|}.
  f is injective.
  f is surjective onto |V|.
  f < Hom(K,V,V).
  Thus f is isomorphism over K from V to V.
 qed.
 Let us show that (f is isomorphism over K from V to V) => f < Aut(K,V).
  Let f be isomorphism over K from V to V.
  f^(-1) < Endo(K,V).
  f *{Endo(K,V)} (f^(-1)) = f*(f^(-1)) = id{|V|} = 1{Endo(K,V)}.
  (f^(-1)) *{Endo(K,V)} f = (f^(-1))*f.
  Let us show that (f^(-1))*f = id{|V|}.
   (f^(-1))*f is a map.
   Dmn((f^(-1))*f) = |V|.
   id{|V|} is a map.
   Dmn(id{|V|}) = |V|.
   For all v < V : ((f^(-1))*f)(v) = v = id{|V|}(v).
   Therefore the thesis (by MapExt).
  qed.
  id{|V|} = 1{Endo(K,V)}.
 qed.
Qed.

##########

Let Ob{C} stand for |C|.

Definition Category. A category is an object C such that 
     (Ob{C} is a set)
 and (for all X,Y,Z << Ob{C} and all f << C(X,Y) and all g << C(Y,Z) : g*f << C(X,Z))
 and (for all X << Ob{C} : 1{X,C} << C(X,X))
 and (for all X,Y << Ob{C} and all f << C(X,Y) : f*1{X,C} = f)
 and (for all X,Y << Ob{C} and all f << C(Y,X) : 1{X,C}*f = f)
 and (for all W,X,Y,Z << Ob{C} and all f << C(W,X) and all g << C(X,Y) and all h << C(Y,Z) : 
      h*(g*f) = (h*g)*f).

##########

Definition Functor. Let C,D be objects. A functor from C to D is an object F such that
     (C and D are categories)
 and (for all X << Ob{C} : F(X) << Ob{D})
 and (for all X,Y << Ob{C} and all f << C(X,Y) : F(f) << D(F(X),F(Y)))
 and (for all X << Ob{C} : F(1{X,C}) = 1{F(X),D})
 and (for all X,Y,Z << Ob{C} and all f << C(X,Y) and all g << C(Y,Z) : F(g*f) = F(g)*F(f)).

Definition ContraFunctor. Let C,D be objects. A contravariant functor from C to D is an object F such that
     (C and D are categories)
 and (for all X << Ob{C} : F(X) << Ob{D})
 and (for all X,Y << Ob{C} and all f << C(X,Y) : F(f) << D(F(Y),F(X)))
 and (for all X << Ob{C} : F(1{X,C}) = 1{F(X),D})
 and (for all X,Y,Z << Ob{C} and all f << C(X,Y) and all g << C(Y,Z) : F(g*f) = F(f)*F(g)).

##########

Definition. Let C,D,F,G be objects.
 A natural transformation from F to G over C to D is an object n such that
     (F,G are functors from C to D)
 and (for all X << Ob{C} : n(X) << D(F(X),G(X)))
 and (for all X,Y << Ob{C} and all h << C(X,Y) : G(h)*n(X) = n(Y)*F(h)).

Definition. Let C,D,F,G be objects.
 A contravariant natural transformation from F to G over C to D is an object n such that
     (F,G are contravariant functors from C to D)
 and (for all X << Ob{C} : n(X) << D(F(X),G(X)))
 and (for all X,Y << Ob{C} and all h << C(X,Y) : G(h)*n(Y) = n(X)*F(h)).

##########

Axiom. Let x be an object. id(x) = x.

Theorem. Let C be a category. id is a functor from C to C.
Proof.
 For all X < C : id(X) < C.
 For all X,Y < C and all f << C(X,Y) : id(f) << C(id(X),id(Y)).
 For all X < C : id(1{X,C}) = 1{id(X),C}.
 For all X,Y,Z < C and all f << C(X,Y) and all g << C(Y,Z) : id(g*f) = id(g)*id(f).
Qed.

Axiom. Let F,G,B,C,D be objects. Assume F is a functor from B to C. Assume G is a functor from
 C to D. Then for all objects x : (G*F)(x) = G(F(x)).

Theorem. Let F,G,B,C,D be objects. Assume F is a functor from B to C. Assume G is a functor
 from C to D. Then G*F is a functor from B to D.
Proof.
 For all objects x : (G*F)(x) = G(F(x)).
 B,C,D are categories.
 For all X < B : (G*F)(X) = G(F(X)) < D.
 For all X,Y < B and all f << B(X,Y) : (G*F)(f) = G(F(f)) << D(G(F(X)),G(F(Y)))
                                                             = D((G*F)(X),(G*F)(Y)).
 For all X < B : (G*F)(1{X,B}) = G(F(1{X,B})) = G(1{F(X),C}) = 1{G(F(X)),D} = 1{(G*F)(X),D}.
 For all X,Y,Z < B and all f << B(X,Y) and all g << B(Y,Z) :
  (G*F)(g*f) = G(F(g*f)) = G(F(g)*F(f)) = G(F(g))*G(F(f)) = (G*F)(g)*(G*F)(f).
Qed.


Definition. Let C,X,Y be objects. An isomorphism from X to Y in C is an object f such that
     (C is a category and X,Y < C)
 and (f << C(X,Y))
 and (there exists g << C(Y,X) such that g*f = 1{X,C} and f*g = 1{Y,C}).

Definition. Let X,Y,C be objects. X and Y are isomorphic in C iff
     (C is a category and X,Y < C)
 and (there exist an isomorphism from X to Y in C).

Theorem. Let C be a category. Let X,Y < C.
 X and Y are isomorphic in C iff Y and X are isomorphic in C.
Proof.
 Let us show that (X and Y are isomorphic in C) => (Y and X are isomorphic in C).
  Assume X and Y are isomorphic in C.
  Take an isomorphism f from X to Y in C.
 qed.
 Let us show that (Y and X are isomorphic in C) => (X and Y are isomorphic in C).
  Assume Y and X are isomorphic in C.
  Take an isomorphism g from Y to X in C.
 qed. 
Qed.


Definition NaturalIso. Let C,D,F,G be objects.
 A natural isomorphism from F to G over C to D is an object alpha such that
     (alpha is a natural transformation from F to G over C to D)
 and (for all X < C : (alpha(X) is an isomorphism from F(X) to G(X) in D)).

Definition. Let F,C,D be objects. A quasiinverse of F between C and D is an object G such that
     (F is a functor from C to D)
 and (G is a functor from D to C)
 and (there exists a natural isomorphism from G*F to id over C to C)
 and (there exists a natural isomorphism from F*G to id over D to D).

Definition. Let C,D be objects. An equivalence from C to D is an object F such that there exists a
 quasiinverse of F between C and D.


Definition. Let F,C,D be objects. F is full from C to D iff
     (F is a functor from C to D)
 and (for all X,Y < C and all g << D(F(X),F(Y)) there exists f << C(X,Y) such that F(f) = g).

Definition. Let F,C,D be objects. F is faithful from C to D iff
     (F is a functor from C to D)
 and (for all X,Y < C and all f,g << C(X,Y) : (F(f) = F(g) => f = g)).

Definition. Let F,C,D be objects. F is dense from C to D iff
     (F is a functor from C to D)
 and (for all Y < D there exists X < C such that F(X) and Y are isomorphic in D).


Theorem. Let C,D be categories. Let F be an equivalence from C to D.
 Then F is full from C to D and F is faithful from C to D and F is dense from C to D.
Proof.
 Take an object G such that G is a quasiinverse of F between C and D.
 F is a functor from C to D.
 G is a functor from D to C.
 Take a natural isomorphism alpha from G*F to id over C to C.
 Take a natural isomorphism gamma from F*G to id over D to D.

 Let us show that F is dense from C to D.  
  Let us show that for all Y < D there exists X < C such that F(X) and Y are isomorphic in D.
   Let Y < D.
   Take X = G(Y).
   X < C.
   Let us show that Y and F(X) are isomorphic in D.
    gamma(Y) is an isomorphism from (F*G)(Y) to id(Y) in D (by NaturalIso).
    (F*G)(Y) = F(X).
   qed.
  qed.
 qed.

 Let us show that F is faithful from C to D.
  Let us show that for all X1,X2 < C and all f,g << C(X1,X2) : (F(f) = F(g) => f = g).
   Let X1,X2 < C. Let f,g << C(X1,X2).
   Assume F(f) = F(g).
   Let us show that f * alpha(X1) = g * alpha(X1).
    f * alpha(X1) = alpha(X2) * (G*F)(f).
    g * alpha(X1) = alpha(X2) * (G*F)(g).
    (G*F)(f) = (G*F)(g).
   qed.
   (G*F)(X1) < C.
   alpha(X1) << C((G*F)(X1), X1).
   Take beta << C(X1, (G*F)(X1)) such that alpha(X1) * beta = 1{X1,C}.
   f = f * 1{X1,C} = f * (alpha(X1) * beta) = (f * alpha(X1)) * beta (by Category).
   g = g * 1{X1,C} = g * (alpha(X1) * beta) = (g * alpha(X1)) * beta (by Category).
   Therefore f = g.
  qed.
 qed.

 Let us show that G is faithful from D to C.
  Let us show that for all Y1,Y2 < D and all f,g << D(Y1,Y2) : (G(f) = G(g) => f = g).
   Let Y1,Y2 < D. Let f,g << D(Y1,Y2).
   Assume G(f) = G(g).
   Let us show that f * gamma(Y1) = g * gamma(Y1).
    f * gamma(Y1) = gamma(Y2) * (F*G)(f).
    g * gamma(Y1) = gamma(Y2) * (F*G)(g).
    (F*G)(f) = (F*G)(g).
   qed.
   (F*G)(Y1) < D.
   gamma(Y1) << D((F*G)(Y1), Y1).
   Take beta << D(Y1, (F*G)(Y1)) such that gamma(Y1) * beta = 1{Y1,D}.
   f = f * 1{Y1,D} = f * (gamma(Y1) * beta) = (f * gamma(Y1)) * beta (by Category).
   g = g * 1{Y1,D} = g * (gamma(Y1) * beta) = (g * gamma(Y1)) * beta (by Category).
   Therefore f = g.
  qed.
 qed.

 Let us show that F is full from C to D.
  Let us show that for all X1,X2 < C and all g << D(F(X1),F(X2))
  there exists f << C(X1,X2) such that F(f) = g.
   Let X1,X2 < C. Let g << D(F(X1),F(X2)).
   Take beta << C(X1, (G*F)(X1)) such that beta * alpha(X1) = 1{(G*F)(X1),C}.
   Take delta << C(X2, (G*F)(X2)) such that delta * alpha(X2) = 1{(G*F)(X2),C}. 
   Take f = alpha(X2) * (G(g) * beta).
   G(g) << C(G(F(X1)),G(F(X2))) (by Functor).
   G(g) << C((G*F)(X1),(G*F)(X2)).
   alpha(X1) << C((G*F)(X1),X1).
   alpha(X2) << C((G*F)(X2),X2).
   f << C(X1,X2) (by Category).
   f * alpha(X1) = alpha(X2) * (G*F)(f).
   Let us show that G(F(f)) = G(g).
    (G*F)(f) << C((G*F)(X1),(G*F)(X2)).
    G(F(f)) = (G*F)(f) = 1{(G*F)(X2),C} * (G*F)(f) = (delta * alpha(X2)) * (G*F)(f).
    (delta * alpha(X2)) * (G*F)(f) = delta * (alpha(X2) * (G*F)(f)) (by Category).
    delta * (alpha(X2) * (G*F)(f)) = delta * (f * alpha(X1)).
    f * alpha(X1) = (alpha(X2) * (G(g) * beta)) * alpha(X1).
    G(g) * beta << C(X1, (G*F)(X2)) (by Category).
    (alpha(X2) * (G(g) * beta)) * alpha(X1) = alpha(X2) * ((G(g) * beta) * alpha(X1)) (by Category).
    (G(g) * beta) * alpha(X1) = G(g) * (beta * alpha(X1)) = G(g) * 1{(G*F)(X1),C}
    = G(g) (by Category).
    Therefore G(F(f)) = delta * (alpha(X2) * G(g)).
    delta * (alpha(X2) * G(g)) = (delta * alpha(X2)) * G(g) = 1{(G*F)(X2),C} * G(g)
    = G(g) (by Category).
   qed.
  qed.
 qed.
Qed.

##########

Let K denote a field.

Definition Algebra. An algebra over K is an object A such that
     (A is a vector space over K)
 and (A is a ring)
 and (for all x < K and all a,b < A : x @{A} (a *{A} b) = (x @{A} a) *{A} b = a *{A} (x @{A} b)).

Theorem. K is an algebra over K.
Proof.
 K is a vector space over K.
 Let us show that K is a ring.
  K is an abelian group.
  1{K} < K.
  For all a,b < K   : a *{K} b < K.
  For all a < K     :       a *{K} 1{K} = a.
  For all a < K     :       1{K} *{K} a = a.
  For all a,b,c < K : a *{K} (b *{K} c) = (a *{K} b) *{K} c (by Field).
  For all a,b,c < K : a *{K} (b +{K} c) = (a *{K} b) +{K} (a *{K} c) (by Field).
  For all a,b,c < K : (a +{K} b) *{K} c = (a *{K} c) +{K} (b *{K} c) (by Field).  
 qed.
 Let us show that for all x < K and all a,b < K :
 x @{K} (a *{K} b) = (x @{K} a) *{K} b = a *{K} (x @{K} b).
  Let x,a,b < K.
  x *{K} (a *{K} b) = (x *{K} a) *{K} b.
  (x *{K} a) *{K} b = (a *{K} x) *{K} b = a *{K} (x *{K} b).
 qed.
Qed.

Definition Module. Let A be an object. A module over A over K is an object V such that
     (A is an algebra over K)
 and (V is a vector space over K)
 and (for all a < A and all v < V : a @@{V} v < V)
 and (for all a < A and all v,w < V :             a @@{V} (v +{V} w) = (a @@{V} v) +{V} (a @@{V} w))
 and (for all x < K and all a < A and all v < V : a @@{V} (x @{V} v) = x @{V} (a @@{V} v))
 and (for all a,b < A and all v < V :             (a +{A} b) @@{V} v = (a @@{V} v) +{V} (b @@{V} v))
 and (for all x < K and all a < A and all v < V : (x @{A} a) @@{V} v = x @{V} (a @@{V} v))
 and (for all a,b < A and all v < V :             (a *{A} b) @@{V} v = a @@{V} (b @@{V} v))
 and (for all v < V :                                   1{A} @@{V} v = v).

Axiom. Let V be a vector space over K. Let x < K and v < V. x @@{V} v = x @{V} v.

Theorem. Let V be a vector space over K. V is a module over K over K.
Proof.
 K is an algebra over K.
 V is a vector space over K.
 For all a < K and all v < V : a @@{V} v < V.
 Let us show that for all a < K and all v,w < V : a @@{V} (v +{V} w) = (a @@{V} v) +{V} (a @@{V} w).
  Let a < K and v,w < V.
 a @{V} (v +{V} w) = (a @{V} v) +{V} (a @{V} w) (by VectorSpace).
 qed.
 Let us show that for all x,a < K and all v < V : a @@{V} (x @{V} v) = x @{V} (a @@{V} v).
  Let x,a < K and v < V.
  a @{V} (x @{V} v) = x @{V} (a @{V} v) (by VectorSpace).
 qed.
 Let us show that for all a,b < K and all v < V : (a +{K} b) @@{V} v = (a @@{V} v) +{V} (b @@{V} v).
  Let a,b < K and v < V.
  (a +{K} b) @{V} v = (a @{V} v) +{V} (b @{V} v) (by VectorSpace).
  a +{K} b < K.
 qed.
 Let us show that for all x,a < K and all v < V : (x @{K} a) @@{V} v = x @{V} (a @@{V} v).
  Let x,a < K and v < V.
  (x *{K} a) @{V} v = x @{V} (a @{V} v) (by VectorSpace).
  x @{K} a = x *{K} a < K.
 qed.
 Let us show that for all a,b < K and all v < V : (a *{K} b) @@{V} v = a @@{V} (b @@{V} v).
  Let a,b < K and v < V.
  a *{K} b < K.
  (a *{K} b) @@{V} v = (a *{K} b) @{V} v.
  a @@{V} (b @@{V} v) = a @{V} (b @{V} v).
  (a *{K} b) @{V} v = a @{V} (b @{V} v) (by VectorSpace).
 qed.
 For all v < V : 1{K} @@{V} v = v.
Qed.

##########

Let K denote a field.

Definition AlgebraHom. Let A,B be objects. An algebrahom over K from A to B is a map f such that
     (A,B are algebras over K)
 and (f is linear over K from A to B)
 and (for all a,b < A : f(a *{A} b) = f(a) *{B} f(b))
 and (f(1{A}) = 1{B}).

Theorem. Let A be an algebra over K. Then id{|A|} is an algebrahom over K from A to A.
Proof.
 id{|A|} is linear over K from A to A.
Qed.

Theorem. Let V be a vector space over K. Endo(K,V) is an algebra over K.
Proof.
 Take A = Endo(K,V).
 A is a vector space over K.
 A is a ring.
 Let us show that for all x < K and all f,g < A :
 x @{A} (f *{A} g) = (x @{A} f) *{A} g = f *{A} (x @{A} g).
  Let x < K. Let f,g < A.
  Let us show that for all v < V : (x @{A} (f *{A} g))(v) = ((x @{A} f) *{A} g)(v).
   Let v < V.
   (x @{A} (f *{A} g))(v) = x @{V} (f *{A} g)(v).
   x @{V} (f *{A} g)(v) = x @{V} (f*g)(v).
   x @{V} (f*g)(v) = x @{V} f(g(v)).
   Let us show that x @{V} f(g(v)) = (x @{A} f)(g(v)).
    x < K.
    f < Hom(K,V,V).
    For all w < V : (x @{Hom(K,V,V)} f)(w) = x @{V} f(w) (by MapSmul).
    g(v) < V.
   qed.
   (x @{A} f)(g(v)) = ((x @{A} f)*g)(v).
   x @{A} f < A.
   ((x @{A} f)*g)(v) = ((x @{A} f) *{A} g)(v).
  qed.
  x @{A} (f *{A} g), (x @{A} f) *{A} g < A.
  Dmn(x @{A} (f *{A} g)) = |V|.
  Dmn((x @{A} f) *{A} g) = |V|.
  Thus x @{A} (f *{A} g) = (x @{A} f) *{A} g.
  Let us show that for all v < V : ((x @{A} f) *{A} g)(v) = (f *{A} (x @{A} g))(v).
   Let v < V.
   ((x @{A} f) *{A} g)(v) = ((x @{A} f)*g)(v).
   ((x @{A} f)*g)(v) = (x @{A} f)(g(v)).
   Let us show that (x @{A} f)(g(v)) = x @{V} f(g(v)).
    x < K.
    f < Hom(K,V,V).
    For all w < V : (x @{Hom(K,V,V)} f)(w) = x @{V} f(w) (by MapSmul).
    g(v) < V.
   qed.
   Let us show that x @{V} f(g(v)) = f(x @{V} g(v)).
    f is linear over K from V to V.
    x < K.
    g(v) < V.
   qed.
   f(x @{V} g(v)) = f((x @{A} g)(v)).
   f((x @{A} g)(v)) = (f*(x @{A} g))(v).
   (f*(x @{A} g))(v) = (f *{A} (x @{A} g))(v).
  qed.
  f *{A} (x @{A} g) < A.
  Dmn(f *{A} (x @{A} g)) = |V|.
  Thus (x @{A} f) *{A} g = f *{A} (x @{A} g).
 qed.
 Therefore the thesis (by Algebra).
Qed.

Definition Representation. Let A,V be objects. A representation of A in V over K is an object p such that
     (A is an algebra over K)
 and (V is a vector space over K)
 and (p is an algebrahom over K from A to Endo(K,V)).

Let rep(p,K,A,V) stand for (A is an algebra over K and V is a vector space over K
                            and p is a representation of A in V over K).

# every representation gives a module

Axiom. Let rep(p,K,A,V).  |rep2mod(p,K,A,V)| = |V|.
Axiom. Let rep(p,K,A,V). For all a < A and all v < V : a @@{rep2mod(p,K,A,V)} v = p(a)(v).

Lemma. Let rep(p,K,A,V). rep2mod(p,K,A,V) is a subspace of V over K.
Proof.
 V is a vector space over K.
 |rep2mod(p,K,A,V)| = |V|.
Qed.

Theorem. Let rep(p,K,A,V). rep2mod(p,K,A,V) is a vector space over K.
Theorem. Let rep(p,K,A,V). Let v,w < V.          v +{rep2mod(p,K,A,V)} w = v +{V} w.
Theorem. Let rep(p,K,A,V). Let v < V.              ~{rep2mod(p,K,A,V)} v =   ~{V} v.
Theorem. Let rep(p,K,A,V). Let x < K. Let v < V. x @{rep2mod(p,K,A,V)} v = x @{V} v.
Proof.
 rep2mod(p,K,A,V) is a subspace of V over K.
Qed.

Theorem. Let rep(p,K,A,V). rep2mod(p,K,A,V) is a module over A over K.
Proof.
 Take M = rep2mod(p,K,A,V).
 M is a vector space over K.
 Endo(K,V) is a vector space over K.
 p is linear over K from A to Endo(K,V).
 Dmn(p) = |A|.

 Let us show that M is a module over A over K.
  Let us show that for all a < A and all v < M : a @@{M} v < M.
   Let a < A and v < M.
   v < V.
   a << Dmn(p).      # When dealing with representations, more detailed proofs are needed.
   p(a) is a map.
   p(a) is linear over K from V to V.
   v << Dmn(p(a)).
   a @@{M} v = p(a)(v).
  qed.
  
  Let us show that for all a < A and all v,w < M :
  a @@{M} (v +{M} w) = (a @@{M} v) +{M} (a @@{M} w).
   Let a < A and v,w < M.
   a @@{M} (v +{M} w) = a @@{M} (v +{V} w).
   (a @@{M} v) +{M} (a @@{M} w) = (a @@{M} v) +{V} (a @@{M} w).
   Let us show that a @@{M} (v +{V} w) = (a @@{M} v) +{V} (a @@{M} w).
    a << Dmn(p).
    p(a) is a map.
    p(a) is linear over K from V to V.
    v +{V} w, v, w << Dmn(p(a)).
    a @@{M} (v +{V} w) = p(a)(v +{V} w) = p(a)(v) +{V} p(a)(w) = (a @@{M} v) +{V} (a @@{M} w).
   qed.
  qed.

  Let us show that for all x < K and all a < A and all v < M :
  a @@{M} (x @{M} v) = x @{M} (a @@{M} v).
   Let x < K and a < A and v < M.
   a @@{M} (x @{M} v) = a @@{M} (x @{V} v).
   x @{M} (a @@{M} v) = x @{V} (a @@{M} v).
   Let us show that a @@{M} (x @{V} v) = x @{V} (a @@{M} v).
    a << Dmn(p).
    p(a) is a map.
    p(a) is linear over K from V to V.
    x @{V} v, v << Dmn(p(a)).
    a @@{M} (x @{V} v) = p(a)(x @{V} v) = x @{V} p(a)(v) = x @{V} (a @@{M} v).
   qed.
  qed.

  Let us show that for all a,b < A and all v < M :
  (a +{A} b) @@{M} v = (a @@{M} v) +{M} (b @@{M} v).
   Let a,b < A and v < M.
   (a @@{M} v) +{M} (b @@{M} v) = (a @@{M} v) +{V} (b @@{M} v).
   Let us show that (a +{A} b) @@{M} v = (a @@{M} v) +{V} (b @@{M} v).
    a << Dmn(p).
    p(a) is a map.
    p(a) is linear over K from V to V.
    v << Dmn(p(a)).
    b << Dmn(p).
    p(b) is a map.
    p(b) is linear over K from V to V.
    v << Dmn(p(b)).
    a +{A} b << Dmn(p).
    p(a +{A} b) is a map.
    p(a +{A} b) is linear over K from V to V.
    v << Dmn(p(a +{A} b)).
    (a +{A} b) @@{M} v = p(a +{A} b)(v).
    p(a) +{Endo(K,V)} p(b) is a map.
    Let us show that p(a +{A} b) = p(a) +{Endo(K,V)} p(b).
     p is an algebrahom over K from A to Endo(K,V).
    qed.
    v << Dmn(p(a) +{Endo(K,V)} p(b)).
    p(a +{A} b)(v) = (p(a) +{Endo(K,V)} p(b))(v).
    p(a), p(b) < Hom(K,V,V).
    (p(a) +{Hom(K,V,V)} p(b))(v) = p(a)(v) +{V} p(b)(v) (by MapAdd).
    p(a)(v) +{V} p(b)(v) = (a @@{M} v) +{V} (b @@{M} v).
   qed.
  qed.

  Let us show that for all x < K and all a < A and all v < M :
  (x @{A} a) @@{M} v = x @{M} (a @@{M} v).
   Let x < K and a < A and v < M.
   x @{M} (a @@{M} v) = x @{V} (a @@{M} v).
   Let us show that (x @{A} a) @@{M} v = x @{V} (a @@{M} v).
    a << Dmn(p).
    p(a) is a map.
    p(a) is linear over K from V to V.
    v << Dmn(p(a)).
    x @{A} a << Dmn(p).
    p(x @{A} a) is a map.
    p(x @{A} a) is linear over K from V to V.
    v << Dmn(p(x @{A} a)).
    (x @{A} a) @@{M} v = p(x @{A} a)(v).
    x @{Endo(K,V)} p(a) is a map.
    Let us show that p(x @{A} a) = x @{Endo(K,V)} p(a).
     p is an algebrahom over K from A to Endo(K,V).
    qed.
    v << Dmn(x @{Endo(K,V)} p(a)).
    p(x @{A} a)(v) = (x @{Endo(K,V)} p(a))(v).
    (x @{Endo(K,V)} p(a))(v) = x @{V} p(a)(v).
    x @{V} p(a)(v) = x @{V} (a @@{M} v).
   qed.
  qed.

  Let us show that for all a,b < A and all v < M : (a *{A} b) @@{M} v = a @@{M} (b @@{M} v).
   Let a,b < A and v < M.
   Let us show that (a *{A} b) @@{M} v = a @@{M} (b @@{M} v).
    b << Dmn(p).
    p(b) is a map.
    p(b) is linear over K from V to V.
    v << Dmn(p(b)).
    a << Dmn(p).
    p(a) is a map.
    p(a) is linear over K from V to V.
    p(b)(v) << Dmn(p(a)).
    a *{A} b << Dmn(p).
    p(a *{A} b) is a map.
    p(a *{A} b) is linear over K from V to V.
    v << Dmn(p(a *{A} b)).
    (a *{A} b) @@{M} v = p(a *{A} b)(v).
    p(a) *{Endo(K,V)} p(b) is a map.
    Let us show that p(a *{A} b) = p(a)*p(b).
     p is an algebrahom over K from A to Endo(K,V).
     p(a *{A} b) = p(a) *{Endo(K,V)} p(b).
     p(a) *{Endo(K,V)} p(b) = p(a)*p(b).
    qed.
    v << Dmn(p(a)*p(b)).
    p(a *{A} b)(v) = (p(a)*p(b))(v).
    (p(a)*p(b))(v) = p(a)(p(b)(v)).
    p(a)(p(b)(v)) = a @@{M} (p(b)(v)).
    a @@{M} (p(b)(v)) = a @@{M} (b @@{M} v).
   qed.
  qed.

  Let us show that for all v < M : 1{A} @@{M} v = v.
   Let v < M.
   1{A} << Dmn(p).
   p is an algebrahom over K from A to Endo(K,V).
   p(1{A}) = 1{Endo(K,V)}.
   1{A} @@{M} v = p(1{A})(v) = 1{Endo(K,V)}(v) = id{|V|}(v) = v.
  qed.
 qed.
Qed.


# every module gives a representation

Axiom. Let A be an algebra over K. Let V be a module over A over K.
 mod2rep(K,A,V) is a map p such that Dmn(p) = |A| and for all a < A :
 (p(a) is a map such that Dmn(p(a)) = |V| and for all v < V : p(a)(v) = a @@{V} v).

Theorem. Let A be an algebra over K. Let V be a module over A over K.
 Then mod2rep(K,A,V) is a representation of A in V over K.
Proof.
 Take a map p such that p = mod2rep(K,A,V).
 A is a vector space over K.
 Endo(K,V) is a vector space over K.
 |A| is a set.
 |Endo(K,V)| is a set.
 Let us show that p is linear over K from A to Endo(K,V).
  Let us show that p is a map from |A| to |Endo(K,V)|.
   p is a map.
   Dmn(p) = |A|.
   For all a < A : a << Dmn(p).
   |Endo(K,V)| is a set.
   Let us show that for all a < A : p(a) < Endo(K,V).
    Let a < A.
    p(a) is a map.
    Let us show that p(a) is linear over K from V to V.
     Dmn(p(a)) = |V|.
     Let us show that for all v < V : p(a)(v) < V.
      Let v < V.
      p(a)(v) = a @@{V} v < V.
     qed.
     Let us show that for all u,v < V : p(a)(u +{V} v) = p(a)(u) +{V} p(a)(v).
      Let u,v < V.
      p(a)(u +{V} v) = a @@{V} (u +{V} v).
      a @@{V} (u +{V} v) = (a @@{V} u) +{V} (a @@{V} v) (by Module).
      (a @@{V} u) +{V} (a @@{V} v) = p(a)(u) +{V} p(a)(v).
     qed.
     Let us show that for all x < K and all v < V : p(a)(x @{V} v) = x @{V} p(a)(v).
      Let x < K and v < V.
      x @{V} v < V.
      p(a)(x @{V} v) = a @@{V} (x @{V} v).
      a @@{V} (x @{V} v) = x @{V} (a @@{V} v) (by Module).
      x @{V} (a @@{V} v) = x @{V} p(a)(v).
     qed.
    qed.
   qed.  
  qed.
  Let us show that for all a,b < A : p(a +{A} b) = p(a) +{Endo(K,V)} p(b).
   Let a,b < A.
   Let us show that for all v < V : p(a +{A} b)(v) = (p(a) +{Endo(K,V)} p(b))(v).
    Let v < V.
    a +{A} b < A.
    p(a +{A} b)(v) = (a +{A} b) @@{V} v.
    (a +{A} b) @@{V} v = (a @@{V} v) +{V} (b @@{V} v) (by Module).
    p(a), p(b) < Hom(K,V,V).
    (a @@{V} v) +{V} (b @@{V} v) = p(a)(v) +{V} p(b)(v) = (p(a) +{Hom(K,V,V)} p(b))(v).
   qed.
  qed.
  Let us show that for all x < K and all a < A : p(x @{A} a) = x @{Endo(K,V)} p(a).
   Let x < K and a < A.
   Let us show that for all v < V : p(x @{A} a)(v) = (x @{Endo(K,V)} p(a))(v).
    Let v < V.
    x @{A} a < A.
    p(x @{A} a)(v) = (x @{A} a) @@{V} v.
    (x @{A} a) @@{V} v = x @{V} (a @@{V} v) (by Algebra).
    x @{V} (a @@{V} v) = x @{V} p(a)(v).
    x @{V} p(a)(v) = (x @{Endo(K,V)} p(a))(v).
   qed.
  qed.
 qed.
 p is a map.
 Let us show that p is an algebrahom over K from A to Endo(K,V).
  Let us show that for all a,b < A : p(a *{A} b) = p(a) *{Endo(K,V)} p(b).
   Let a,b < A.
   Dmn(p(a *{A} b)) = |V|.
   Dmn(p(a) *{Endo(K,V)} p(b)) = |V|.
   Let us show that for all v < V : p(a *{A} b)(v) = (p(a) *{Endo(K,V)} p(b))(v).
    Let v < V.
    p(a *{A} b)(v) = (a *{A} b) @@{V} v.
    (a *{A} b) @@{V} v = a @@{V} (b @@{V} v).
    a @@{V} (b @@{V} v) = p(a)(b @@{V} v).
    p(a)(b @@{V} v) = p(a)(p(b)(v)).
    p(a)(p(b)(v)) = (p(a)*p(b))(v).
    (p(a)*p(b))(v) = (p(a) *{Endo(K,V)} p(b))(v).
   qed.
   Dmn(p(a *{A} b)) = |V|.
   Dmn(p(a) *{Endo(K,V)} p(b)) = |V|.
   Therefore the thesis.
  qed.
  Let us show that p(1{A}) = 1{Endo(K,V)}.
   Let us show that for all v < V : p(1{A})(v) = 1{Endo(K,V)}(v).
    Let v < V.
    p(1{A})(v) = 1{A} @@{V} v = v = id{|V|}(v) = 1{Endo(K,V)}(v).
   qed.
  qed.
 qed.
Qed.

##########

Let K denote a field.

Definition ModuleHom. Let A,M,N be objects.
 A modulehom over A over K from M to N is a map f such that
     (A is an algebra over K)
 and (M,N are modules over A over K)
 and (f is from |M| to |N|)
 and (for all x,y < M             : f(x +{M} y) = f(x) +{N} f(y))
 and (for all a < A and all x < M : f(a @@{M} x) = a @@{N} f(x)).

Axiom. Let A be an algebra over K. Let M,N be modules over A over K.
 |Hom(K,A,M,N)| is the set of modulehoms over A over K from M to N.

Lemma ModuleHomSubset. Let A be an algebra over K. Let M,N be modules over A over K.
 |Hom(K,A,M,N)| is a subset of |Hom(K,M,N)|.
Proof.
 Take V = Hom(K,M,N).
 Take U = Hom(K,A,M,N).
 Let us show that |U| is a subset of |V|.
  Let us show that for all f < U : f < V.
   Let f < U.
   f is a map.
   Let us show that f is linear over K from M to N.
    f is from |M| to |N|.
    Let us show that for all x,y < M : f(x +{M} y) = f(x) +{N} f(y).
     Let x,y < M.
     Let us show that f(x +{M} y) = f(x) +{N} f(y).
      f is a modulehom over A over K from M to N.
      Therefore the thesis (by ModuleHom).
     qed.
     Therefore the thesis.
    qed.
    Let us show that for all a < K and all x < M : f(a @{M} x) = a @{N} f(x).
     Let a < K and x < M.
     a @{M} x = a @{M} (1{A} @@{M} x).
     a @{M} (1{A} @@{M} x) = (a @{A} 1{A}) @@{M} x (by Module).
     f(a @{M} x) = f((a @{A} 1{A}) @@{M} x).
     Let us show that f((a @{A} 1{A}) @@{M} x) = (a @{A} 1{A}) @@{N} f(x).
      f is a modulehom over A over K from M to N.
      (a @{A} 1{A}) < A.
      Therefore the thesis (by ModuleHom).
     qed.
     (a @{A} 1{A}) @@{N} f(x) = a @{N} (1{A} @@{N} f(x)) = a @{N} f(x) (by Module).
    qed.   
   qed.
  qed.
 qed.
Qed.

Lemma ModuleHomAddClosed. Let A be an algebra over K. Let M,N be modules over A over K.
 Let f,g < Hom(K,A,M,N). Then f +{Hom(K,M,N)} g < Hom(K,A,M,N).
Proof.
 f,g < Hom(K,M,N) (by ModuleHomSubset).
 f,g are maps.
 f +{Hom(K,M,N)} g is a map and for all x < M : (f +{Hom(K,M,N)} g)(x) = f(x) +{N} g(x) (by MapAdd).
 Take V = Hom(K,M,N).
 Take U = Hom(K,A,M,N).
 V is a vector space over K.
 Let us show that f +{V} g < U.
  f and g are maps.
  Let us show that f +{V} g is a modulehom over A over K from M to N.
   f < V. g < V.
   f +{V} g < V (by VectorSpace).
   f +{V} g < Hom(K,M,N).
   f +{V} g is a map.
   f +{V} g is linear over K from M to N.
   For all x,y < M : (f +{V} g)(x +{M} y) = (f +{V} g)(x) +{N} (f +{V} g)(y) (by MapAdd).
   Let us show that for all a < A and all x < M : (f +{V} g)(a @@{M} x) = a @@{N} (f +{V} g)(x).
    Let a < A and x < M.
    (f +{V} g)(a @@{M} x) = f(a @@{M} x) +{N} g(a @@{M} x).
    Let us show that f(a @@{M} x) +{N} g(a @@{M} x) = (a @@{N} f(x)) +{N} (a @@{N} g(x)).
     f is a modulehom over A over K from M to N.
     g is a modulehom over A over K from M to N.
     f(a @@{M} x) = a @@{N} f(x) (by ModuleHom).
     g(a @@{M} x) = a @@{N} g(x) (by ModuleHom).
    qed.
    N is a module over A over K.
    f(x) < N.
    g(x) < N.
    (a @@{N} f(x)) +{N} (a @@{N} g(x)) = a @@{N} (f(x) +{N} g(x)) (by Module).
    a @@{N} (f(x) +{N} g(x)) = a @@{N} (f +{V} g)(x).
   qed.
  qed.
 qed.
Qed.

Lemma ModuleHomSmulClosed. Let A be an algebra over K. Let M,N be modules over A over K.
 Let f < Hom(K,A,M,N). Let a < K. Then a @{Hom(K,M,N)} f < Hom(K,A,M,N).
Proof.
 f < Hom(K,M,N) (by ModuleHomSubset).
 f is a map.
 a @{Hom(K,M,N)} f is a map and for all x < M : (a @{Hom(K,M,N)} f)(x) = a @{N} f(x) (by MapSmul).
 Take V = Hom(K,M,N).
 Take U = Hom(K,A,M,N).
 V is a vector space over K.
 Let us show that a @{V} f < U.
  f is a map.
  Let us show that a @{V} f is a modulehom over A over K from M to N.
   f < V.
   a @{V} f < V (by VectorSpace).
   a @{V} f < Hom(K,M,N).
   a @{V} f is a map.
   a @{V} f is linear over K from M to N.
   For all x,y < M : (a @{V} f)(x +{M} y) = (a @{V} f)(x) +{N} (a @{V} f)(y) (by MapAdd).
   Let us show that for all b < A and all x < M : (a @{V} f)(b @@{M} x) = b @@{N} (a @{V} f)(x).
    Let b < A and x < M.
    (a @{V} f)(b @@{M} x) = a @{N} f(b @@{M} x).
    Let us show that a @{N} f(b @@{M} x) = a @{N} (b @@{N} f(x)).
     f is a modulehom over A over K from M to N.
     f(b @@{M} x) = b @@{N} f(x) (by ModuleHom).
    qed.
    N is a module over A over K.
    f(x) < N.
    a @{N} (b @@{N} f(x)) = b @@{N} (a @{N} f(x)) (by Module).
    b @@{N} (a @{N} f(x)) = b @@{N} (a @{V} f)(x).
   qed.
  qed.
 qed.
Qed.

Theorem ModuleHomSubspace. Let A be an algebra over K. Let M,N be modules over A over K.
 Hom(K,M,N) is a vector space over K and Hom(K,A,M,N) is a subspace of Hom(K,M,N) over K.
Proof.
 Hom(K,M,N) is a vector space over K.
 Take V = Hom(K,M,N).
 Take U = Hom(K,A,M,N).
 Let us show that U is a subspace of V over K.
  |U| is subset of |V| (by ModuleHomSubset).
  For all f,g < U             : f +{V} g < U (by ModuleHomAddClosed).
  For all a < K and all f < U : a @{V} f < U (by ModuleHomSmulClosed).
  Let us show that 0{V} < U.
   0{V} < V.
   0{V} is a map linear over K from M to N.
   Let us show that 0{V} is a modulehom over A over K from M to N.
    0{V} is from |M| to |N|.
    For all x,y < M : 0{V}(x +{M} y) = 0{V}(x) +{N} 0{V}(y) (by MapZero).
    Let us show that for all a < A and all x < M : 0{V}(a @@{M} x) = a @@{N} 0{V}(x).
     Let a < A and x < M.
     0{V}(a @@{M} x) = 0{N} (by MapZero).
     0{N} = 0{K} @{N} (a @@{N} 0{N}) (by ZeroSmul).
     Let us show that 0{K} @{N} (a @@{N} 0{N}) = a @@{N} (0{K} @{N} 0{N}).
      0{K} < K.
      0{N} < N.
      a < A.
      N is a module over A over K.
      Therefore the thesis (by Module).
     qed.
     a @@{N} (0{K} @{N} 0{N}) = a @@{N} 0{N}.
     a @@{N} 0{N} = a @@{N} 0{V}(x).
    qed.
   qed.
  qed.
 qed.
Qed.

Theorem ModuleHomVectorSpace. Let A be an algebra over K. Let M,N be modules over A over K.
 Hom(K,A,M,N) is a vector space over K.
Proof.
 Hom(K,A,M,N) is a subspace of Hom(K,M,N) over K.
Qed.

Theorem ModuleHomZero. Let A be an algebra over K. Let M,N be modules over A over K.
 0{Hom(K,A,M,N)} is a map h such that Dmn(h) = |M| and
 for all v < M : h(v) = 0{N}.
Proof.
 Hom(K,A,M,N) is a subspace of Hom(K,M,N) over K.
 0{Hom(K,A,M,N)} = 0{Hom(K,M,N)} (by SubZero).
 Therefore the thesis (by MapZero).
Qed.

Theorem ModuleHomAdd. Let A be an algebra over K. Let M,N be modules over A over K.
 Let f,g < Hom(K,A,M,N). f +{Hom(K,A,M,N)} g is a map h such that Dmn(h) = |M| and
 for all v < M : h(v) = f(v) +{N} g(v).
Proof.
 Hom(K,A,M,N) is a subspace of Hom(K,M,N) over K.
 f +{Hom(K,A,M,N)} g = f +{Hom(K,M,N)} g (by SubAdd).
 Therefore the thesis (by MapAdd).
Qed.

Theorem ModuleHomNeg. Let A be an algebra over K. Let M,N be modules over A over K.
 Let f < Hom(K,A,M,N). ~{Hom(K,A,M,N)} f is a map h such that Dmn(h) = |M| and
 for all v < M : h(v) = ~{N} f(v).
Proof.
 Hom(K,A,M,N) is a subspace of Hom(K,M,N) over K.
 ~{Hom(K,A,M,N)} f = ~{Hom(K,M,N)} f (by SubNeg).
 Therefore the thesis (by MapNeg).
Qed.

Theorem ModuleHomSmul. Let A be an algebra over K. Let M,N be modules over A over K.
 Let x < K. Let f < Hom(K,A,M,N). x @{Hom(K,A,M,N)} f is a map h such that Dmn(h) = |M| and
 for all v < M : h(v) = x @{N} f(v).
Proof.
 Hom(K,A,M,N) is a subspace of Hom(K,M,N) over K.
 x @{Hom(K,A,M,N)} f = x @{Hom(K,M,N)} f (by SubSmul).
 Therefore the thesis (by MapSmul).
Qed.

##########

Let K denote a field.

Axiom ModOb.  Let A be an algebra over K. Ob{Mod(K,A)} is the set of modules over A over K.
Axiom ModMor. Let A be an algebra over K. Let M,N << Ob{Mod(K,A)}. Mod(K,A)(M,N) = |Hom(K,A,M,N)|.
Axiom ModId.  Let A be an algebra over K. Let M << Ob{Mod(K,A)}.  1{M,Mod(K,A)} = id{|M|}.

Theorem ModuleHomComp. Let A be an algebra over K. Let L,M,N be modules over A over K.
 Let f < Hom(K,A,L,M). Let g < Hom(K,A,M,N). Then g*f < Hom(K,A,L,N).
Proof.
 For all modules M1,M2 over A over K :
 (|Hom(K,A,M1,M2)| is the set of maps h such that h is a modulehom over A over K from M1 to M2).
 Let us show that g*f is a modulehom over A over K from L to N.
  f is a modulehom over A over K from L to M.
  g is a modulehom over A over K from M to N.
  g*f is a map from |L| to |N| (by CompFromTo).
  Let us show that for all x,y < L : (g*f)(x +{L} y) = (g*f)(x) +{N} (g*f)(y).
   Let x,y < L.
   (g*f)(x +{L} y) = g(f(x +{L} y)).
   Let us show that g(f(x +{L} y)) = g(f(x) +{M} f(y)).
    f is a modulehom over A over K from L to M.
    x,y < L.
    f(x +{L} y) = f(x) +{M} f(y).
   qed.
   g(f(x) +{M} f(y)) = g(f(x)) +{N} g(f(y)) (by MapAdd).
   g(f(x)) +{N} g(f(y)) = (g*f)(x) +{N} (g*f)(y).
  qed.
  Let us show that for all a < A and all x < L : (g*f)(a @@{L} x) = a @@{N} (g*f)(x).
   Let a < A and x < L.
   f(a @@{L} x) = a @@{M} f(x) (by ModuleHom).
   (g*f)(a @@{L} x) = g(f(a @@{L} x)) = g(a @@{M} f(x)).
   f(x) < M.
   g(a @@{M} f(x)) = a @@{N} g(f(x)) (by ModuleHom).
   a @@{N} g(f(x)) = a @@{N} (g*f)(x).
  qed.
 qed.
Qed.

Theorem. Let A be an algebra over K. Mod(K,A) is a category.
Proof.
 Take C = Mod(K,A).
 For all modules M,N over A over K :
 (|Hom(K,A,M,N)| is the set of maps f such that f is a modulehom over A over K from M to N).
 For all modules M,N over A over K and all f < Hom(K,A,M,N) : (f is a map from |M| to |N|).
 Let us show that C is a category.
  Ob{C} is a set.
  Let us show that for all L,M,N << Ob{C} and all f << C(L,M) and all g << C(M,N) : g*f << C(L,N).
   Let L,M,N << Ob{C} and f << C(L,M) and g << C(M,N).
   L,M,N are modules over A over K.
   f < Hom(K,A,L,M) (by ModMor).
   g < Hom(K,A,M,N) (by ModMor).
   Thus g*f < Hom(K,A,L,N).
   C(L,N) = |Hom(K,A,L,N)| (by ModMor).
  qed.
  Let us show that for all M << Ob{C} : 1{M,C} << C(M,M).
   Let M << Ob{C}.
   M is a module over A over K.
   Let us show that id{|M|} is a modulehom over A over K from M to M.
     id{|M|} is from |M| to |M|.
    For all x,y < M : id{|M|}(x +{M} y) = id{|M|}(x) +{M} id{|M|}(y).
    For all a < A and all x < M : id{|M|}(a @@{M} x) = a @@{M} id{|M|}(x).
   qed.
   Thus id{|M|} < Hom(K,A,M,M).
   C(M,M) = |Hom(K,A,M,M)| (by ModMor).
  qed.
  Let us show that for all M,N << Ob{C} and all f << C(M,N) : f*1{M,C} = f.
   Let M,N << Ob{C} and f << C(M,N).
   f < Hom(K,A,M,N) (by ModMor).
   f : |M| -> |N|.
   Dmn(f) = |M|.
  qed.
  Let us show that for all M,N << Ob{C} and all f << C(N,M) : 1{M,C}*f = f.
   Let M,N << Ob{C} and f << C(N,M).
   |M| is a set.
   f < Hom(K,A,N,M) (by ModMor).
   f : |N| -> |M|.
   id{|M|} is a map.
   id{|M|} and f are composable.
  qed.
  Let us show that for all L,M,N,O << Ob{C} and all f << C(L,M) and all g << C(M,N)
  and all h << C(N,O) : h*(g*f) = (h*g)*f.
   Let L,M,N,O << Ob{C} and f << C(L,M) and g << C(M,N) and h << C(N,O).
   f < Hom(K,A,L,M) (by ModMor).
   g < Hom(K,A,M,N) (by ModMor).
   h < Hom(K,A,N,O) (by ModMor).
   f : |L| -> |M|.
   g : |M| -> |N|.
   h : |N| -> |O|.
   Thus h*(g*f) = (h*g)*f (by ThreeComp).
  qed.
 qed.
Qed.

##########

Let K denote a field.

Axiom. Let K,A,x,y be objects. Hom(K,A,x,-)(y) = Hom(K,A,x,y).
Axiom. Let K,A,x,y be objects. Hom(K,A,-,y)(x) = Hom(K,A,x,y).

Axiom HomFun. Let A be an algebra over K. Let M,N1,N2 be modules over A over K.
 Let f < Hom(K,A,N1,N2). Hom(K,A,M,f) is a map F such that
 Dmn(F) = |Hom(K,A,M,N1)| and for all g < Hom(K,A,M,N1) : F(g) = f*g.

Axiom ContraHomFun. Let A be an algebra over K. Let M1,M2,N be modules over A over K.
 Let f < Hom(K,A,M1,M2). Hom(K,A,f,N) is a map F such that
 Dmn(F) = |Hom(K,A,M2,N)| and for all g < Hom(K,A,M2,N) : F(g) = g*f.

Theorem HomIsFunctor. Let A be an algebra over K. Let M be a module over A over K.
 Hom(K,A,M,-) is a functor from Mod(K,A) to Mod(K,K).
Proof.
 Take F = Hom(K,A,M,-).
 Let us show that F is a functor from Mod(K,A) to Mod(K,K).
  K is a field.
  Mod(K,A) and Mod(K,K) are categories.
  Let us show that for all N < Mod(K,A) : F(N) < Mod(K,K).
   Let N < Mod(K,A).
   N is a module over A over K.
   F(N) = Hom(K,A,M,N).
   Hom(K,A,M,N) is a vector space over K.
   Thus Hom(K,A,M,N) is a module over K over K.
  qed.
  For all modules L,N over A over K and all f < Hom(K,A,L,N) :
  (f is a modulehom over A over K from L to N).
  Let us show that for all N1,N2 < Mod(K,A) and all f << Mod(K,A)(N1,N2) :
  F(f) << Mod(K,K)(F(N1),F(N2)).
   Let N1,N2 < Mod(K,A) and f << Mod(K,A)(N1,N2).
   f < Hom(K,A,N1,N2) (by ModMor).
   K is a field.
   f is a modulehom over A over K from N1 to N2.
   F(N1) = Hom(K,A,M,N1).
   F(N2) = Hom(K,A,M,N2).
   Let us show that F(f) is a modulehom over K over K from Hom(K,A,M,N1) to Hom(K,A,M,N2).
    F(f) = Hom(K,A,M,f).
    Let us show that Hom(K,A,M,f) is a map from |Hom(K,A,M,N1)| to |Hom(K,A,M,N2)|.
     Hom(K,A,M,f) is a map (by HomFun).
     Dmn(Hom(K,A,M,f)) = |Hom(K,A,M,N1)| (by HomFun).
     Let us show that for all g < Hom(K,A,M,N1) : Hom(K,A,M,f)(g) < Hom(K,A,M,N2).
      Let g < Hom(K,A,M,N1).
      Hom(K,A,M,f)(g) = f*g (by HomFun).
      Let us show that f*g < Hom(K,A,M,N2).
       M,N1,N2 < Mod(K,A).
       g << Mod(K,A)(M,N1) (by ModMor).
       f << Mod(K,A)(N1,N2) (by ModMor).
       Mod(K,A) is a category.
       Thus f*g << Mod(K,A)(M,N2) (by Category).
       Therefore the thesis (by ModMor).
      qed.
     qed.
    qed.
    For all g < Hom(K,A,M,N1) : Hom(K,A,M,f)(g) = f*g (by HomFun).
    Let us show that for all g,h < Hom(K,A,M,N1) :
    F(f)(g +{Hom(K,A,M,N1)} h) = F(f)(g) +{Hom(K,A,M,N2)} F(f)(h).
     Let g,h < Hom(K,A,M,N1).
     Hom(K,A,M,N1) is a vector space over K.
     g +{Hom(K,A,M,N1)} h < Hom(K,A,M,N1) (by VectorSpace).
     F(f)(g +{Hom(K,A,M,N1)} h) = f*(g +{Hom(K,A,M,N1)} h) (by HomFun).
     F(f)(g) = f*g.
     F(f)(h) = f*h.
     M,N1 are modules over A over K.
     Let us show that f*(g +{Hom(K,A,M,N1)} h) = (f*g) +{Hom(K,A,M,N2)} (f*h).
      f*(g +{Hom(K,A,M,N1)} h) is a map.
      Let us show that (f*g) +{Hom(K,A,M,N2)} (f*h) is a map.
       f*g, f*h < Hom(K,A,M,N2).
       K is a field.
       M,N2 are modules over A over K.
       Hom(K,A,M,N2) is a vector space over K.
       (f*g) +{Hom(K,A,M,N2)} (f*h) < Hom(K,A,M,N2) (by VectorSpace).      
      qed.
      Let us show that Dmn(f*(g +{Hom(K,A,M,N1)} h)) = |M|.
       g +{Hom(K,A,M,N1)} h < Hom(K,A,M,N1).
       K is a field.
       g +{Hom(K,A,M,N1)} h is a modulehom over A over K from M to N1.
       g +{Hom(K,A,M,N1)} h is from |M| to |N1|.
       qed.
      Let us show that Dmn((f*g) +{Hom(K,A,M,N2)} (f*h)) = |M|.
       f*g < Hom(K,A,M,N2).
       f*h < Hom(K,A,M,N2).
       Hom(K,A,M,N2) is a vector space over K.
       (f*g) +{Hom(K,A,M,N2)} (f*h) < Hom(K,A,M,N2) (by VectorSpace).
       (f*g) +{Hom(K,A,M,N2)} (f*h) is a modulehom over A over K from M to N2.
      qed.
      Let us show that for all x < M : (f*(g +{Hom(K,A,M,N1)} h))(x)
                                       = ((f*g) +{Hom(K,A,M,N2)} (f*h))(x).
       Let x < M.
       f and g +{Hom(K,A,M,N1)} h are maps.
       (f*(g +{Hom(K,A,M,N1)} h))(x) = f((g +{Hom(K,A,M,N1)} h)(x)).
       M,N1 are modules over A over K.
       g,h < Hom(K,A,M,N1).
       (g +{Hom(K,A,M,N1)} h)(x) = g(x) +{N1} h(x) (by ModuleHomAdd).
       f((g +{Hom(K,A,M,N1)} h)(x)) = f(g(x) +{N1} h(x)).
       Let us show that f(g(x) +{N1} h(x)) = f(g(x)) +{N2} f(h(x)).
        f is a modulehom over A over K from N1 to N2.
        g,h are modulehoms over A over K from M to N1.
        g,h are from |M| to |N1|.
        g(x),h(x) < N1.
        Therefore the thesis (by ModuleHom).
       qed.
       f(g(x)) +{N2} f(h(x)) = (f*g)(x) +{N2} (f*h)(x).
       Let us show that (f*g)(x) +{N2} (f*h)(x) = ((f*g) +{Hom(K,A,M,N2)} (f*h))(x).
        M,N2 are modules over A over K.
        f*g,f*h < Hom(K,A,M,N2).
        ((f*g) +{Hom(K,A,M,N2)} (f*h))(x) = (f*g)(x) +{N2} (f*h)(x) (by ModuleHomAdd).
       qed.
      qed.
      Therefore the thesis (by MapExt).
     qed.
    qed.
    Let us show that for all a < K and all g < Hom(K,A,M,N1) :
    F(f)(a @@{Hom(K,A,M,N1)} g) = a @@{Hom(K,A,M,N2)} F(f)(g).
     Let a < K and g < Hom(K,A,M,N1).
     Hom(K,A,M,N1) is a vector space over K.
     a @@{Hom(K,A,M,N1)} g = a @{Hom(K,A,M,N1)} g.
     a @{Hom(K,A,M,N1)} g < Hom(K,A,M,N1) (by VectorSpace).
     F(f)(a @{Hom(K,A,M,N1)} g) = f*(a @{Hom(K,A,M,N1)} g) (by HomFun).
     F(f)(g) = f*g.
     f*g < Hom(K,A,M,N2).
     Let us show that f*(a @{Hom(K,A,M,N1)} g) = a @{Hom(K,A,M,N2)} (f*g).
      f*(a @{Hom(K,A,M,N1)} g) < Hom(K,A,M,N2).
      f*(a @{Hom(K,A,M,N1)} g) is a map.
      f*(a @{Hom(K,A,M,N1)} g) is a modulehom over A over K from M to N2.
      Dmn(f*(a @{Hom(K,A,M,N1)} g)) = |M|.
      Hom(K,A,M,N2) is a vector space over K.
      a @{Hom(K,A,M,N2)} (f*g) < Hom(K,A,M,N2) (by VectorSpace).
      a @{Hom(K,A,M,N2)} (f*g) is a map.
      a @{Hom(K,A,M,N2)} (f*g) is a modulehom over A over K from M to N2.
      Dmn(a @{Hom(K,A,M,N2)} (f*g)) = |M|.
      Let us show that for all x < M: (f*(a @{Hom(K,A,M,N1)} g))(x) = (a @{Hom(K,A,M,N2)} (f*g))(x).
       Let x < M.
       f and a @{Hom(K,A,M,N1)} g are maps.
       (f*(a @{Hom(K,A,M,N1)} g))(x) = f((a @{Hom(K,A,M,N1)} g)(x)).
       Let us show that (a @{Hom(K,A,M,N1)} g)(x) = a @{N1} g(x).
        M,N1 are modules over A over K.
        a < K.
        g < Hom(K,A,M,N1).
        x < M.
        Therefore the thesis (by ModuleHomSmul).
       qed.
       f((a @{Hom(K,A,M,N1)} g)(x)) = f(a @{N1} g(x)).
       Let us show that f(a @{N1} g(x)) = a @{N2} f(g(x)).
        K is a field.
        Hom(K,N1,N2) is a vector space over K.
        Hom(K,A,N1,N2) is a subspace of Hom(K,N1,N2) over K (by ModuleHomSubspace).
        |Hom(K,A,N1,N2)| is a subset of |Hom(K,N1,N2)|.
        f < Hom(K,A,N1,N2).     
        f < Hom(K,N1,N2).
        f is linear over K from N1 to N2.
        g is from |M| to |N1|.
        g(x) < N1.
        Therefore the thesis (by Homomorphism).
       qed.
       a @{N2} f(g(x)) = a @{N2} (f*g)(x).
       Let us show that a @{N2} (f*g)(x) = (a @{Hom(K,A,M,N2)} (f*g))(x).
        K is a field.
        M,N2 are modules over A over K.
        a < K.
        f*g < Hom(K,A,M,N2).
        x < M.
        Therefore the thesis (by ModuleHomSmul).
       qed.
      qed.
      Therefore the thesis (by MapExt).
     qed.
     a @{Hom(K,A,M,N2)} (f*g) = a @@{Hom(K,A,M,N2)} (f*g).
    qed.
   qed.
   K is a field.
   K is an algebra over K.
   F(N1),F(N2) are modules over K over K.
   Let us show that F(f) < Hom(K,K,F(N1),F(N2)).
    |Hom(K,K,F(N1),F(N2))| is the set of modulehoms over K over K from F(N1) to F(N2).
   qed.
   |Hom(K,K,F(N1),F(N2))| = Mod(K,K)(F(N1),F(N2)) (by ModMor).
  qed.
 
  Let us show that for all N < Mod(K,A) : F(1{N,Mod(K,A)}) = 1{F(N),Mod(K,K)}.
   Let N < Mod(K,A).
   K is a field.
   A is an algebra over K.
   N is a module over A over K.
   M is a module over A over K.
   F(N) = Hom(K,A,M,N).
   1{F(N),Mod(K,K)} = id{|Hom(K,A,M,N)|}.
   F(1{N,Mod(K,A)}) = Hom(K,A,M,id{|N|}).
   Let us show that Hom(K,A,M,id{|N|}) = id{|Hom(K,A,M,N)|}.
    id{|N|} = 1{N,Mod(K,A)}.
    id{|N|} < Hom(K,A,N,N).
    id{|N|} is a modulehom over A over K from N to N.
    Hom(K,A,M,id{|N|}) is a map.
    id{|Hom(K,A,M,N)|} is a map.
    Dmn(Hom(K,A,M,id{|N|})) = |Hom(K,A,M,N)|.
    Dmn(id{|Hom(K,A,M,N)|}) = |Hom(K,A,M,N)|.
    Let us show that for all g < Hom(K,A,M,N) : Hom(K,A,M,id{|N|})(g) = id{|Hom(K,A,M,N)|}(g).
     Let g < Hom(K,A,M,N).
     Hom(K,A,M,id{|N|})(g) = id{|N|}*g (by HomFun).
     Let us show that id{|N|}*g = g.
      g is a modulehom over A over K from M to N.
      g is from |M| to |N|.
      id{|N|} and g are composable.
      id{|N|}*g = g.
     qed.
     g = id{|Hom(K,A,M,N)|}(g).
    qed.
    Therefore the thesis (by MapExt).
   qed.
   Therefore F(1{N,Mod(K,A)}) = id{|Hom(K,A,M,N)|} (by MapExt).
  Qed.
 
  Let us show that for all N1,N2,N3 < Mod(K,A) and all f << Mod(K,A)(N1,N2)
  and all g << Mod(K,A)(N2,N3) : F(g*f) = F(g)*F(f).
   Let N1,N2,N3 < Mod(K,A). Let f << Mod(K,A)(N1,N2). Let g << Mod(K,A)(N2,N3).
   K is a field.
   A is an algebra over K.
   Ob{Mod(K,A)} is the set of modules over A over K (by ModOb).
   N1,N2,N3 are modules over A over K.
   g*f << Mod(K,A)(N1,N3) (by Category).
   F(g*f) << Mod(K,K)(F(N1),F(N3)) (by Functor).
   K is a field.
   F(N1),F(N3) are modules over K over K.
   F(g*f) < Hom(K,K,F(N1),F(N3)) (by ModMor).
   Let us show that F(g*f) is a modulehom over K over K from F(N1) to F(N3).
    |Hom(K,K,F(N1),F(N3))| is the set of modulehoms over K over K from F(N1) to F(N3).
   qed.
   F(g*f) is a map.
   Dmn(F(g*f)) = |F(N1)|.
   Let us show that F(g)*F(f) << Mod(K,K)(F(N1),F(N3)).
    Mod(K,K) is a category.
    F(N1),F(N2),F(N3) < Mod(K,K).
    F(f) << Mod(K,K)(F(N1),F(N2)).
    F(g) << Mod(K,K)(F(N2),F(N3)).
    Therefore the thesis (by Category).
   qed.
   F(g)*F(f) < Hom(K,K,F(N1),F(N3)) (by ModMor).
   F(g)*F(f) is a modulehom over K over K from F(N1) to F(N3).
   F(g)*F(f) is a map.
   Dmn(F(g)*F(f)) = |F(N1)|.
   Let us show that for all h < F(N1) : F(g*f)(h) = (F(g)*F(f))(h).
    Let h < F(N1).
    F(N1) = Hom(K,A,M,N1).
    h < Hom(K,A,M,N1).
    Let us show that F(g*f)(h) = (g*f)*h.
     N1,N3 are modules over A over K.
     g*f << Mod(K,A)(N1,N3).
     g*f < Hom(K,A,N1,N3) (by ModMor).
     For all i < Hom(K,A,M,N1) : Hom(K,A,M,g*f)(i) = (g*f)*i (by HomFun).
    qed.
    Let us show that (F(g)*F(f))(h) = g*(f*h).
     Let us show that F(f) is a map.
      F(f) << Mod(K,K)(F(N1),F(N2)).
      F(f) < Hom(K,K,F(N1),F(N2)) (by ModMor).
      F(f) is a modulehom over K over K from F(N1) to F(N2).
     qed.
     Let us show that F(g) is a map.
      F(g) << Mod(K,K)(F(N2),F(N3)).
      F(g) < Hom(K,K,F(N2),F(N3)) (by ModMor).
      F(g) is a modulehom over K over K from F(N2) to F(N3).
     qed.
     (F(g)*F(f))(h) = F(g)(F(f)(h)).
     N1,N2 are modules over A over K.
     f < Hom(K,A,N1,N2) (by ModMor).
     For all i < Hom(K,A,M,N1) : Hom(K,A,M,f)(i) = f*i (by HomFun).
     F(f)(h) = f*h.
     f*h < Hom(K,A,M,N2) (by ModuleHomComp).
     N2,N3 are modules over A over K.
     g < Hom(K,A,N2,N3) (by ModMor).
     For all i < Hom(K,A,M,N2) : Hom(K,A,M,g)(i) = g*i (by HomFun).
     F(g)(f*h) = g*(f*h).
    qed.
    Let us show that (g*f)*h = g*(f*h).   
     h is a modulehom over A over K from M to N1.
     f < Hom(K,A,N1,N2) (by ModMor).
     f is a modulehom over A over K from N1 to N2.
      g < Hom(K,A,N2,N3) (by ModMor).
     g is a modulehom over A over K from N2 to N3.
     h : |M|  -> |N1|.
     f : |N1| -> |N2|.
     g : |N2| -> |N3|.
    qed.
   qed.
  qed.
 qed.
Qed.


Axiom HomIsContraFunctor. Let A be an algebra over K. Let N be a module over A over K.
 Hom(K,A,-,N) is a contravariant functor from Mod(K,A) to Mod(K,K).
# The proof is very similar.

# Up to here (including all necessary proofs): 5:56 minutes.

##########

Let K denote a field.

Theorem. Let A be an algebra over K. Let M1,M2 be modules over A over K. Let f be a modulehom over A
 over K from M1 to M2. Hom(K,A,f,-) is a natural transformation
 from Hom(K,A,M2,-) to Hom(K,A,M1,-) over Mod(K,A) to Mod(K,K).
Proof.
 Mod(K,A) is a category.
 K is an algebra over K.
 Mod(K,K) is a category.
 Take F = Hom(K,A,M2,-).
 Take G = Hom(K,A,M1,-).
 F is a functor from Mod(K,A) to Mod(K,K).
 G is a functor from Mod(K,A) to Mod(K,K).
 Take n = Hom(K,A,f,-).
 Let us show that n is a natural transformation from F to G over Mod(K,A) to Mod(K,K).
  Let us show that for all N < Mod(K,A) : n(N) << Mod(K,K)(F(N),G(N)).
   Let N < Mod(K,A).
   N is a module over A over K.
   n(N) = Hom(K,A,-,N)(f).
   F(N) = Hom(K,A,-,N)(M2).
   G(N) = Hom(K,A,-,N)(M1).
   Hom(K,A,-,N) is a contravariant functor from Mod(K,A) to Mod(K,K).
   Let us show that f << Mod(K,A)(M1,M2).
    |Hom(K,A,M1,M2)| is the set of modulehoms over A over K from M1 to M2.
    f < Hom(K,A,M1,M2).
   qed.
   Take H = Hom(K,A,-,N).
   H is a contravariant functor from Mod(K,A) to Mod(K,K).
   M1,M2 < Mod(K,A).
   Therefore H(f) << Mod(K,K)(H(M2),H(M1)) (by ContraFunctor).
  qed.
  Let us show that for all N1,N2 < Mod(K,A) and all h << Mod(K,A)(N1,N2) : G(h)*n(N1) = n(N2)*F(h).
   Let N1,N2 < Mod(K,A).
   Let h << Mod(K,A)(N1,N2).
   N1,N2 are modules over A over K.
   G(h)*n(N1) = Hom(K,A,M1,h)*Hom(K,A,f,N1).
   n(N2)*F(h) = Hom(K,A,f,N2)*Hom(K,A,M2,h).  
   f < Hom(K,A,M1,M2).
   h < Hom(K,A,N1,N2) (by ModMor).
   Hom(K,A,M1,h),Hom(K,A,f,N1) are maps (by HomFun, ContraHomFun).
   Hom(K,A,M1,h)*Hom(K,A,f,N1) is a map.
   Dmn(Hom(K,A,f,N1)) = |Hom(K,A,M2,N1)| (by ContraHomFun).
    Dmn(Hom(K,A,M1,h)*Hom(K,A,f,N1)) = |Hom(K,A,M2,N1)|.
   Hom(K,A,f,N2),Hom(K,A,M2,h) are maps (by HomFun, ContraHomFun).
   Hom(K,A,f,N2)*Hom(K,A,M2,h) is a map.
   Dmn(Hom(K,A,M2,h)) = |Hom(K,A,M2,N1)| (by HomFun).
   Dmn(Hom(K,A,f,N2)*Hom(K,A,M2,h)) = |Hom(K,A,M2,N1)|.
   Let us show that for all g < Hom(K,A,M2,N1) : (Hom(K,A,M1,h)*Hom(K,A,f,N1))(g) = h*(g*f).
    Let g < Hom(K,A,M2,N1).
    (Hom(K,A,M1,h)*Hom(K,A,f,N1))(g) = Hom(K,A,M1,h)(Hom(K,A,f,N1)(g)).
    Hom(K,A,f,N1)(g) = g*f (by ContraHomFun).
    g*f < Hom(K,A,M1,N1) (by ModuleHomComp).
    Hom(K,A,M1,h)(g*f) = h*(g*f) (by HomFun).
   qed.
   Let us show that for all g < Hom(K,A,M2,N1) : (Hom(K,A,f,N2)*Hom(K,A,M2,h))(g) = (h*g)*f.
    Let g < Hom(K,A,M2,N1).
    (Hom(K,A,f,N2)*Hom(K,A,M2,h))(g) = Hom(K,A,f,N2)(Hom(K,A,M2,h)(g)).
    Hom(K,A,M2,h)(g) = h*g (by HomFun).
    Let us show that h*g < Hom(K,A,M2,N2).
     K is a field.
     A is an algebra over K.
     N1,N2,M2 are modules over A over K.
     h < Hom(K,A,N1,N2).
     g < Hom(K,A,M2,N1).
     Therefore the thesis (by ModuleHomComp).
    qed.
    Hom(K,A,f,N2)(h*g) = (h*g)*f (by ContraHomFun).  
   qed.
   Let us show that for all g < Hom(K,A,M2,N1) : h*(g*f) = (h*g)*f.
    Let g < Hom(K,A,M2,N1).
    K is a field.
    f is a modulehom over A over K from M1 to M2.
    f : |M1| -> |M2|.
    g is a modulehom over A over K from M2 to N1.
    g : |M2| -> |N1|.
    h is a modulehom over A over K from N1 to N2.
    h : |N1| -> |N2|.
    Therefore the thesis (by ThreeComp).
   qed.
  qed.
 qed.
Qed.

Axiom. Let A be an algebra over K. Let N1,N2 be modules over A over K. Let f be a modulehom over A
 over K from N1 to N2. Hom(K,A,-,f) is a contravariant natural transformation
 from Hom(K,A,-,N1) to Hom(K,A,-,N2) over Mod(K,A) to Mod(K,K).
# The proof is similar.

##########

Let K denote a field.

# sequence = short sequence

Signature. Let a,b,c,d,e be objects. (a,b,c,d,e) is an object.
Signature. Let K,A be objects. A sequence over A over K is a notion.
Signature. Let K,A be objects. A left exact sequence over A over K is a notion.

Axiom Sequence. Let A,X,Y,Z,f,g be objects. (X,f,Y,g,Z) is a sequence over A over K iff
     (A is an algebra over K)
 and (X,Y,Z < Mod(K,A))
 and (f << Mod(K,A)(X,Y))
 and (g << Mod(K,A)(Y,Z)).

Signature. Let f be an object. Im(f) is an object.
Axiom Image. Let V,W be vector spaces over K. Let f < Hom(K,V,W).
 |Im(f)| is a set and |Im(f)| = {f(v) | v < V}.
 
Axiom LeftExactSequence. Let K,A,X,Y,Z,f,g be objects.
 (X,f,Y,g,Z) is a left exact sequence over A over K iff
     ((X,f,Y,g,Z) is a sequence over A over K)
 and (f is injective)
 and (|Im(f)| = |Ker(g)|).


Definition PreserveLeftExactness. Let A,B,F be objects.
 F preserves left exactness from A to B over K iff
 (for all X,Y,Z < Mod(K,A) and all f << Mod(K,A)(X,Y) and all g << Mod(K,A)(Y,Z) :
 (((X,f,Y,g,Z) is a left exact sequence over A over K)
  => ((F(X),F(f),F(Y),F(g),F(Z)) is a left exact sequence over B over K))).

Signature. A left exact functor is a notion.

Axiom LeftExactFunctor. Let A,B be algebras over K. Let F be a functor from Mod(K,A) to Mod(K,B).
 (F is a left exact functor) iff
 (F preserves left exactness from A to B over K).

##########

# 1.8 quivers

Definition. A quiver is an object Q such that
     (Q(0) is a set)
 and (Q(1) is a set)
 and (Q(st) is a map from Q(1) to Q(0))
 and (Q(tl) is a map from Q(1) to Q(0)).

Let Q denote a quiver.

Definition. A vertex of Q is a member of Q(0).
Definition. An arrow of Q is a member of Q(1).

Definition. Let a,i be objects. a starts in i in Q iff
 a is an arrow of Q and i is a vertex of Q and Q(st)(a) = i.

Definition. Let a,i be objects. a ends in i in Q iff
 a is an arrow of Q and i is a vertex of Q and Q(tl)(a) = i.

Definition. Let a,i,j be objects. a is from i to j in Q iff a starts in i in Q and ends in j in Q.

##########

Let K denote a field.

# The following two statements are proven in 14_endormophism.ftl resp. 15_automorphism.ftl
# but reading both files entirely interferes extremely with the performance of checking this file.

Axiom. Let U,V,W be vector spaces over K. Let f,g be maps.
 Let g be linear over K from U to V. Let f be linear over K from V to W.
 Then f*g is linear over K from U to W.

Axiom InverseHom. Let V,W be vector spaces over K. Let f < Hom(K,V,W).
 Let f be bijective from |V| to |W|. Then f^(-1) < Hom(K,W,V).

Lemma. Let A be an algebra over K. Let M be a module over A over K.
 Let F be an object such that F = Hom(K,A,M,-).
 Then F preserves left exactness from A to K over K.
Proof.
 F is a functor from Mod(K,A) to Mod(K,K).
 Let us show that for all X,Y,Z < Mod(K,A) and all f << Mod(K,A)(X,Y) and all g << Mod(K,A)(Y,Z) :
 (((X,f,Y,g,Z) is a left exact sequence over A over K)
 => ((F(X),F(f),F(Y),F(g),F(Z)) is a left exact sequence over K over K)).
  Let X,Y,Z < Mod(K,A). Let f << Mod(K,A)(X,Y). Let g << Mod(K,A)(Y,Z).
  Assume (X,f,Y,g,Z) is a left exact sequence over A over K.
  K is a field.
  K is an algebra over K.
  Let us show that (F(X),F(f),F(Y),F(g),F(Z)) is a left exact sequence over K over K.
   F(X),F(Y),F(Z) < Mod(K,K) (by Functor).
   F(f) << Mod(K,K)(F(X),F(Y)) (by Functor).
   F(g) << Mod(K,K)(F(Y),F(Z)) (by Functor).
   Therefore (F(X),F(f),F(Y),F(g),F(Z)) is a sequence over K over K (by Sequence).
 
   Let us show that F(f) is injective.
    F(f) < Hom(K,K,F(X),F(Y)) (by ModMor).
    K is a field.
    F(f) is a modulehom over K over K from F(X) to F(Y).
    F(f) is a map.
    Dmn(F(f)) = |F(X)|.
    Let us show that for all h,k < F(X) : (F(f)(h) = F(f)(k) => h = k).
     Let h,k < F(X).
     Assume F(f)(h) = F(f)(k).
     F(X) = Hom(K,A,M,X).
     h,k are modulehoms over A over K from M to X.
     Let us show that h = k.
      h,k are maps.
      Dmn(h) = |M|.
      Dmn(k) = |M|.
      Let us show that for all m < M : h(m) = k(m).
       Let m < M.
       f < Hom(K,A,X,Y) (by ModMor).
       Let us show that Hom(K,A,M,f)(h) = f*h.
        K is a field.
        X,Y,M are modules over A over K.
        f < Hom(K,A,X,Y).
        h < Hom(K,A,M,X).
        Therefore the thesis (by HomFun).
       qed.
       F(f)(h) = f*h.
       Let us show that F(f)(k) = f*k.
        F(f)(k) = Hom(K,A,M,f)(k).
        k < Hom(K,A,M,X).
        K is a field.
        X,Y,M are modules over A over K.
        Therefore the thesis (by HomFun).
       qed.
       f*h = f*k.
       K is a field.
       f is a modulehom over A over K from X to Y.
       f,h,k are maps.
       f(h(m)) = (f*h)(m) = (f*k)(m) = f(k(m)).
       h(m) < X.
       k(m) < X.
       Dmn(f) = |X|.
       f is injective.
       Therefore h(m) = k(m).
      qed.
     qed.
    qed.
   qed.
 
   K is a field.
   Let us show that F(X),F(Y),F(Z) are vector spaces over K.
    F(X),F(Y),F(Z) < Mod(K,K).
    F(X),F(Y),F(Z) are modules over K over K.
    F(X),F(Y),F(Z) are vector spaces over K.     
   qed.
   Let us show that F(f) < Hom(K,F(X),F(Y)).
    K is an algebra over K.
    F(X),F(Y) are modules over K over K.
    Hom(K,K,F(X),F(Y)) is a subspace of Hom(K,F(X),F(Y)) over K (by ModuleHomSubspace).
    |Hom(K,K,F(X),F(Y))| is a subset of |Hom(K,F(X),F(Y))|.
    F(f) < Hom(K,K,F(X),F(Y)) (by ModMor).
   qed.
   Let us show that F(g) < Hom(K,F(Y),F(Z)).
    F(g) < Hom(K,K,F(Y),F(Z)) (by ModMor).
    F(Y),F(Z) are modules over K over K.
    Hom(K,K,F(Y),F(Z)) is a subspace of Hom(K,F(Y),F(Z)) over K (by ModuleHomSubspace).
    |Hom(K,K,F(Y),F(Z))| is a subset of |Hom(K,F(Y),F(Z))|.
   qed.
 
   Let us show that for all h < Im(F(f)) : h < Ker(F(g)).
    Let h < Im(F(f)).
    F(X),F(Y) are vector spaces over K.
    |Im(F(f))| is a set and |Im(F(f))| = {F(f)(k) | k < F(X)} (by Image).
    Take k < F(X) such that F(f)(k) = h. 
    f < Hom(K,A,X,Y) (by ModMor).
    Let us show that h = f*k.
     F(f)(k) = Hom(K,A,M,f)(k).
     k < Hom(K,A,M,X).
     K is a field.
     X,Y,M are modules over A over K.
     Therefore Hom(K,A,M,f)(k) = f*k (by HomFun).
    qed.
    F(Y),F(Z) are vector spaces over K.
    |Ker(F(g))| is a set and |Ker(F(g))| = {h | h < F(Y) and F(g)(h) = 0{F(Z)}} (by Kernel).
    Let us show that h < F(Y).
     F(f) is linear over K from F(X) to F(Y).
     k < F(X).
     Therefore F(f)(k) < F(Y).
    qed.
    Let us show that F(g)(h) = 0{F(Z)}.
     Let us show that F(g)(h) is a map from |M| to |Z|.
      F(g) is linear over K from F(Y) to F(Z).
      F(g)(h) < F(Z).
      F(g)(h) < Hom(K,A,M,Z).
      F(g)(h) is a modulehom over A over K from M to Z.
     qed.
     Dmn(F(g)(h)) = |M|.
     0{F(Z)} is a map.
     Dmn(0{F(Z)}) = |M|.
     Let us show that for all m < M : F(g)(h)(m) = 0{F(Z)}(m).
      Let m < M.
      g < Hom(K,A,Y,Z) (by ModMor).
      Let us show that F(g)(h) = g*(f*k).
       F(g)(h) = Hom(K,A,M,g)(h).
       h < Hom(K,A,M,Y).
       K is a field.
       Y,Z,M are modules over A over K.
       Therefore Hom(K,A,M,g)(h) = g*h (by HomFun).
      qed.
      g,f,k,f*k are maps.
      (F(g)(h))(m) = (g*(f*k))(m) = g((f*k)(m)) = g(f(k(m))).
      k is a modulehom over A over K from M to X.
      k(m) < X.
      X,Y,Z are vector spaces over K.
      Let us show that f < Hom(K,X,Y).
       A is an algebra over K.
       X,Y are modules over A over K.
       f < Hom(K,A,X,Y).
       Therefore the thesis (by ModuleHomSubspace).
      qed.
      |Im(f)| is a set and |Im(f)| = {f(x) | x < X} (by Image).
      f(k(m)) < Im(f).
      |Im(f)| = |Ker(g)|.
      f(k(m)) < Ker(g).
      Let us show that g < Hom(K,Y,Z).
       A is an algebra over K.
       Y,Z are modules over A over K.
       g < Hom(K,A,Y,Z).
       Therefore the thesis (by ModuleHomSubspace).
      qed.
      |Ker(g)| is a set and |Ker(g)| = {y | y < Y and g(y) = 0{Z}} (by Kernel).
      g(f(k(m))) = 0{Z}.
      0{Z} = 0{Hom(K,A,M,Z)}(m) = 0{F(Z)}(m).
     qed.
     Therefore the thesis (by MapExt).
    qed.
    Therefore h < Ker(F(g)).
   qed.
   
   Let us show that for all h < Ker(F(g)) : h < Im(F(f)).
    K is a field.
    Let h < Ker(F(g)).
    Let us show that F(g)(h) = 0{F(Z)}.
     F(Y),F(Z) are vector spaces over K.
     F(g) < Hom(K,F(Y),F(Z)).
     |Ker(F(g))| is a set and |Ker(F(g))| = {h | h < F(Y) and F(g)(h) = 0{F(Z)}} (by Kernel).
     h < F(Y).
    qed.
    Let us show that F(g)(h) = g*h.
     Y,Z,M are modules over A over K.
     g < Hom(K,A,Y,Z) (by ModMor).
     h < F(Y).
     h < Hom(K,A,M,Y).
     K is a field.
     Therefore Hom(K,A,M,g)(h) = g*h (by HomFun).
     F(g)(h) = Hom(K,A,M,g)(h).
    qed.
    g*h = 0{F(Z)}.    
    Let us show that Ker(g) is a subspace of Y over K.
     Y,Z are vector spaces over K.
     Let us show that g < Hom(K,Y,Z).
      Y,Z are modules over A over K.
      Hom(K,A,Y,Z) is a subspace of Hom(K,Y,Z) over K (by ModuleHomSubspace).
      |Hom(K,A,Y,Z)| is a subset of |Hom(K,Y,Z)|.
      g < Hom(K,A,Y,Z) (by ModMor).
     qed.
     Therefore the thesis (by KernelSubspace).
    qed.
    Ker(g) is a vector space over K.

    Let us show that h < Hom(K,M,Ker(g)).
     Let us show that h is a map from |M| to |Ker(g)|.
      h < F(Y).
      h < Hom(K,A,M,Y).
      h is a map from |M| to |Y|.
      Dmn(h) = |M|.
      Let us show that for all m < M : h(m) < Ker(g).
       Let m < M.
       h(m) < Y.
       g < Hom(K,A,Y,Z) (by ModMor).
       g(h(m)) = (g*h)(m) = 0{F(Z)}(m) = 0{Hom(K,A,M,Z)}(m) = 0{Z}.
       K is a field.
       Y,Z are vector spaces over K.
       Let us show that g < Hom(K,Y,Z).
        Y,Z are modules over A over K.
        Hom(K,A,Y,Z) is a subspace of Hom(K,Y,Z) over K (by ModuleHomSubspace).
        |Hom(K,A,Y,Z)| is a subset of |Hom(K,Y,Z)|.
       qed.
       |Ker(g)| is a set and |Ker(g)| = {y | y < Y and g(y) = 0{Z}} (by Kernel).
      qed.
     qed.
     M,Y are vector spaces over K.
     Hom(K,A,M,Y) is a subspace of Hom(K,M,Y) over K.
     |Hom(K,A,M,Y)| is a subset of |Hom(K,M,Y)|.
     h < F(Y).
     h < Hom(K,A,M,Y).
     Therefore h < Hom(K,M,Y).
     K is a field.
     Let us show that h is linear over K from M to Ker(g).
      h is a map from |M| to |Ker(g)|.
      Let us show that for all u,v < M : h(u +{M} v) = h(u) +{Ker(g)} h(v).
        Let u,v < M.
        h is linear over K from M to Y.
        h(u +{M} v) = h(u) +{Y} h(v) (by Homomorphism).
        h(u),h(v) < Ker(g).
        h(u) +{Ker(g)} h(v) = h(u) +{Y} h(v) (by SubAdd).
       qed.
       Let us show that for all a < K and all v < M : h(a @{M} v) = a @{Ker(g)} h(v).
        Let a < K. Let v < M.
        h is linear over K from M to Y.
        h(a @{M} v) = a @{Y} h(v) (by Homomorphism).
        h(v) < Ker(g).
        a @{Ker(g)} h(v) = a @{Y} h(v) (by SubSmul).
       qed.
      qed.
    qed.

    Let us show that f < Hom(K,X,Ker(g)).
     Let us show that f < Hom(K,X,Y).
      K is a field.
      X,Y are modules over A over K.
      Hom(K,A,X,Y) is a subspace of Hom(K,X,Y) over K (by ModuleHomSubspace).
      |Hom(K,A,X,Y)| is a subset of |Hom(K,X,Y)|.
      f < Hom(K,A,X,Y) (by ModMor).
     qed.
     K is a field.
     f is linear over K from X to Y.
     f is a map from |X| to |Y|.
     Dmn(f) = |X|.
     Let us show that for all x < X : f(x) < Ker(g).
      Let x < X.
      |Im(f)| is a set and |Im(f)| = {f(v) | v < X} (by Image).
      f(x) < Im(f).
     qed.
     Let us show that f is linear over K from X to Ker(g).
      X,Ker(g) are vector spaces over K.
      f is from |X| to |Ker(g)|.
      Let us show that for all u,v < X : f(u +{X} v) = f(u) +{Ker(g)} f(v).
       Let u,v < X.
       f(u +{X} v) = f(u) +{Y} f(v) (by Homomorphism).
       f(u),f(v) < Ker(g).
       f(u) +{Ker(g)} f(v) = f(u) +{Y} f(v) (by SubAdd).
      qed.
      Let us show that for all a < K and all v < X : f(a @{X} v) = a @{Ker(g)} f(v).
       Let a < K. Let v < X.
       f(a @{X} v) = a @{Y} f(v) (by Homomorphism).
       f(v) < Ker(g).
       a @{Ker(g)} f(v) = a @{Y} f(v) (by SubSmul).
      qed.
     qed.
    qed.

    K is a field.
    X,Ker(g) are vector spaces over K.
    f is a map.
    Let us show that f is bijective from |X| to |Ker(g)|.
     f < Hom(K,X,Ker(g)).
     f is injective.
     Let us show that f is surjective onto |Ker(g)|.
      Let us show that f < Hom(K,X,Y).
       X,Y are modules over A over K.
       Hom(K,A,X,Y) is a subspace of Hom(K,X,Y) over K (by ModuleHomSubspace).
       |Hom(K,A,X,Y)| is a subset of |Hom(K,X,Y)|.
       f < Hom(K,A,X,Y) (by ModMor).
      qed.
      |Im(f)| is a set and |Im(f)| = {f(x) | x < X} (by Image).
      For all y < Im(f) there is an x < X such that f(x) = y.
      |Ker(g)| = |Im(f)|.
      Dmn(f) = |X|.
      For all y < Ker(g) there is an x << Dmn(f) such that f(x) = y.
     qed.
    qed.
    Therefore f^(-1) < Hom(K,Ker(g),X) (by InverseHom).

    Take k = f^(-1) * h.
    Let us show that k < F(X).
     F(X) = Hom(K,A,M,X).
     K is a field.
     Let us show that k is a modulehom over A over K from M to X.
      h is linear over K from M to Ker(g).
      f^(-1) is linear over K from Ker(g) to X.
      Therefore k is linear over K from M to X.
      k is a map from |M| to |X|.
      Let us show that for all u,v < M : k(u +{M} v) = k(u) +{X} k(v).
       Let u,v < M.
       k is linear over K from M to X.
       Therefore k(u +{M} v) = k(u) +{X} k(v) (by Homomorphism).  # 1.7 GB of RAM needed here
      qed.
      Let us show that for all a < A and all v < M : k(a @@{M} v) = a @@{X} k(v).
       Let a < A. Let v < M.
       k(a @@{M} v) = (f^(-1)*h)(a @@{M} v).
       f^(-1),h are maps.
       (f^(-1)*h)(a @@{M} v) = f^(-1)(h(a @@{M} v)).
       Let us show that h(a @@{M} v) = a @@{Y} h(v).
        h < F(Y).
        h < Hom(K,A,M,Y).
        K is a field.
        h is a modulehom over A over K from M to Y.
        a < A.
        v < M.
        Therefore the thesis (by ModuleHom).
       qed.
       Take y = h(v).
       f^(-1)(h(a @@{M} v)) = f^(-1)(a @@{Y} y).
       Let us show that f^(-1)(a @@{Y} y) = a @@{X} f^(-1)(y).
        y < Y.
        f(f^(-1)(a @@{Y} y)) = a @@{Y} y.
        Take x = f^(-1)(y).
        Let us show that f(a @@{X} x) = a @@{Y} f(x).
         f < Hom(K,A,X,Y) (by ModMor).
         K is a field.
         f is a modulehom over A over K from X to Y.
         a < A.
         x < X.
         Therefore the thesis (by Modulehom).
        qed.
        f(f^(-1)(a @@{Y} y)) = f(a @@{X} x).
        f is injective.
        f^(-1)(a @@{Y} y) = a @@{X} x.
       qed.
       f^(-1)(h(a @@{M} v)) = a @@{X} f^(-1)(h(v)).
       a @@{X} f^(-1)(h(v)) = a @@{X} k(v).
      qed.
     qed.
    qed.

    Let us show that h < Im(F(f)).
     h < F(Y).
     h < Hom(K,A,M,Y).
     h is a map from |M| to |Y|.
     id{|Ker(g)|} and h are composable.
     h = id{|Ker(g)|} * h.
     Let us show that id{|Ker(g)|} = f * f^(-1).
      id{|Ker(g)|} is a map.
      Dmn(id{|Ker(g)|}) = |Ker(g)|.
      f * f^(-1) is a map.
      Dmn(f * f^(-1)) = Dmn(f^(-1)) = |Ker(g)|.
      For all y < Ker(g) : id{|Ker(g)|}(y) = y = f(f^(-1)(y)) = (f * f^(-1))(y).
      Therefore the thesis (by MapExt).
     qed.
     h = (f * f^(-1)) * h = f * (f^(-1) * h) = f * k.
     Let us show that f * k = F(f)(k).
      K is a field.
      X,Y,M are modules over A over K.
      f < Hom(K,A,X,Y) (by ModMor).
      k < Hom(K,A,M,X).
      Therefore Hom(K,A,M,f)(k) = f*k (by HomFun).
      F(f)(k) = Hom(K,A,M,f)(k).
     qed.
     F(f)(k) = h.
     K is a field.
     F(X),F(Y) are modules over K over K.
     F(X),F(Y) are vector spaces over K.
     F(f) < Hom(K,F(X),F(Y)).
     |Im(F(f))| is a set and |Im(F(f))| = {F(f)(k1) | k1 < F(X)} (by Image).
     Therefore h < Im(F(f)).
    qed.
   qed.
   Therefore |Im(F(f))| = |Ker(F(g))|.
   Therefore the thesis (by LeftExactSequence).
  qed.
 qed.
 Therefore the thesis (by PreserveLeftExactness).
Qed.


Theorem. Let A be an algebra over K. Let M be a module over A over K.
 Hom(K,A,M,-) is a left exact functor.
Proof.
 Take F = Hom(K,A,M,-).
 Let us show that F is a left exact functor.
  K is a field.
  A,K are algebras over K.
  F is a functor from Mod(K,A) to Mod(K,K).
  F preserves left exactness from A to K over K.
 qed.
Qed.

##########

Let K denote a field.
Let Q denote a quiver.

Definition. A representation of Q over K is an object V such that
     (for all vertices i of Q : (V(i) is a vector space over K))
 and (for all arrows a of Q : V(a) < Hom(K,V(Q(st)(a)),V(Q(tl)(a)))).

##########

Let K denote a field.
Let M,N denote sets.

Signature. Let K,N be objects. K^^N is an object.
Signature. 2 is an object.
Signature. 3 is an object.
Signature. 4 is an object.
Signature. Let n be an object. upto(n) is a set.

Axiom. upto(1) = {1}.
Axiom. upto(2) = {1,2}.
Axiom. upto(3) = {1,2,3}.
Axiom. upto(4) = {1,2,3,4}.
Let K^n stand for K^^upto(n).

Axiom KNSet. |K^^N| is the set of maps f such that f is from N to |K|.
Axiom KNZero. 0{K^^N} is a map such that Dmn(0{K^^N}) = N and for all n << N : 0{K^^N}(n) = 0{K}.
Axiom KNAdd. Let v,w < K^^N. v +{K^^N} w is a map u such that Dmn(u) = N
 and for all n << N : u(n) = v(n) +{K} w(n).
Axiom KNNeg. Let v < K^^N. ~{K^^N} v is a map u such that Dmn(u) = N
 and for all n << N : u(n) = ~{K} v(n).
Axiom KNSmul. Let a < K and v < K^^N. a @{K^^N} v is a map u such that Dmn(u) = N
 and for all n << N : u(n) = a *{K} v(n).

Theorem. K^^N is a vector space over K.
Proof.
 Take V = K^^N.
 Let us show that V is a vector space over K.
  Let us show that K^^N is an abelian group.
   |K^^N| is a set.
   Let us show that 0{K^^N} < K^^N.
    Dmn(0{K^^N}) = N.
    For all n << N : 0{K^^N}(n) = 0{K}.
   qed.
   Let us show that for all v,w < K^^N : v +{K^^N} w < K^^N.
    Let v,w < K^^N.
    For all n << N : (v +{K^^N} w)(n) = v(n) +{K} w(n) < K.
   qed.
   Let us show that for all v < K^^N : ~{K^^N} v < K^^N.
    Let v < K^^N.
    For all n << N : (~{K^^N} v)(n) = ~{K} v(n) < K.
   qed.
   Let us show that for all v < K^^N : v +{K^^N} 0{K^^N} = v.
    Let v < K^^N.
    v is a map.
    v +{K^^N} 0{K^^N} is a map.
    Dmn(v) = N.
    Dmn(v +{K^^N} 0{K^^N}) = N.
    For all n << N : (v +{K^^N} 0{K^^N})(n) = v(n) +{K} 0{K^^N}(n) = v(n) +{K} 0{K} = v(n).
    Thus v +{K^^N} 0{K^^N} = v (by MapExt).
   qed.
   Let us show that for all v < K^^N : v -{K^^N} v = 0{K^^N}.
    Let v < K^^N.
    For all n << N : (v -{K^^N} v)(n) = v(n) +{K} (~{K^^N} v)(n) = v(n) -{K} v(n) = 0{K^^N}(n).
   qed.
   Let us show that for all u,v,w < K^^N : u +{K^^N} (v +{K^^N} w) = (u +{K^^N} v) +{K^^N} w.
    Let u,v,w < K^^N.
    u +{K^^N} (v +{K^^N} w) is a map.
    (u +{K^^N} v) +{K^^N} w is a map.
    Dmn(u +{K^^N} (v +{K^^N} w)) = N.
    Dmn((u +{K^^N} v) +{K^^N} w) = N.
    For all n << N : (u +{K^^N} (v +{K^^N} w))(n) = u(n) +{K} (v(n) +{K} w(n))
                     = (u(n) +{K} v(n)) +{K} w(n) = ((u +{K^^N} v) +{K^^N} w)(n).
    Thus u +{K^^N} (v +{K^^N} w) = (u +{K^^N} v) +{K^^N} w (by MapExt).
   qed.
   Let us show that for all v,w < K^^N : v +{K^^N} w = w +{K^^N} v.
    Let v,w < K^^N.
    For all n << N : (v +{K^^N} w)(n) = v(n) +{K} w(n) = w(n) +{K} v(n) = (w +{K^^N} v)(n).
   qed.
  qed.
  Let us show that K^^N is a vector space over K.
   Let us show that for all a < K and all v < K^^N : a @{K^^N} v < K^^N.
    Let a < K. Let v < K^^N.
    For all n << N : (a @{K^^N} v)(n) = a *{K} v(n) < K.
   qed.
   Let us show that for all v < K^^N : 1{K} @{K^^N} v = v.
    Let v < K ^^N.
    1{K} @{K^^N} v is a map.
    Dmn(1{K} @{K^^N} v) = N.
    v is a map.
    Dmn(v) = N.
    For all n << N : (1{K} @{K^^N} v)(n) = 1{K} *{K} v(n) = v(n).
    Thus 1{K} @{K^^N} v = v (by MapExt).
   qed.
   Let us show that for all a,b < K and all v < K^^N : (a *{K} b) @{K^^N} v = a @{K^^N} (b @{K^^N} v).
    Let a,b < K. Let v < K^^N.
    (a *{K} b) @{K^^N} v is a map.
    Dmn((a *{K} b) @{K^^N} v) = N.
    a @{K^^N} (b @{K^^N} v) is a map.
    Dmn(a @{K^^N} (b @{K^^N} v)) = N.
    For all n << N : ((a *{K} b) @{K^^N} v)(n) = (a *{K} b) *{K} v(n)
                     = a *{K} (b *{K} v(n)) = a *{K} (b @{K^^N} v)(n) = (a @{K^^N} (b @{K^^N} v))(n).
    Therefore the thesis (by MapExt).
   qed.
   Let us show that for all a,b < K and all v < K^^N :
   (a +{K} b) @{K^^N} v = (a @{K^^N} v) +{K^^N} (b @{K^^N} v).
    Let a,b < K. Let v < K^^N.
    (a +{K} b) @{K^^N} v is a map.
    Dmn((a +{K} b) @{K^^N} v) = N.
    (a @{K^^N} v) +{K^^N} (b @{K^^N} v) is a map.
    Dmn((a @{K^^N} v) +{K^^N} (b @{K^^N} v)) = N.
    Let us show that for all n << N :
    ((a +{K} b) @{K^^N} v)(n) = ((a @{K^^N} v) +{K^^N} (b @{K^^N} v))(n).
     Let n << N.
     ((a +{K} b) @{K^^N} v)(n) = (a +{K} b) *{K} v(n).
     Let us show that (a +{K} b) *{K} v(n) = (a *{K} v(n)) +{K} (b *{K} v(n)).
      For all c,d,e < K : (c +{K} d) *{K} e = (c *{K} e) +{K} (d *{K} e).
     qed.
     (a *{K} v(n)) +{K} (b *{K} v(n)) = (a @{K^^N} v)(n) +{K} (b @{K^^N} v)(n).
     (a @{K^^N} v)(n) +{K} (b @{K^^N} v)(n) = ((a @{K^^N} v) +{K^^N} (b @{K^^N} v))(n).
    qed.
   qed.
   Let us show that for all a < K and all v,w < K^^N :
   a @{K^^N} (v +{K^^N} w) = (a @{K^^N} v) +{K^^N} (a @{K^^N} w).
    Let a < K. Let v,w < K^^N.
    a @{K^^N} (v +{K^^N} w) is a map.
    Dmn(a @{K^^N} (v +{K^^N} w)) = N.
    (a @{K^^N} v) +{K^^N} (a @{K^^N} w) is a map.
    Dmn((a @{K^^N} v) +{K^^N} (a @{K^^N} w)) = N.
    Let us show that for all n << N :
    (a @{K^^N} (v +{K^^N} w))(n) = ((a @{K^^N} v) +{K^^N} (a @{K^^N} w))(n).
     Let n << N.
     For all c,d,e < K : c *{K} (d +{K} e) = (c *{K} d) +{K} (c *{K} e).
     a,v(n),w(n) < K.
     (a @{K^^N} (v +{K^^N} w))(n) = a *{K} (v(n) +{K} w(n)).
     a *{K} (v(n) +{K} w(n)) = (a *{K} v(n)) +{K} (a *{K} w(n)).
     (a *{K} v(n)) +{K} (a *{K} w(n)) = (a @{K^^N} v)(n) +{K} (a @{K^^N} w)(n).
     Let us show that (a @{K^^N} v)(n) +{K} (a @{K^^N} w)(n)
                      = ((a @{K^^N} v) +{K^^N} (a @{K^^N} w))(n).
      For all u1,u2 < K^^N : u1(n) +{K} u2(n) = (u1 +{K^^N} u2)(n).
      a @{K^^N} v < K^^N.
      a @{K^^N} w < K^^N.
     qed.
    qed.
   qed.
  qed.
 qed.
Qed.

Signature. Let K,N,i be objects. std(K,N,i) is an object.
Signature. Let K,M,N,i,j be objects. std(K,M,N,i,j) is an object.
Let vec(K,n,i) stand for std(K,upto(n),i).
Let mat(K,m,n,i,j) stand for std(K,upto(m),upto(n),i,j).
Let Mat(K,m,n) stand for Hom(K,K^n,K^m).

Axiom. Let i << N. std(K,N,i) is a map v such that Dmn(v) = N
 and v(i) = 1{K} and for all j << N\{i} : v(j) = 0{K}.

Lemma. Let i << N. std(K,N,i) < K^^N.
Proof.
 For all j << N : std(K,N,i)(j) < K.
Qed.

Axiom. Let i << M. Let j << N. std(K,M,N,i,j) is a map A such that Dmn(A) = |K^^N|
 and for all v < K^^N : A(v) = v(j) @{K^^M} std(K,M,i).

Theorem. Let i << M. Let j << N. std(K,M,N,i,j) is linear over K from K^^N to K^^M.
Proof.
 Take A = std(K,M,N,i,j).
 Let us show that A is linear over K from K^^N to K^^M.
  K^^N and K^^M are vector spaces over K.
  Let us show that A is a map from |K^^N| to |K^^M|.
   std(K,M,i) < K^^M.
   For all v < K^^N : v(j) < K.
   K^^M is a vector space over K.
   For all v < K^^N : A(v) = v(j) @{K^^M} std(K,M,i) < K^^M.
  qed.
  Let us show that for all u,v < K^^N : A(u +{K^^N} v) = A(u) +{K^^M} A(v).
   Let u,v < K^^N.
   K^^N is a vector space over K.
   K^^M is a vector space over K.
   u +{K^^N} v < K^^N (by AbelianGroup).
   u(j), v(j) < K.
   std(K,M,i) < K^^M.
   A(u +{K^^N} v) = (u +{K^^N} v)(j) @{K^^M} std(K,M,i) = (u(j) +{K} v(j)) @{K^^M} std(K,M,i).
   (u(j) +{K} v(j)) @{K^^M} std(K,M,i) = (u(j) @{K^^M} std(K,M,i)) +{K^^M} (v(j) @{K^^M} std(K,M,i))
   (by VectorSpace).
   u(j) @{K^^M} std(K,M,i) = A(u).
   v(j) @{K^^M} std(K,M,i) = A(v).
  qed.
  Let us show that for all a < K and all v < K^^N : A(a @{K^^N} v) = a @{K^^M} A(v).
   Let a < K. Let v < K^^N.
   K^^N is a vector space over K.
   K^^M is a vector space over K.
   a @{K^^N} v < K^^N (by VectorSpace).
   v(j) < K.
   std(K,M,i) < K^^M.
   A(a @{K^^N} v) = (a @{K^^N} v)(j) @{K^^M} std(K,M,i) = (a *{K} v(j)) @{K^^M} std(K,M,i).
   (a *{K} v(j)) @{K^^M} std(K,M,i) = a @{K^^M} (v(j) @{K^^M} std(K,M,i)) (by VectorSpace).
   v(j) @{K^^M} std(K,M,i) = A(v).
  qed.
 qed.
Qed.

Let [[a,b],[c,d]]{K} stand for
  (a @{Mat(K,2,2)} mat(K,2,2,1,1)) +{Mat(K,2,2)} ((b @{Mat(K,2,2)} mat(K,2,2,1,2)) +{Mat(K,2,2)}
 ((c @{Mat(K,2,2)} mat(K,2,2,2,1)) +{Mat(K,2,2)} ((d @{Mat(K,2,2)} mat(K,2,2,2,2))))).

Lemma 2x2Matrix. Let a,b,c,d < K. [[a,b],[c,d]]{K} < Mat(K,2,2).
Proof.
 Take V = Mat(K,2,2).
 Take A = a @{Mat(K,2,2)} mat(K,2,2,1,1).
 Take B = b @{Mat(K,2,2)} mat(K,2,2,1,2).
 Take C = c @{Mat(K,2,2)} mat(K,2,2,2,1).
 Take D = d @{Mat(K,2,2)} mat(K,2,2,2,2).
 Let us show that for all i,j << upto(2) :  mat(K,2,2,i,j) < V.
  Let i,j << upto(2).
  mat(K,2,2,i,j) is linear over K from K^2 to K^2.
  |V| is the set of homomorphisms over K from K^2 to K^2.
 qed.
 V is a vector space over K.
 A,B,C,D < V.
 C +{V} D < V.
 B +{V} (C +{V} D) < V.
 A +{V} (B +{V} (C +{V} D)) < V.
Qed.

Signature. F2 is an object.
Axiom. |F2| is a set.
Axiom. |F2| = {0,1}.
Axiom. 0{F2} = 0.
Axiom. 1{F2} = 1.
Axiom. 1 != 0.
Axiom. 0 +{F2} 0 = 0.
Axiom. 0 +{F2} 1 = 1.
Axiom. 1 +{F2} 0 = 1.
Axiom. 1 +{F2} 1 = 0.
Axiom. 0 *{F2} 0 = 0.
Axiom. 0 *{F2} 1 = 0.
Axiom. 1 *{F2} 0 = 0.
Axiom. 1 *{F2} 1 = 1.
Axiom. ~{F2} 0 = 0.
Axiom. ~{F2} 1 = 1.
Axiom. inv{F2} 1 = 1.

Theorem. F2 is a field.
Proof.
 Let us show that F2 is an abelian group.
  |F2| is a set.
  0{F2} < F2.
  For all a,b < F2   : a +{F2} b < F2.
  For all a < F2     :   ~{F2} a < F2.
  For all a < F2     :       a +{F2} 0{F2} = a.
  For all a < F2     :           a -{F2} a = 0{F2}.
  For all a,b,c < F2 : a +{F2} (b +{F2} c) = (a +{F2} b) +{F2} c.
  For all a,b < F2   :           a +{F2} b = b +{F2} a.
 qed.
 1{F2} < F2.
 1{F2} != 0{F2}.
 For all a,b < F2   : a *{F2} b < F2.
 For all a < F2*    : inv{F2} a < F2.
 For all a < F2     :       a *{F2} 1{F2} = a.
 For all a < F2*    :           a /{F2} a = 1{F2}.
 For all a,b,c < F2 : a *{F2} (b *{F2} c) = (a *{F2} b) *{F2} c.
 For all a,b < F2   :           a *{F2} b = b *{F2} a.
 For all a,b,c < F2 : a *{F2} (b +{F2} c) = (a *{F2} b) +{F2} (a *{F2} c).
Qed.

Lemma. [[1,1],[0,1]]{F2} < Mat(F2,2,2).
Proof.
 F2 is a field.
 1,0 < F2.
 Therefore the thesis (by 2x2Matrix).
Qed.

Lemma. [[0,1],[1,0]]{F2} < Mat(F2,2,2).
Proof.
 F2 is a field.
 1,0 < F2.
 Therefore the thesis (by 2x2Matrix).
Qed.

#    b     c,d
# 0 ---> 1 ===> 2

Signature. quiv is an object.
Axiom. quiv(0) is a set.
Axiom. quiv(0) = {0,1,2}.
Signature. b is an object.
Signature. c is an object.
Signature. d is an object.
Axiom. quiv(1) is a set.
Axiom. quiv(1) = {b,c,d}.
Axiom. quiv(st) is a map.
Axiom. quiv(tl) is a map.
Axiom. Dmn(quiv(st)) = quiv(1).
Axiom. Dmn(quiv(tl)) = quiv(1).
Axiom. quiv(st)(b) = 0.
Axiom. quiv(tl)(b) = 1.
Axiom. quiv(st)(c) = 1.
Axiom. quiv(tl)(c) = 2.
Axiom. quiv(st)(d) = 1.
Axiom. quiv(tl)(d) = 2.

Signature. quivRep is an object.
Axiom. quivRep(0) = F2.
Axiom. quivRep(1) = F2^2.
Axiom. quivRep(2) = F2^2.
Axiom. quivRep(b) is a map h such that Dmn(h) = |F2| and h(0) = 0{F2^2} and h(1) = 0{F2^2}.
Axiom. quivRep(c) = [[1,1],[0,1]]{F2}.
Axiom. quivRep(d) = [[0,1],[1,0]]{F2}.

Theorem. quiv is a quiver.
Proof.
 quiv(0) is a set.
 quiv(1) is a set.
 For all a << quiv(1) : quiv(st)(a) << quiv(0).
 quiv(st) is a map from quiv(1) to quiv(0).
 For all a << quiv(1) : quiv(tl)(a) << quiv(0).
 quiv(tl) is a map from quiv(1) to quiv(0).
Qed.

Theorem. quivRep is a representation of quiv over F2.
Proof.
 F2 is a field.
 F2 is a vector space over F2.
 F2^2 is a vector space over F2.
 For all vertices i of quiv : (quivRep(i) is a vector space over F2).
 Let us show that for all arrows a of quiv :
 (quivRep(a) < Hom(F2,quivRep(quiv(st)(a)),quivRep(quiv(tl)(a)))).
  Let us show that quivRep(b) < Hom(F2,F2,F2^2).
   Let us show that quivRep(b) is linear over F2 from F2 to F2^2.
   quivRep(b) is from |F2| to |F2^2|.
   For all x,y < F2 : quivRep(b)(x +{F2} y) = 0{F2^2} = 0{F2^2} +{F2^2} 0{F2^2}
                      = quivRep(b)(x) +{F2^2} quivRep(b)(y).
   For all x,y < F2 : quivRep(b)(x @{F2} y) = 0{F2^2} = x @{F2^2} 0{F2^2} = x @{F2^2} quivRep(b)(y).
   qed.
   |Hom(F2,F2,F2^2)| is the set of homomorphisms over F2 from F2 to F2^2.
  qed.  
  quivRep(c) < Hom(F2,F2^2,F2^2).
  quivRep(d) < Hom(F2,F2^2,F2^2).
 qed. 
Qed.