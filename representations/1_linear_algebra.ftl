# This formalization is a rewrite of the linear algebra library at
# https://github.com/Felix-Thiele/linear_algebra_ftl
# The main difference is in the implementation of operations on algebraic structures.
# For example, every abelian group G used to have a function add{G} from Prod(|G|,|G|) to |G|.
# In this version, a +{G} b is always defined, but for G to be an abelian group, we demand that
# "for all a,b < G : a +{G} b < G".
# This avoidance of chains of functions and cartesian products makes the checking process way more
# efficient. Unlike the original library, the following proofs don't need any additional statements
# just to help the ontological checking. This makes the proofs much shorter and more readable.
# Using a new "map" signature instead of built-in functions avoids ontological problems because
# a term like f[g[x]] is now always defined without having to check the domains.


[read representations/0_synonyms_and_signatures.ftl]

#000 set

Axiom. Let A be a set. Let x be an object. x << A iff x is an element of A.

Let A is subset of B stand for (A is a set and for all x << A : x << B).

Axiom SetEq. Let A,B be sets. Assume A is subset of B. Assume B is subset of A. Then A = B.

Axiom. Let A be a set. Let a << A. A\{a} is a set.
Axiom. Let A be a set. Let a << A. A\{a} = {x | x << A and x != a}.


#001 maps

Definition. Let f be an object.
 f is injective iff (for all x,y << Dmn(f) : (f(x) = f(y) => x = y)).

Definition. Let f,A,B be objects.
 f is from A to B iff Dmn(f) = A and for all x << A : f(x) << B.

Signature. A map is a notion.

Let f:A->B stand for (f is a map from A to B).

Axiom MapExt. Let f,g be maps.
 If Dmn(f) = Dmn(g) and (for all x <<  Dmn(f) : f(x) = g(x)) then f = g.

Axiom MapId. Let A be a set.
 id{A} is a map h such that Dmn(h) = A and for all a << A : h(a) = a.

Axiom MapRestr. Let f be a map. Let A be subset of Dmn(f). f|A is a map h such that
 Dmn(h) = A and for all x << A we have h(x) = f(x).

Axiom. Let f,g be maps. f*g is a map.
Axiom. Let f,g be maps. Dmn(f*g) = Dmn(g).
Axiom. Let f,g be maps. Let x be an object. (f*g)(x) = f(g(x)).

Definition. Let f,g be maps.
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
 For all x << A : ((f*g)*h)(x) = (f*(g*h))(x).
Qed.


#002 structure


#003 abelian group

Definition. An abelian group is an object G such that
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


#004 field

Definition. A field is an object K such that
     (K is an abelian group)
 and (1{K} < K)
 and (1{K} != 0{K})
 and (for all a,b < K   : a *{K} b < K)
 and (for all a < K     : inv{K} a < K)
 and (for all a < K     :       a *{K} 1{K} = a)
 and (for all a < K*    :          a /{K} a = 1{K})
 and (for all a,b,c < K : a *{K} (b *{K} c) = (a *{K} b) *{K} c)
 and (for all a,b < K   :          a *{K} b = b *{K} a)
 and (for all a,b,c < K : a *{K} (b +{K} c) = (a *{K} b) +{K} (a *{K} c)).

Let K denote a field.


#005 vector space

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


#005-011 homomorphisms

Definition. Let V and W be vector spaces over K. Let f be a map.
 f is linear over K from V to W iff
     (f is from |V| to |W|)
 and (for all u,v < V             : f(u +{V} v) = f(u) +{W} f(v))
 and (for all a < K for all v < V : f(a @{V} v) = a @{W} f(v)).

Axiom. Let V and W be vector spaces over K.
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

Lemma. Let V and W be vector spaces over K.
 0{Hom(K,V,W)} is linear over K from V to W.
Proof.
 Take a map h such that h = 0{Hom(K,V,W)}.
 Let us show that h is linear over K from V to W.
  h is from |V| to |W|.
  For all u,v < V             : h(u +{V} v) = h(u) +{W} h(v).
  For all a < K for all v < V : h(a @{V} v) = a @{W} h(v).
 qed.
Qed.

Lemma. Let V and W be vector spaces over K. Let f,g < Hom(K,V,W).
 Then f +{Hom(K,V,W)} g is linear over K from V to W.
Proof.
 Take a map h such that h = f +{Hom(K,V,W)} g.
 Let us show that h is linear over K from V to W.
  h is from |V| to |W|.
  Let us show that for all u,v < V : h(u +{V} v) = h(u) +{W} h(v).
   Let u,v < V.
   h(u +{V} v) = f(u +{V} v) +{W} g(u +{V} v).
   f(u +{V} v) +{W} g(u +{V} v) = (f(u) +{W} f(v)) +{W} (g(u) +{W} g(v)).
   Let us show that (f(u) +{W} f(v)) +{W} (g(u) +{W} g(v)) = (f(u) +{W} g(u)) +{W} (f(v) +{W} g(v)).
    f(u),f(v),g(u),g(v) < W.
    W is an abelian group.
    Therefore the thesis (by AblianGroup).
   qed.
  qed.
  Let us show that for all a < K for all v < V : h(a @{V} v) = a @{W} h(v).
   Let a < K and v < V.
   h(a @{V} v) = f(a @{V} v) +{W} g(a @{V} v).
   f(a @{V} v) +{W} g(a @{V} v) = (a @{W} f(v)) +{W} (a @{W} g(v)).
   (a @{W} f(v)) +{W} (a @{W} g(v)) = a @{W} (f(v) +{W} g(v)).
   a @{W} (f(v) +{W} g(v)) = a @{W} h(v).
  qed.
 qed.
Qed.

Lemma. Let V and W be vector spaces over K. Let f < Hom(K,V,W).
 Then ~{Hom(K,V,W)} f is linear over K from V to W.
Proof.
 Take a map h such that h = ~{Hom(K,V,W)} f.
 Let us show that h is linear over K from V to W.
  h is from |V| to |W|.
  Let us show that for all u,v < V : h(u +{V} v) = h(u) +{W} h(v).
   Let u,v < V.
   h(u +{V} v) = ~{W} f(u +{V} v).
   ~{W} f(u +{V} v) = ~{W} (f(u) +{W} f(v)).
   ~{W} (f(u) +{W} f(v)) = (~{W} f(u)) +{W} (~{W} f(v)).
   (~{W} f(u)) +{W} (~{W} f(v)) = h(u) +{W} h(v).
  qed.
  Let us show that for all a < K for all v < V : h(a @{V} v) = a @{W} h(v).
   Let a < K and v < V.
   h(a @{V} v)
   = ~{W} f(a @{V} v)
   = ~{W} (a @{W} f(v))
   = a @{W} (~{W} f(v))
   = a @{W} h(v).
  qed.
 qed.
Qed.

Lemma. Let V and W be vector spaces over K. Let a < K and f < Hom(K,V,W).
 Then a @{Hom(K,V,W)} f is linear over K from V to W.
Proof.
 Take a map h such that h = a @{Hom(K,V,W)} f.
 Let us show that h is linear over K from V to W.
  h is from |V| to |W|.
  Let us show that for all u,v < V : h(u +{V} v) = h(u) +{W} h(v).
   Let u,v < V.
   h(u +{V} v) = a @{W} f(u +{V} v).
   a @{W} f(u +{V} v) = a @{W} (f(u) +{W} f(v)).
   a @{W} (f(u) +{W} f(v)) = (a @{W} f(u)) +{W} (a @{W} f(v)).
   (a @{W} f(u)) +{W} (a @{W} f(v)) = h(u) +{W} h(v).
  qed.
  Let us show that for all b < K for all v < V : h(b @{V} v) = b @{W} h(v).
   Let b < K and v < V.
   h(b @{V} v)
   = a @{W} f(b @{V} v)
   = a @{W} (b @{W} f(v))
   = b @{W} (a @{W} f(v))
   = b @{W} h(v).
  qed.
 qed.
Qed.

Theorem. Let V and W be vector spaces over K. Then Hom(K,V,W) is a vector space over K.
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


#012 field2VS (this axiom is fairly different from the original)

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


#013 dual

Axiom Exi. Let V be a vector space over K. Let v,w < V. Assume that v != w.
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
   Take a map g such that g is linear over K from V to K and g(v) != g(w) (by Exi).
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


#100 ring (= ring with 1)

Definition. A ring is an object R such that
     (R is an abelian group)
 and (1{R} < R)
 and (for all a,b < R   : a *{R} b < R)
 and (for all a < R     :       a *{R} 1{R} = a)
 and (for all a < R     :       1{R} *{R} a = a)
 and (for all a,b,c < R : a *{R} (b *{R} c) = (a *{R} b) *{R} c)
 and (for all a,b,c < R : a *{R} (b +{R} c) = (a *{R} b) +{R} (a *{R} c))
 and (for all a,b,c < R : (a +{R} b) *{R} c = (a *{R} c) +{R} (b *{R} c)).

Let R denote a ring.


#101 unit group

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

Definition. A group is an object G such that
     (|G| is a set)
 and (1{G} < G)
 and (for all a,b < G   : a *{G} b < G)
 and (for all a < G     : inv{G} a < G)
 and (for all a < G     :       a *{G} 1{G} = a)
 and (for all a < G     :          a /{G} a = 1{G})
 and (for all a,b,c < G : a *{G} (b *{G} c) = (a *{G} b) *{G} c).

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


#102 endomorphisms

Axiom. Let V be a vector space over K. End(K,V) = Hom(K,V,V).

Axiom. Let V be a vector space over K. 1{End(K,V)} = id{|V|}.
Axiom MapMul. Let V be a vector space over K. Let f,g < End(K,V). f *{End(K,V)} g  = f*g.

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

Theorem. Let V be a vector space over K. End(K,V) is a ring.
Proof.
 Take an object R such that R = End(K,V).
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


#103 automorphisms

Axiom. Let V be a vector space over K. Aut(K,V) = Un(End(K,V)).

Definition. Let f,B be objects.
 f is surjective onto B iff for all y << B there is an x << Dmn(f) such that f(x) = y.

Definition. Let f,A,B be objects.
 f is bijective from A to B iff (f is from A to B and f is injective and f is surjective onto B).

Definition. Let V,W be vector spaces over K. Let f be a map.
 f is isomorphism over K from V to W iff (f < Hom(K,V,W) and f is bijective from |V| to |W|).

Axiom. Let f be a map. f^(-1) is a map.
Axiom. Let f be a map. Let A,B be sets. Let f be bijective from A to B. Then f^(-1) is a map
 from B to A  and (for all x << A : f^(-1)(f(x)) = x) and (for all y << B : f(f^(-1)(y)) = y).

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
  Take g < End(K,V) such that (g *{End(K,V)} f = 1{End(K,V)} and f *{End(K,V)} g = 1{End(K,V)}).
  g*f = id{|V|}.
  f*g = id{|V|}.
  f is injective.
  f is surjective onto |V|.
  f < Hom(K,V,V).
  Thus f is isomorphism over K from V to V.
 qed.
 Let us show that (f is isomorphism over K from V to V) => f < Aut(K,V).
  Let f be isomorphism over K from V to V.
  f^(-1) < End(K,V).
  f *{End(K,V)} (f^(-1)) = f*(f^(-1)) = id{|V|} = 1{End(K,V)}.
  (f^(-1)) *{End(K,V)} f = (f^(-1))*f = id{|V|} = 1{End(K,V)}.
 qed.
Qed.


#201 subspace

Definition. Let K be a field. Let V be a vector space over K.
A subspace of V over K is an object U such that
     (|U| is subset of |V|)
 and (0{V} < U)
 and (for all u,v < U             : u +{V} v < U)
 and (for all a < K and all u < U : a @{V} u < U).

Let sub(K,V,U) stand for (V is a vector space over K and U is a subspace of V over K).

Axiom. Let sub(K,V,U). 0{U} = 0{V}.
Axiom. Let sub(K,V,U). Let u,v < (U).       u +{U} v = u +{V} v.
Axiom. Let sub(K,V,U). Let u < U.             ~{U} u = ~{V} u.
Axiom. Let sub(K,V,U). Let a < K and u < U. a @{U} u = a @{V} u.

# Especially, every structure with the same carrier as V inherits its vector space structure.
# This follows from the next theorem and becomes useful later on.

Theorem. Let V be a vector space over K. Let W be an object. Assume |V|=|W|.
 Then W is a subspace of V over K.
Proof.
 0{V} < W.
 For all u,v < W             : u +{V} v < W.
 For all a < K for all u < W : a @{V} u < W.
Qed.

Theorem. Let V be a vector space over K. Then V is a subspace of V over K.

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


#202 kernel

Axiom. Let V,W be vector spaces over K. Let f < Hom(K,V,W). |Ker(f)| is a set.
Axiom. Let V,W be vector spaces over K. Let f < Hom(K,V,W). |Ker(f)| = {v | v < V and f(v) = 0{W}}.

Theorem. Let V,W be vector spaces over K. Let f < Hom(K,V,W).
 Let v,w < V. Let f(v) = f(w). Then v -{V} w < Ker(f).
Proof.
 f is linear over K from V to W.
 v -{V} w < V.
 f(v -{V} w) = f(v) -{W} f(w).
 f(v) -{W} f(w) = f(v) -{W} f(w) = 0{W}.
Qed.

Theorem. Let V,W be vector spaces over K. Let f < Hom(K,V,W).
 Assume |Ker(f)| = {0{V}}. Then f is injective.
Proof.
 Let us show that for all v,w < V : f(v) = f(w) => v = w.
  Let v,w < V. Assume f(v) = f(w).
  v -{V} w < Ker(f).
  v -{V} w = 0{V}.
  w = w +{V} 0{V} = w +{V} (v -{V} w).
  ~{V} w < V.
  w +{V} (v -{V} w) = v +{V} (w -{V} w) (by VectorSpace).
  v +{V} (w -{V} w) = v +{V} 0{V} = v.
 qed.
Qed.

Theorem. Let V,W be vector spaces over K. Let f < Hom(K,V,W). Then Ker(f) is a subspace of V over K.
Proof.
 |Ker(f)| is subset of |V|.
 Let us show that 0{V} < Ker(f).
  f is linear over K from V to W.
  f(0{V}) = f(0{K} @{V} 0{V}) = 0{K} @{W} f(0{V}) = 0{W}.
 qed.
 Let us show that for all u,v < Ker(f) : u +{V} v < Ker(f).
  Let u,v < Ker(f).
  f(u) = 0{W}.
  f(v) = 0{W}.
  f is linear over K from V to W.
  f(u +{V} v) = f(u) +{W} f(v) = 0{W} +{W} 0{W} = 0{W}.
 qed.
 Let us show that for all a < K and all u < Ker(f) : a @{V} u < Ker(f).
  Let a < K and u < Ker(f).
  f(u) = 0{W}.
  Let us show that f(a @{V} u) = a @{W} f(u).
   f is linear over K from V to W.
   u < V.
  qed.
  a @{W} f(u) = a @{W} 0{W}.
  a @{W} 0{W} = 0{W} (by SmulZero).
 qed.
Qed.


# Up to this point, this formalization is 66% shorter than the corresponding parts of the
# original library (26 kB instead of 76 kB).
# It takes only 3:42 to check instead of approximately 100 minutes.
# The eprover.exe needs way less RAM now (ca. 600 MB instead of 4 GB).
