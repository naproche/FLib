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

Axiom. Let f be a map. Let A be a set. Let id{A} and f be composable. Then id{A}*f = f.

Axiom. Let f be a map. Let A be a set. Let Dmn(f) = A. Then f*id{A} = f.

Axiom CompFromTo. Let A,B,C be objects. Let g:A->B. Let f:B->C. Then f*g : A -> C.

Axiom. Let A,B,C,D be objects. Let h:A->B. Let g:B->C. Let f:C->D. Then (f*g)*h : A -> D.

Axiom. Let A,B,C,D be objects. Let h:A->B. Let g:B->C. Let f:C->D. Then f*(g*h) : A->D.

Axiom ThreeComp. Let A,B,C,D be objects. Let h:A->B. Let g:B->C. Let f:C->D. Then (f*g)*h = f*(g*h).


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

Axiom NegZero. Let G be an abelian group.
 Then ~{G} 0{G} = 0{G}.

Axiom ZeroAdd. Let G be an abelian group. Let a < G.
 Then 0{G} +{G} a = a.

Axiom NegAdd. Let G be an abelian group. Let a,b < G.
 Then ~{G} (a +{G} b) = (~{G} a) -{G} b.


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

Axiom ZeroSmul. Let V be a vector space over K. Let v < V.
 Then 0{K} @{V} v = 0{V}.

Axiom SmulZero. Let V be a vector space over K. Let a < K.
 Then a @{V} 0{V} = 0{V}.

Axiom NegSmul. Let V be a vector space over K. Let a < K. Let v < V.
 Then (~{K} a) @{V} v = ~{V} (a @{V} v).

Axiom NegOneSmul. Let V be a vector space over K. Let v < V.
 Then (~{K} 1{K}) @{V} v = ~{V} v.

Axiom SmulNeg. Let V be a vector space over K. Let a < K. Let v < V.
 Then a @{V} (~{V} v) = ~{V} (a @{V} v).


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

Axiom. Let V and W be vector spaces over K.
 0{Hom(K,V,W)} is linear over K from V to W.

Axiom. Let V and W be vector spaces over K. Let f,g < Hom(K,V,W).
 Then f +{Hom(K,V,W)} g is linear over K from V to W.

Axiom. Let V and W be vector spaces over K. Let f < Hom(K,V,W).
 Then ~{Hom(K,V,W)} f is linear over K from V to W.

Axiom. Let V and W be vector spaces over K. Let a < K and f < Hom(K,V,W).
 Then a @{Hom(K,V,W)} f is linear over K from V to W.

Axiom. Let V and W be vector spaces over K. Then Hom(K,V,W) is a vector space over K.


#012 field2VS (this axiom is fairly different from the original)

Axiom. Let a,b < K. a @{K} b = a *{K} b.

Axiom. K is a vector space over K.


#013 dual

Axiom Exi. Let V be a vector space over K. Let v,w < V. Assume that v != w.
 There exists a map g such that g is linear over K from V to K and g(v) != g(w).

Axiom. Let V be a vector space over K. dual(K,V) = Hom(K,V,K).

Definition. Let V be a vector space over K. Let v < V. eval(dual(K,V), v) is a map f such that
 Dmn(f) = |dual(K,V)| and (for all h < dual(K,V) : f(h) = h(v)).

Axiom. Let V be a vector space over K. V2ddV(K,V) is a map f such that
 Dmn(f) = |V| and (for all v < V : f(v) = eval(dual(K,V),v)).

Axiom. Let V be a vector space over K.
 V2ddV(K,V) is injective and linear over K from V to dual(K,dual(K,V)).


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

Axiom. Let r,s,t < Un(R).
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

Axiom. Un(R) is a group.


#102 endomorphisms

Axiom. Let V be a vector space over K. End(K,V) = Hom(K,V,V).

Axiom. Let V be a vector space over K. 1{End(K,V)} = id{|V|}.
Axiom MapMul. Let V be a vector space over K. Let f,g < End(K,V). f *{End(K,V)} g  = f*g.

Axiom. Let V be a vector space over K. Then id{|V|} is linear over K from V to V.

Axiom. Let U,V,W be vector spaces over K. Let f,g be maps.
 Let g be linear over K from U to V. Let f be linear over K from V to W.
 Then f*g is linear over K from U to W.

Axiom. Let V be a vector space over K. End(K,V) is a ring.


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

Axiom. Let V,W be vector spaces over K. Let f be a map.
 Let f be isomorphism over K from V to W. Then f^(-1) < Hom(K,W,V).

Axiom. Let V be a vector space over K. Let f be a map.
 f < Aut(K,V) iff f is isomorphism over K from V to V.


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

Axiom. Let V be a vector space over K. Let W be an object. Assume |V|=|W|.
 Then W is a subspace of V over K.

Axiom. Let V be a vector space over K. Then V is a subspace of V over K.

Axiom. Let sub(K,V,U). Then U is a vector space over K.


#202 kernel

Axiom. Let V,W be vector spaces over K. Let f < Hom(K,V,W). |Ker(f)| is a set.
Axiom. Let V,W be vector spaces over K. Let f < Hom(K,V,W). |Ker(f)| = {v | v < V and f(v) = 0{W}}.

Axiom. Let V,W be vector spaces over K. Let f < Hom(K,V,W).
 Let v,w < V. Let f(v) = f(w). Then v -{V} w < Ker(f).

Axiom. Let V,W be vector spaces over K. Let f < Hom(K,V,W).
 Assume |Ker(f)| = {0{V}}. Then f is injective.

Axiom. Let V,W be vector spaces over K. Let f < Hom(K,V,W). Then Ker(f) is a subspace of V over K.


# Up to this point, this formalization is 66% shorter than the corresponding parts of the
# original library (26 kB instead of 76 kB).
# It takes only 3:42 to check instead of approximately 100 minutes.
# The eprover.exe needs way less RAM now (ca. 600 MB instead of 4 GB).
