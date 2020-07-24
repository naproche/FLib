[read RepresentationTheory/01_map.ftl]
[read RepresentationTheory/05_vector_space.ftl]

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