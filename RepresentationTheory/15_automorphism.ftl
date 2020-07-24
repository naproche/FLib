[read RepresentationTheory/13_unit_group.ftl]
[read RepresentationTheory/14_endomorphism.ftl]

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