[read RepresentationTheory/06_homomorphism.ftl]
[read RepresentationTheory/07_field_is_vector_space.ftl]

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