[read RepresentationTheory/06_homomorphism.ftl]
[read RepresentationTheory/09_subspace.ftl]

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