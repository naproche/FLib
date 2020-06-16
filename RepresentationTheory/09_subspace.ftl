[read RepresentationTheory/05_vector_space.ftl]

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