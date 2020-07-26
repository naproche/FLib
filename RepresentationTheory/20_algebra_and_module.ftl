[read RepresentationTheory/07_field_is_vector_space.ftl]
[read RepresentationTheory/12_ring.ftl]

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