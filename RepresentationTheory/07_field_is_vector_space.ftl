[read RepresentationTheory/05_vector_space.ftl]

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