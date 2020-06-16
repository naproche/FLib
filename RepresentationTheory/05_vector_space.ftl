[read RepresentationTheory/04_field.ftl]

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