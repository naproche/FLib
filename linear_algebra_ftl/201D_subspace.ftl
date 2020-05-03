[read linear_algebra_ftl/A_Props/005A_vector_space.ftl] 

Let K denote a field.

Definition. Let K be a field. Let V be a vector space over K.
A subspace of V over K is a set U such that
     (U is subset of |V|)
 and (0{V} << U)
 and (for all u,v << U             :  u +{V} v << U)
 and (for all u << U               : neg{V}[u] << U)
 and (for all a < K for all u << U :  a @{V} u << U).


Let subspace(K,V,U) stand for
(K is a field and V is a vector space over K and U is a subspace of V over K).

Signature. subspace2VS(U) is a function.

Axiom. Let subspace(K,V,U). Dom(subspace2VS(U)) = {carr,zero,add,neg,smul}.
Axiom. Let subspace(K,V,U). subspace2VS(U)[carr] = U.
Axiom. Let subspace(K,V,U). subspace2VS(U)[zero] = 0{V}.
Axiom. Let subspace(K,V,U). subspace2VS(U)[add] = (add{V}|{Prod(U,U)}).
Axiom. Let subspace(K,V,U). subspace2VS(U)[neg] = (neg{V}|{U}).
Axiom. Let subspace(K,V,U). subspace2VS(U)[smul] = (smul{V}|{Prod(|K|,U)}).

