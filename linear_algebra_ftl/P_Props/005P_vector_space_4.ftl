[read linear_algebra_ftl/005D_vector_space.ftl]

Let K denote a field.


Definition. Let V be a vector space over K. Let a < K. Let v < V.
localVar(K,V,a,v) is ((a @{V} (~{V} v)) +{V} (a @{V} v) , ~{V} (a @{V} v)).

# This makes the ontological checking faster.
# It doesn't work when you substitute the "localVar(K,V,a,v)" below by its Definition.


Axiom. Let V be a vector space over K. Let a < K. Let v < V.
Then localVar(K,V,a,v) = ~{V} (a @{V} v).
# proof : 005P_vector_space_3.ftl

Axiom. Let V be a vector space over K. Let a < K. Let v < V.
Then localVar(K,V,a,v) = a @{V} (~{V} v).
# proof : 005P_vector_space_3.ftl


Theorem SmulNeg. Let V be a vector space over K. Let a < K. Let v < V.
Then a @{V} (~{V} v) = ~{V} (a @{V} v).
