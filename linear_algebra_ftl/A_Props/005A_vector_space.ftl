[read linear_algebra_ftl/005D_vector_space.ftl]

Let K denote a field.

Axiom ZeroSmul. Let V be a vector space over K. Let v < V.
Then 0{K} @{V} v = 0{V}.

Axiom SmulZero. Let V be a vector space over K. Let a < K.
Then a @{V} 0{V} = 0{V}.

Axiom NegSmul. Let V be a vector space over K. Let a < K. Let v < V.
Then neg{K}[a] @{V} v = neg{V}[a @{V} v].

Axiom SmulNeg. Let V be a vector space over K. Let a < K. Let v < V.
Then a @{V} neg{V}[v] = neg{V}[a @{V} v].

Axiom NegOneSmul. Let V be a vector space over K. Let v < V.
Then neg{K}[1{K}] @{V} v = neg{V}[v].
