[read linear_algebra_ftl/006D_linear_function.ftl]

Let K denote a Field.

Axiom. Let V,W be vector spaces over K. Let f < Hom(K,V,W). Let u,v < V. Then f[v +{V} u] = f[v] +{W} f[u].
Axiom. Let V,W be vector spaces over K. Let f < Hom(K,V,W). Let a < K. Let v < V. Then f[a @{V} v] = a @{W} f[v].

Axiom neg_linear. Let V,W be vector spaces over K.
Let f < Hom(K,V,W). Let v < V. Then f[neg{V}[v]] = neg{W}[f[v]].

Axiom zero_linear. Let V,W be vector spaces over K. Let f < Hom(K,V,W). Then f[0{V}] = 0{W}.
