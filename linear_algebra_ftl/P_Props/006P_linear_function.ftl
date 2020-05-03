[read linear_algebra_ftl/006D_linear_function.ftl]

Let K denote a Field.


Lemma. Let V,W be vector spaces over K. Let v,w < V. v +{V} w < V.

Lemma. Let V,W be vector spaces over K. Let f < Hom(K,V,W). Let u,v < V. Then f[v +{V} u] = f[v] +{W} f[u].

Lemma. Let V,W be vector spaces over K. Let f < Hom(K,V,W). Let a < K. Let v < V. Then f[a @{V} v] = a @{W} f[v].


Theorem neg_linear. Let V,W be vector spaces over K.
Let f < Hom(K,V,W). Let v < V. Then f[neg{V}[v]] = neg{W}[f[v]].
proof.
 f[neg{K}[1{K}] @{V} v] = neg{K}[1{K}] @{W} f[v].
 neg{K}[1{K}] @{W} f[v] = neg{W}[f[v]].
end.
 
 
Theorem zero_linear. Let V,W be vector spaces over K. Let f < Hom(K,V,W). Then f[0{V}] = 0{W}.
proof.
 0{V} = 0{K} @{V} 0{V}.
 f[0{V}] = f[0{K} @{V} 0{V}].
 f[0{K} @{V} 0{V}] = 0{K} @{W} f[0{V}].
 0{K} @{W} f[0{V}] = 0{W}.
end.