[read linear_algebra_ftl/A_Props/007A_func_zero.ftl]

# Function Addition

Definition funcadd. Let 2Vectorspace(K,V,W).
FuncAdd(K,V,W) is a function such that (Dom(FuncAdd(K,V,W)) = Prod(|Hom(K,V,W)|,|Hom(K,V,W)|))
  and (for all g,h < Hom(K,V,W) FuncAdd(K,V,W)[(g,h)] is a function d such that
    (Dom(d) = |V| and (for all v<V d[v] = g[v] +{W} h[v]))).
