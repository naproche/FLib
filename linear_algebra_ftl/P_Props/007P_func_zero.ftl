[read linear_algebra_ftl/007D_func_zero.ftl]

Let K denote a field.


Theorem. Let 2Vectorspace(K,V,W).
Then FuncZero(K,V,W) is linear over K from V to W.
proof. 
  K is a field.
  V and W are vector spaces over K. 
  FuncZero(K,V,W) is a function.
  FuncZero(K,V,W) is from |V| to |W|.
  proof.
    Dom(FuncZero(K,V,W)) = |V|.
    for all v<V FuncZero(K,V,W)[v] << |W|.
  end.
  for all u,v < V             : FuncZero(K,V,W)[u +{V} v] 
                              = FuncZero(K,V,W)[u] +{W} FuncZero(K,V,W)[v].
  for all a < K for all v < V : a @{V} v < V.
  for all a < K for all v < V FuncZero(K,V,W)[a @{V} v] < W.
  for all v < V FuncZero(K,V,W)[v] < W.
  W[smul] is a function from Prod(|K|,|W|) to |W|.
  for all a < K for all v < V a @{W} FuncZero(K,V,W)[v] < W.
  let us show that for all a < K for all v < V : FuncZero(K,V,W)[a @{V} v] =a @{W} FuncZero(K,V,W)[v].
    let a < K and v < V.
    FuncZero(K,V,W)[a @{V} v] = 0{W}.
    0{W} = a @{W} 0{W} = a @{W} FuncZero(K,V,W)[v].
    a @{W} FuncZero(K,V,W)[v] = a @{W} FuncZero(K,V,W)[v].
  end.
end.
