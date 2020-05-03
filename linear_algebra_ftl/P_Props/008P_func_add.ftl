[read linear_algebra_ftl/008D_func_add.ftl]


Theorem. Let 2Vectorspace(K,V,W).
Then FuncAdd(K,V,W) is from Prod(|Hom(K,V,W)|,|Hom(K,V,W)|) to |Hom(K,V,W)|.
proof.

  Dom(FuncAdd(K,V,W)) = Prod(|Hom(K,V,W)|,|Hom(K,V,W)|).

  Let g,h < Hom(K,V,W).
  Let us show that FuncAdd(K,V,W)[(g,h)] < Hom(K,V,W).
    Let us show that FuncAdd(K,V,W)[(g,h)] is linear over K from V to W.

      FuncAdd(K,V,W)[(g,h)] is from |V| to |W|.
      proof.
        Dom(FuncAdd(K,V,W)[(g,h)]) = |V|.
        For all v<V FuncAdd(K,V,W)[(g,h)][v] = g[v] +{W} h[v] << |W|.
      end.
    
      g,h are linear over K from V to W. 
      Let u,v < V.
    
      Let a < K.
      FuncAdd(K,V,W)[(g,h)][v] < W.
      a @{V} v < V.
      FuncAdd(K,V,W)[(g,h)][a @{V} v] < W.
      Let us show that FuncAdd(K,V,W)[(g,h)][a @{V} v]  = a @{W} FuncAdd(K,V,W)[(g,h)][v].
      
        a @{V} v < V.
        g[a @{V} v] = a @{W} g[v].
        h[a @{V} v] = a @{W} h[v].
      
        FuncAdd(K,V,W)[(g,h)][a @{V} v] = g[a @{V} v] +{W} h[a @{V} v].
        g[a @{V} v] +{W} h[a @{V} v] = (a @{W} g[v]) +{W} h[a @{V} v].
        (a @{W} g[v]) +{W} h[a @{V} v] = (a @{W} g[v]) +{W} (a @{W} h[v]).
        (a @{W} g[v]) +{W} (a @{W} h[v]) = a @{W} (g[v] +{W}  h[v]).
        g[v] +{W}  h[v] = FuncAdd(K,V,W)[(g,h)][v].
        a @{W} (g[v] +{W}  h[v]) = a @{W} FuncAdd(K,V,W)[(g,h)][v].
        
      end.

      Let us show that FuncAdd(K,V,W)[(g,h)][u +{V} v] 
          = FuncAdd(K,V,W)[(g,h)][u] +{W} FuncAdd(K,V,W)[(g,h)][v].
    
        u +{V} v < V. 
        g[u +{V} v] = g[u] +{W} g[v].
        h[u +{V} v] = h[u] +{W} h[v].
    
        FuncAdd(K,V,W)[(g,h)][u +{V} v]        = g[u +{V} v] +{W} h[u +{V} v].
        g[u +{V} v] +{W} h[u +{V} v]           = (g[u] +{W} g[v]) +{W} h[u +{V} v].
        (g[u] +{W} g[v]) +{W} h[u +{V} v]      = g[u] +{W} (g[v] +{W} h[u +{V} v]).
        g[u] +{W} (g[v] +{W} h[u +{V} v])      = g[u] +{W} (g[v] +{W} (h[u] +{W} h[v])).
        g[u] +{W} (g[v] +{W} (h[u] +{W} h[v])) = g[u] +{W} ((g[v] +{W} h[u]) +{W} h[v]).
        g[u] +{W} ((g[v] +{W} h[u]) +{W} h[v]) = g[u] +{W} ((h[u] +{W} g[v]) +{W} h[v]).
        g[u] +{W} ((h[u] +{W} g[v]) +{W} h[v]) = g[u] +{W} (h[u] +{W} (g[v] +{W} h[v])).
        g[u] +{W} (h[u] +{W} (g[v] +{W} h[v])) = (g[u] +{W} h[u]) +{W} (g[v] +{W} h[v]).
        (g[u] +{W} h[u]) +{W} (g[v] +{W} h[v]) = FuncAdd(K,V,W)[(g,h)][u] +{W} FuncAdd(K,V,W)[(g,h)][v].
        
      end.
    
      
    end.
  end.   
end.


Theorem. Let 2Vectorspace(K,V,W).
Let g < Hom(K,V,W). Then FuncAdd(K,V,W)[(g,FuncZero(K,V,W))] = g.
proof.
  FuncAdd(K,V,W)[(g,FuncZero(K,V,W))] and g are functions.
  Dom(FuncAdd(K,V,W)[(g,FuncZero(K,V,W))]) = |V| = Dom(g).
  For all v < V  FuncAdd(K,V,W)[(g,FuncZero(K,V,W))][v] = g[v] +{W} FuncZero(K,V,W)[v]
        = g[v] +{W} 0{W} = g[v].
  Hence the thesis (by FunExt).
end.

Theorem. Let 2Vectorspace(K,V,W).
Let g,h < Hom(K,V,W).  Then FuncAdd(K,V,W)[(g,h)] < Hom(K,V,W).
proof.
  (g,h) << Prod(|Hom(K,V,W)|,|Hom(K,V,W)|).
end.

Theorem. Let 2Vectorspace(K,V,W).
Let g,h < Hom(K,V,W). Then FuncAdd(K,V,W)[(g,h)] = FuncAdd(K,V,W)[(h,g)].
proof.
  FuncAdd(K,V,W)[(g,h)] and FuncAdd(K,V,W)[(h,g)] are functions.
  Dom(FuncAdd(K,V,W)[(g,h)]) = |V| = Dom(FuncAdd(K,V,W)[(h,g)]).
  For all v<V FuncAdd(K,V,W)[(g,h)][v] = g[v] +{W} h[v] = h[v] +{W} g[v] = FuncAdd(K,V,W)[(h,g)][v].
  Hence the thesis (by FunExt).
end.

Theorem. Let 2Vectorspace(K,V,W).
Let g,h,j < Hom(K,V,W).  Then FuncAdd(K,V,W)[(FuncAdd(K,V,W)[(g,h)],j)] 
          = FuncAdd(K,V,W)[(g,FuncAdd(K,V,W)[(h,j)])].
proof.
  FuncAdd(K,V,W)[(FuncAdd(K,V,W)[(g,h)],j)] and FuncAdd(K,V,W)[(g,FuncAdd(K,V,W)[(h,j)])] are functions.
  Dom(FuncAdd(K,V,W)[(FuncAdd(K,V,W)[(g,h)],j)]) = |V| 
      = Dom(FuncAdd(K,V,W)[(g,FuncAdd(K,V,W)[(h,j)])]).
  Let us show that for all v<V FuncAdd(K,V,W)[(FuncAdd(K,V,W)[(g,h)],j)][v] 
    = FuncAdd(K,V,W)[(g,FuncAdd(K,V,W)[(h,j)])][v].
    Let v<V.
    FuncAdd(K,V,W)[(FuncAdd(K,V,W)[(g,h)],j)][v] = FuncAdd(K,V,W)[(g,h)][v] +{W} j[v].
    FuncAdd(K,V,W)[(g,h)][v] +{W} j[v] = (g[v] +{W} h[v]) +{W} j[v].
    (g[v] +{W} h[v]) +{W} j[v] = g[v] +{W} (h[v] +{W} j[v]).
    g[v] +{W} (h[v] +{W} j[v]) = g[v] +{W} FuncAdd(K,V,W)[(h,j)][v].
    g[v] +{W} FuncAdd(K,V,W)[(h,j)][v] = FuncAdd(K,V,W)[(g,FuncAdd(K,V,W)[(h,j)])][v].
  end.
  Hence the thesis (by FunExt).
end.
 