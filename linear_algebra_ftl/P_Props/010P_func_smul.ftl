[read linear_algebra_ftl/010D_func_smul.ftl] 

Lemma. Let 2Vectorspace(K,V,W). Let a,b < K. a *{K} b < K.
Lemma. Let 2Vectorspace(K,V,W). Let a,b < K. a +{K} b < K.

Theorem. Let 2Vectorspace(K,V,W).
Then FuncSMul(K,V,W) is from Prod(|K|,|Hom(K,V,W)|) to |Hom(K,V,W)|.
proof.
 
  Dom(FuncSMul(K,V,W)) = Prod(|K|,|Hom(K,V,W)|).

  Let g < Hom(K,V,W).
  Let a < K.
  Let us show that FuncSMul(K,V,W)[(a,g)] < Hom(K,V,W).
    Let us show that FuncSMul(K,V,W)[(a,g)] is linear over K from V to W.

      FuncSMul(K,V,W)[(a,g)] is from |V| to |W|.
      proof.
        W[smul] is a function from Prod(|K|,|W|) to |W|.
        Dom(FuncSMul(K,V,W)[(a,g)]) = |V|.
        For all v<V FuncSMul(K,V,W)[(a,g)][v] = (a @{W} g[v]).
        For all v<V a @{W} g[v] << |W|.
        For all v<V FuncSMul(K,V,W)[(a,g)][v] = a @{W} g[v] << |W|.
      end.
    
      g is linear over K from V to W. 
      Let u,v < V.
    
      Let us show that FuncSMul(K,V,W)[(a,g)][u +{V} v] 
          = FuncSMul(K,V,W)[(a,g)][u] +{W} FuncSMul(K,V,W)[(a,g)][v].
    
        W[smul] is a function from Prod(|K|,|W|) to |W|.
        u +{V} v < V. 
        g[u +{V} v] = g[u] +{W} g[v].
        FuncSMul(K,V,W)[(a,g)][u +{V} v]       = a @{W} g[u +{V} v].
        a @{W} g[u +{V} v]                     = a @{W} (g[u] +{W} g[v]).
        a @{W} (g[u] +{W} g[v])                = (a @{W} g[u]) +{W} (a @{W} g[v]).
        (a @{W} g[u]) +{W} (a @{W} g[v])       
              =FuncSMul(K,V,W)[(a,g)][u] +{W} FuncSMul(K,V,W)[(a,g)][v].
      end.
    
      Let c < K.
        
      W[smul] is a function from Prod(|K|,|W|) to |W|.
      V[smul] is a function from Prod(|K|,|V|) to |V|.
      Let us show that FuncSMul(K,V,W)[(a,g)][c @{V} v]  = c @{W} FuncSMul(K,V,W)[(a,g)][v].
      
        c @{V} v < V.
        g[c @{V} v] = c @{W} g[v].
        FuncSMul(K,V,W)[(a,g)][c @{V} v]    = a @{W} g[c @{V} v].
        a @{W} g[c @{V} v]                  = a @{W} (c @{W}g[v]).
        a @{W} (c @{W}g[v])                 = (a *{K} c) @{W} g[v].
        (a *{K} c) @{W} g[v]                = (c *{K} a) @{W} g[v].
        (c *{K} a) @{W} g[v]                = c @{W} (a @{W} g[v]).
        c @{W} (a @{W} g[v])                = c @{W} FuncSMul(K,V,W)[(a,g)][v].
        
      end.
    end.
  end.   
end.

Theorem. Let 2Vectorspace(K,V,W).
Let g < Hom(K,V,W). Then FuncSMul(K,V,W)[(1{K},g)] = g.
proof.
  FuncSMul(K,V,W)[(1{K},g)] and g are functions.
  Dom(FuncSMul(K,V,W)[(1{K},g)]) = |V| = Dom(g).
  W[smul] is a function from Prod(|K|,|W|) to |W|.
  For all v<V FuncSMul(K,V,W)[(1{K},g)][v] = 1{K} @{W} g[v] = g[v].
  Hence the thesis (by FunExt).
end.

Theorem. Let 2Vectorspace(K,V,W).
Let g < Hom(K,V,W). Let a < K.  Then FuncSMul(K,V,W)[(a,g)] < Hom(K,V,W).
proof.
  (a,g) << Prod(|K|,|Hom(K,V,W)|).
end.



Theorem. Let 2Vectorspace(K,V,W).
Let a,b < K. Let g < Hom(K,V,W). 
Then FuncSMul(K,V,W)[((a *{K} b),g)] = FuncSMul(K,V,W)[(a,FuncSMul(K,V,W)[(b,g)])].
proof.
  a *{K} b < K.
  Dom(FuncSMul(K,V,W)[((a *{K} b),g)]) = |V| = Dom(FuncSMul(K,V,W)[(a,FuncSMul(K,V,W)[(b,g)])]).
  Let v<V.
  W[smul] is a function from Prod(|K|,|W|) to |W| 
    and for all a1,b1 < K for all v1 < W : (a1 *{K} b1) @{W} v1 = a1 @{W} (b1 @{W} v1).
  FuncSMul(K,V,W)[((a *{K} b),g)][v] = (a *{K} b) @{W} g[v].
  (a *{K} b) @{W} g[v] = a @{W} (b @{W} g[v]).
  a @{W} (b @{W} g[v]) = a @{W} FuncSMul(K,V,W)[(b,g)][v].
  a @{W} FuncSMul(K,V,W)[(b,g)][v] = FuncSMul(K,V,W)[(a,FuncSMul(K,V,W)[(b,g)])][v].
end.
 
Theorem. Let 2Vectorspace(K,V,W).
Let a,b < K. Let g < Hom(K,V,W). 
Then FuncSMul(K,V,W)[((a +{K} b),g)] 
  = FuncAdd(K,V,W)[(FuncSMul(K,V,W)[(a, g)],FuncSMul(K,V,W)[(b, g)])].
proof.
  FuncSMul(K,V,W)[((a +{K} b),g)] < Hom(K,V,W).
  FuncAdd(K,V,W)[(FuncSMul(K,V,W)[(a, g)],FuncSMul(K,V,W)[(b, g)])] is a function.
  a +{K} b < K.
  Dom(FuncSMul(K,V,W)[((a +{K} b),g)]) = |V| 
    = Dom(FuncAdd(K,V,W)[(FuncSMul(K,V,W)[(a, g)],FuncSMul(K,V,W)[(b, g)])]).
  Let v<V.
  Let us show that FuncSMul(K,V,W)[((a +{K} b),g)][v] 
    = FuncAdd(K,V,W)[(FuncSMul(K,V,W)[(a, g)],FuncSMul(K,V,W)[(b, g)])][v].
    W[smul] is a function from Prod(|K|,|W|) to |W|.
    FuncSMul(K,V,W)[((a +{K} b),g)][v] = (a +{K} b) @{W} g[v].
    (a +{K} b) @{W} g[v] = (a @{W} g[v]) +{W} (b @{W} g[v]).
    (a @{W} g[v]) +{W} (b @{W} g[v]) = FuncSMul(K,V,W)[(a, g)][v] +{W} (b @{W} g[v]).
    FuncSMul(K,V,W)[(a, g)][v] +{W} (b @{W} g[v]) 
      = FuncSMul(K,V,W)[(a, g)][v] +{W} FuncSMul(K,V,W)[(b, g)][v].
    FuncSMul(K,V,W)[(a, g)][v] +{W} FuncSMul(K,V,W)[(b, g)][v] 
      = FuncAdd(K,V,W)[(FuncSMul(K,V,W)[(a, g)],FuncSMul(K,V,W)[(b, g)])][v].
  end.
end.

Theorem. Let 2Vectorspace(K,V,W).
Let a < K. Let g,h < Hom(K,V,W).
Then FuncSMul(K,V,W)[(a,FuncAdd(K,V,W)[(g,h)])] 
    = FuncAdd(K,V,W)[(FuncSMul(K,V,W)[(a,g)], FuncSMul(K,V,W)[(a,h)])].
proof.
  Dom(FuncSMul(K,V,W)[(a,FuncAdd(K,V,W)[(g,h)])]) = |V|
    = Dom(FuncAdd(K,V,W)[(FuncSMul(K,V,W)[(a,g)], FuncSMul(K,V,W)[(a,h)])]).
  Let v<V.
  Let us show that FuncSMul(K,V,W)[(a,FuncAdd(K,V,W)[(g,h)])][v]
      = FuncAdd(K,V,W)[(FuncSMul(K,V,W)[(a,g)], FuncSMul(K,V,W)[(a,h)])][v].
    W[smul] is a function from Prod(|K|,|W|) to |W|.
    FuncSMul(K,V,W)[(a,FuncAdd(K,V,W)[(g,h)])][v] = a @{W} FuncAdd(K,V,W)[(g,h)][v].
    a @{W} FuncAdd(K,V,W)[(g,h)][v] = a @{W} (g[v] +{W} h[v]).
    a @{W} (g[v] +{W} h[v]) = (a @{W} g[v]) +{W} (a @{W} h[v]).
    (a @{W} g[v]) +{W} (a @{W} h[v]) = FuncSMul(K,V,W)[(a,g)][v] +{W} (a @{W} h[v]).
    FuncSMul(K,V,W)[(a,g)][v] +{W} (a @{W} h[v]) 
      = FuncSMul(K,V,W)[(a,g)][v] +{W} FuncSMul(K,V,W)[(a,h)][v].
    FuncSMul(K,V,W)[(a,g)][v] +{W} FuncSMul(K,V,W)[(a,h)] [v]
      = FuncAdd(K,V,W)[(FuncSMul(K,V,W)[(a,g)], FuncSMul(K,V,W)[(a,h)])][v].
  end.
end.
