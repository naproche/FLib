[read linear_algebra_ftl/010D_func_smul.ftl]

Axiom. Let 2Vectorspace(K,V,W). Let a,b < K. a *{K} b < K.
Axiom. Let 2Vectorspace(K,V,W). Let a,b < K. a +{K} b < K.

Axiom. Let 2Vectorspace(K,V,W).
Then FuncSMul(K,V,W) is from Prod(|K|,|Hom(K,V,W)|) to |Hom(K,V,W)|.

Axiom. Let 2Vectorspace(K,V,W).
Let g < Hom(K,V,W). Then FuncSMul(K,V,W)[(1{K},g)] = g.

Axiom. Let 2Vectorspace(K,V,W).
Let g < Hom(K,V,W). Let a < K.  Then FuncSMul(K,V,W)[(a,g)] < Hom(K,V,W).

Axiom. Let 2Vectorspace(K,V,W).
Let a,b < K. Let g < Hom(K,V,W). 
Then FuncSMul(K,V,W)[((a *{K} b),g)] = FuncSMul(K,V,W)[(a,FuncSMul(K,V,W)[(b,g)])].

Axiom. Let 2Vectorspace(K,V,W).
Let a,b < K. Let g < Hom(K,V,W). 
Then FuncSMul(K,V,W)[((a +{K} b),g)] 
  = FuncAdd(K,V,W)[(FuncSMul(K,V,W)[(a, g)],FuncSMul(K,V,W)[(b, g)])].

Axiom. Let 2Vectorspace(K,V,W).
Let a < K. Let g,h < Hom(K,V,W).
Then FuncSMul(K,V,W)[(a,FuncAdd(K,V,W)[(g,h)])] 
    = FuncAdd(K,V,W)[(FuncSMul(K,V,W)[(a,g)], FuncSMul(K,V,W)[(a,h)])].
