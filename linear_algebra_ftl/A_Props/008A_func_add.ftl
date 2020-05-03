[read linear_algebra_ftl/008D_func_add.ftl]

Let K denote a Field.

# Function Addition

Axiom. Let 2Vectorspace(K,V,W).
Then FuncAdd(K,V,W) is from Prod(|Hom(K,V,W)|,|Hom(K,V,W)|) to |Hom(K,V,W)|.

Axiom. Let 2Vectorspace(K,V,W).
Let g < Hom(K,V,W). Then FuncAdd(K,V,W)[(g,FuncZero(K,V,W))] = g.

Axiom. Let 2Vectorspace(K,V,W).
Let g,h < Hom(K,V,W).  Then FuncAdd(K,V,W)[(g,h)] < Hom(K,V,W).

Axiom. Let 2Vectorspace(K,V,W).
Let g,h < Hom(K,V,W). Then FuncAdd(K,V,W)[(g,h)] = FuncAdd(K,V,W)[(h,g)].

Axiom. Let 2Vectorspace(K,V,W).
Let g,h,j < Hom(K,V,W).  Then FuncAdd(K,V,W)[(FuncAdd(K,V,W)[(g,h)],j)] 
          = FuncAdd(K,V,W)[(g,FuncAdd(K,V,W)[(h,j)])].
