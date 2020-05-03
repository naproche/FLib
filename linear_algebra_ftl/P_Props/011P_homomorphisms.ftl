[read linear_algebra_ftl/011D_homomorphisms.ftl]


Theorem. Let 2Vectorspace(K,V,W). 
Then Hom(K,V,W) is a vector space over K.
proof.
 Let H = Hom(K,V,W).
  (H has carr,zero,add,neg,smul).
  Let us show that H is an abelian group.
    (H has carr,zero,add,neg).
    |H| is a set.
    0{H} < H.
    add{H} is a function from Prod(|H|,|H|) to |H|.
    neg{H} is a function from |H| to |H|.
    For all a < H : a +{H} 0{H} = a.
    For all a < H : a -{H} a = 0{H}.
    proof.
      Let a < H.
      a -{H} a = a +{H} ~{H}a.
      a +{H} ~{H}a = FuncAdd(K,V,W)[(a, FuncNeg(K,V,W)[a])].
      FuncAdd(K,V,W)[(a, FuncNeg(K,V,W)[a])] = FuncZero(K,V,W).
      FuncZero(K,V,W) = 0{H}.
    end.
    Let us show that for all a,b,c < H : a +{H} (b +{H} c) = (a +{H} b) +{H} c.
      Let a,b,c < H.
      a +{H} (b +{H} c) = FuncAdd(K,V,W)[(a,FuncAdd(K,V,W)[(b,c)])]
      = FuncAdd(K,V,W)[(FuncAdd(K,V,W)[(a,b)],c)] = (a +{H} b) +{H} c.
    end.
    For all a,b < H : a +{H} b = b +{H} a.
  end.
  smul{H} is a function from Prod(|K|,|H|) to |H|.
  for all u < H : 1{K} @{H} u = u.
  Let us show that for all a,b < K for all v < H : (a *{K} b) @{H} v =  a @{H} (b @{H} v).
    Let a,b < K and v < H.
    (a *{K} b) @{H} v = FuncSMul(K,V,W)[((a *{K} b),v)]
    = FuncSMul(K,V,W)[(a,FuncSMul(K,V,W)[(b,v)])] = a @{H} (b @{H} v).
  end.
  Let us show that for all a,b < K for all v < H : (a +{K} b) @{H} v = (a @{H} v) +{H} (b @{H} v).
    Let a,b < K and v < H.
    (a +{K} b) @{H} v = FuncSMul(K,V,W)[((a +{K} b),v)] 
    = FuncAdd(K,V,W)[(FuncSMul(K,V,W)[(a, v)],FuncSMul(K,V,W)[(b, v)])] = (a @{H} v) +{H} (b @{H} v).
  end.
  Let us show that for all a < K for all v,w < H : a @{H} (v +{H} w)  =(a @{H} v) +{H} (a @{H} w).
    Let a < K and v,w < H.
    a @{H} (v +{H} w) = FuncSMul(K,V,W)[(a,FuncAdd(K,V,W)[(v,w)])] 
    = FuncAdd(K,V,W)[(FuncSMul(K,V,W)[(a,v)], FuncSMul(K,V,W)[(a,w)])] =(a @{H} v) +{H} (a @{H} w).
  end.
  # For some reason, repetition accelerates the process massively.
  Let us show that H is a vector space over K.
    (H has carr,zero,add,neg,smul)
     and (H is an abelian group)
     and (smul{H} is a function from Prod(|K|,|H|) to |H|)
     and (for all u < H                 :       1{K} @{H} u = u)
     and (for all a,b < K for all v < H : (a *{K} b) @{H} v = a @{H} (b @{H} v))
     and (for all a,b < K for all v < H : (a +{K} b) @{H} v = (a @{H} v) +{H} (b @{H} v))
     and (for all a < K for all v,w < H : a @{H} (v +{H} w) = (a @{H} v) +{H} (a @{H} w)).
  end.
end.
