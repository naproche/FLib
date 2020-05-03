[read linear_algebra_ftl/201D_subspace.ftl]

Let K denote a field.


Theorem. Let V be a vector space over K. Then |V| is a subspace of V over K.
proof.
 |V| is a set.
 0{V} << |V|.
 For all u,v << |V|             :  u +{V} v << |V|.
 For all u << |V|               : neg{V}[u] << |V|.
 For all a < K for all u << |V| :  a @{V} u << |V|.
end.


Lemma. Let V be a vector space over K. Let a < K. Let v,w < V.
Then a @{V} (v +{V} w) = (a @{V} v) +{V} (a @{V} w).


Theorem. Let subspace(K,V,U). Then subspace2VS(U) is a vector space over K.
proof.
 Let W = subspace2VS(U).

 Let us show that W is a vector space over K.
  carr,zero,add,neg,smul << Dom(W).
  |W| is a set.
  0{W} < W.

  Let us show that add{W} is a function from Prod(|W|,|W|) to |W|.
   |W| = U.
   Dom(add{W}) = Prod(|W|,|W|).
   Let x << Prod(|W|,|W|).
   Then add{W}[x] << U.
  end.

  neg{W} is a function from |W| to |W|.
  0{W} = 0{V}.
  add{W} = add{V}|{Prod(|W|,|W|)}.
  For all x << Prod(|W|,|W|) : add{W}[x] = add{V}[x].
  For all v,w < W : v +{W} w = v +{V} w.
  neg{W} = neg{V}|{|W|}.
  For all v < W : neg{W}[v] = neg{V}[v].

  Let us show that for all a < W : a +{W} 0{W} = a.
   Let a < W.
   a +{W} 0{W} = a +{V} 0{W}.
   a +{V} 0{W} = a +{V} 0{V}.
   a +{V} 0{V} = a.
  end.

  Let us show that for all v < W : v -{W} v = 0{W}.
   Let v < W.
   v -{W} v = v -{V} v.
   v -{V} v = 0{V}.
   0{V} = 0{W}.
  end.

  Let us show that for all u,v,w < W :u +{W} (v +{W} w) = (u +{W} v) +{W} w.
   Let u,v,w < W.
    u +{W} (v +{W} w) = u +{V} (v +{V} w).
    u +{V} (v +{V} w) = (u +{V} v) +{V} w.
    (u +{V} v) +{V} w = (u +{W} v) +{W} w.
  end.

  For all v,w < W : v +{W} w = v +{W} w.

  smul{W} = smul{V}|{Prod(|K|,|W|)}.
  For all x << Prod(|K|,|W|) : smul{W}[x] = smul{V}[x].
  For all a < K for all v < W : a @{W} v = a @{V} v.

  Let us show that smul{W} is a function from Prod(|K|,|W|) to |W|.    
   |W| = U.
   Dom(smul{W}) = Prod(|K|,|W|).
   Let x << Prod(|K|,|W|).
   Take a < K and v << |W| such that x = (a,v).
   Then smul{W}[x] = smul{V}[(a,v)].
   smul{V}[(a,v)] << U.
  end.

  Let us show that for all a < K for all v,w < W : a @{W} (v +{W} w) = (a @{W} v) +{W} (a @{W} w).
   Let a < K. Let v,w < W.
   a @{W} (v +{W} w) = a @{V} (v +{V} w).
   a @{V} (v +{V} w) = (a @{V} v) +{V} (a @{V} w).
   (a @{V} v) +{V} (a @{V} w) = (a @{W} v) +{W} (a @{W} w).
  end.

  For all u < W : 1{K} @{W} u = u.

  Let us show that for all a,b < K for all v < W : (a *{K} b) @{W} v = a @{W} (b @{W} v).
   Let a,b < K. Let v < W.
   (a *{K} b) @{W} v = (a *{K} b) @{V} v.
   (a *{K} b) @{V} v = a @{V} (b @{V} v).
   a @{V} (b @{V} v) = a @{W} (b @{W} v).
  end.

  Let us show that for all a,b < K for all v < W : (a +{K} b) @{W} v = (a @{W} v) +{W} (b @{W} v).
   Let a,b < K. Let v < W.
   (a +{K} b) @{W} v = (a +{K} b) @{W} v.
   (a +{K} b) @{V} v = (a @{V} v) +{V} (b @{V} v).
   (a @{W} v) +{V} (b @{V} v) = (a @{W} v) +{W} (b @{W} v).
  end.
 end.
end.
