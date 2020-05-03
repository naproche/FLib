[read linear_algebra_ftl/103D_automorphisms.ftl]

Let K denote a field.
Let M,N denote sets.
Let f,g denote functions.


Lemma. Let f be bijective from M to N. Then f^(-1)*f = id{M}.
proof.
 Dom(f^(-1)*f) = Dom(id{M}).
 Let us show that for all x << M : (f^(-1)*f)[x] = f^(-1)[f[x]].
  For all x << Dom(f) : f[x] << Dom(f^(-1)).
 end.
end.


Lemma. Let f be bijective from M to N. Then f*f^(-1) = id{N}.
proof.
 Dom(f*f^(-1)) = Dom(id{N}).
 Let us show that for all y << N : (f*f^(-1))[y] = f[f^(-1)[y]].
  For all y << Dom(f^(-1)) : f^(-1)[y] << Dom(f).
 end.
end.


Lemma. Let f be from M to N. Let g be from N to M. Assume f*g=id{N} and g*f=id{M}.
Then f is bijective from M to N.
proof.
 Let us show that f is injective.
  Let us show that for all x,y << M : (f[x] = f[y] => x = y).
   Let x,y << M. Assume f[x] = f[y].
   g[f[x]] = g[f[y]].
   g[f[x]] = (g*f)[x] = id{M}[x] = x.
   g[f[y]] = (g*f)[y] = id{M}[y] = y.
   Thus x = y.
  end.
 end.
 Let us show that f is surjective onto N.
  Let us show that for all y << N there is x << M such that f[x] = y.
   Let y << N.
   g[y] << M.
   f[g[y]] = (f*g)[y] = id{N}[y] = y.
  end.
 end.
end.


Lemma. Let V,W be vector spaces over K. Let f be an isomorphism over K from V to W.
Then f^(-1) < Hom(K,W,V).
proof.
 f^(-1) is from |W| to |V|.
 Let us show that for all v,w < W : f^(-1)[v +{W} w] = f^(-1)[v] +{V} f^(-1)[w].
  Let v,w < W.
  v +{W} w < W.
  f[f^(-1)[v] +{V} f^(-1)[w]] = f[f^(-1)[v]] +{W} f[f^(-1)[w]].
  f[f^(-1)[v]] = v.
  f[f^(-1)[w]] = w.
  f[f^(-1)[v] +{V} f^(-1)[w]] = v +{W} w.
  f[f^(-1)[v +{W} w]] = v +{W} w.
  f is injective.
  Thus f^(-1)[v] +{V} f^(-1)[w] = f^(-1)[v +{W} w].
 end.
 smul{W} is from Prod(|K|,|W|) to |W|.
 For all a < K and all w < W : a @{W} w << Dom(f^(-1)).
 For all a < K and all w < W : (a , f^(-1)[w]) << Prod(|K|,|V|).
 smul{V} is from Prod(|K|,|V|) to |V|.
 Let us show that for all a < K and all w < W : f^(-1)[a @{W} w] = a @{V} f^(-1)[w].
  Let a < K. Let w < W.
  a @{W} w < W.
  f[a @{V} f^(-1)[w]] = a @{W} f[f^(-1)[w]].
  f[f^(-1)[w]] = w.
  f[a @{V} f^(-1)[w]] = a @{W} w.
  f[f^(-1)[a @{W} w]] = a @{W} w.
  f is injective.
  Thus f^(-1)[a @{W} w] = a @{V} f^(-1)[w].
 end.
 Let us show that f^(-1) is linear over K from W to V.
  f^(-1) is a function from |W| to |V|.
  For all v,w < W : f^(-1)[v +{W} w] = f^(-1)[v] +{V} f^(-1)[w].
  For all a < K and all w < W : f^(-1)[a @{W} w] = a @{V} f^(-1)[w].
 end.
end.


Theorem. Let V be a vector space over K.
|Aut(K,V)| = {h | h is an isomorphism over K from V to V}.
proof.
 Then End(K,V) is a ring.
 mul{End(K,V)} is from Prod(|End(K,V)|,|End(K,V)|) to |End(K,V)|.
 Let us show that for all f : ((f < Aut(K,V)) => (f is an isomorphism over K from V to V)).
  Let f < Aut(K,V).
  Then f < Hom(K,V,V).
  Let us show that f is bijective from |V| to |V|.
   f < Un(End(K,V)).
   Take g < End(K,V) such that f *{End(K,V)} g = 1{End(K,V)} and g *{End(K,V)} f = 1{End(K,V)}.
   Thus f*g = id{|V|} and g*f = id{|V|}.
   f is from |V| to |V|.
   g is from |V| to |V|.
   Thus f is bijective from |V| to |V|.
  end.
 end.
 Let us show that for all f : ((f < Aut(K,V)) iff (f is an isomorphism over K from V to V)).
  Let f be an isomorphism over K from V to V.
  Then f < End(K,V).
  f^(-1) < End(K,V).
  Let us show that f *{End(K,V)} f^(-1) = 1{End(K,V)} and f^(-1) *{End(K,V)} f = 1{End(K,V)}.
   f *{End(K,V)} f^(-1) = f*f^(-1) = id{|V|}.
   f^(-1) *{End(K,V)} f = f^(-1)*f = id{|V|}.   
  end.
  Thus f < Aut(K,V).
 end.
end.
