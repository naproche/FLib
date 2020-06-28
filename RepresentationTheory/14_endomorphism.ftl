[read RepresentationTheory/02_composition.ftl]
[read RepresentationTheory/06_homomorphism.ftl]
[read RepresentationTheory/12_ring.ftl]

Let K denote a field.

Axiom. Let V be a vector space over K. Endo(K,V) = Hom(K,V,V).

Axiom MapOne. Let V be a vector space over K. 1{Endo(K,V)} = id{|V|}.
Axiom MapMul. Let V be a vector space over K. Let f,g < Endo(K,V). f *{Endo(K,V)} g  = f*g.

Theorem. Let V be a vector space over K. Then id{|V|} is linear over K from V to V.
Proof.
 id{|V|} is a map from |V| to |V|.
Qed.

Theorem. Let U,V,W be vector spaces over K. Let f,g be maps.
 Let g be linear over K from U to V. Let f be linear over K from V to W.
 Then f*g is linear over K from U to W.
Proof.
 f*g is a map from |U| to |W|.
Qed.

Theorem. Let V be a vector space over K. Endo(K,V) is a ring.
Proof.
 Take R = Endo(K,V).
 Let us show that R is a ring.
  R is an abelian group.
  1{R} < R.
  Let us show that for all f,g < R : f *{R} g < R.
   Let f,g < R.
   f,g are linear over K from V to V.
   f*g is linear over K from V to V.
  qed.
  For all f < R : f *{R} 1{R} = f.
  For all f < R : 1{R} *{R} f = f.
  Let us show that for all f,g,h < R : f *{R} (g *{R} h) = (f *{R} g) *{R} h.
   Let f,g,h < R.
   f *{R} (g *{R} h) = f*(g*h).
   (f *{R} g) *{R} h = (f*g)*h.
   f,g,h are maps from |V| to |V|.
   f*(g*h) = (f*g)*h.
  qed.
  Let us show that for all f,g,h < R : f *{R} (g +{R} h) = (f *{R} g) +{R} (f *{R} h).
   Let f,g,h < R.
   Let us show that for all v < V : (f *{R} (g +{R} h))(v) = ((f *{R} g) +{R} (f *{R} h))(v).
    Let v < V.
    (f *{R} (g +{R} h))(v)
    = (f*(g +{R} h))(v)
    = f((g +{R} h)(v))
    = f(g(v) +{V} h(v))
    = f(g(v)) +{V} f(h(v))
    = (f*g)(v) +{V} (f*h)(v)
    = (f *{R} g)(v) +{V} (f *{R} h)(v)
    = ((f *{R} g) +{R} (f *{R} h))(v).
   qed.
   Dmn(f *{R} (g +{R} h)) = |V| = Dmn((f *{R} g) +{R} (f *{R} h)).
  qed.
  Let us show that for all f,g,h < R : (f +{R} g) *{R} h = (f *{R} h) +{R} (g *{R} h).
   Let f,g,h < R.
   Let us show that for all v < V : ((f +{R} g) *{R} h)(v) = ((f *{R} h) +{R} (g *{R} h))(v).
    Let v < V.
    ((f +{R} g) *{R} h)(v)
    = (f +{R} g)(h(v))
    = f(h(v)) +{V} g(h(v))
    = (f *{R} h)(v) +{V} (g *{R} h)(v)
    = ((f *{R} h) +{R} (g *{R} h))(v).
   qed.
  qed.
 qed.
Qed.