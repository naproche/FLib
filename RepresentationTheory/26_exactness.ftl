[read RepresentationTheory/23_module_category.ftl]
[read RepresentationTheory/17_functor.ftl]
[read RepresentationTheory/10_kernel.ftl]

Let K denote a field.

# sequence = short sequence

Signature. Let a,b,c,d,e be objects. (a,b,c,d,e) is an object.
Signature. Let K,A be objects. A sequence over A over K is a notion.
Signature. Let K,A be objects. A left exact sequence over A over K is a notion.

Axiom Sequence. Let A,X,Y,Z,f,g be objects. (X,f,Y,g,Z) is a sequence over A over K iff
     (A is an algebra over K)
 and (X,Y,Z < Mod(K,A))
 and (f << Mod(K,A)(X,Y))
 and (g << Mod(K,A)(Y,Z)).

Signature. Let f be an object. Im(f) is an object.
Axiom Image. Let V,W be vector spaces over K. Let f < Hom(K,V,W).
 |Im(f)| is a set and |Im(f)| = {f(v) | v < V}.
 
Axiom LeftExactSequence. Let K,A,X,Y,Z,f,g be objects.
 (X,f,Y,g,Z) is a left exact sequence over A over K iff
     ((X,f,Y,g,Z) is a sequence over A over K)
 and (f is injective)
 and (|Im(f)| = |Ker(g)|).


Definition PreserveLeftExactness. Let A,B,F be objects.
 F preserves left exactness from A to B over K iff
 (for all X,Y,Z < Mod(K,A) and all f << Mod(K,A)(X,Y) and all g << Mod(K,A)(Y,Z) :
 (((X,f,Y,g,Z) is a left exact sequence over A over K)
  => ((F(X),F(f),F(Y),F(g),F(Z)) is a left exact sequence over B over K))).

Signature. A left exact functor is a notion.

Axiom LeftExactFunctor. Let A,B be algebras over K. Let F be a functor from Mod(K,A) to Mod(K,B).
 (F is a left exact functor) iff
 (F preserves left exactness from A to B over K).