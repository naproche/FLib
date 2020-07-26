[read RepresentationTheory/02_composition.ftl]
[read RepresentationTheory/22_module_homomorphism.ftl]
[read RepresentationTheory/16_category.ftl]

Let K denote a field.

Axiom ModOb.  Let A be an algebra over K. Ob{Mod(K,A)} is the set of modules over A over K.
Axiom ModMor. Let A be an algebra over K. Let M,N << Ob{Mod(K,A)}. Mod(K,A)(M,N) = |Hom(K,A,M,N)|.
Axiom ModId.  Let A be an algebra over K. Let M << Ob{Mod(K,A)}.  1{M,Mod(K,A)} = id{|M|}.

Theorem ModuleHomComp. Let A be an algebra over K. Let L,M,N be modules over A over K.
 Let f < Hom(K,A,L,M). Let g < Hom(K,A,M,N). Then g*f < Hom(K,A,L,N).
Proof.
 For all modules M1,M2 over A over K :
 (|Hom(K,A,M1,M2)| is the set of maps h such that h is a modulehom over A over K from M1 to M2).
 Let us show that g*f is a modulehom over A over K from L to N.
  f is a modulehom over A over K from L to M.
  g is a modulehom over A over K from M to N.
  g*f is a map from |L| to |N| (by CompFromTo).
  Let us show that for all x,y < L : (g*f)(x +{L} y) = (g*f)(x) +{N} (g*f)(y).
   Let x,y < L.
   (g*f)(x +{L} y) = g(f(x +{L} y)).
   Let us show that g(f(x +{L} y)) = g(f(x) +{M} f(y)).
    f is a modulehom over A over K from L to M.
    x,y < L.
    f(x +{L} y) = f(x) +{M} f(y).
   qed.
   g(f(x) +{M} f(y)) = g(f(x)) +{N} g(f(y)) (by MapAdd).
   g(f(x)) +{N} g(f(y)) = (g*f)(x) +{N} (g*f)(y).
  qed.
  Let us show that for all a < A and all x < L : (g*f)(a @@{L} x) = a @@{N} (g*f)(x).
   Let a < A and x < L.
   f(a @@{L} x) = a @@{M} f(x) (by ModuleHom).
   (g*f)(a @@{L} x) = g(f(a @@{L} x)) = g(a @@{M} f(x)).
   f(x) < M.
   g(a @@{M} f(x)) = a @@{N} g(f(x)) (by ModuleHom).
   a @@{N} g(f(x)) = a @@{N} (g*f)(x).
  qed.
 qed.
Qed.

Theorem. Let A be an algebra over K. Mod(K,A) is a category.
Proof.
 Take C = Mod(K,A).
 For all modules M,N over A over K :
 (|Hom(K,A,M,N)| is the set of maps f such that f is a modulehom over A over K from M to N).
 For all modules M,N over A over K and all f < Hom(K,A,M,N) : (f is a map from |M| to |N|).
 Let us show that C is a category.
  Ob{C} is a set.
  Let us show that for all L,M,N << Ob{C} and all f << C(L,M) and all g << C(M,N) : g*f << C(L,N).
   Let L,M,N << Ob{C} and f << C(L,M) and g << C(M,N).
   L,M,N are modules over A over K.
   f < Hom(K,A,L,M) (by ModMor).
   g < Hom(K,A,M,N) (by ModMor).
   Thus g*f < Hom(K,A,L,N).
   C(L,N) = |Hom(K,A,L,N)| (by ModMor).
  qed.
  Let us show that for all M << Ob{C} : 1{M,C} << C(M,M).
   Let M << Ob{C}.
   M is a module over A over K.
   Let us show that id{|M|} is a modulehom over A over K from M to M.
     id{|M|} is from |M| to |M|.
    For all x,y < M : id{|M|}(x +{M} y) = id{|M|}(x) +{M} id{|M|}(y).
    For all a < A and all x < M : id{|M|}(a @@{M} x) = a @@{M} id{|M|}(x).
   qed.
   Thus id{|M|} < Hom(K,A,M,M).
   C(M,M) = |Hom(K,A,M,M)| (by ModMor).
  qed.
  Let us show that for all M,N << Ob{C} and all f << C(M,N) : f*1{M,C} = f.
   Let M,N << Ob{C} and f << C(M,N).
   f < Hom(K,A,M,N) (by ModMor).
   f : |M| -> |N|.
   Dmn(f) = |M|.
  qed.
  Let us show that for all M,N << Ob{C} and all f << C(N,M) : 1{M,C}*f = f.
   Let M,N << Ob{C} and f << C(N,M).
   |M| is a set.
   f < Hom(K,A,N,M) (by ModMor).
   f : |N| -> |M|.
   id{|M|} is a map.
   id{|M|} and f are composable.
  qed.
  Let us show that for all L,M,N,O << Ob{C} and all f << C(L,M) and all g << C(M,N)
  and all h << C(N,O) : h*(g*f) = (h*g)*f.
   Let L,M,N,O << Ob{C} and f << C(L,M) and g << C(M,N) and h << C(N,O).
   f < Hom(K,A,L,M) (by ModMor).
   g < Hom(K,A,M,N) (by ModMor).
   h < Hom(K,A,N,O) (by ModMor).
   f : |L| -> |M|.
   g : |M| -> |N|.
   h : |N| -> |O|.
   Thus h*(g*f) = (h*g)*f (by ThreeComp).
  qed.
 qed.
Qed.