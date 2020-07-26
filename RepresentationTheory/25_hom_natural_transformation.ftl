[read RepresentationTheory/24_hom_functor.ftl]
[read RepresentationTheory/18_natural_transformation.ftl]

Let K denote a field.

Theorem. Let A be an algebra over K. Let M1,M2 be modules over A over K. Let f be a modulehom over A
 over K from M1 to M2. Hom(K,A,f,-) is a natural transformation
 from Hom(K,A,M2,-) to Hom(K,A,M1,-) over Mod(K,A) to Mod(K,K).
Proof.
 Mod(K,A) is a category.
 K is an algebra over K.
 Mod(K,K) is a category.
 Take F = Hom(K,A,M2,-).
 Take G = Hom(K,A,M1,-).
 F is a functor from Mod(K,A) to Mod(K,K).
 G is a functor from Mod(K,A) to Mod(K,K).
 Take n = Hom(K,A,f,-).
 Let us show that n is a natural transformation from F to G over Mod(K,A) to Mod(K,K).
  Let us show that for all N < Mod(K,A) : n(N) << Mod(K,K)(F(N),G(N)).
   Let N < Mod(K,A).
   N is a module over A over K.
   n(N) = Hom(K,A,-,N)(f).
   F(N) = Hom(K,A,-,N)(M2).
   G(N) = Hom(K,A,-,N)(M1).
   Hom(K,A,-,N) is a contravariant functor from Mod(K,A) to Mod(K,K).
   Let us show that f << Mod(K,A)(M1,M2).
    |Hom(K,A,M1,M2)| is the set of modulehoms over A over K from M1 to M2.
    f < Hom(K,A,M1,M2).
   qed.
   Take H = Hom(K,A,-,N).
   H is a contravariant functor from Mod(K,A) to Mod(K,K).
   M1,M2 < Mod(K,A).
   Therefore H(f) << Mod(K,K)(H(M2),H(M1)) (by ContraFunctor).
  qed.
  Let us show that for all N1,N2 < Mod(K,A) and all h << Mod(K,A)(N1,N2) : G(h)*n(N1) = n(N2)*F(h).
   Let N1,N2 < Mod(K,A).
   Let h << Mod(K,A)(N1,N2).
   N1,N2 are modules over A over K.
   G(h)*n(N1) = Hom(K,A,M1,h)*Hom(K,A,f,N1).
   n(N2)*F(h) = Hom(K,A,f,N2)*Hom(K,A,M2,h).  
   f < Hom(K,A,M1,M2).
   h < Hom(K,A,N1,N2) (by ModMor).
   Hom(K,A,M1,h),Hom(K,A,f,N1) are maps (by HomFun, ContraHomFun).
   Hom(K,A,M1,h)*Hom(K,A,f,N1) is a map.
   Dmn(Hom(K,A,f,N1)) = |Hom(K,A,M2,N1)| (by ContraHomFun).
    Dmn(Hom(K,A,M1,h)*Hom(K,A,f,N1)) = |Hom(K,A,M2,N1)|.
   Hom(K,A,f,N2),Hom(K,A,M2,h) are maps (by HomFun, ContraHomFun).
   Hom(K,A,f,N2)*Hom(K,A,M2,h) is a map.
   Dmn(Hom(K,A,M2,h)) = |Hom(K,A,M2,N1)| (by HomFun).
   Dmn(Hom(K,A,f,N2)*Hom(K,A,M2,h)) = |Hom(K,A,M2,N1)|.
   Let us show that for all g < Hom(K,A,M2,N1) : (Hom(K,A,M1,h)*Hom(K,A,f,N1))(g) = h*(g*f).
    Let g < Hom(K,A,M2,N1).
    (Hom(K,A,M1,h)*Hom(K,A,f,N1))(g) = Hom(K,A,M1,h)(Hom(K,A,f,N1)(g)).
    Hom(K,A,f,N1)(g) = g*f (by ContraHomFun).
    g*f < Hom(K,A,M1,N1) (by ModuleHomComp).
    Hom(K,A,M1,h)(g*f) = h*(g*f) (by HomFun).
   qed.
   Let us show that for all g < Hom(K,A,M2,N1) : (Hom(K,A,f,N2)*Hom(K,A,M2,h))(g) = (h*g)*f.
    Let g < Hom(K,A,M2,N1).
    (Hom(K,A,f,N2)*Hom(K,A,M2,h))(g) = Hom(K,A,f,N2)(Hom(K,A,M2,h)(g)).
    Hom(K,A,M2,h)(g) = h*g (by HomFun).
    Let us show that h*g < Hom(K,A,M2,N2).
     K is a field.
     A is an algebra over K.
     N1,N2,M2 are modules over A over K.
     h < Hom(K,A,N1,N2).
     g < Hom(K,A,M2,N1).
     Therefore the thesis (by ModuleHomComp).
    qed.
    Hom(K,A,f,N2)(h*g) = (h*g)*f (by ContraHomFun).  
   qed.
   Let us show that for all g < Hom(K,A,M2,N1) : h*(g*f) = (h*g)*f.
    Let g < Hom(K,A,M2,N1).
    K is a field.
    f is a modulehom over A over K from M1 to M2.
    f : |M1| -> |M2|.
    g is a modulehom over A over K from M2 to N1.
    g : |M2| -> |N1|.
    h is a modulehom over A over K from N1 to N2.
    h : |N1| -> |N2|.
    Therefore the thesis (by ThreeComp).
   qed.
  qed.
 qed.
Qed.

Axiom. Let A be an algebra over K. Let N1,N2 be modules over A over K. Let f be a modulehom over A
 over K from N1 to N2. Hom(K,A,-,f) is a contravariant natural transformation
 from Hom(K,A,-,N1) to Hom(K,A,-,N2) over Mod(K,A) to Mod(K,K).
# The proof is similar.