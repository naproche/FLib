[read RepresentationTheory/23_module_category.ftl]
[read RepresentationTheory/17_functor.ftl]

Let K denote a field.

Axiom. Let K,A,x,y be objects. Hom(K,A,x,-)(y) = Hom(K,A,x,y).
Axiom. Let K,A,x,y be objects. Hom(K,A,-,y)(x) = Hom(K,A,x,y).

Axiom HomFun. Let A be an algebra over K. Let M,N1,N2 be modules over A over K.
 Let f < Hom(K,A,N1,N2). Hom(K,A,M,f) is a map F such that
 Dmn(F) = |Hom(K,A,M,N1)| and for all g < Hom(K,A,M,N1) : F(g) = f*g.

Axiom ContraHomFun. Let A be an algebra over K. Let M1,M2,N be modules over A over K.
 Let f < Hom(K,A,M1,M2). Hom(K,A,f,N) is a map F such that
 Dmn(F) = |Hom(K,A,M2,N)| and for all g < Hom(K,A,M2,N) : F(g) = g*f.

Theorem HomIsFunctor. Let A be an algebra over K. Let M be a module over A over K.
 Hom(K,A,M,-) is a functor from Mod(K,A) to Mod(K,K).
Proof.
 Take F = Hom(K,A,M,-).
 Let us show that F is a functor from Mod(K,A) to Mod(K,K).
  K is a field.
  Mod(K,A) and Mod(K,K) are categories.
  Let us show that for all N < Mod(K,A) : F(N) < Mod(K,K).
   Let N < Mod(K,A).
   N is a module over A over K.
   F(N) = Hom(K,A,M,N).
   Hom(K,A,M,N) is a vector space over K.
   Thus Hom(K,A,M,N) is a module over K over K.
  qed.
  For all modules L,N over A over K and all f < Hom(K,A,L,N) :
  (f is a modulehom over A over K from L to N).
  Let us show that for all N1,N2 < Mod(K,A) and all f << Mod(K,A)(N1,N2) :
  F(f) << Mod(K,K)(F(N1),F(N2)).
   Let N1,N2 < Mod(K,A) and f << Mod(K,A)(N1,N2).
   f < Hom(K,A,N1,N2) (by ModMor).
   K is a field.
   f is a modulehom over A over K from N1 to N2.
   F(N1) = Hom(K,A,M,N1).
   F(N2) = Hom(K,A,M,N2).
   Let us show that F(f) is a modulehom over K over K from Hom(K,A,M,N1) to Hom(K,A,M,N2).
    F(f) = Hom(K,A,M,f).
    Let us show that Hom(K,A,M,f) is a map from |Hom(K,A,M,N1)| to |Hom(K,A,M,N2)|.
     Hom(K,A,M,f) is a map (by HomFun).
     Dmn(Hom(K,A,M,f)) = |Hom(K,A,M,N1)| (by HomFun).
     Let us show that for all g < Hom(K,A,M,N1) : Hom(K,A,M,f)(g) < Hom(K,A,M,N2).
      Let g < Hom(K,A,M,N1).
      Hom(K,A,M,f)(g) = f*g (by HomFun).
      Let us show that f*g < Hom(K,A,M,N2).
       M,N1,N2 < Mod(K,A).
       g << Mod(K,A)(M,N1) (by ModMor).
       f << Mod(K,A)(N1,N2) (by ModMor).
       Mod(K,A) is a category.
       Thus f*g << Mod(K,A)(M,N2) (by Category).
       Therefore the thesis (by ModMor).
      qed.
     qed.
    qed.
    For all g < Hom(K,A,M,N1) : Hom(K,A,M,f)(g) = f*g (by HomFun).
    Let us show that for all g,h < Hom(K,A,M,N1) :
    F(f)(g +{Hom(K,A,M,N1)} h) = F(f)(g) +{Hom(K,A,M,N2)} F(f)(h).
     Let g,h < Hom(K,A,M,N1).
     Hom(K,A,M,N1) is a vector space over K.
     g +{Hom(K,A,M,N1)} h < Hom(K,A,M,N1) (by VectorSpace).
     F(f)(g +{Hom(K,A,M,N1)} h) = f*(g +{Hom(K,A,M,N1)} h) (by HomFun).
     F(f)(g) = f*g.
     F(f)(h) = f*h.
     M,N1 are modules over A over K.
     Let us show that f*(g +{Hom(K,A,M,N1)} h) = (f*g) +{Hom(K,A,M,N2)} (f*h).
      f*(g +{Hom(K,A,M,N1)} h) is a map.
      Let us show that (f*g) +{Hom(K,A,M,N2)} (f*h) is a map.
       f*g, f*h < Hom(K,A,M,N2).
       K is a field.
       M,N2 are modules over A over K.
       Hom(K,A,M,N2) is a vector space over K.
       (f*g) +{Hom(K,A,M,N2)} (f*h) < Hom(K,A,M,N2) (by VectorSpace).      
      qed.
      Let us show that Dmn(f*(g +{Hom(K,A,M,N1)} h)) = |M|.
       g +{Hom(K,A,M,N1)} h < Hom(K,A,M,N1).
       K is a field.
       g +{Hom(K,A,M,N1)} h is a modulehom over A over K from M to N1.
       g +{Hom(K,A,M,N1)} h is from |M| to |N1|.
       qed.
      Let us show that Dmn((f*g) +{Hom(K,A,M,N2)} (f*h)) = |M|.
       f*g < Hom(K,A,M,N2).
       f*h < Hom(K,A,M,N2).
       Hom(K,A,M,N2) is a vector space over K.
       (f*g) +{Hom(K,A,M,N2)} (f*h) < Hom(K,A,M,N2) (by VectorSpace).
       (f*g) +{Hom(K,A,M,N2)} (f*h) is a modulehom over A over K from M to N2.
      qed.
      Let us show that for all x < M : (f*(g +{Hom(K,A,M,N1)} h))(x)
                                       = ((f*g) +{Hom(K,A,M,N2)} (f*h))(x).
       Let x < M.
       f and g +{Hom(K,A,M,N1)} h are maps.
       (f*(g +{Hom(K,A,M,N1)} h))(x) = f((g +{Hom(K,A,M,N1)} h)(x)).
       M,N1 are modules over A over K.
       g,h < Hom(K,A,M,N1).
       (g +{Hom(K,A,M,N1)} h)(x) = g(x) +{N1} h(x) (by ModuleHomAdd).
       f((g +{Hom(K,A,M,N1)} h)(x)) = f(g(x) +{N1} h(x)).
       Let us show that f(g(x) +{N1} h(x)) = f(g(x)) +{N2} f(h(x)).
        f is a modulehom over A over K from N1 to N2.
        g,h are modulehoms over A over K from M to N1.
        g,h are from |M| to |N1|.
        g(x),h(x) < N1.
        Therefore the thesis (by ModuleHom).
       qed.
       f(g(x)) +{N2} f(h(x)) = (f*g)(x) +{N2} (f*h)(x).
       Let us show that (f*g)(x) +{N2} (f*h)(x) = ((f*g) +{Hom(K,A,M,N2)} (f*h))(x).
        M,N2 are modules over A over K.
        f*g,f*h < Hom(K,A,M,N2).
        ((f*g) +{Hom(K,A,M,N2)} (f*h))(x) = (f*g)(x) +{N2} (f*h)(x) (by ModuleHomAdd).
       qed.
      qed.
      Therefore the thesis (by MapExt).
     qed.
    qed.
    Let us show that for all a < K and all g < Hom(K,A,M,N1) :
    F(f)(a @@{Hom(K,A,M,N1)} g) = a @@{Hom(K,A,M,N2)} F(f)(g).
     Let a < K and g < Hom(K,A,M,N1).
     Hom(K,A,M,N1) is a vector space over K.
     a @@{Hom(K,A,M,N1)} g = a @{Hom(K,A,M,N1)} g.
     a @{Hom(K,A,M,N1)} g < Hom(K,A,M,N1) (by VectorSpace).
     F(f)(a @{Hom(K,A,M,N1)} g) = f*(a @{Hom(K,A,M,N1)} g) (by HomFun).
     F(f)(g) = f*g.
     f*g < Hom(K,A,M,N2).
     Let us show that f*(a @{Hom(K,A,M,N1)} g) = a @{Hom(K,A,M,N2)} (f*g).
      f*(a @{Hom(K,A,M,N1)} g) < Hom(K,A,M,N2).
      f*(a @{Hom(K,A,M,N1)} g) is a map.
      f*(a @{Hom(K,A,M,N1)} g) is a modulehom over A over K from M to N2.
      Dmn(f*(a @{Hom(K,A,M,N1)} g)) = |M|.
      Hom(K,A,M,N2) is a vector space over K.
      a @{Hom(K,A,M,N2)} (f*g) < Hom(K,A,M,N2) (by VectorSpace).
      a @{Hom(K,A,M,N2)} (f*g) is a map.
      a @{Hom(K,A,M,N2)} (f*g) is a modulehom over A over K from M to N2.
      Dmn(a @{Hom(K,A,M,N2)} (f*g)) = |M|.
      Let us show that for all x < M: (f*(a @{Hom(K,A,M,N1)} g))(x) = (a @{Hom(K,A,M,N2)} (f*g))(x).
       Let x < M.
       f and a @{Hom(K,A,M,N1)} g are maps.
       (f*(a @{Hom(K,A,M,N1)} g))(x) = f((a @{Hom(K,A,M,N1)} g)(x)).
       Let us show that (a @{Hom(K,A,M,N1)} g)(x) = a @{N1} g(x).
        M,N1 are modules over A over K.
        a < K.
        g < Hom(K,A,M,N1).
        x < M.
        Therefore the thesis (by ModuleHomSmul).
       qed.
       f((a @{Hom(K,A,M,N1)} g)(x)) = f(a @{N1} g(x)).
       Let us show that f(a @{N1} g(x)) = a @{N2} f(g(x)).
        K is a field.
        Hom(K,N1,N2) is a vector space over K.
        Hom(K,A,N1,N2) is a subspace of Hom(K,N1,N2) over K (by ModuleHomSubspace).
        |Hom(K,A,N1,N2)| is a subset of |Hom(K,N1,N2)|.
        f < Hom(K,A,N1,N2).     
        f < Hom(K,N1,N2).
        f is linear over K from N1 to N2.
        g is from |M| to |N1|.
        g(x) < N1.
        Therefore the thesis (by Homomorphism).
       qed.
       a @{N2} f(g(x)) = a @{N2} (f*g)(x).
       Let us show that a @{N2} (f*g)(x) = (a @{Hom(K,A,M,N2)} (f*g))(x).
        K is a field.
        M,N2 are modules over A over K.
        a < K.
        f*g < Hom(K,A,M,N2).
        x < M.
        Therefore the thesis (by ModuleHomSmul).
       qed.
      qed.
      Therefore the thesis (by MapExt).
     qed.
     a @{Hom(K,A,M,N2)} (f*g) = a @@{Hom(K,A,M,N2)} (f*g).
    qed.
   qed.
   K is a field.
   K is an algebra over K.
   F(N1),F(N2) are modules over K over K.
   Let us show that F(f) < Hom(K,K,F(N1),F(N2)).
    |Hom(K,K,F(N1),F(N2))| is the set of modulehoms over K over K from F(N1) to F(N2).
   qed.
   |Hom(K,K,F(N1),F(N2))| = Mod(K,K)(F(N1),F(N2)) (by ModMor).
  qed.
 
  Let us show that for all N < Mod(K,A) : F(1{N,Mod(K,A)}) = 1{F(N),Mod(K,K)}.
   Let N < Mod(K,A).
   K is a field.
   A is an algebra over K.
   N is a module over A over K.
   M is a module over A over K.
   F(N) = Hom(K,A,M,N).
   1{F(N),Mod(K,K)} = id{|Hom(K,A,M,N)|}.
   F(1{N,Mod(K,A)}) = Hom(K,A,M,id{|N|}).
   Let us show that Hom(K,A,M,id{|N|}) = id{|Hom(K,A,M,N)|}.
    id{|N|} = 1{N,Mod(K,A)}.
    id{|N|} < Hom(K,A,N,N).
    id{|N|} is a modulehom over A over K from N to N.
    Hom(K,A,M,id{|N|}) is a map.
    id{|Hom(K,A,M,N)|} is a map.
    Dmn(Hom(K,A,M,id{|N|})) = |Hom(K,A,M,N)|.
    Dmn(id{|Hom(K,A,M,N)|}) = |Hom(K,A,M,N)|.
    Let us show that for all g < Hom(K,A,M,N) : Hom(K,A,M,id{|N|})(g) = id{|Hom(K,A,M,N)|}(g).
     Let g < Hom(K,A,M,N).
     Hom(K,A,M,id{|N|})(g) = id{|N|}*g (by HomFun).
     Let us show that id{|N|}*g = g.
      g is a modulehom over A over K from M to N.
      g is from |M| to |N|.
      id{|N|} and g are composable.
      id{|N|}*g = g.
     qed.
     g = id{|Hom(K,A,M,N)|}(g).
    qed.
    Therefore the thesis (by MapExt).
   qed.
   Therefore F(1{N,Mod(K,A)}) = id{|Hom(K,A,M,N)|} (by MapExt).
  Qed.
 
  Let us show that for all N1,N2,N3 < Mod(K,A) and all f << Mod(K,A)(N1,N2)
  and all g << Mod(K,A)(N2,N3) : F(g*f) = F(g)*F(f).
   Let N1,N2,N3 < Mod(K,A). Let f << Mod(K,A)(N1,N2). Let g << Mod(K,A)(N2,N3).
   K is a field.
   A is an algebra over K.
   Ob{Mod(K,A)} is the set of modules over A over K (by ModOb).
   N1,N2,N3 are modules over A over K.
   g*f << Mod(K,A)(N1,N3) (by Category).
   F(g*f) << Mod(K,K)(F(N1),F(N3)) (by Functor).
   K is a field.
   F(N1),F(N3) are modules over K over K.
   F(g*f) < Hom(K,K,F(N1),F(N3)) (by ModMor).
   Let us show that F(g*f) is a modulehom over K over K from F(N1) to F(N3).
    |Hom(K,K,F(N1),F(N3))| is the set of modulehoms over K over K from F(N1) to F(N3).
   qed.
   F(g*f) is a map.
   Dmn(F(g*f)) = |F(N1)|.
   Let us show that F(g)*F(f) << Mod(K,K)(F(N1),F(N3)).
    Mod(K,K) is a category.
    F(N1),F(N2),F(N3) < Mod(K,K).
    F(f) << Mod(K,K)(F(N1),F(N2)).
    F(g) << Mod(K,K)(F(N2),F(N3)).
    Therefore the thesis (by Category).
   qed.
   F(g)*F(f) < Hom(K,K,F(N1),F(N3)) (by ModMor).
   F(g)*F(f) is a modulehom over K over K from F(N1) to F(N3).
   F(g)*F(f) is a map.
   Dmn(F(g)*F(f)) = |F(N1)|.
   Let us show that for all h < F(N1) : F(g*f)(h) = (F(g)*F(f))(h).
    Let h < F(N1).
    F(N1) = Hom(K,A,M,N1).
    h < Hom(K,A,M,N1).
    Let us show that F(g*f)(h) = (g*f)*h.
     N1,N3 are modules over A over K.
     g*f << Mod(K,A)(N1,N3).
     g*f < Hom(K,A,N1,N3) (by ModMor).
     For all i < Hom(K,A,M,N1) : Hom(K,A,M,g*f)(i) = (g*f)*i (by HomFun).
    qed.
    Let us show that (F(g)*F(f))(h) = g*(f*h).
     Let us show that F(f) is a map.
      F(f) << Mod(K,K)(F(N1),F(N2)).
      F(f) < Hom(K,K,F(N1),F(N2)) (by ModMor).
      F(f) is a modulehom over K over K from F(N1) to F(N2).
     qed.
     Let us show that F(g) is a map.
      F(g) << Mod(K,K)(F(N2),F(N3)).
      F(g) < Hom(K,K,F(N2),F(N3)) (by ModMor).
      F(g) is a modulehom over K over K from F(N2) to F(N3).
     qed.
     (F(g)*F(f))(h) = F(g)(F(f)(h)).
     N1,N2 are modules over A over K.
     f < Hom(K,A,N1,N2) (by ModMor).
     For all i < Hom(K,A,M,N1) : Hom(K,A,M,f)(i) = f*i (by HomFun).
     F(f)(h) = f*h.
     f*h < Hom(K,A,M,N2) (by ModuleHomComp).
     N2,N3 are modules over A over K.
     g < Hom(K,A,N2,N3) (by ModMor).
     For all i < Hom(K,A,M,N2) : Hom(K,A,M,g)(i) = g*i (by HomFun).
     F(g)(f*h) = g*(f*h).
    qed.
    Let us show that (g*f)*h = g*(f*h).   
     h is a modulehom over A over K from M to N1.
     f < Hom(K,A,N1,N2) (by ModMor).
     f is a modulehom over A over K from N1 to N2.
      g < Hom(K,A,N2,N3) (by ModMor).
     g is a modulehom over A over K from N2 to N3.
     h : |M|  -> |N1|.
     f : |N1| -> |N2|.
     g : |N2| -> |N3|.
    qed.
   qed.
  qed.
 qed.
Qed.


Axiom HomIsContraFunctor. Let A be an algebra over K. Let N be a module over A over K.
 Hom(K,A,-,N) is a contravariant functor from Mod(K,A) to Mod(K,K).
# The proof is very similar.

# Up to here (including all necessary proofs): 5:56 minutes.