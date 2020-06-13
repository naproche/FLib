[read RepresentationTheory/20_functor.ftl]
[read RepresentationTheory/22_module_category.ftl]

Let K denote a field.

Axiom. Let K,A,x,y be objects. Hom(K,A,x,-)(y) = Hom(K,A,x,y).
Axiom. Let K,A,x,y be objects. Hom(K,A,-,y)(x) = Hom(K,A,x,y).

Axiom CoHomFun. Let A be an algebra over K. Let M,N1,N2 be modules over A over K.
 Let f be a modulehom over A over K from N1 to N2. Hom(K,A,M,f) is a map F such that
 Dmn(F) = |Hom(K,A,M,N1)| and for all g < Hom(K,A,M,N1) : F(g) = f*g.

Axiom ContraHomFun. Let A be an algebra over K. Let M1,M2,N be modules over A over K.
 Let f be a modulehom over A over K from M1 to M2. Hom(K,A,f,N) is a map F such that
 Dmn(F) = |Hom(K,A,M2,N)| and for all g < Hom(K,A,M2,N) : F(g) = g*f.

Theorem. Let A be an algebra over K. Let M be a module over A over K.
 Hom(K,A,M,-) is a covariant functor from Mod(K,A) to Mod(K,K).
Proof.
 Take F = Hom(K,A,M,-).
 Mod(K,A) and Mod(K,K) are categories.
 Let us show that for all N < Mod(K,A) : F(N) < Mod(K,K).
  Let N < Mod(K,A).
  N is a module over A over K.
  F(N) = Hom(K,A,M,N).
  Hom(K,A,M,N) is a vector space over K.
  Thus Hom(K,A,M,N) is a module over K over K.
 qed.

 Let us show that for all N1,N2 < Mod(K,A) and all f << Mod(K,A)(N1,N2) :
 F(f) << Mod(K,K)(F(N1),F(N2)).
  Let N1,N2 < Mod(K,A) and f << Mod(K,A)(N1,N2).
  f < Hom(K,A,N1,N2).
  f is a modulehom over A over K from N1 to N2.
  F(N1) = Hom(K,A,M,N1).
  F(N2) = Hom(K,A,M,N2).
  Let us show that F(f) is a modulehom over K over K from Hom(K,A,M,N1) to Hom(K,A,M,N2).
   F(f) = Hom(K,A,M,f).
   Let us show that Hom(K,A,M,f) is a map from |Hom(K,A,M,N1)| to |Hom(K,A,M,N2)|.
    Hom(K,A,M,f) is a map.
    Dmn(Hom(K,A,M,f)) = |Hom(K,A,M,N1)|.
    Let us show that for all g < Hom(K,A,M,N1) : Hom(K,A,M,f)(g) < Hom(K,A,M,N2).
     Let g < Hom(K,A,M,N1).
     Hom(K,A,M,f)(g) = f*g (by CoHomFun).
     Let us show that f*g < Hom(K,A,M,N2).
      M,N1,N2 < Mod(K,A).
      g << Mod(K,A)(M,N1) (by ModMor).
      f << Mod(K,A)(N1,N2) (by ModMor).
      Mod(K,A) is a category.
      Thus f*g << Mod(K,A)(M,N2).
     qed.
    qed.
   qed.
   Let us show that for all g,h < Hom(K,A,M,N1) :
   F(f)(g +{Hom(K,A,M,N1)} h) = F(f)(g) +{Hom(K,A,M,N2)} F(f)(h).
    Let g,h < Hom(K,A,M,N1).
    Hom(K,A,M,N1) is a vector space over K.
    g +{Hom(K,A,M,N1)} h < Hom(K,A,M,N1) (by VectorSpace).
    F(f)(g +{Hom(K,A,M,N1)} h) = f*(g +{Hom(K,A,M,N1)} h) (by CoHomFun).
    F(f)(g) = f*g.
    F(f)(h) = f*h.
    M,N1 are modules over A over K.
    Hom(K,M,N1) is a vector space over K.
    Hom(K,A,M,N1) is a subspace of Hom(K,M,N1) over K.
    sub(K,Hom(K,M,N1),Hom(K,A,M,N1)).
    g +{Hom(K,A,M,N1)} h = g +{Hom(K,M,N1)} h.
    M,N2 are modules over A over K.
    Hom(K,M,N2) is a vector space over K.
    Hom(K,A,M,N2) is a subspace of Hom(K,M,N2) over K.
    sub(K,Hom(K,M,N2),Hom(K,A,M,N2)).
    f*g < Hom(K,A,M,N2).
    f*h < Hom(K,A,M,N2).
    (f*g) +{Hom(K,A,M,N2)} (f*h) = (f*g) +{Hom(K,M,N2)} (f*h).
    Dmn(f*(g +{Hom(K,M,N1)} h)) = |M|.
    (f*g) +{Hom(K,M,N2)} (f*h) < Hom(K,M,N2) (by VectorSpace).
    Dmn((f*g) +{Hom(K,M,N2)} (f*h)) = |M|.
    Let us show that for all x < M : (f*(g +{Hom(K,M,N1)} h))(x) = ((f*g) +{Hom(K,M,N2)} (f*h))(x).
     Let x < M.
     f and g +{Hom(K,M,N1)} h are maps.
     (f*(g +{Hom(K,M,N1)} h))(x) = f((g +{Hom(K,M,N1)} h)(x)).
     M,N1 are vector spaces over K.
     g,h < Hom(K,M,N1).
     (g +{Hom(K,M,N1)} h)(x) = g(x) +{N1} h(x).
     f((g +{Hom(K,M,N1)} h)(x)) = f(g(x) +{N1} h(x)).
     Let us show that f(g(x) +{N1} h(x)) = f(g(x)) +{N2} f(h(x)).
      f is a modulehom over A over K from N1 to N2.
      g,h are from |M| to |N1|.
      g(x),h(x) < N1.
     qed.
     f(g(x)) +{N2} f(h(x)) = (f*g)(x) +{N2} (f*h)(x).
     Let us show that (f*g)(x) +{N2} (f*h)(x) = ((f*g) +{Hom(K,M,N2)} (f*h))(x).     
      f*g,f*h < Hom(K,M,N2).
      M,N2 are vector spaces over K.
     qed.
    qed.
   qed.
   Let us show that for all a < K and all g < Hom(K,A,M,N1) :
   F(f)(a @@{Hom(K,A,M,N1)} g) = a @@{Hom(K,A,M,N2)} F(f)(g).
    Let a < K and g < Hom(K,A,M,N1).
    Hom(K,A,M,N1) is a vector space over K.
    a @@{Hom(K,A,M,N1)} g = a @{Hom(K,A,M,N1)} g.
    a @{Hom(K,A,M,N1)} g < Hom(K,A,M,N1) (by VectorSpace).
    F(f)(a @{Hom(K,A,M,N1)} g) = f*(a @{Hom(K,A,M,N1)} g) (by CoHomFun).
    F(f)(g) = f*g.
    M,N1 are modules over A over K.
    Hom(K,M,N1) is a vector space over K.
    Hom(K,A,M,N1) is a subspace of Hom(K,M,N1) over K.
    sub(K,Hom(K,M,N1),Hom(K,A,M,N1)).
    a @{Hom(K,A,M,N1)} g = a @{Hom(K,M,N1)} g.
    M,N2 are modules over A over K.
    Hom(K,M,N2) is a vector space over K.
    Hom(K,A,M,N2) is a subspace of Hom(K,M,N2) over K.
    sub(K,Hom(K,M,N2),Hom(K,A,M,N2)).
    f*g < Hom(K,A,M,N2).
    a @{Hom(K,A,M,N2)} (f*g) = a @{Hom(K,M,N2)} (f*g).
    Let us show that f*(a @{Hom(K,M,N1)} g) = a @{Hom(K,M,N2)} (f*g)
     Dmn(f*(a @{Hom(K,M,N1)} g)) = |M|.
     Let us show that a @{Hom(K,M,N2)} (f*g) < Hom(K,M,N2).
      f*g < Hom(K,M,N2).
      Hom(K,M,N2) is a vector space over K.
     qed.
     Dmn(a @{Hom(K,M,N2)} (f*g)) = |M|.
     Let us show that for all x < M : (f*(a @{Hom(K,M,N1)} g))(x) = (a @{Hom(K,M,N2)} (f*g))(x).
      Let x < M.
      f and a @{Hom(K,M,N1)} g are maps.
      (f*(a @{Hom(K,M,N1)} g))(x) = f((a @{Hom(K,M,N1)} g)(x)).
      M,N1 are vector spaces over K.
      g < Hom(K,M,N1).
      (a @{Hom(K,M,N1)} g)(x) = a @{N1} g(x).
      f((a @{Hom(K,M,N1)} g)(x)) = f(a @{N1} g(x)).
      Let us show that f(a @{N1} g(x)) = a @{N2} f(g(x)).
       Hom(K,N1,N2) is a vector space over K.
       Hom(K,A,N1,N2) is a subspace of Hom(K,N1,N2) over K.      
       f < Hom(K,N1,N2).
       f is linear over K from N1 to N2.
       g is from |M| to |N1|.
       g(x) < N1.
      qed.
      a @{N2} f(g(x)) = a @{N2} (f*g)(x).
      f*g < Hom(K,M,N2).
      a @{N2} (f*g)(x) = (a @{Hom(K,M,N2)} (f*g))(x).
     qed.
    qed.
    a @{Hom(K,M,N2)} (f*g) = a @@{Hom(K,M,N2)} (f*g).
   qed.
  qed.
 qed.

# and (for all X << Ob{C} : F(1{X,C}) = 1{F(X),D})
# and (for all X,Y,Z << Ob{C} and all f << C(X,Y) and all g << C(Y,Z) : F(g*f) = F(g)*F(f)).
Qed.


Theorem. Let A be an algebra over K. Let N be a module over A over K.
 Hom(K,A,-,N) is a contravariant functor from Mod(K,A) to Mod(K,K).
Proof.
 # similar
Qed.