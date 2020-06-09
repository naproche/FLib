[read representations/3_representations_axioms.ftl]

Let K denote a field.

# 1.5 categories

Let Ob{C} stand for |C|.

Definition Category. A category is an object C such that 
     (Ob{C} is a set)
 and (for all X,Y,Z << Ob{C} and all f << C(X,Y) and all g << C(Y,Z) : g*f << C(X,Z))
 and (for all X << Ob{C} : 1{X,C} << C(X,X))
 and (for all X,Y << Ob{C} and all f << C(X,Y) : f*1{X,C} = f)
 and (for all X,Y << Ob{C} and all f << C(Y,X) : 1{X,C}*f = f)
 and (for all W,X,Y,Z << Ob{C} and all f << C(W,X) and all g << C(X,Y) and all h << C(Y,Z) : 
      h*(g*f) = (h*g)*f).

Axiom ModOb.  Let A be an algebra over K. Ob{Mod(K,A)} is the set of modules over A over K.
Axiom ModMor. Let A be an algebra over K. Let M,N << Ob{Mod(K,A)}. Mod(K,A)(M,N) = |Hom(K,A,M,N)|.
Axiom ModId.  Let A be an algebra over K. Let M << Ob{Mod(K,A)}.  1{M,Mod(K,A)} = id{|M|}.

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
   Let us show that g*f is a modulehom over A over K from L to N.
    f < Hom(K,A,L,M) (by ModMor).
    f is a modulehom over A over K from L to M.
    g < Hom(K,A,M,N) (by ModMor).
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


# 1.6 functors

# The setup for the definitions of functors introduces C and D only as objects.
# This helps with the translation of statements about functors.

Definition. Let C,D be objects. A covariant functor from C to D is an object F such that
     (C and D are categories)
 and (for all X << Ob{C} : F(X) << Ob{D})
 and (for all X,Y << Ob{C} and all f << C(X,Y) : F(f) << D(F(X),F(Y)))
 and (for all X << Ob{C} : F(1{X,C}) = 1{F(X),D})
 and (for all X,Y,Z << Ob{C} and all f << C(X,Y) and all g << C(Y,Z) : F(g*f) = F(g)*F(f)).

Definition. Let C,D be objects. A contravariant functor from C to D is an object F such that
     (C and D are categories)
 and (for all X << Ob{C} : F(X) << Ob{D})
 and (for all X,Y << Ob{C} and all f << C(X,Y) : F(f) << D(F(Y),F(X)))
 and (for all X << Ob{C} : F(1{X,C}) = 1{F(X),D})
 and (for all X,Y,Z << Ob{C} and all f << C(X,Y) and all g << C(Y,Z) : F(g*f) = F(f)*F(g)).

Axiom. Let x be an object. id(x) = x.

Theorem. Let C be a category. id is a covariant functor from C to C.
Proof.
 For all X << Ob{C} : id(X) << Ob{C}.
 For all X,Y << Ob{C} and all f << C(X,Y) : id(f) << C(id(X),id(Y)).
 For all X << Ob{C} : id(1{X,C}) = 1{id(X),C}.
 For all X,Y,Z << Ob{C} and all f << C(X,Y) and all g << C(Y,Z) : id(g*f) = id(g)*id(f).
Qed.


Axiom. Let K,A,x,y be objects. Hom(K,A,x,-)(y) = Hom(K,A,x,y).
Axiom. Let K,A,x,y be objects. Hom(K,A,-,y)(x) = Hom(K,A,x,y).

Axiom. Let A be an algebra over K. Let M,N1,N2 be modules over A over K.
 Let f be a modulehom over A over K from N1 to N2. Hom(K,A,M,f) is a map F such that
 Dmn(F) = |Hom(K,A,M,N1)| and for all g < Hom(K,A,M,N1) : F(g) = f*g.

Axiom. Let A be an algebra over K. Let M1,M2,N be modules over A over K.
 Let f be a modulehom over A over K from M1 to M2. Hom(K,A,f,N) is a map F such that
 Dmn(F) = |Hom(K,A,M1,N)| and for all g < Hom(K,A,M1,N) : F(g) = g*f.

Theorem. Let A be an algebra over K. Let M be a module over A over K.
 Hom(K,A,M,-) is a covariant functor from Mod(K,A) to Mod(K,K).
Proof.

Qed.

Theorem. Let A be an algebra over K. Let N be a module over A over K.
 Hom(K,A,-,N) is a contravariant functor from Mod(K,A) to Mod(K,K).
Proof.
 Contradiction.
Qed.


# 1.7 natural transformations

Definition. Let C,D,F,G be objects.
 A covariant natural transformation from F to G over C to D is an object n such that
     (F,G are covariant functors from C to D)
 and (for all X << Ob{C} : n(X) << D(F(X),G(X)))
 and (for all X,Y << Ob{C} and all h << C(X,Y) : G(h)*n(X) = n(Y)*F(h)).

Definition. Let C,D,F,G be objects.
 A contravariant natural transformation from F to G over C to D is an object n such that
     (F,G are contravariant functors from C to D)
 and (for all X << Ob{C} : n(X) << D(F(X),G(X)))
 and (for all X,Y << Ob{C} and all h << C(X,Y) : G(h)*n(Y) = n(X)*F(h)).


Theorem. Let A be an algebra over K. Let M1,M2 be modules over A over K. Let f be a modulehom over A
 over K from M1 to M2. Hom(K,A,f,-) is a covariant natural transformation
 from Hom(K,A,M2,-) to Hom(K,A,M1,-) over Mod(K,A) to Mod(K,K).
Proof.

Qed.

Theorem. Let A be an algebra over K. Let N1,N2 be modules over A over K. Let f be a modulehom over A
 over K from N1 to N2. Hom(K,A,-,f) is a contravariant natural transformation
 from Hom(K,A,-,N1) to Hom(K,A,-,N2) over Mod(K,A) to Mod(K,K).
Proof.

Qed.
