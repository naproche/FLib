[read RepresentationTheory/18_natural_transformation.ftl]

Axiom. Let x be an object. id(x) = x.

Theorem. Let C be a category. id is a functor from C to C.
Proof.
 For all X < C : id(X) < C.
 For all X,Y < C and all f << C(X,Y) : id(f) << C(id(X),id(Y)).
 For all X < C : id(1{X,C}) = 1{id(X),C}.
 For all X,Y,Z < C and all f << C(X,Y) and all g << C(Y,Z) : id(g*f) = id(g)*id(f).
Qed.

Axiom. Let F,G,B,C,D be objects. Assume F is a functor from B to C. Assume G is a functor from
 C to D. Then for all objects x : (G*F)(x) = G(F(x)).

Theorem. Let F,G,B,C,D be objects. Assume F is a functor from B to C. Assume G is a functor
 from C to D. Then G*F is a functor from B to D.
Proof.
 For all objects x : (G*F)(x) = G(F(x)).
 B,C,D are categories.
 For all X < B : (G*F)(X) = G(F(X)) < D.
 For all X,Y < B and all f << B(X,Y) : (G*F)(f) = G(F(f)) << D(G(F(X)),G(F(Y)))
                                                             = D((G*F)(X),(G*F)(Y)).
 For all X < B : (G*F)(1{X,B}) = G(F(1{X,B})) = G(1{F(X),C}) = 1{G(F(X)),D} = 1{(G*F)(X),D}.
 For all X,Y,Z < B and all f << B(X,Y) and all g << B(Y,Z) :
  (G*F)(g*f) = G(F(g*f)) = G(F(g)*F(f)) = G(F(g))*G(F(f)) = (G*F)(g)*(G*F)(f).
Qed.


Definition. Let C,X,Y be objects. An isomorphism from X to Y in C is an object f such that
     (C is a category and X,Y < C)
 and (f << C(X,Y))
 and (there exists g << C(Y,X) such that g*f = 1{X,C} and f*g = 1{Y,C}).

Definition. Let X,Y,C be objects. X and Y are isomorphic in C iff
     (C is a category and X,Y < C)
 and (there exist an isomorphism from X to Y in C).

Theorem. Let C be a category. Let X,Y < C.
 X and Y are isomorphic in C iff Y and X are isomorphic in C.
Proof.
 Let us show that (X and Y are isomorphic in C) => (Y and X are isomorphic in C).
  Assume X and Y are isomorphic in C.
  Take an isomorphism f from X to Y in C.
 qed.
 Let us show that (Y and X are isomorphic in C) => (X and Y are isomorphic in C).
  Assume Y and X are isomorphic in C.
  Take an isomorphism g from Y to X in C.
 qed. 
Qed.


Definition NaturalIso. Let C,D,F,G be objects.
 A natural isomorphism from F to G over C to D is an object alpha such that
     (alpha is a natural transformation from F to G over C to D)
 and (for all X < C : (alpha(X) is an isomorphism from F(X) to G(X) in D)).

Definition. Let F,C,D be objects. A quasiinverse of F between C and D is an object G such that
     (F is a functor from C to D)
 and (G is a functor from D to C)
 and (there exists a natural isomorphism from G*F to id over C to C)
 and (there exists a natural isomorphism from F*G to id over D to D).

Definition. Let C,D be objects. An equivalence from C to D is an object F such that there exists a
 quasiinverse of F between C and D.


Definition. Let F,C,D be objects. F is full from C to D iff
     (F is a functor from C to D)
 and (for all X,Y < C and all g << D(F(X),F(Y)) there exists f << C(X,Y) such that F(f) = g).

Definition. Let F,C,D be objects. F is faithful from C to D iff
     (F is a functor from C to D)
 and (for all X,Y < C and all f,g << C(X,Y) : (F(f) = F(g) => f = g)).

Definition. Let F,C,D be objects. F is dense from C to D iff
     (F is a functor from C to D)
 and (for all Y < D there exists X < C such that F(X) and Y are isomorphic in D).


Theorem. Let C,D be categories. Let F be an equivalence from C to D.
 Then F is full from C to D and F is faithful from C to D and F is dense from C to D.
Proof.
 Take an object G such that G is a quasiinverse of F between C and D.
 F is a functor from C to D.
 G is a functor from D to C.
 Take a natural isomorphism alpha from G*F to id over C to C.
 Take a natural isomorphism gamma from F*G to id over D to D.

 Let us show that F is dense from C to D.  
  Let us show that for all Y < D there exists X < C such that F(X) and Y are isomorphic in D.
   Let Y < D.
   Take X = G(Y).
   X < C.
   Let us show that Y and F(X) are isomorphic in D.
    gamma(Y) is an isomorphism from (F*G)(Y) to id(Y) in D (by NaturalIso).
    (F*G)(Y) = F(X).
   qed.
  qed.
 qed.

 Let us show that F is faithful from C to D.
  Let us show that for all X1,X2 < C and all f,g << C(X1,X2) : (F(f) = F(g) => f = g).
   Let X1,X2 < C. Let f,g << C(X1,X2).
   Assume F(f) = F(g).
   Let us show that f * alpha(X1) = g * alpha(X1).
    f * alpha(X1) = alpha(X2) * (G*F)(f).
    g * alpha(X1) = alpha(X2) * (G*F)(g).
    (G*F)(f) = (G*F)(g).
   qed.
   (G*F)(X1) < C.
   alpha(X1) << C((G*F)(X1), X1).
   Take beta << C(X1, (G*F)(X1)) such that alpha(X1) * beta = 1{X1,C}.
   f = f * 1{X1,C} = f * (alpha(X1) * beta) = (f * alpha(X1)) * beta (by Category).
   g = g * 1{X1,C} = g * (alpha(X1) * beta) = (g * alpha(X1)) * beta (by Category).
   Therefore f = g.
  qed.
 qed.

 Let us show that G is faithful from D to C.
  Let us show that for all Y1,Y2 < D and all f,g << D(Y1,Y2) : (G(f) = G(g) => f = g).
   Let Y1,Y2 < D. Let f,g << D(Y1,Y2).
   Assume G(f) = G(g).
   Let us show that f * gamma(Y1) = g * gamma(Y1).
    f * gamma(Y1) = gamma(Y2) * (F*G)(f).
    g * gamma(Y1) = gamma(Y2) * (F*G)(g).
    (F*G)(f) = (F*G)(g).
   qed.
   (F*G)(Y1) < D.
   gamma(Y1) << D((F*G)(Y1), Y1).
   Take beta << D(Y1, (F*G)(Y1)) such that gamma(Y1) * beta = 1{Y1,D}.
   f = f * 1{Y1,D} = f * (gamma(Y1) * beta) = (f * gamma(Y1)) * beta (by Category).
   g = g * 1{Y1,D} = g * (gamma(Y1) * beta) = (g * gamma(Y1)) * beta (by Category).
   Therefore f = g.
  qed.
 qed.

 Let us show that F is full from C to D.
  Let us show that for all X1,X2 < C and all g << D(F(X1),F(X2))
  there exists f << C(X1,X2) such that F(f) = g.
   Let X1,X2 < C. Let g << D(F(X1),F(X2)).
   Take beta << C(X1, (G*F)(X1)) such that beta * alpha(X1) = 1{(G*F)(X1),C}.
   Take delta << C(X2, (G*F)(X2)) such that delta * alpha(X2) = 1{(G*F)(X2),C}. 
   Take f = alpha(X2) * (G(g) * beta).
   G(g) << C(G(F(X1)),G(F(X2))) (by Functor).
   G(g) << C((G*F)(X1),(G*F)(X2)).
   alpha(X1) << C((G*F)(X1),X1).
   alpha(X2) << C((G*F)(X2),X2).
   f << C(X1,X2) (by Category).
   f * alpha(X1) = alpha(X2) * (G*F)(f).
   Let us show that G(F(f)) = G(g).
    (G*F)(f) << C((G*F)(X1),(G*F)(X2)).
    G(F(f)) = (G*F)(f) = 1{(G*F)(X2),C} * (G*F)(f) = (delta * alpha(X2)) * (G*F)(f).
    (delta * alpha(X2)) * (G*F)(f) = delta * (alpha(X2) * (G*F)(f)) (by Category).
    delta * (alpha(X2) * (G*F)(f)) = delta * (f * alpha(X1)).
    f * alpha(X1) = (alpha(X2) * (G(g) * beta)) * alpha(X1).
    G(g) * beta << C(X1, (G*F)(X2)) (by Category).
    (alpha(X2) * (G(g) * beta)) * alpha(X1) = alpha(X2) * ((G(g) * beta) * alpha(X1)) (by Category).
    (G(g) * beta) * alpha(X1) = G(g) * (beta * alpha(X1)) = G(g) * 1{(G*F)(X1),C}
    = G(g) (by Category).
    Therefore G(F(f)) = delta * (alpha(X2) * G(g)).
    delta * (alpha(X2) * G(g)) = (delta * alpha(X2)) * G(g) = 1{(G*F)(X2),C} * G(g)
    = G(g) (by Category).
   qed.
  qed.
 qed.
Qed.