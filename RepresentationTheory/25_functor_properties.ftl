[read RepresentationTheory/21_natural_transformation.ftl]

Axiom. Let x be an object. id(x) = x.

Theorem. Let C be a category. id is a functor from C to C.
Proof.
 For all X << Ob{C} : id(X) << Ob{C}.
 For all X,Y << Ob{C} and all f << C(X,Y) : id(f) << C(id(X),id(Y)).
 For all X << Ob{C} : id(1{X,C}) = 1{id(X),C}.
 For all X,Y,Z << Ob{C} and all f << C(X,Y) and all g << C(Y,Z) : id(g*f) = id(g)*id(f).
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

Definition. Let F,C,D be objects. A quasiinverse of F between C and D is an object G such that
     (F is a functor from C to D)
 and (G is a functor from D to C)
 and (there exists a natural transformation from G*F to id over C to C)
 and (there exists a natural transformation from F*G to id over D to D).

Definition. Let C,D be objects. An equivalence from C to D is an object F such that there exists a
 quasiinverse of F between C and D.

Definition. Let F,C,D be objects. F is full from C to D iff
     (F is a functor from C to D)
 and (for all X,Y << Ob{C} and all g << D(F(X),F(Y)) there exists f << C(X,Y) such that F(f) = g).

Definition. Let F,C,D be objects. F is faithful from C to D iff
     (F is a functor from C to D)
 and (for all X,Y << Ob{C} and all f,g << C(X,Y) : (F(X) = F(Y) => X = Y)).

Definition. Let X,Y,C be objects. X and Y are isomorphic in C iff
     (C is a category and X,Y << Ob{C})
 and (there exist f << C(X,Y) and g << C(Y,X) such that g*f = 1{X,C} and f*g = 1{Y,C}).

Theorem. Let C be a category. Let X,Y << Ob{C}.
 X and Y are isomorphic in C iff Y and X are isomorphic in C.

Definition. Let F,C,D be objects. F is dense from C to D iff
     (F is a functor from C to D)
 and (for all Y << Ob{D} there exists X << Ob{C} such that F(X) and Y are isomorphic in C).

Theorem. Let C,D be categories. Let F be a functor from C to D. F is an equivalence from C to D iff
 (F is full from C to D and F is faithful from C to D and F is dense from C to D).
Proof.
 [prove off]
Qed.