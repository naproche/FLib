[read RepresentationTheory/19_category.ftl]

Definition CoFunctor. Let C,D be objects. A covariant functor from C to D is an object F such that
     (C and D are categories)
 and (for all X << Ob{C} : F(X) << Ob{D})
 and (for all X,Y << Ob{C} and all f << C(X,Y) : F(f) << D(F(X),F(Y)))
 and (for all X << Ob{C} : F(1{X,C}) = 1{F(X),D})
 and (for all X,Y,Z << Ob{C} and all f << C(X,Y) and all g << C(Y,Z) : F(g*f) = F(g)*F(f)).

Definition ContraFunctor. Let C,D be objects. A contravariant functor from C to D is an object F such that
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