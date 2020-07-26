[read RepresentationTheory/17_functor.ftl]

Definition. Let C,D,F,G be objects.
 A natural transformation from F to G over C to D is an object n such that
     (F,G are functors from C to D)
 and (for all X << Ob{C} : n(X) << D(F(X),G(X)))
 and (for all X,Y << Ob{C} and all h << C(X,Y) : G(h)*n(X) = n(Y)*F(h)).

Definition. Let C,D,F,G be objects.
 A contravariant natural transformation from F to G over C to D is an object n such that
     (F,G are contravariant functors from C to D)
 and (for all X << Ob{C} : n(X) << D(F(X),G(X)))
 and (for all X,Y << Ob{C} and all h << C(X,Y) : G(h)*n(Y) = n(X)*F(h)).