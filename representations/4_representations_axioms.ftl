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

Axiom. Let A be an algebra over K. Mod(K,A) is a category.


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

Axiom. Let C be a category. id is a covariant functor from C to C.


Axiom. Let K,A,x,y be objects. Hom(K,A,x,-)(y) = Hom(K,A,x,y).
Axiom. Let K,A,x,y be objects. Hom(K,A,-,y)(x) = Hom(K,A,x,y).

Axiom. Let A be an algebra over K. Let M,N1,N2 be modules over A over K.
 Let f be a modulehom over A over K from N1 to N2. Hom(K,A,M,f) is a map F such that
 Dmn(F) = |Hom(K,A,M,N1)| and for all g < Hom(K,A,M,N1) : F(g) = f*g.

Axiom. Let A be an algebra over K. Let M1,M2,N be modules over A over K.
 Let f be a modulehom over A over K from M1 to M2. Hom(K,A,f,N) is a map F such that
 Dmn(F) = |Hom(K,A,M1,N)| and for all g < Hom(K,A,M1,N) : F(g) = g*f.

Axiom. Let A be an algebra over K. Let M be a module over A over K.
 Hom(K,A,M,-) is a covariant functor from Mod(K,A) to Mod(K,K).

Axiom. Let A be an algebra over K. Let N be a module over A over K.
 Hom(K,A,-,N) is a contravariant functor from Mod(K,A) to Mod(K,K).


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


Axiom. Let A be an algebra over K. Let M1,M2 be modules over A over K. Let f be a modulehom over A
 over K from M1 to M2. Hom(K,A,f,-) is a covariant natural transformation
 from Hom(K,A,M2,-) to Hom(K,A,M1,-) over Mod(K,A) to Mod(K,K).

Axiom. Let A be an algebra over K. Let N1,N2 be modules over A over K. Let f be a modulehom over A
 over K from N1 to N2. Hom(K,A,-,f) is a contravariant natural transformation
 from Hom(K,A,-,N1) to Hom(K,A,-,N2) over Mod(K,A) to Mod(K,K).