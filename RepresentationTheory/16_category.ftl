[read RepresentationTheory/00_introduction.ftl]

Let Ob{C} stand for |C|.

Definition Category. A category is an object C such that 
     (Ob{C} is a set)
 and (for all X,Y,Z << Ob{C} and all f << C(X,Y) and all g << C(Y,Z) : g*f << C(X,Z))
 and (for all X << Ob{C} : 1{X,C} << C(X,X))
 and (for all X,Y << Ob{C} and all f << C(X,Y) : f*1{X,C} = f)
 and (for all X,Y << Ob{C} and all f << C(Y,X) : 1{X,C}*f = f)
 and (for all W,X,Y,Z << Ob{C} and all f << C(W,X) and all g << C(X,Y) and all h << C(Y,Z) : 
      h*(g*f) = (h*g)*f).