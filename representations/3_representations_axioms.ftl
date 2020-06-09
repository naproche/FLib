[read representations/2_representations_axioms.ftl]

Let K denote a field.

# 1.4 A-module homomorphisms

Definition ModuleHom. Let A,M,N be objects.
 A modulehom over A over K from M to N is a map f such that
     (A is an algebra over K)
 and (M,N are modules over A over K)
 and (f is from |M| to |N|)
 and (for all x,y < M             : f(x +{M} y) = f(x) +{N} f(y))
 and (for all a < A and all x < M : f(a @@{M} x) = a @@{N} f(x)).

Axiom. Let A be an algebra over K. Let M,N be modules over A over K.
 |Hom(K,A,M,N)| is the set of maps f such that f is a modulehom over A over K from M to N.

Axiom. Let A be an algebra over K. Let M,N be modules over A over K.
 Hom(K,M,N) is a vector space over K and Hom(K,A,M,N) is a subspace of Hom(K,M,N) over K.

Axiom. Let A be an algebra over K. Let M,N be modules over A over K.
 Hom(K,A,M,N) is a vector space over K.
