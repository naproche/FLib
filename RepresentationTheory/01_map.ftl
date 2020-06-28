[read RepresentationTheory/00_introduction.ftl]

Definition. Let f,A,B be objects.
 f is from A to B iff Dmn(f) = A and for all x << A : f(x) << B.

Definition. Let f be an object.
 f is injective iff (for all x,y << Dmn(f) : (f(x) = f(y) => x = y)).

Definition. Let f,B be objects.
 f is surjective onto B iff for all y << B there is an x << Dmn(f) such that f(x) = y.

Definition. Let f,A,B be objects.
 f is bijective from A to B iff (f is from A to B and f is injective and f is surjective onto B).

Signature. A map is a notion.

Let f:A->B stand for (f is a map from A to B).

Axiom MapExt. Let f,g be maps.
 If Dmn(f) = Dmn(g) and (for all x <<  Dmn(f) : f(x) = g(x)) then f = g.