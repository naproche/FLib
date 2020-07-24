[read RepresentationTheory/01_map.ftl]

Axiom MapId. Let A be a set.
 id{A} is a map h such that Dmn(h) = A and for all a << A : h(a) = a.

Axiom. Let f,g be maps. f*g is a map.
Axiom. Let f,g be maps. Dmn(f*g) = Dmn(g).
Axiom. Let f,g be maps. Let x be an object. (f*g)(x) = f(g(x)).

Definition. Let f,g be objects.
 f and g are composable iff for all x << Dmn(g) we have g(x) << Dmn(f).

Theorem. Let f be a map. Let A be a set. Let id{A} and f be composable. Then id{A}*f = f.
Proof.
 For all x << Dmn(f) : (id{A}*f)(x) = f(x).
Qed.

Theorem. Let f be a map. Let A be a set. Let Dmn(f) = A. Then f*id{A} = f.
Proof.
 For all x << A : (f*id{A})(x) = f(x).
Qed.

Theorem CompFromTo. Let A,B,C be objects. Let g:A->B. Let f:B->C. Then f*g : A -> C.
Proof.
 For all x << A : (f*g)(x) << C.
Qed.

Theorem. Let A,B,C,D be objects. Let h:A->B. Let g:B->C. Let f:C->D. Then (f*g)*h : A -> D.
Proof.
 (f*g) : B -> D.
Qed.

Theorem. Let A,B,C,D be objects. Let h:A->B. Let g:B->C. Let f:C->D. Then f*(g*h) : A->D.

Theorem ThreeComp. Let A,B,C,D be objects. Let h:A->B. Let g:B->C. Let f:C->D. Then (f*g)*h = f*(g*h).
Proof.
 Dmn((f*g)*h) = A.
 Dmn(f*(g*h)) = A.
 For all x << A : ((f*g)*h)(x) = f(g(h(x))) = (f*(g*h))(x).
Qed.

Axiom. Let f be a map. f^(-1) is a map.
Axiom InverseMap. Let f be a map. Let A,B be sets. Let f be bijective from A to B. Then f^(-1) is a map
 from B to A and (for all x << A : f^(-1)(f(x)) = x) and (for all y << B : f(f^(-1)(y)) = y).