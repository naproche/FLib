[read representations/1_linear_algebra_axioms.ftl]

Let K denote a field.

# 1.1 K-algebras

Definition Algebra. An algebra over K is an object A such that
     (A is a vector space over K)
 and (A is a ring)
 and (for all x < K and all a,b < A : x @{A} (a *{A} b) = (x @{A} a) *{A} b = a *{A} (x @{A} b)).

Axiom. K is an algebra over K.

Axiom. Let V be a vector space over K. Then End(K,V) is an algebra over K.


# 1.2 K-algebra homomorphisms

Definition. Let A,B be algebras over K.
 An algebrahom over K from A to B is a map f such that
     (f is linear over K from A to B)
 and (for all a,b < A : f(a *{A} b) = f(a) *{B} f(b))
 and (f(1{A}) = 1{B}).

Axiom. Let A be an algebra over K. Then id{|A|} is an algebrahom over K from A to A.


# 1.3 representations and A-modules

Definition. Let A,V be objects. A representation of A in V over K is an object p such that
     (A is an algebra over K)
 and (V is a vector space over K)
 and (p is an algebrahom over K from A to End(K,V)).

Let rep(p,K,A,V) stand for (A is an algebra over K and V is a vector space over K
                            and p is a representation of A in V over K).

Definition. Let A be an object. A module over A over K is an object V such that
     (A is an algebra over K)
 and (V is a vector space over K)
 and (for all a < A and all v < V : a @@{V} v < V)
 and (for all a < A and all v,w < V :             a @@{V} (v +{V} w) = (a @@{V} v) +{V} (a @@{V} w))
 and (for all x < K and all a < A and all v < V : a @@{V} (x @{V} v) = x @{V} (a @@{V} v))
 and (for all a,b < A and all v < V :             (a +{A} b) @@{V} v = (a @@{V} v) +{V} (b @@{V} v))
 and (for all x < K and all a < A and all v < V : (x @{A} a) @@{V} v = x @{V} (a @@{V} v))
 and (for all a,b < A and all v < V :             (a *{A} b) @@{V} v = a @@{V} (b @@{V} v))
 and (for all v < V :                                   1{A} @@{V} v = v).

Axiom. Let V be a vector space over K. Let x < K and v < V. x @@{V} v = x @{V} v.

Axiom. Let V be a vector space over K. K is an algebra over K and V is a module over K over K.


# 1.3.1 every representation gives a module

Axiom. Let rep(p,K,A,V).  |rep2mod(p,K,A,V)| = |V|.
Axiom. Let rep(p,K,A,V). 0{rep2mod(p,K,A,V)} = 0{V}.
Axiom. Let rep(p,K,A,V). For all v,w < V :              v +{rep2mod(p,K,A,V)} w = v +{V} w.
Axiom. Let rep(p,K,A,V). For all v < V :                  ~{rep2mod(p,K,A,V)} v = ~{V} v.
Axiom. Let rep(p,K,A,V). For all x < K and all v < V :  x @{rep2mod(p,K,A,V)} v = x @{V} v.
Axiom. Let rep(p,K,A,V). For all a < A and all v < V : a @@{rep2mod(p,K,A,V)} v = p(a)(v).

Axiom. Let rep(p,K,A,V). rep2mod(p,K,A,V) is a module over A over K.


# 1.3.2 every module gives a representation

Axiom. Let A be an algebra over K. Let V be a module over A over K.
 mod2rep(K,A,V) is a map p such that Dmn(p) = |A| and for all a < A :
 (p(a) is a map such that Dmn(p(a)) = |V| and for all v < V : p(a)(v) = a @@{V} v).

Axiom. Let A be an algebra over K. Let V be a module over A over K.
 Then mod2rep(K,A,V) is a representation of A in V over K.
