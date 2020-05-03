[read linear_algebra_ftl/A_Props/101A_unit_group.ftl]
[read linear_algebra_ftl/A_Props/102A_endomorphisms.ftl]

Let K denote a field.

Definition. Let V be a vector space over K. Aut(K,V) is Un(End(K,V)).


Let M,N denote sets.
Let f denote a function.

Definition. f is surjective onto N iff for all y << N there is an x << Dom(f) such that f[x] = y.

Definition. f is bijective from M to N
iff (f is from M to N and f is injective and f is surjective onto N).

Definition. Let V,W be vector spaces over K. An isomorphism over K from V to W is
a function f such that f < Hom(K,V,W) and f is bijective from |V| to |W|.


Signature. f^(-1) is a notion.

Axiom. Let f be bijective from M to N. Then f^(-1) is a function from N to M
and (for all x << M : f^(-1)[f[x]] = x) and (for all y << N : f[f^(-1)[y]] = y).