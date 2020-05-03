[read linear_algebra_ftl/A_Props/011A_homomorphisms.ftl]
[read linear_algebra_ftl/A_Props/100A_ring.ftl]

Let K denote a field.

Definition. Let V be a vector space over K. End(K,V) is Hom(K,V,V).

Definition. Let V be a vector space over K.
FuncComp(K,V) is a function such that (Dom(FuncComp(K,V)) = Prod(|End(K,V)|,|End(K,V)|))
  and (for all f,g < End(K,V) FuncComp(K,V)[(f,g)] = f*g).


Axiom. Let V be a vector space over K. (End(K,V) has one,mul).
Axiom. Let V be a vector space over K. 1{End(K,V)}   = id{|V|}.
Axiom. Let V be a vector space over K. mul{End(K,V)} = FuncComp(K,V).
