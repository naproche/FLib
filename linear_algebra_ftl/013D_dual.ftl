[read linear_algebra_ftl/A_Props/012A_field2VS.ftl]

Let K denote a field. 

# We assume this axiom for now.
Axiom Exi. Let V be a vector space over K. Let x,y < V. Assume that x != y.
There exists a function g such that g is linear over K from V to K and g[x] != g[y].

Definition.
Let V be a vector space over K. 
dual(K,V) = Hom(K,V,K).

Definition.
Let V be a vector space over K.
Let v < V.
eval(dual(K,V), v) is a function f such that Dom(f) = |dual(K,V)|
  and (for every element h of |dual(K,V)| f[h] = h[v]).

Definition.
Let V be a vector space over K.
V2ddV(K,V) is a function f such that Dom(f) = |V|
  and (for every element v of |V| f[v] = eval(dual(K,V),v)).