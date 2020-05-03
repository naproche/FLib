[read linear_algebra_ftl/005D_vector_space.ftl]

Let K denote a field.


Axiom ZeroSmul. Let V be a vector space over K. Let v < V.
Then 0{K} @{V} v = 0{V}.
# proof : 005P_vector_space_1.ftl


Lemma. Let V be a vector space over K. Let a < K. Let v < V.
Then neg{K}[a] @{V} v = ((neg{K}[a] @{V} v) +{V} (a @{V} v)) +{V} neg{V}[a @{V} v].
proof.
 Let us show that (neg{K}[a] @{V} v) +{V} ((a @{V} v) +{V} neg{V}[a @{V} v])
                = ((neg{K}[a] @{V} v) +{V} (a @{V} v)) +{V} neg{V}[a @{V} v].
  Take x < V such that x = neg{K}[a] @{V} v.
  Take y < V such that y = a @{V} v.
  Take z < V such that z = neg{V}[a @{V} v].
  x +{V} (y +{V} z) = (x +{V} y) +{V} z.
 end.
 
 smul{V} is from Prod(|K|,|V|) to |V|.
 add{V} is from Prod(|V|,|V|) to |V|.

 neg{K}[a] @{V} v = (neg{K}[a] @{V} v) +{V} 0{V}.

 Let us show that (a @{V} v , neg{V}[a @{V} v]) << Dom(add{V}).
  a @{V} v < V.
  neg{V}[a @{V} v] < V.
  (a @{V} v , neg{V}[a @{V} v]) << Prod(|V|,|V|).
  Dom(add{V}) = Prod(|V|,|V|).
 end.

 0{V} = (a @{V} v) +{V} neg{V}[a @{V} v].
 (neg{K}[a] @{V} v) +{V} 0{V} = (neg{K}[a] @{V} v) +{V} ((a @{V} v) +{V} neg{V}[a @{V} v]).
end.


Lemma. Let V be a vector space over K. Let a < K. Let v < V.
Then ((neg{K}[a] @{V} v) +{V} (a @{V} v)) +{V} neg{V}[a @{V} v] = neg{V}[a @{V} v].
proof.
 Let us show that ((neg{K}[a] @{V} v) +{V} (a @{V} v)) +{V} neg{V}[a @{V} v] = ((neg{K}[a] +{K} a) @{V} v) +{V} neg{V}[a @{V} v].
   (neg{K}[a] @{V} v) +{V} (a @{V} v) = (neg{K}[a] +{K} a) @{V} v.
 end.

 Let us show that ((neg{K}[a] +{K} a) @{V} v ,  neg{V}[a @{V} v]) << Dom(add{V}).
  (neg{K}[a] +{K} a) @{V} v < V.
  neg{V}[a @{V} v] < V.
  ((neg{K}[a] +{K} a) @{V} v ,  neg{V}[a @{V} v]) << Prod(|V|,|V|).
  Dom(add{V}) =  Prod(|V|,|V|).
 end.
 Let us show that (0{K} @{V} v , neg{V}[a @{V} v]) << Dom(add{V}).
  0{K} @{V} v < V.
  neg{V}[a @{V} v] < V.
  (0{K} @{V} v ,  neg{V}[a @{V} v]) << Prod(|V|,|V|).
  Dom(add{V}) =  Prod(|V|,|V|).
 end.
 Let us show that ((neg{K}[a] +{K} a) @{V} v) +{V} neg{V}[a @{V} v] = (0{K} @{V} v) +{V} neg{V}[a @{V} v].
  (neg{K}[a] +{K} a) = 0{K}.
 end.

 Let us show that (0{K} @{V} v) +{V} neg{V}[a @{V} v] = 0{V} +{V} neg{V}[a @{V} v].
  0{K} @{V} v = 0{V}.
 end.

 0{V} +{V} neg{V}[a @{V} v] = neg{V}[a @{V} v].
end.


Theorem NegSmul. Let V be a vector space over K. Let a < K. Let v < V.
Then neg{K}[a] @{V} v  = neg{V}[a @{V} v].


Theorem NegOneSmul. Let V be a vector space over K. Let v < V.
Then neg{K}[1{K}] @{V} v = neg{V}[v].
proof.
 neg{K}[1{K}] @{V} v = neg{V}[1{K} @{V} v].
 1{K} @{V} v = v.
 neg{V}[1{K} @{V} v] = neg{V}[v].
end.