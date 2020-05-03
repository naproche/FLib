[read linear_algebra_ftl/005D_vector_space.ftl]

Let K denote a field.

Axiom SmulZero. Let V be a vector space over K. Let a < K.
Then a @{V} 0{V} = 0{V}.
# proof : 005P_vector_space_1.ftl


Lemma. Let V be a vector space over K. Let a < K. Let v < V.
Then (a @{V} (~{V} v)) +{V} ((a @{V} v) -{V} (a @{V} v))
   = ((a @{V} (~{V} v)) +{V} (a @{V} v)) -{V} (a @{V} v).
proof. 
 Take x < V such that x = a @{V} (~{V} v).
 Take y < V such that y = a @{V} v.
 Take z < V such that z = neg{V}[a @{V} v].
 x +{V} (y +{V} z) = (x +{V} y) +{V} z.
end.


Lemma. Let V be a vector space over K. Let a < K. Let v < V.
Then ((a @{V} (~{V} v)) +{V} (a @{V} v)) -{V} (a @{V} v) = ~{V} (a @{V} v).
proof.
 Let us show that ((a @{V} (~{V} v)) +{V} (a @{V} v)) -{V} (a @{V} v)  = 0{V} -{V} (a @{V} v).
  Let us show that (a @{V} (~{V} v)) +{V} (a @{V} v) = 0{V}.
   ((a @{V} (~{V} v)) +{V} (a @{V} v)) = a @{V} ((~{V} v) +{V} v).
   ((~{V} v) +{V} v) = 0{V}.
   a @{V} 0{V} = 0{V}.
  end.
 end.
 ~{V} (a @{V} v) < V.
 0{V} -{V} (a @{V} v) = ~{V} (a @{V} v).
end.


Lemma. Let V be a vector space over K. Let a < K. Let v < V.
Then a @{V} (~{V} v) = (a @{V} (~{V} v)) +{V} ((a @{V} v) -{V} (a @{V} v)).
proof.
 a @{V} (~{V} v) = (a @{V} (~{V} v)) +{V} 0{V}.

 Let us show that (a @{V} v , ~{V} (a @{V} v)) << Dom(add{V}).
  a @{V} v < V.
  ~{V} (a @{V} v) < V.
  (a @{V} v , ~{V} (a @{V} v)) << Prod(|V|,|V|).
  Dom(add{V}) = Prod(|V|,|V|).
 end.

 Let us show that 0{V} = (a @{V} v) -{V} (a @{V} v).
  a @{V} v < V.
 end.
end.


Lemma. Let V be a vector space over K. Let a < K. Let v < V.
Then a @{V} (~{V} v) = ((a @{V} (~{V} v)) +{V} (a @{V} v)) -{V} (a @{V} v).
proof.
 (a @{V} (~{V} v)) +{V} ((a @{V} v) -{V} (a @{V} v))
   = ((a @{V} (~{V} v)) +{V} (a @{V} v)) -{V} (a @{V} v).

 Let us show that (a @{V} v , ~{V} (a @{V} v)) << Dom(add{V}).
  a @{V} v < V.
  ~{V} (a @{V} v) < V.
  (a @{V} v , ~{V} (a @{V} v)) << Prod(|V|,|V|).
  Dom(add{V}) = Prod(|V|,|V|).
 end.

 Let us show that (a @{V} (~{V} v) , (a @{V} v) -{V} (a @{V} v)) << Dom(add{V}).
  a @{V} (~{V} v) < V.
  (a @{V} v) -{V} (a @{V} v) < V.
  (a @{V} (~{V} v) , (a @{V} v) -{V} (a @{V} v)) << Prod(|V|,|V|).
  Dom(add{V}) = Prod(|V|,|V|).
 end.

 a @{V} (~{V} v) = (a @{V} (~{V} v)) +{V} ((a @{V} v) -{V} (a @{V} v)).
end.