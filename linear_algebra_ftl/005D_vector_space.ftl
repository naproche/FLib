[read linear_algebra_ftl/A_Props/004A_field.ftl]

[synonym space/-s]

Definition. Let K be a field. A vector space over K is a structure V such that
     (V has carr,zero,add,neg,smul)
 and (V is an abelian group)
 and (smul{V} is a function from Prod(|K|,|V|) to |V|)
 and (for all u < V                 :       1{K} @{V} u = u)
 and (for all a,b < K for all v < V : (a *{K} b) @{V} v = a @{V} (b @{V} v))
 and (for all a,b < K for all v < V : (a +{K} b) @{V} v = (a @{V} v) +{V} (b @{V} v))
 and (for all a < K for all v,w < V : a @{V} (v +{V} w) = (a @{V} v) +{V} (a @{V} w)).
