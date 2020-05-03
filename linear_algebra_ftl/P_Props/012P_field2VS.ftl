[read linear_algebra_ftl/012D_field2VS.ftl]

Let K denote a field.


Theorem. Let K be a field. Then K is a vector space over K.
proof.
 (K has carr,zero,add,neg,smul).
 K is an abelian group.
 smul{K} is a function from Prod(|K|,|K|) to |K|.
 For all u < K                 :       1{K} @{K} u = u.
 For all a,b < K for all v < K : (a *{K} b) @{K} v = a @{K} (b @{K} v).
 For all a,b < K for all v < K : (a +{K} b) @{K} v = (a @{K} v) +{K} (b @{K} v).
 For all a < K for all v,w < K : a @{K} (v +{K} w) = (a @{K} v) +{K} (a @{K} w).
end.