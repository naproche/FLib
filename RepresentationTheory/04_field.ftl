[read RepresentationTheory/03_abelian_group.ftl]

Definition Field. A field is an object K such that
     (K is an abelian group)
 and (1{K} < K)
 and (1{K} != 0{K})
 and (for all a,b < K   : a *{K} b < K)
 and (for all a < K*    : inv{K} a < K)
 and (for all a < K     :       a *{K} 1{K} = a)
 and (for all a < K*    :          a /{K} a = 1{K})
 and (for all a,b,c < K : a *{K} (b *{K} c) = (a *{K} b) *{K} c)
 and (for all a,b < K   :          a *{K} b = b *{K} a)
 and (for all a,b,c < K : a *{K} (b +{K} c) = (a *{K} b) +{K} (a *{K} c)).