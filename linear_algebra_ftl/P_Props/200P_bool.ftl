[read linear_algebra_ftl/200D_bool.ftl]


Theorem. B is a field.
proof.
 (B has carr,zero,one,add,neg,mul,inv).
 |B| is a set.
 0{B} < B.
 add{B} is a function from Prod(|B|,|B|) to |B|.
 neg{B} is a function from |B| to |B|.
 For all a < B     :       a +{B} 0{B} = a.
 For all a < B     :          a -{B} a = 0{B}.
 For all a,b,c < B : a +{B} (b +{B} c) = (a +{B} b) +{B} c.
 For all a,b < B   :          a +{B} b = b +{B} a.
 1{B} < B.
 mul{B} is a function from Prod(|B|,|B|) to |B|.
 inv{B} is a function from |B|\{0{B}} to |B|.
 For all a < B     :       a *{B} 1{B} = a.
 For all a < B*    :          a /{B} a = 1{B}.
 For all a,b,c < B : a *{B} (b *{B} c) = (a *{B} b) *{B} c.
 For all a,b < B   :          a *{B} b = b *{B} a.
 For all a,b,c < B : a *{B} (b +{B} c) = (a *{B} b) +{B} (a *{B} c).
end.
