[read RepresentationTheory/06_homomorphism.ftl]

Let K denote a field.
Let M,N denote sets.

Signature. Let K,N be objects. K^^N is an object.
Signature. 2 is an object.
Signature. 3 is an object.
Signature. 4 is an object.
Signature. Let n be an object. upto(n) is a set.

Axiom. upto(1) = {1}.
Axiom. upto(2) = {1,2}.
Axiom. upto(3) = {1,2,3}.
Axiom. upto(4) = {1,2,3,4}.
Let K^n stand for K^^upto(n).

Axiom KNSet. |K^^N| is the set of maps f such that f is from N to |K|.
Axiom KNZero. 0{K^^N} is a map such that Dmn(0{K^^N}) = N and for all n << N : 0{K^^N}(n) = 0{K}.
Axiom KNAdd. Let v,w < K^^N. v +{K^^N} w is a map u such that Dmn(u) = N
 and for all n << N : u(n) = v(n) +{K} w(n).
Axiom KNNeg. Let v < K^^N. ~{K^^N} v is a map u such that Dmn(u) = N
 and for all n << N : u(n) = ~{K} v(n).
Axiom KNSmul. Let a < K and v < K^^N. a @{K^^N} v is a map u such that Dmn(u) = N
 and for all n << N : u(n) = a *{K} v(n).

Theorem. K^^N is a vector space over K.
Proof.
 Take V = K^^N.
 Let us show that V is a vector space over K.
  Let us show that K^^N is an abelian group.
   |K^^N| is a set.
   Let us show that 0{K^^N} < K^^N.
    Dmn(0{K^^N}) = N.
    For all n << N : 0{K^^N}(n) = 0{K}.
   qed.
   Let us show that for all v,w < K^^N : v +{K^^N} w < K^^N.
    Let v,w < K^^N.
    For all n << N : (v +{K^^N} w)(n) = v(n) +{K} w(n) < K.
   qed.
   Let us show that for all v < K^^N : ~{K^^N} v < K^^N.
    Let v < K^^N.
    For all n << N : (~{K^^N} v)(n) = ~{K} v(n) < K.
   qed.
   Let us show that for all v < K^^N : v +{K^^N} 0{K^^N} = v.
    Let v < K^^N.
    v is a map.
    v +{K^^N} 0{K^^N} is a map.
    Dmn(v) = N.
    Dmn(v +{K^^N} 0{K^^N}) = N.
    For all n << N : (v +{K^^N} 0{K^^N})(n) = v(n) +{K} 0{K^^N}(n) = v(n) +{K} 0{K} = v(n).
    Thus v +{K^^N} 0{K^^N} = v (by MapExt).
   qed.
   Let us show that for all v < K^^N : v -{K^^N} v = 0{K^^N}.
    Let v < K^^N.
    For all n << N : (v -{K^^N} v)(n) = v(n) +{K} (~{K^^N} v)(n) = v(n) -{K} v(n) = 0{K^^N}(n).
   qed.
   Let us show that for all u,v,w < K^^N : u +{K^^N} (v +{K^^N} w) = (u +{K^^N} v) +{K^^N} w.
    Let u,v,w < K^^N.
    u +{K^^N} (v +{K^^N} w) is a map.
    (u +{K^^N} v) +{K^^N} w is a map.
    Dmn(u +{K^^N} (v +{K^^N} w)) = N.
    Dmn((u +{K^^N} v) +{K^^N} w) = N.
    For all n << N : (u +{K^^N} (v +{K^^N} w))(n) = u(n) +{K} (v(n) +{K} w(n))
                     = (u(n) +{K} v(n)) +{K} w(n) = ((u +{K^^N} v) +{K^^N} w)(n).
    Thus u +{K^^N} (v +{K^^N} w) = (u +{K^^N} v) +{K^^N} w (by MapExt).
   qed.
   Let us show that for all v,w < K^^N : v +{K^^N} w = w +{K^^N} v.
    Let v,w < K^^N.
    For all n << N : (v +{K^^N} w)(n) = v(n) +{K} w(n) = w(n) +{K} v(n) = (w +{K^^N} v)(n).
   qed.
  qed.
  Let us show that K^^N is a vector space over K.
   Let us show that for all a < K and all v < K^^N : a @{K^^N} v < K^^N.
    Let a < K. Let v < K^^N.
    For all n << N : (a @{K^^N} v)(n) = a *{K} v(n) < K.
   qed.
   Let us show that for all v < K^^N : 1{K} @{K^^N} v = v.
    Let v < K ^^N.
    1{K} @{K^^N} v is a map.
    Dmn(1{K} @{K^^N} v) = N.
    v is a map.
    Dmn(v) = N.
    For all n << N : (1{K} @{K^^N} v)(n) = 1{K} *{K} v(n) = v(n).
    Thus 1{K} @{K^^N} v = v (by MapExt).
   qed.
   Let us show that for all a,b < K and all v < K^^N : (a *{K} b) @{K^^N} v = a @{K^^N} (b @{K^^N} v).
    Let a,b < K. Let v < K^^N.
    (a *{K} b) @{K^^N} v is a map.
    Dmn((a *{K} b) @{K^^N} v) = N.
    a @{K^^N} (b @{K^^N} v) is a map.
    Dmn(a @{K^^N} (b @{K^^N} v)) = N.
    For all n << N : ((a *{K} b) @{K^^N} v)(n) = (a *{K} b) *{K} v(n)
                     = a *{K} (b *{K} v(n)) = a *{K} (b @{K^^N} v)(n) = (a @{K^^N} (b @{K^^N} v))(n).
    Therefore the thesis (by MapExt).
   qed.
   Let us show that for all a,b < K and all v < K^^N :
   (a +{K} b) @{K^^N} v = (a @{K^^N} v) +{K^^N} (b @{K^^N} v).
    Let a,b < K. Let v < K^^N.
    (a +{K} b) @{K^^N} v is a map.
    Dmn((a +{K} b) @{K^^N} v) = N.
    (a @{K^^N} v) +{K^^N} (b @{K^^N} v) is a map.
    Dmn((a @{K^^N} v) +{K^^N} (b @{K^^N} v)) = N.
    Let us show that for all n << N :
    ((a +{K} b) @{K^^N} v)(n) = ((a @{K^^N} v) +{K^^N} (b @{K^^N} v))(n).
     Let n << N.
     ((a +{K} b) @{K^^N} v)(n) = (a +{K} b) *{K} v(n).
     Let us show that (a +{K} b) *{K} v(n) = (a *{K} v(n)) +{K} (b *{K} v(n)).
      For all c,d,e < K : (c +{K} d) *{K} e = (c *{K} e) +{K} (d *{K} e).
     qed.
     (a *{K} v(n)) +{K} (b *{K} v(n)) = (a @{K^^N} v)(n) +{K} (b @{K^^N} v)(n).
     (a @{K^^N} v)(n) +{K} (b @{K^^N} v)(n) = ((a @{K^^N} v) +{K^^N} (b @{K^^N} v))(n).
    qed.
   qed.
   Let us show that for all a < K and all v,w < K^^N :
   a @{K^^N} (v +{K^^N} w) = (a @{K^^N} v) +{K^^N} (a @{K^^N} w).
    Let a < K. Let v,w < K^^N.
    a @{K^^N} (v +{K^^N} w) is a map.
    Dmn(a @{K^^N} (v +{K^^N} w)) = N.
    (a @{K^^N} v) +{K^^N} (a @{K^^N} w) is a map.
    Dmn((a @{K^^N} v) +{K^^N} (a @{K^^N} w)) = N.
    Let us show that for all n << N :
    (a @{K^^N} (v +{K^^N} w))(n) = ((a @{K^^N} v) +{K^^N} (a @{K^^N} w))(n).
     Let n << N.
     For all c,d,e < K : c *{K} (d +{K} e) = (c *{K} d) +{K} (c *{K} e).
     a,v(n),w(n) < K.
     (a @{K^^N} (v +{K^^N} w))(n) = a *{K} (v(n) +{K} w(n)).
     a *{K} (v(n) +{K} w(n)) = (a *{K} v(n)) +{K} (a *{K} w(n)).
     (a *{K} v(n)) +{K} (a *{K} w(n)) = (a @{K^^N} v)(n) +{K} (a @{K^^N} w)(n).
     Let us show that (a @{K^^N} v)(n) +{K} (a @{K^^N} w)(n)
                      = ((a @{K^^N} v) +{K^^N} (a @{K^^N} w))(n).
      For all u1,u2 < K^^N : u1(n) +{K} u2(n) = (u1 +{K^^N} u2)(n).
      a @{K^^N} v < K^^N.
      a @{K^^N} w < K^^N.
     qed.
    qed.
   qed.
  qed.
 qed.
Qed.

Signature. Let K,N,i be objects. e(K,N,i) is an object.
Signature. Let K,M,N,i,j be objects. Mat(K,M,N,i,j) is an object.

Axiom. Let i << N. e(K,N,i) is a map e such that Dmn(e) = N
 and e(i) = 1{K} and for all j << N\{i} : e(j) = 0{K}.

Theorem. Let i << N. e(K,N,i) < K^^N.
Proof.
 Let us show that for all j << N : e(K,N,i)(j) < K.
  Let j << N.
  Case j = i.  end.
  Case j != i. end.
 qed.
Qed.

Axiom. Let i << N. Let j << M. Mat(K,M,N,i,j) is a map A such that Dmn(A) = K^^N
 and A(e(K,N,i)) = e(K,M,i) and for all v << K^^N\{e(K,M,i)} : A(v) = 0{K^^M}.

Theorem. Let i << N. Let j << M. Mat(K,M,N,i,j) is linear over K from K^^N to K^^M.
Proof.
[prove off]
Qed.



