[read RepresentationTheory/07_field_is_vector_space.ftl]
[read RepresentationTheory/29_quiver_representation.ftl]

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

Signature. Let K,N,i be objects. std(K,N,i) is an object.
Signature. Let K,M,N,i,j be objects. std(K,M,N,i,j) is an object.
Let vec(K,n,i) stand for std(K,upto(n),i).
Let mat(K,m,n,i,j) stand for std(K,upto(m),upto(n),i,j).
Let Mat(K,m,n) stand for Hom(K,K^n,K^m).

Axiom. Let i << N. std(K,N,i) is a map v such that Dmn(v) = N
 and v(i) = 1{K} and for all j << N\{i} : v(j) = 0{K}.

Lemma. Let i << N. std(K,N,i) < K^^N.
Proof.
 For all j << N : std(K,N,i)(j) < K.
Qed.

Axiom. Let i << M. Let j << N. std(K,M,N,i,j) is a map A such that Dmn(A) = |K^^N|
 and for all v < K^^N : A(v) = v(j) @{K^^M} std(K,M,i).

Theorem. Let i << M. Let j << N. std(K,M,N,i,j) is linear over K from K^^N to K^^M.
Proof.
 Take A = std(K,M,N,i,j).
 Let us show that A is linear over K from K^^N to K^^M.
  K^^N and K^^M are vector spaces over K.
  Let us show that A is a map from |K^^N| to |K^^M|.
   std(K,M,i) < K^^M.
   For all v < K^^N : v(j) < K.
   K^^M is a vector space over K.
   For all v < K^^N : A(v) = v(j) @{K^^M} std(K,M,i) < K^^M.
  qed.
  Let us show that for all u,v < K^^N : A(u +{K^^N} v) = A(u) +{K^^M} A(v).
   Let u,v < K^^N.
   K^^N is a vector space over K.
   K^^M is a vector space over K.
   u +{K^^N} v < K^^N (by AbelianGroup).
   u(j), v(j) < K.
   std(K,M,i) < K^^M.
   A(u +{K^^N} v) = (u +{K^^N} v)(j) @{K^^M} std(K,M,i) = (u(j) +{K} v(j)) @{K^^M} std(K,M,i).
   (u(j) +{K} v(j)) @{K^^M} std(K,M,i) = (u(j) @{K^^M} std(K,M,i)) +{K^^M} (v(j) @{K^^M} std(K,M,i))
   (by VectorSpace).
   u(j) @{K^^M} std(K,M,i) = A(u).
   v(j) @{K^^M} std(K,M,i) = A(v).
  qed.
  Let us show that for all a < K and all v < K^^N : A(a @{K^^N} v) = a @{K^^M} A(v).
   Let a < K. Let v < K^^N.
   K^^N is a vector space over K.
   K^^M is a vector space over K.
   a @{K^^N} v < K^^N (by VectorSpace).
   v(j) < K.
   std(K,M,i) < K^^M.
   A(a @{K^^N} v) = (a @{K^^N} v)(j) @{K^^M} std(K,M,i) = (a *{K} v(j)) @{K^^M} std(K,M,i).
   (a *{K} v(j)) @{K^^M} std(K,M,i) = a @{K^^M} (v(j) @{K^^M} std(K,M,i)) (by VectorSpace).
   v(j) @{K^^M} std(K,M,i) = A(v).
  qed.
 qed.
Qed.

Let [[a,b],[c,d]]{K} stand for
  (a @{Mat(K,2,2)} mat(K,2,2,1,1)) +{Mat(K,2,2)} ((b @{Mat(K,2,2)} mat(K,2,2,1,2)) +{Mat(K,2,2)}
 ((c @{Mat(K,2,2)} mat(K,2,2,2,1)) +{Mat(K,2,2)} ((d @{Mat(K,2,2)} mat(K,2,2,2,2))))).

Lemma 2x2Matrix. Let a,b,c,d < K. [[a,b],[c,d]]{K} < Mat(K,2,2).
Proof.
 Take V = Mat(K,2,2).
 Take A = a @{Mat(K,2,2)} mat(K,2,2,1,1).
 Take B = b @{Mat(K,2,2)} mat(K,2,2,1,2).
 Take C = c @{Mat(K,2,2)} mat(K,2,2,2,1).
 Take D = d @{Mat(K,2,2)} mat(K,2,2,2,2).
 Let us show that for all i,j << upto(2) :  mat(K,2,2,i,j) < V.
  Let i,j << upto(2).
  mat(K,2,2,i,j) is linear over K from K^2 to K^2.
  |V| is the set of homomorphisms over K from K^2 to K^2.
 qed.
 V is a vector space over K.
 A,B,C,D < V.
 C +{V} D < V.
 B +{V} (C +{V} D) < V.
 A +{V} (B +{V} (C +{V} D)) < V.
Qed.

Signature. F2 is an object.
Axiom. |F2| is a set.
Axiom. |F2| = {0,1}.
Axiom. 0{F2} = 0.
Axiom. 1{F2} = 1.
Axiom. 1 != 0.
Axiom. 0 +{F2} 0 = 0.
Axiom. 0 +{F2} 1 = 1.
Axiom. 1 +{F2} 0 = 1.
Axiom. 1 +{F2} 1 = 0.
Axiom. 0 *{F2} 0 = 0.
Axiom. 0 *{F2} 1 = 0.
Axiom. 1 *{F2} 0 = 0.
Axiom. 1 *{F2} 1 = 1.
Axiom. ~{F2} 0 = 0.
Axiom. ~{F2} 1 = 1.
Axiom. inv{F2} 1 = 1.

Theorem. F2 is a field.
Proof.
 Let us show that F2 is an abelian group.
  |F2| is a set.
  0{F2} < F2.
  For all a,b < F2   : a +{F2} b < F2.
  For all a < F2     :   ~{F2} a < F2.
  For all a < F2     :       a +{F2} 0{F2} = a.
  For all a < F2     :           a -{F2} a = 0{F2}.
  For all a,b,c < F2 : a +{F2} (b +{F2} c) = (a +{F2} b) +{F2} c.
  For all a,b < F2   :           a +{F2} b = b +{F2} a.
 qed.
 1{F2} < F2.
 1{F2} != 0{F2}.
 For all a,b < F2   : a *{F2} b < F2.
 For all a < F2*    : inv{F2} a < F2.
 For all a < F2     :       a *{F2} 1{F2} = a.
 For all a < F2*    :           a /{F2} a = 1{F2}.
 For all a,b,c < F2 : a *{F2} (b *{F2} c) = (a *{F2} b) *{F2} c.
 For all a,b < F2   :           a *{F2} b = b *{F2} a.
 For all a,b,c < F2 : a *{F2} (b +{F2} c) = (a *{F2} b) +{F2} (a *{F2} c).
Qed.

Lemma. [[1,1],[0,1]]{F2} < Mat(F2,2,2).
Proof.
 F2 is a field.
 1,0 < F2.
 Therefore the thesis (by 2x2Matrix).
Qed.

Lemma. [[0,1],[1,0]]{F2} < Mat(F2,2,2).
Proof.
 F2 is a field.
 1,0 < F2.
 Therefore the thesis (by 2x2Matrix).
Qed.

#    b     c,d
# 0 ---> 1 ===> 2

Signature. quiv is an object.
Axiom. quiv(0) is a set.
Axiom. quiv(0) = {0,1,2}.
Signature. b is an object.
Signature. c is an object.
Signature. d is an object.
Axiom. quiv(1) is a set.
Axiom. quiv(1) = {b,c,d}.
Axiom. quiv(st) is a map.
Axiom. quiv(tl) is a map.
Axiom. Dmn(quiv(st)) = quiv(1).
Axiom. Dmn(quiv(tl)) = quiv(1).
Axiom. quiv(st)(b) = 0.
Axiom. quiv(tl)(b) = 1.
Axiom. quiv(st)(c) = 1.
Axiom. quiv(tl)(c) = 2.
Axiom. quiv(st)(d) = 1.
Axiom. quiv(tl)(d) = 2.

Signature. quivRep is an object.
Axiom. quivRep(0) = F2.
Axiom. quivRep(1) = F2^2.
Axiom. quivRep(2) = F2^2.
Axiom. quivRep(b) is a map h such that Dmn(h) = |F2| and h(0) = 0{F2^2} and h(1) = 0{F2^2}.
Axiom. quivRep(c) = [[1,1],[0,1]]{F2}.
Axiom. quivRep(d) = [[0,1],[1,0]]{F2}.

Theorem. quiv is a quiver.
Proof.
 quiv(0) is a set.
 quiv(1) is a set.
 For all a << quiv(1) : quiv(st)(a) << quiv(0).
 quiv(st) is a map from quiv(1) to quiv(0).
 For all a << quiv(1) : quiv(tl)(a) << quiv(0).
 quiv(tl) is a map from quiv(1) to quiv(0).
Qed.

Theorem. quivRep is a representation of quiv over F2.
Proof.
 F2 is a field.
 F2 is a vector space over F2.
 F2^2 is a vector space over F2.
 For all vertices i of quiv : (quivRep(i) is a vector space over F2).
 Let us show that for all arrows a of quiv :
 (quivRep(a) < Hom(F2,quivRep(quiv(st)(a)),quivRep(quiv(tl)(a)))).
  Let us show that quivRep(b) < Hom(F2,F2,F2^2).
   Let us show that quivRep(b) is linear over F2 from F2 to F2^2.
   quivRep(b) is from |F2| to |F2^2|.
   For all x,y < F2 : quivRep(b)(x +{F2} y) = 0{F2^2} = 0{F2^2} +{F2^2} 0{F2^2}
                      = quivRep(b)(x) +{F2^2} quivRep(b)(y).
   For all x,y < F2 : quivRep(b)(x @{F2} y) = 0{F2^2} = x @{F2^2} 0{F2^2} = x @{F2^2} quivRep(b)(y).
   qed.
   |Hom(F2,F2,F2^2)| is the set of homomorphisms over F2 from F2 to F2^2.
  qed.  
  quivRep(c) < Hom(F2,F2^2,F2^2).
  quivRep(d) < Hom(F2,F2^2,F2^2).
 qed. 
Qed.

# The RAM accumulated by Naproche-SAD.exe seems to grow exponentially with the input length at this
# point.