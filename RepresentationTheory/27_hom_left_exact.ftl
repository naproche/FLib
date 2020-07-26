[read RepresentationTheory/24_hom_functor.ftl]
[read RepresentationTheory/26_exactness.ftl]

Let K denote a field.

# The following two statements are proven in 14_endormophism.ftl resp. 15_automorphism.ftl
# but reading both files entirely interferes extremely with the performance of checking this file.

Axiom. Let U,V,W be vector spaces over K. Let f,g be maps.
 Let g be linear over K from U to V. Let f be linear over K from V to W.
 Then f*g is linear over K from U to W.

Axiom InverseHom. Let V,W be vector spaces over K. Let f < Hom(K,V,W).
 Let f be bijective from |V| to |W|. Then f^(-1) < Hom(K,W,V).

Lemma. Let A be an algebra over K. Let M be a module over A over K.
 Let F be an object such that F = Hom(K,A,M,-).
 Then F preserves left exactness from A to K over K.
Proof.
 F is a functor from Mod(K,A) to Mod(K,K).
 Let us show that for all X,Y,Z < Mod(K,A) and all f << Mod(K,A)(X,Y) and all g << Mod(K,A)(Y,Z) :
 (((X,f,Y,g,Z) is a left exact sequence over A over K)
 => ((F(X),F(f),F(Y),F(g),F(Z)) is a left exact sequence over K over K)).
  Let X,Y,Z < Mod(K,A). Let f << Mod(K,A)(X,Y). Let g << Mod(K,A)(Y,Z).
  Assume (X,f,Y,g,Z) is a left exact sequence over A over K.
  K is a field.
  K is an algebra over K.
  Let us show that (F(X),F(f),F(Y),F(g),F(Z)) is a left exact sequence over K over K.
   F(X),F(Y),F(Z) < Mod(K,K) (by Functor).
   F(f) << Mod(K,K)(F(X),F(Y)) (by Functor).
   F(g) << Mod(K,K)(F(Y),F(Z)) (by Functor).
   Therefore (F(X),F(f),F(Y),F(g),F(Z)) is a sequence over K over K (by Sequence).
 
   Let us show that F(f) is injective.
    F(f) < Hom(K,K,F(X),F(Y)) (by ModMor).
    K is a field.
    F(f) is a modulehom over K over K from F(X) to F(Y).
    F(f) is a map.
    Dmn(F(f)) = |F(X)|.
    Let us show that for all h,k < F(X) : (F(f)(h) = F(f)(k) => h = k).
     Let h,k < F(X).
     Assume F(f)(h) = F(f)(k).
     F(X) = Hom(K,A,M,X).
     h,k are modulehoms over A over K from M to X.
     Let us show that h = k.
      h,k are maps.
      Dmn(h) = |M|.
      Dmn(k) = |M|.
      Let us show that for all m < M : h(m) = k(m).
       Let m < M.
       f < Hom(K,A,X,Y) (by ModMor).
       Let us show that Hom(K,A,M,f)(h) = f*h.
        K is a field.
        X,Y,M are modules over A over K.
        f < Hom(K,A,X,Y).
        h < Hom(K,A,M,X).
        Therefore the thesis (by HomFun).
       qed.
       F(f)(h) = f*h.
       Let us show that F(f)(k) = f*k.
        F(f)(k) = Hom(K,A,M,f)(k).
        k < Hom(K,A,M,X).
        K is a field.
        X,Y,M are modules over A over K.
        Therefore the thesis (by HomFun).
       qed.
       f*h = f*k.
       K is a field.
       f is a modulehom over A over K from X to Y.
       f,h,k are maps.
       f(h(m)) = (f*h)(m) = (f*k)(m) = f(k(m)).
       h(m) < X.
       k(m) < X.
       Dmn(f) = |X|.
       f is injective.
       Therefore h(m) = k(m).
      qed.
     qed.
    qed.
   qed.
 
   K is a field.
   Let us show that F(X),F(Y),F(Z) are vector spaces over K.
    F(X),F(Y),F(Z) < Mod(K,K).
    F(X),F(Y),F(Z) are modules over K over K.
    F(X),F(Y),F(Z) are vector spaces over K.     
   qed.
   Let us show that F(f) < Hom(K,F(X),F(Y)).
    K is an algebra over K.
    F(X),F(Y) are modules over K over K.
    Hom(K,K,F(X),F(Y)) is a subspace of Hom(K,F(X),F(Y)) over K (by ModuleHomSubspace).
    |Hom(K,K,F(X),F(Y))| is a subset of |Hom(K,F(X),F(Y))|.
    F(f) < Hom(K,K,F(X),F(Y)) (by ModMor).
   qed.
   Let us show that F(g) < Hom(K,F(Y),F(Z)).
    F(g) < Hom(K,K,F(Y),F(Z)) (by ModMor).
    F(Y),F(Z) are modules over K over K.
    Hom(K,K,F(Y),F(Z)) is a subspace of Hom(K,F(Y),F(Z)) over K (by ModuleHomSubspace).
    |Hom(K,K,F(Y),F(Z))| is a subset of |Hom(K,F(Y),F(Z))|.
   qed.
 
   Let us show that for all h < Im(F(f)) : h < Ker(F(g)).
    Let h < Im(F(f)).
    F(X),F(Y) are vector spaces over K.
    |Im(F(f))| is a set and |Im(F(f))| = {F(f)(k) | k < F(X)} (by Image).
    Take k < F(X) such that F(f)(k) = h. 
    f < Hom(K,A,X,Y) (by ModMor).
    Let us show that h = f*k.
     F(f)(k) = Hom(K,A,M,f)(k).
     k < Hom(K,A,M,X).
     K is a field.
     X,Y,M are modules over A over K.
     Therefore Hom(K,A,M,f)(k) = f*k (by HomFun).
    qed.
    F(Y),F(Z) are vector spaces over K.
    |Ker(F(g))| is a set and |Ker(F(g))| = {h | h < F(Y) and F(g)(h) = 0{F(Z)}} (by Kernel).
    Let us show that h < F(Y).
     F(f) is linear over K from F(X) to F(Y).
     k < F(X).
     Therefore F(f)(k) < F(Y).
    qed.
    Let us show that F(g)(h) = 0{F(Z)}.
     Let us show that F(g)(h) is a map from |M| to |Z|.
      F(g) is linear over K from F(Y) to F(Z).
      F(g)(h) < F(Z).
      F(g)(h) < Hom(K,A,M,Z).
      F(g)(h) is a modulehom over A over K from M to Z.
     qed.
     Dmn(F(g)(h)) = |M|.
     0{F(Z)} is a map.
     Dmn(0{F(Z)}) = |M|.
     Let us show that for all m < M : F(g)(h)(m) = 0{F(Z)}(m).
      Let m < M.
      g < Hom(K,A,Y,Z) (by ModMor).
      Let us show that F(g)(h) = g*(f*k).
       F(g)(h) = Hom(K,A,M,g)(h).
       h < Hom(K,A,M,Y).
       K is a field.
       Y,Z,M are modules over A over K.
       Therefore Hom(K,A,M,g)(h) = g*h (by HomFun).
      qed.
      g,f,k,f*k are maps.
      (F(g)(h))(m) = (g*(f*k))(m) = g((f*k)(m)) = g(f(k(m))).
      k is a modulehom over A over K from M to X.
      k(m) < X.
      X,Y,Z are vector spaces over K.
      Let us show that f < Hom(K,X,Y).
       A is an algebra over K.
       X,Y are modules over A over K.
       f < Hom(K,A,X,Y).
       Therefore the thesis (by ModuleHomSubspace).
      qed.
      |Im(f)| is a set and |Im(f)| = {f(x) | x < X} (by Image).
      f(k(m)) < Im(f).
      |Im(f)| = |Ker(g)|.
      f(k(m)) < Ker(g).
      Let us show that g < Hom(K,Y,Z).
       A is an algebra over K.
       Y,Z are modules over A over K.
       g < Hom(K,A,Y,Z).
       Therefore the thesis (by ModuleHomSubspace).
      qed.
      |Ker(g)| is a set and |Ker(g)| = {y | y < Y and g(y) = 0{Z}} (by Kernel).
      g(f(k(m))) = 0{Z}.
      0{Z} = 0{Hom(K,A,M,Z)}(m) = 0{F(Z)}(m).
     qed.
     Therefore the thesis (by MapExt).
    qed.
    Therefore h < Ker(F(g)).
   qed.
   
   Let us show that for all h < Ker(F(g)) : h < Im(F(f)).
    K is a field.
    Let h < Ker(F(g)).
    Let us show that F(g)(h) = 0{F(Z)}.
     F(Y),F(Z) are vector spaces over K.
     F(g) < Hom(K,F(Y),F(Z)).
     |Ker(F(g))| is a set and |Ker(F(g))| = {h | h < F(Y) and F(g)(h) = 0{F(Z)}} (by Kernel).
     h < F(Y).
    qed.
    Let us show that F(g)(h) = g*h.
     Y,Z,M are modules over A over K.
     g < Hom(K,A,Y,Z) (by ModMor).
     h < F(Y).
     h < Hom(K,A,M,Y).
     K is a field.
     Therefore Hom(K,A,M,g)(h) = g*h (by HomFun).
     F(g)(h) = Hom(K,A,M,g)(h).
    qed.
    g*h = 0{F(Z)}.    
    Let us show that Ker(g) is a subspace of Y over K.
     Y,Z are vector spaces over K.
     Let us show that g < Hom(K,Y,Z).
      Y,Z are modules over A over K.
      Hom(K,A,Y,Z) is a subspace of Hom(K,Y,Z) over K (by ModuleHomSubspace).
      |Hom(K,A,Y,Z)| is a subset of |Hom(K,Y,Z)|.
      g < Hom(K,A,Y,Z) (by ModMor).
     qed.
     Therefore the thesis (by KernelSubspace).
    qed.
    Ker(g) is a vector space over K.

    Let us show that h < Hom(K,M,Ker(g)).
     Let us show that h is a map from |M| to |Ker(g)|.
      h < F(Y).
      h < Hom(K,A,M,Y).
      h is a map from |M| to |Y|.
      Dmn(h) = |M|.
      Let us show that for all m < M : h(m) < Ker(g).
       Let m < M.
       h(m) < Y.
       g < Hom(K,A,Y,Z) (by ModMor).
       g(h(m)) = (g*h)(m) = 0{F(Z)}(m) = 0{Hom(K,A,M,Z)}(m) = 0{Z}.
       K is a field.
       Y,Z are vector spaces over K.
       Let us show that g < Hom(K,Y,Z).
        Y,Z are modules over A over K.
        Hom(K,A,Y,Z) is a subspace of Hom(K,Y,Z) over K (by ModuleHomSubspace).
        |Hom(K,A,Y,Z)| is a subset of |Hom(K,Y,Z)|.
       qed.
       |Ker(g)| is a set and |Ker(g)| = {y | y < Y and g(y) = 0{Z}} (by Kernel).
      qed.
     qed.
     M,Y are vector spaces over K.
     Hom(K,A,M,Y) is a subspace of Hom(K,M,Y) over K.
     |Hom(K,A,M,Y)| is a subset of |Hom(K,M,Y)|.
     h < F(Y).
     h < Hom(K,A,M,Y).
     Therefore h < Hom(K,M,Y).
     K is a field.
     Let us show that h is linear over K from M to Ker(g).
      h is a map from |M| to |Ker(g)|.
      Let us show that for all u,v < M : h(u +{M} v) = h(u) +{Ker(g)} h(v).
        Let u,v < M.
        h is linear over K from M to Y.
        h(u +{M} v) = h(u) +{Y} h(v) (by Homomorphism).
        h(u),h(v) < Ker(g).
        h(u) +{Ker(g)} h(v) = h(u) +{Y} h(v) (by SubAdd).
       qed.
       Let us show that for all a < K and all v < M : h(a @{M} v) = a @{Ker(g)} h(v).
        Let a < K. Let v < M.
        h is linear over K from M to Y.
        h(a @{M} v) = a @{Y} h(v) (by Homomorphism).
        h(v) < Ker(g).
        a @{Ker(g)} h(v) = a @{Y} h(v) (by SubSmul).
       qed.
      qed.
    qed.

    Let us show that f < Hom(K,X,Ker(g)).
     Let us show that f < Hom(K,X,Y).
      K is a field.
      X,Y are modules over A over K.
      Hom(K,A,X,Y) is a subspace of Hom(K,X,Y) over K (by ModuleHomSubspace).
      |Hom(K,A,X,Y)| is a subset of |Hom(K,X,Y)|.
      f < Hom(K,A,X,Y) (by ModMor).
     qed.
     K is a field.
     f is linear over K from X to Y.
     f is a map from |X| to |Y|.
     Dmn(f) = |X|.
     Let us show that for all x < X : f(x) < Ker(g).
      Let x < X.
      |Im(f)| is a set and |Im(f)| = {f(v) | v < X} (by Image).
      f(x) < Im(f).
     qed.
     Let us show that f is linear over K from X to Ker(g).
      X,Ker(g) are vector spaces over K.
      f is from |X| to |Ker(g)|.
      Let us show that for all u,v < X : f(u +{X} v) = f(u) +{Ker(g)} f(v).
       Let u,v < X.
       f(u +{X} v) = f(u) +{Y} f(v) (by Homomorphism).
       f(u),f(v) < Ker(g).
       f(u) +{Ker(g)} f(v) = f(u) +{Y} f(v) (by SubAdd).
      qed.
      Let us show that for all a < K and all v < X : f(a @{X} v) = a @{Ker(g)} f(v).
       Let a < K. Let v < X.
       f(a @{X} v) = a @{Y} f(v) (by Homomorphism).
       f(v) < Ker(g).
       a @{Ker(g)} f(v) = a @{Y} f(v) (by SubSmul).
      qed.
     qed.
    qed.

    K is a field.
    X,Ker(g) are vector spaces over K.
    f is a map.
    Let us show that f is bijective from |X| to |Ker(g)|.
     f < Hom(K,X,Ker(g)).
     f is injective.
     Let us show that f is surjective onto |Ker(g)|.
      Let us show that f < Hom(K,X,Y).
       X,Y are modules over A over K.
       Hom(K,A,X,Y) is a subspace of Hom(K,X,Y) over K (by ModuleHomSubspace).
       |Hom(K,A,X,Y)| is a subset of |Hom(K,X,Y)|.
       f < Hom(K,A,X,Y) (by ModMor).
      qed.
      |Im(f)| is a set and |Im(f)| = {f(x) | x < X} (by Image).
      For all y < Im(f) there is an x < X such that f(x) = y.
      |Ker(g)| = |Im(f)|.
      Dmn(f) = |X|.
      For all y < Ker(g) there is an x << Dmn(f) such that f(x) = y.
     qed.
    qed.
    Therefore f^(-1) < Hom(K,Ker(g),X) (by InverseHom).

    Take k = f^(-1) * h.
    Let us show that k < F(X).
     F(X) = Hom(K,A,M,X).
     K is a field.
     Let us show that k is a modulehom over A over K from M to X.
      h is linear over K from M to Ker(g).
      f^(-1) is linear over K from Ker(g) to X.
      Therefore k is linear over K from M to X.
      k is a map from |M| to |X|.
      Let us show that for all u,v < M : k(u +{M} v) = k(u) +{X} k(v).
       Let u,v < M.
       k is linear over K from M to X.
       Therefore k(u +{M} v) = k(u) +{X} k(v) (by Homomorphism).  # 1.7 GB of RAM needed here
      qed.
      Let us show that for all a < A and all v < M : k(a @@{M} v) = a @@{X} k(v).
       Let a < A. Let v < M.
       k(a @@{M} v) = (f^(-1)*h)(a @@{M} v).
       f^(-1),h are maps.
       (f^(-1)*h)(a @@{M} v) = f^(-1)(h(a @@{M} v)).
       Let us show that h(a @@{M} v) = a @@{Y} h(v).
        h < F(Y).
        h < Hom(K,A,M,Y).
        K is a field.
        h is a modulehom over A over K from M to Y.
        a < A.
        v < M.
        Therefore the thesis (by ModuleHom).
       qed.
       Take y = h(v).
       f^(-1)(h(a @@{M} v)) = f^(-1)(a @@{Y} y).
       Let us show that f^(-1)(a @@{Y} y) = a @@{X} f^(-1)(y).
        y < Y.
        f(f^(-1)(a @@{Y} y)) = a @@{Y} y.
        Take x = f^(-1)(y).
        Let us show that f(a @@{X} x) = a @@{Y} f(x).
         f < Hom(K,A,X,Y) (by ModMor).
         K is a field.
         f is a modulehom over A over K from X to Y.
         a < A.
         x < X.
         Therefore the thesis (by Modulehom).
        qed.
        f(f^(-1)(a @@{Y} y)) = f(a @@{X} x).
        f is injective.
        f^(-1)(a @@{Y} y) = a @@{X} x.
       qed.
       f^(-1)(h(a @@{M} v)) = a @@{X} f^(-1)(h(v)).
       a @@{X} f^(-1)(h(v)) = a @@{X} k(v).
      qed.
     qed.
    qed.

    Let us show that h < Im(F(f)).
     h < F(Y).
     h < Hom(K,A,M,Y).
     h is a map from |M| to |Y|.
     id{|Ker(g)|} and h are composable.
     h = id{|Ker(g)|} * h.
     Let us show that id{|Ker(g)|} = f * f^(-1).
      id{|Ker(g)|} is a map.
      Dmn(id{|Ker(g)|}) = |Ker(g)|.
      f * f^(-1) is a map.
      Dmn(f * f^(-1)) = Dmn(f^(-1)) = |Ker(g)|.
      For all y < Ker(g) : id{|Ker(g)|}(y) = y = f(f^(-1)(y)) = (f * f^(-1))(y).
      Therefore the thesis (by MapExt).
     qed.
     h = (f * f^(-1)) * h = f * (f^(-1) * h) = f * k.
     Let us show that f * k = F(f)(k).
      K is a field.
      X,Y,M are modules over A over K.
      f < Hom(K,A,X,Y) (by ModMor).
      k < Hom(K,A,M,X).
      Therefore Hom(K,A,M,f)(k) = f*k (by HomFun).
      F(f)(k) = Hom(K,A,M,f)(k).
     qed.
     F(f)(k) = h.
     K is a field.
     F(X),F(Y) are modules over K over K.
     F(X),F(Y) are vector spaces over K.
     F(f) < Hom(K,F(X),F(Y)).
     |Im(F(f))| is a set and |Im(F(f))| = {F(f)(k1) | k1 < F(X)} (by Image).
     Therefore h < Im(F(f)).
    qed.
   qed.
   Therefore |Im(F(f))| = |Ker(F(g))|.
   Therefore the thesis (by LeftExactSequence).
  qed.
 qed.
 Therefore the thesis (by PreserveLeftExactness).
Qed.


Theorem. Let A be an algebra over K. Let M be a module over A over K.
 Hom(K,A,M,-) is a left exact functor.
Proof.
 Take F = Hom(K,A,M,-).
 Let us show that F is a left exact functor.
  K is a field.
  A,K are algebras over K.
  F is a functor from Mod(K,A) to Mod(K,K).
  F preserves left exactness from A to K over K.
 qed.
Qed.