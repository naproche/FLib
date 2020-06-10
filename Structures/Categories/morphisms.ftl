#
# Morphisms
# (Marcel Schütz, 2020)
#


#[prove off]
[read ForTheLib/Categories/cats.ftl]
#[prove on]


# 1. Morphisms

Definition CatMor000. A morphism is an object f such that f is an element of Hom(C) for some
category C.

Definition CatMor005. Let X,Y be objects. A morphism between X and Y is a morphism f such that
dom(f) = X and codom(f) = Y.


Definition CatMor007. Let X,Y be objects. Hom(X,Y) = {f | f is a morphism between X and Y}.


Definition CatMor010. An endomorphism is a morphism f such that dom(f) = codom(f).


Proposition CatMor012. Let C be a category and f \in Hom(C). Then dom(f) and codom(f) are objects of
C.


# 1.1 Composition

Proposition CatMor017. Let f,g be morphisms. Assume that dom(g) = codom(f). Then g \circ f is a
morphism between dom(f) and codom(g).

Proof.
  Take a category C such that f \in Hom(C). Then codom(f) \in Obj(C). Hence dom(g) \in Obj(C). Thus
  g \in Hom(C) (by CatCat180). Then we have g \circ f \in Hom(C). dom(g \circ f) = dom(f).
  codom(g \circ f) = codom(g).
qed.


Proposition CatMor021. Let f,g,h be morphisms. Assume that dom(g) = codom(f) and dom(h) = codom(g).
Then h \circ (g \circ f) is a morphism between dom(f) and codom(h).

Proof.
  g \circ f is a morphism between dom(f) and codom(g). Hence g \circ f is a morphism such that
  codom(g \circ f) = dom(h). Thus h \circ (g \circ f) is a morphism between dom(g \circ f) and
  codom(h).
qed.


Proposition CatMor023. Let C be a category and f,g,h be morphisms. Assume that dom(g) = codom(f) and
dom(h) = codom(g). Then (h \circ g) \circ f is a morphism between dom(f) and codom(h).

Proof.
  h \circ g is a morphism between dom(g) and codom(h). Hence h \circ g is a morphism such that
  dom(h \circ g) = codom(f). Thus (h \circ g) \circ f is a morphism between dom(f) and
  codom(h \circ g).
qed.


Proposition CatMor024. Let f,g,h be morphisms. Assume that dom(g) = codom(f) and dom(h) = codom(g).
Then h \circ (g \circ f) = (h \circ g) \circ f.

Proof.
  Take a category C such that f \in Hom(C). codom(f) \in Obj(C). Hence dom(g) \in Obj(C). Thus
  g \in Hom(C). Then codom(g) \in Obj(C). Hence dom(h) \in Obj(C). Thus h \in Hom(C). Then we have
  the thesis (by CatCat160).
qed.


# 1.2 Identity

Proposition CatMor025. Let X be an object of some category. Then id_{X} is a morphism between X and
X.


Proposition CatMor030. Let X be an object and f be a morphism. Assume that dom(f) = X. Then
f \circ id_{X} = f.

Proof.
  Take a category C such that f \in Hom(C). Then X \in Obj(C). Hence id_{X} \in Hom(C). Thus we have
  the thesis (by CatCat145).
qed.


Proposition CatMor035. Let X be an object of some category and f be a morphism. Assume that
codom(f) = X. Then id_{X} \circ f = f.

Proof.
  Take a category C such that f \in Hom(C). Then X \in Obj(C). Hence id_{X} \in Hom(C). Thus we have
  the thesis (by CatCat140).
qed.


Proposition CatMor037. Let X be an object and f be a morphism between X and X. Assume that
f \circ g = g for all morphisms g such that codom(g) = X. Assume that g \circ f = g for all
morphisms g such that dom(g) = X. Then f = id_{X}.

Proof.
  f = f \circ id_{X} = id_{X}.
qed.


# 2. Inverses

Definition CatMor040. Let f be a morphism. A leftinverse of f is a morphism g such that
dom(g) = codom(f) and g \circ f = id_{dom(f)}.

Let a retraction of f stand for a leftinverse of f.


Proposition CatMor042. Let f be a morphism and g be a leftinverse of f. Then codom(g) = dom(f).


Definition CatMor045. Let f be a morphism. A rightinverse of f is a morphism g such that
dom(f) = codom(g) and f \circ g = id_{dom(g)}.

Let a section of f stand for a rightinverse of f.


Proposition CatMor047. Let f be a morphism and g be a rightinverse of f. Then dom(g) = codom(f).


Definition CatMor050. Let f be a morphism. An inverse of f is a morphism g such that g is a
rightinverse of f and g is a leftinverse of f.


Proposition CatMor055. Let f,g,h be morphisms. Assume that g and h are inverses of f. Then g = h.

Proof.
  Take objects X,Y such that f is a morphism between X and Y. Then g,h are morphisms between Y and
  X. Then we have

  g = g \circ id_{Y} = g \circ (f \circ h) = (g \circ f) \circ h = id_{X} \circ h = h.
qed.


Axiom CatMor060. Let f be a morphism that has an inverse. f^{-1} is the inverse of f.


Proposition CatMor062. Let f be a morphism that has an inverse. Then f^{-1} is a morphism between
codom(f) and dom(f).


# 3. Monic, epic, iso

# 3.1 Monomorphisms

Definition CatMor065. A monomorphism is a morphism f such that for all morphisms g,h such that
codom(g),codom(h) = dom(f) we have f \circ g = f \circ h  =>  g = h.

Let f is monic stand for f is a monomorphism.

Let a monomorphism between X and Y stand for a monic morphism between X and Y.


Proposition CatMor070. Let f be a morphism. Assume that f has a leftinverse. Then f is monic.

Proof.
  Take objects X,Y such that f is a morphism between X and Y. Take a morphism g that is a
  leftinverse of f. Then dom(g) = codom(f). Hence g \circ f = id_{X}.

  For all morphisms h,k such that codom(h),codom(k) = dom(f) we have f \circ h = f \circ k  =>
  h = k.
  proof.
    Let h,k be morphisms such that codom(h),codom(k) = dom(f). Assume that f \circ h = f \circ k.
    Then g \circ (f \circ h) = g \circ (f \circ k). Hence (g \circ f) \circ h = (g \circ f) \circ k.
    Thus id_{X} \circ h = id_{X} \circ k. id_{X} \circ h = h. id_{X} \circ k = k. Therefore we have 
    the thesis.
  end.
qed.


Proposition CatMor072. Let f,g be monomorphisms. Assume that codom(f) = dom(g). Then g \circ f is
monic.

Proof.
  Take objects X,Y,Z such that f is a morphism between X and Y and g is a morphism between Y and Z.
  g \circ f is a morphism between X and Z.

  For all morphisms h,k such that codom(h),codom(k) = dom(g \circ f) we have (g \circ f) \circ h =
  (g \circ f) \circ k  =>  h = k.
  proof.
    Let h,k be morphisms such that codom(h),codom(k) = dom(g \circ f). Assume that
    (g \circ f) \circ h = (g \circ f) \circ k. Then g \circ (f \circ h) = g \circ (f \circ k). Hence
    f \circ h = f \circ k (by CatMor065). Indeed f \circ h and f \circ k are morphisms such that
    codom(f \circ h),codom(f \circ k) = dom(g). Thus we have the thesis (by CatMor065).
  end.
qed.


# 3.2 Epimorphisms

Definition CatMor075. An epimorphism is a morphism f such that for all morphism g,h such that
dom(g),dom(h) = codom(f) we have g \circ f = h \circ f  =>  g = h.

Let f is epic stand for f is an epimorphism.

Let an epimorphism between X and Y stand for an epic morphism between X and Y.


Proposition CatMor080. Let f be a morphism. Assume that f has a rightinverse. Then f is epic.

Proof.
  Take objects X,Y such that f is a morphism between X and Y. Take a morphism g that is a
  rightinverse of f. Then codom(g) = dom(f). Hence f \circ g = id_{Y} (by CatMor045). Indeed Y =
  dom(g).

  For all morphisms h,k such that dom(h),dom(k) = codom(f) we have h \circ f = k \circ f  =>
  h = k.
  proof.
    Let h,k be morphisms such that dom(h),dom(k) = codom(f). Assume that h \circ f = k \circ f. Then
    (h \circ f) \circ g = (k \circ f) \circ g. Hence h \circ (f \circ g) = k \circ (f \circ g). Thus
    h \circ id_{Y} = k \circ id_{Y}. Therefore we have the thesis.
  end.
qed.


Proposition CatMor082. Let f,g be epimorphisms such that codom(f) = dom(g). Then g \circ f is epic.

Proof.
  Take objects X,Y,Z such that f is a morphism between X and Y and g is a morphism between Y and Z.
  g \circ f is a morphism between X and Z.

  For all morphisms h,k such that dom(h),dom(k) = codom(g \circ f) we have h \circ (g \circ f) =
  k \circ (g \circ f)  =>  h = k.
  proof.
    Let h,k be morphisms such that dom(h),dom(k) = codom(g \circ f). Assume that h \circ (g \circ f)
    = k \circ (g \circ f). Then (k \circ g) \circ f = (h \circ g) \circ f. Hence k \circ g =
    h \circ g (by CatMor075). Indeed k \circ g and h \circ g are morphisms such that dom(k \circ g),
    dom(h \circ g) = codom(f). Thus we have the thesis (by CatMor075).
  end.
qed.


Definition CatMor085. A bimorphism is a morphism that is monic and epic.


# 3.3 Isomorphisms

Definition CatMor090. An isomorphism is a morphism f that has an inverse.

Let f is iso stand for f is an isomorphism.

Let an isomorphism between X and Y stand for an iso morphism between X and Y.


Definition CatMor095. An automorphism is an endomorphism that is iso.


Proposition CatMor100. Let f be an isomorphism. Then f is the inverse of f^{-1}.

Proof.
  Take objects X,Y such that f is a morphism between X and Y. f^{-1} is a morphism between Y and X.
  Hence dom(f^{-1}) = codom(f) and dom(f) = codom(f^{-1}). f^{-1} is a leftinverse of f and a
  rightinverse of f. Thus we have f^{-1} \circ f = id_{X} and f \circ f^{-1} = id_{Y}. Then f is a
  rightinverse of f^{-1} and a leftinverse of f^{-1} (by CatMor040,CatMor045). Hence f is an inverse
  of f^{-1}.
qed.


Corollary CatMor101. Let f be an isomorphism. Then f^{-1} is an isomorphism.


Proposition CatMor102. Any isomorphism is monic and epic.

Proof.
  Let f be an isomorphism. f has a leftinverse. Hence f is monic. f has a rightinverse. Hence f is
  epic.
qed.


Proposition CatMor103. Let X be an object of some category. id_{X} is an isomorphism.

Proof.
  id_{X} \circ id_{X} = id_{X}. Hence id_{X} is a leftinverse of id_{X} and a rightinverse of
  id_{X}.
qed.


Proposition CatMor104. Let f,g be isomorphisms. Assume that codom(f) = dom(g). Then
f^{-1} \circ g^{-1} is an inverse of g \circ f.

Proof.
  Take objects X,Y,Z such that f is a morphism between X and Y and g is a morphism between Y and Z.
  g \circ f is a morphism between X and Z. Hence g \circ f is a morphism. f^{-1},g^{-1} are
  morphisms.

  (1) dom(f) = X and codom(f) = Y.
  (2) dom(g) = Y and codom(g) = Z.

  (3) dom(g^{-1}) = Z and codom(g^{-1}) = Y.
  (4) dom(f^{-1}) = Y and codom(f^{-1}) = X.
  
  Thus f^{-1} \circ g^{-1} is a morphism between Z and X (by CatMor017).

  (5) dom(g \circ f)           = X and codom(g \circ f)           = Z.
  (6) dom(f^{-1} \circ g^{-1}) = Z and codom(f^{-1} \circ g^{-1}) = X.

  (7) g^{-1} \circ g = id_{Y}. Indeed g^{-1} is the inverse of g.
  (8) f \circ f^{-1} = id_{Y}. Indeed f is the inverse of f^{-1}.

  f^{-1} \circ g^{-1} is a leftinverse of g \circ f.
  proof.
    (f^{-1} \circ g^{-1}) \circ (g \circ f) = f^{-1} \circ (g^{-1} \circ (g \circ f)).
    
    f^{-1} \circ (g^{-1} \circ (g \circ f)) = f^{-1} \circ ((g^{-1} \circ g) \circ f) (by
    CatMor024).
    
    f^{-1} \circ ((g^{-1} \circ g) \circ f) = f^{-1} \circ (id_{Y} \circ f).

    f^{-1} \circ (id_{Y} \circ f) = f^{-1} \circ f.
    
    f^{-1} \circ f = id_{X}. Indeed f^{-1} is the inverse of f.
  end.

  f^{-1} \circ g^{-1} is a rightinverse of g \circ f.
  proof.
    (g \circ f) \circ (f^{-1} \circ g^{-1}) = ((g \circ f) \circ f^{-1}) \circ g^{-1}.

    ((g \circ f) \circ f^{-1}) \circ g^{-1} = (g \circ (f \circ f^{-1})) \circ g^{-1}.

    (g \circ (f \circ f^{-1})) \circ g^{-1} = (g \circ id_{Y}) \circ g^{-1}.

    (g \circ id_{Y}) \circ g^{-1} = g \circ g^{-1}.

    g \circ g^{-1} = id_{Z}. Indeed g is the inverse of g^{-1}.
  end.
qed.


Corollary CatMor105. Let f,g be isomorphisms. Assume that codom(f) = dom(g). Then g \circ f is iso.

Proof.
  f^{-1} \circ g^{-1} is an inverse of g \circ f.
qed.


# 4. Isomorphic objects

Definition CatMor106. Let X,Y be objects. X \cong Y iff there exists an isomorphism between X and Y.

Let X and Y are isomorphic stand for X \cong Y.


Proposition CatMor110. Let X be an object of some category. X and X is isomorphic.

Proof.
  id_{X} is an isomorphism between X and X.
qed.


Proposition CatMor115. Let X,Y be objects. Assume that X and Y are isomorphic. Then Y and X are
isomorphic.

Proof.
  Take an isomorphism f between X and Y. Then f^{-1} is an isomorphism between Y and X.
qed.


Proposition CatMor120. Let X,Y,Z be objects. Assume that X and Y are isomorphic and Y and Z are
isomorphic. Then X and Z are isomorphic.

Proof.
  Take an isomorphism f between X and Y and an isomorphism g between Y and Z. Then g \circ f is an
  isomorphism between X and Z.
qed.


# 5. Locally small categories

Axiom CatMor130. Let C be a category. C is locally small iff Hom(X,Y) is a set for all
X,Y \in Obj(C).
