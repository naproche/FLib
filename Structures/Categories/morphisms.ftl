#
# Morphisms
# (Marcel Schütz, 2020)
#

#[prove off][check off]
[read FLib/Structures/Categories/cats.ftl]
#[prove on][check on]


# 1. Morphisms

Definition CatMor000. A morphism is an entity f such that f is an element of Hom(C) for some
category C.

Definition CatMor005. Let X,Y be entities. A morphism between X and Y is a morphism f such that
dom(f) = X and codom(f) = Y.


Lemma CatMor010. Let f be a morphism. Then there is a category C and objects X,Y of C such that f is
a morphism between X and Y.

Proof.
  Take a category C such that f \in Hom(C). Take entities X,Y such that dom(f) = X and codom(f) = Y.
  Then X,Y are objects of C.
qed.


Definition CatMor015. Let X,Y be entities. Hom(X,Y) = {f | f is a morphism between X and Y}.


Definition CatMor020. An endomorphism is a morphism f such that dom(f) = codom(f).


Proposition CatMor025. Let C be a category and f \in Hom(C). Then dom(f) and codom(f) are objects of
C.


Lemma CatMor027. Let O,H be classes such that H is a homomorphism class over O. Let
X,Y \in Obj((O,H)_{CAT}). Let x,y \in O. Assume that X = (O,H)_{CAT}(x) and Y = (O,H)_{CAT}(y). Let
hom be a class such that hom = {f | f is a map from x to y}. Then Hom(X,Y) = (O,H)_{CAT}[hom].

Proof. [prove off] qed.


# 1.1 Composition

Let f: X --> Y stand for f is a morphism between X and Y.

Proposition CatMor030. Let C be a category and X,Y,Z be objects of C. Let f: X --> Y and g: Y --> Z. 
Then g \circ f is a morphism between X and Z that lies in Hom(C).

Proof. [prove off] qed.


Proposition CatMor035. Let C be a category and W,X,Y,Z be objects of C. Let f: W --> X and
g: X --> Y and h: Y --> Z. Then h \circ (g \circ f) is a morphism between W and Z that lies in
Hom(C).

Proof. [prove off] qed.


Proposition CatMor040. Let C be a category and W,X,Y,Z be objects of C. Let f: W --> X and
g: X --> Y and h: Y --> Z. Then (h \circ g) \circ f is a morphism between W and Z that lies in
Hom(C).

Proof. [prove off] qed.


Proposition CatMor045. Let C be a category and W,X,Y,Z be objects of C. Let f: W --> X and
g: X --> Y and h: Y --> Z. Then h \circ (g \circ f) = (h \circ g) \circ f.

Proof. [prove off] qed.


# 1.2 Identity

Proposition CatMor050. Let C be a category and X be an object of C. Then id_{X} is a morphism
between X and X that lies in Hom(C).

Proof. [prove off] qed.


Proposition CatMor055. Let C be a category and X,Y be objects of C. Let f: X --> Y. Then
f \circ id_{X} = f.

Proof. [prove off] qed.


Proposition CatMor060. Let C be a category and X,Y be objects of C. Let f: X --> Y. Then
id_{Y} \circ f = f.

Proof. [prove off] qed.


Proposition CatMor065. Let C be a category and Y be an object of C. Let f: Y --> Y. Assume that
f \circ g = g for all X \in Obj(C) and all g: X --> Y. Then f = id_{Y}.

Proof.
  f = f \circ id_{Y} = id_{Y}.
qed.


# 2. Inverses

Axiom CatMor070. Let C be a category and X,Y be objects of C and f: X --> Y. Let g be an entity. g
is a leftinverse of f iff g: Y --> X and g \circ f = id_{X}.

Let a retraction of f stand for a leftinverse of f.


Axiom CatMor075. Let C be a category and X,Y be objects of C and f: X --> Y. Let g be an entity. g
is a rightinverse of f iff g: Y --> X and f \circ g = id_{Y}.

Let a section of f stand for a rightinverse of f.


Axiom CatMor080. Let f be a morphism and g be an entity. g is an inverse of f iff g is a morphism
and a leftinverse of f and a rightinverse of f.


Proposition CatMor085. Let f,g,h be morphisms. Assume that g and h are inverses of f. Then g = h.

Proof. [prove off] qed.


Axiom CatMor090. Let f be a morphism that has an inverse. f^{-1} is the inverse of f.


Proposition CatMor095. Let C be a category and X,Y be objects of C. Let f: X --> Y. Then f^{-1} is a
morphism between Y and X.

Proof. [prove off] qed.


Proposition CarMor100. Let f be a morphism that has an inverse. Then f is the inverse of f^{-1}.

Proof. [prove off] qed.


# 3. Monic, epic, iso

# 3.1 Monomorphisms

Signature CarMor105. Let f be an entity. f is monic is an statement.

Axiom CatMor110. Let C be a category and Y,Z be objects of C. Let f: Y --> Z. f is monic iff for all
X \in Obj(C) and all g,h: X --> Y we have f \circ g = f \circ h  =>  g = h.


Definition CatMor115. A monomorphism is a monic morphism.

Definition CatMor120. Let X,Y be entities. A monomorphism between X and Y is a monic morphism
between X and Y.

Let f: X >--> Y stand for f is an monomorphism between X and Y.


Proposition CatMor125. Let f be a morphism that has a leftinverse. Then f is monic.

Proof.
  Take A category C and objects Y,Z of C such that f is a morphism between Y and Z (by CatMor010).
  Take a leftinverse g of f. g is a morphism between Z and Y such that g \circ f = id_{Y} (by
  CatMor070).

  For all X \in Obj(C) and all h,k: X --> Y we have f \circ h = f \circ k  =>  h = k.
  proof.
    Let X \in Obj(C) and h,k: X --> Y. Assume that f \circ h = f \circ k. Then g \circ (f \circ h) =
    g \circ (f \circ k). Hence (g \circ f) \circ h = (g \circ f) \circ k (by CatMor045). Indeed X is
    an object of C. Thus id_{Y} \circ h = id_{Y} \circ k. id_{Y} \circ h = h. id_{Y} \circ k = k.
    Therefore we have h = k.
  end.

  Hence the thesis (by CatMor110).
qed.


Proposition CatMor130. Let C be a category and X,Y,Z be objects of C. Let f: X --> Y and g: Y --> Z.
If f and g are monic then g \circ f is monic.

Proof.
  g \circ f is a morphism between X and Z (by CatMor030). Assume that f and g are monic.

  For all W \in Obj(C) and all h,k: W --> X we have (g \circ f) \circ h = (g \circ f) \circ k  =>
  h = k.
  proof.
    Let W \in Obj(C) and h,k: W --> X. Assume that (g \circ f) \circ h = (g \circ f) \circ k. W is
    an object of C. Then g \circ (f \circ h) = g \circ (f \circ k) (by CatMor045). Hence
    f \circ h = f \circ k (by CatMor110). Indeed f \circ h,f \circ k: W --> Y (by CatMor030). Thus
    h = k (by CatMor110).
  end.

  Hence the thesis (by CatMor110).
qed.


# 3.2 Epimorphisms

Signature CatMor135. Let f be an entity. f is epic is an statement.

Axiom CatMor140. Let C be a category and X,Y be objects of C. Let f: X --> Y. f is epic iff for all
Z \in Obj(C) and all g,h: Y --> Z we have g \circ f = h \circ f  =>  g = h.


Definition CatMor145. An epimorphism is an epic morphism.

Definition CatMor150. Let X,Y be entities. An epimorphism between X and Y is an epic morphism
between X and Y.

Let f: X -->> Y stand for f is an epimorphism between X and Y.


Proposition CatMor155. Let f be a morphism. Assume that f has a rightinverse. Then f is epic.

Proof. [prove off] qed.


Proposition CatMor160. Let f,g be epimorphisms such that codom(f) = dom(g). Then g \circ f is epic.

Proof. [prove off] qed.


Definition CatMor165. A bimorphism is a morphism that is monic and epic.

Definition CatMor170. Let X,Y be entities. A bimorphism between X and Y is a morphism between X and
Y that is monic and epic.

Let f: X >-->> Y stand for f is a bimorphism between X and Y.


# 3.3 Isomorphisms

Definition CatMor175. An isomorphism is a morphism f that has an inverse.

Let f is iso stand for f is an isomorphism.


Let an isomorphism between X and Y stand for an iso morphism between X and Y.

Let f: X <--> Y stand for f is an isomorphism between X and Y.


Definition CatMor180. An automorphism is an endomorphism that is iso.


Proposition CatMor185. Let X,Y be objects and f be an isomorphism between X and Y. Then f^{-1} is an
isomorphism between Y and X.

Proof. [prove off] qed.


Proposition CatMor190. Any isomorphism is monic and epic.

Proof.
  Let f be an isomorphism. Take a morphism g that is an inverse of f. Then g is a rightinverse of f
  and a leftinverse of f (by CatMor080). Indeed f is a morphism. Hence the thesis.
qed.


Proposition CatMor195. Let X be an object. id_{X} is an isomorphism.

Proof.
  Take a category C such that X is an object of C. id_{X}: X --> X. id_{X} \circ id_{X} = id_{X}.
  Hence id_{X} is a leftinverse of id_{X} and a rightinverse of id_{X} (by CatMor070, CatMor075).
qed.


Proposition CatMor200. Let C be a category and X,Y,Z be objects of C. Let f: X <--> Y and
g: Y <--> Z. Then f^{-1} \circ g^{-1} is the inverse of g \circ f.

Proof. [prove off] qed.


Corollary CatMor205. Let C be a category and X,Y,Z be objects of C. Let f: X <--> Y and g: Y <--> Z.
Then g \circ f: X <--> Z.

Proof. [prove off] qed.


# 4. Isomorphic objects

Axiom CatMor210. Let X,Y be objects. X and Y are isomorphic iff there exists an isomorphism between
X and Y.


Proposition CatMor215. Let X be an object. Then X and X are isomorphic.

Proof.
  id_{X} is an isomorphism between X and X.
qed.


Proposition CatMor220. Let X and Y be isomorphic objects. Then Y and X are isomorphic.

Proof.
  Take an isomorphism f between X and Y (by CatMor210). Then f^{-1} is an isomorphism between Y and
  X.
qed.


Proposition CatMor225. Let C be a category and X,Y,Z be objects of C. Assume that X and Y are
isomorphic and Y and Z are isomorphic. Then X and Z are isomorphic.

Proof.
  Take an isomorphism f between X and Y and an isomorphism g between Y and Z (by CatMor210). Indeed
  X,Y,Z are objects. Then g \circ f is an isomorphism between X and Z (by CatMor205).
qed.


# 5. Locally small categories

Definition CatMor230. A locally small category is a category C such that Hom(X,Y) is a set for all
X,Y \in Obj(C).
