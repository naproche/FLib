#
# Categories
# (Marcel Schütz, 2020)
#

#[prove off]
[read ForTheLib/Foundations/structures.ftl]
[read ForTheLib/Foundations/axioms.ftl]
#[prove on]


# 1. Morphism classes

# 1.1 Axioms for morphism classes

# 1.1.1 id lies in every morphism class

Signature CatCat010. Hom1 is an axiom.

Axiom CatCat015. Let O,H be classes. (O,H) satisfies Hom1 iff for all X \in O we have id_{X} \in H
and dom(id_{X}) = X = codom(id_{X}).


# 1.1.2 Morphism classes are closed under composition

Signature CatCat020. Hom2 is an axiom.

Axiom CatCat025. Let O,H be classes. (O,H) satisfies Hom2 iff for all f,g \in H such that codom(f) =
dom(g) we have g \circ f \in H and dom(g \circ f) = dom(f) and codom(g \circ f) = codom(g).


# 1.1.3 id is left-neutral

Signature CatCat030. Hom3 is an axiom.

Axiom CatCat035. Let O,H be classes. (O,H) satisfies Hom3 iff for all X \in O and all f \in H such
that codom(f) = X  we have id_{X} \circ f = f.


# 1.1.4 id is right-neutral

Signature CatCat040. Hom4 is an axiom.

Axiom CatCat045. Let O,H be classes. (O,H) satisfies Hom4 iff for all X \in O and all f \in H such
that dom(f) = X we have f \circ id_{X} = f.


# 1.1.5 Composition is associative

Signature CatCat050. Hom5 is an axiom.

Axiom CatCat055. Let O,H be classes. (O,H) satisfies Hom5 iff for all f,g,h \in H such that
codom(f) = dom(g) and codom(g) = dom(h) we have (h \circ g) \circ f = h \circ (g \circ f).


# 1.1.6 dom and codom are objects

Signature CatCat060. Hom6 is an axiom.

Axiom CatCat065. Let O,H be classes. (O,H) satisfies Hom6 iff dom(f) and codom(f) lie in O for all
f \in H.


# 1.1.7 dom and codom determine a unique Category

Signature CatCat070. Hom7 is an axiom.

Axiom CatCat075. Let O,H be classes. (O,H) satisfies Hom7 iff for all objects f if dom(f) \in O or
codom(f) \in O then f \in H.


# 1.2 Definition of morphism classes

Definition CatCat090. Let O be a class. A morphism class over O is a class H such that (O,H)
satisfies Hom1 and Hom2 and Hom3 and Hom4 and Hom5 and Hom6 and Hom7.


# 2. Categories

Signature CatCat093. A category is a structure.

Axiom CatCat095. Let C be a category. Obj(C) is a class.

Axiom CatCat100. Let C be a category. Hom(C) is a morphism class over Obj(C).

Axiom CatCat105. Let C be a category. range(C) = Obj(C) \cup Hom(C).


Proposition CatCat110. Let C be a category. Hom(C) is a class.


Definition CatCat012. Let C be a category. An object of C is an element of Obj(C).


# 2.1 Small and large categories

Axiom CatCat115. Let C be a category. C is small iff Obj(C) and Hom(C) are sets.

Axiom CatCat120. Let C be a category. C is large iff C is not small.


# 2.2 Constructing categories

Axiom CatCat125. Let O be a class and H be a morphism class over O. There is a category C such that
the carrier of C is (O \cup H, O , H) and Obj(C) = C[O] and Hom(C) = C[H].


# 3. Obvious properties of categories

Proposition CatCat130. Let C be a category. id_{X} \in Hom(C) for all X \in Obj(C).

Proof.
  (Obj(C),Hom(C)) satisfies Hom1. Hence the thesis (by CatCat015). Indeed Obj(C),Hom(C) are classes.
qed.


Proposition CatCat135. Let C be a category. dom(id_{X}) = X = codom(id_{X}) for all X \in Obj(C).

Proof.
  (Obj(C),Hom(C)) satisfies Hom1. Hence the thesis (by CatCat015). Indeed Obj(C),Hom(C) are classes.
qed.


Proposition CatCat140. Let C be a category. For all X \in Obj(C) and all f \in Hom(C) such that
codom(f) = X  we have id_{X} \circ f = f.

Proof.
  (Obj(C),Hom(C)) satisfies Hom3. Hence the thesis (by CatCat035). Indeed Obj(C),Hom(C) are classes.
qed.


Proposition CatCat145. Let C be a category. For all X \in Obj(C) and all f \in Hom(C) such that
dom(f) = X we have f \circ id_{X} = f.

Proof.
  (Obj(C),Hom(C)) satisfies Hom4. Hence the thesis (by CatCat045). Indeed Obj(C),Hom(C) are classes.
qed.


Proposition CatCat150. Let C be a category. For all f,g \in Hom(C) such that codom(f) = dom(g) we
have g \circ f \in Hom(C).

Proof.
  (Obj(C),Hom(C)) satisfies Hom2. Hence the thesis (by CatCat025). Indeed Obj(C),Hom(C) are classes.
qed.


Proposition CatCat152. Let C be a category. For all f,g \in Hom(C) such that codom(f) = dom(g) we
have dom(g \circ f) = dom(f) and codom(g \circ f) = codom(g).

Proof.
  (Obj(C),Hom(C)) satisfies Hom2. Hence the thesis (by CatCat025). Indeed Obj(C),Hom(C) are classes.
qed.


Proposition CatCat160. Let C be a category. For all f,g,h \in Hom(C) such that codom(f) = dom(g)
and codom(g) = dom(h) we have (h \circ g) \circ f = h \circ (g \circ f).

Proof.
  (Obj(C),Hom(C)) satisfies Hom5. Hence the thesis (by CatCat055). Indeed Obj(C),Hom(C) are classes.
qed.


Proposition CatCat165. Let C be a category. For all f,g,h \in Hom(C) such that codom(f) = dom(g)
and codom(g) = dom(h) we have dom((h \circ g) \circ f) = dom(f) and codom((h \circ g) \circ f) =
codom(h).

Proof.
  Let f,g,h \in Hom(C). Assume that codom(f) = dom(g) and codom(g) = dom(h). h \circ g lies in
  Hom(C).
qed.


Proposition CatCat175. Let C be a category. For all f \in Hom(C) we have dom(f),codom(f) \in Obj(C).

Proof.
  (Obj(C),Hom(C)) satisfies Hom6. Hence the thesis (by CatCat065). Indeed Obj(C),Hom(C) are classes.
qed.


Proposition CatCat180. Let C be a category. For all objects f if dom(f) \in Obj(C) or
codom(f) \in Obj(C) then f \in Hom(C).

Proof.
  (Obj(C),Hom(C)) satisfies Hom7. Hence the thesis (by CatCat075). Indeed Obj(C),Hom(C) are classes.
qed.
