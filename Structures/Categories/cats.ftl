#
# Categories
# (Marcel Schütz, 2020)
#

#[prove off][check off]
[read FLib/Structures/Foundations/structures.ftl]
#[prove on][check on]


# 1. Categories

Signature CatCat000. CAT is a class.

Definition CatCat005. A category is an element of CAT.

Axiom CatCat010. Every category is a structure.


Lemma CatCat011. Every category is a map.


Definition CatCat015. A small category is a category C such that Obj(C) and Hom(C) are sets.

Definition CatCat020. A large category is a category that is not a small category.


Definition CatCat025. Let C be a category. An object of C is an element of Obj(C).

Definition CatCat027. An object is an object of some category.


# 2. Instances of CAT

# 2.1 Axioms for instances of CAT

Signature CatCat030. Cat1 is an axiom.

Axiom CatCat035. Let O,H be classes and i,d,c,o be functions. (O,H,i,d,c,o) satisfies Cat1 iff
dom(c),dom(d) = H and c(x),d(x) \in O for all x \in H.


Signature CatCat040. Cat2 is an axiom.

Axiom CatCat045. Let O,H be classes and i,d,c,o be functions. (O,H,i,d,c,o) satisfies Cat2 iff
dom(i) = O and for all x \in O we have i(x) \in H and d(i(x)) = x = c(i(x)).


Signature CatCat050. Cat3 is an axiom.

Axiom CatCat055. Let O,H be classes and i,d,c,o be functions. (O,H,i,d,c,o) satisfies Cat3 iff
dom(o) = {(f,g) | f,g \in H and c(f) = d(g)}.


Signature CatCat060. Cat4 is an axiom.

Axiom CatCat065. Let O,H be classes and i,d,c,o be functions. (O,H,i,d,c,o) satisfies Cat4 iff
for all f,g \in H such that c(f) = d(g) we have o(f,g) \in H and d(o(f,g)) = d(f) and
(o(f,g)) = c(g).


Signature CatCat070. Cat5 is an axiom.

Axiom CatCat075. Let O,H be classes and i,d,c,o be functions. (O,H,i,d,c,o) satisfies Cat5 iff
for all f \in H we have o(f,i(c(f))) = f = o(i(d(f)),f).


Signature CatCat080. Cat6 is an axiom.

Axiom CatCat085. Let O,H be classes and i,d,c,o be functions. (O,H,i,d,c,o) satisfies Cat6 iff
for all f,g,h \in H such that c(f) = d(g) and c(g) = d(h) we have o(f,o(g,h)) = o(o(f,g),h).


# 2.2 CAT_{1}

Axiom CatCat090. CAT_{1} is a class such that CAT_{1} = {X | there are classes O,H and functions
i,d,c,o such that X = (O,H,i,d,c,o) and

  X satisfies Cat1 and

  X satisfies Cat2 and

  X satisfies Cat3 and

  X satisfies Cat4 and

  X satisfies Cat5 and

  X satisfies Cat6
}.


# 3. Constructing categories

# 3.1 Axioms that describe the "lifting properties" of a category

Signature CatCat095. CAT1 is an axiom.

Axiom CatCat100. Let C be a category and O,H be classes and i,c,d,o be functions. (C,(O,H,i,d,c,o))
satisfies CAT1 iff dom(C) = O \cup H.


Signature CatCat105. CAT2 is an axiom.

Axiom CatCat110. Let C be a category and O,H be classes and i,c,d,o be functions. (C,(O,H,i,d,c,o))
satisfies CAT2 iff Obj(C) = C[O] and Hom(C) = C[H].


Signature CatCat115. CAT3 is an axiom.

Axiom CatCat120. Let C be a category and O,H be classes and i,c,d,o be functions. (C,(O,H,i,d,c,o))
satisfies CAT3 iff for all x \in O we have C(i(x)) = id_{C(x)}.


Signature CatCat125. CAT4 is an axiom.

Axiom CatCat130. Let C be a category and O,H be classes and i,c,d,o be functions. (C,(O,H,i,d,c,o))
satisfies CAT4 iff for all f \in H we have C(d(f)) = dom(C(f)) and C(c(f)) = codom(C(f)).


Signature CatCat135. CAT5 is an axiom.

Axiom CatCat140. Let C be a category and O,H be classes and i,c,d,o be functions. (C,(O,H,i,d,c,o))
satisfies CAT5 iff for all f,g \in H such that c(f) = d(g) we have C(o(f,g)) = C(g) \circ C(f).


# 3.2 Cat_{1}

Signature CatCat145. Cat_{1} is a bijection between CAT_{1} and CAT.

Axiom CatCat150. Let X \in CAT_{1}. Then

  (Cat_{1}(X),X) satisfies CAT1 and

  (Cat_{1}(X),X) satisfies CAT2 and

  (Cat_{1}(X),X) satisfies CAT3 and

  (Cat_{1}(X),X) satisfies CAT4 and

  (Cat_{1}(X),X) satisfies CAT5.


# 3.3 Some technical lemmas

Lemma CatCat155. Let C be a category. Then there is an element X of CAT_{1} such that
C = Cat_{1}(X).

Proof.
  Cat_{1} is a bijection between CAT_{1} and CAT. Cat_{1} is a surjective map. Thus we can take an
  element X of CAT_{1} such that Cat_{1}(X) = C (by FoundMap100, CatCat005). Indeed dom(Cat_{1}) =
  CAT_{1} and codom(Cat_{1}) = CAT.
qed.


Lemma CatCat157. Let C be a category and A \in Obj(C). Let O,H be classes and i,d,c,o be functions
such that (O,H,i,d,c,o) \in CAT_{1} and C = Cat_{1}(O,H,i,d,c,o). Then C^{-1}(A) \in O.

Proof.
  (C,(O,H,i,d,c,o)) satisfies CAT2 (by CatCat150). Hence Obj(C) = C[O]. Then A \in C[O].
  C[O] = {C(x) | x \in O \cap dom(C)} (by FoundMap180). Indeed C is a map. (C,(O,H,i,d,c,o))
  satisfies CAT1 (by CatCat150). Hence dom(C) = O \cup H. Thus O \cap dom(C) = O. Therefore C[O] =
  {C(x) | x \in O}. Then we can take an element a of O such that C(a) = A. a lies in the domain of
  C. Thus a = C^{-1}(A) (by FoundMap177). Indeed C is a bijective map.
qed.


Lemma CatCat158. Let C be a category and f \in Hom(C). Let O,H be classes and i,d,c,o be functions
such that (O,H,i,d,c,o) \in CAT_{1} and C = Cat_{1}(O,H,i,d,c,o). Then C^{-1}(f) \in H.

Proof.
  (C,(O,H,i,d,c,o)) satisfies CAT2 (by CatCat150). Hence Hom(C) = C[H]. Then f \in C[H].
  C[H] = {C(x) | x \in H \cap dom(C)} (by FoundMap180). Indeed C is a map. (C,(O,H,i,d,c,o))
  satisfies CAT1 (by CatCat150). Hence dom(C) = O \cup H. Thus H \cap dom(C) = H. Therefore C[H] =
  {C(x) | x \in H}. Then we can take an element g of H such that C(g) = f. g lies in the domain of
  C. Thus g = C^{-1}(f) (by FoundMap177). Indeed C is a bijective map.
qed.


# 4. Properties of categories

Proposition CatCat160. Let C be a category. Obj(C) is a class.

Proof.
  Take an element X of CAT_{1} such that C = Cat_{1}(X) (by CatCat155). Then we can take classes O,H
  and functions i,d,c,o such that X = (O,H,i,d,c,o) (by CatCat090). Obj(C) = C[O] (by CatCat110).
  Indeed (C,X) satisfies CAT2 (by CatCat150).
qed.


Proposition CatCat165. Let C be a category. Hom(C) is a class.

Proof.
  Take an element X of CAT_{1} such that C = Cat_{1}(X) (by CatCat155). Then we can take classes O,H
  and functions i,d,c,o such that X = (O,H,i,d,c,o) (by CatCat090). Hom(C) = C[H] (by CatCat110).
  Indeed (C,X) satisfies CAT2 (by CatCat150).
qed.


Proposition CatCat170. Let C be a category. range(C) = Obj(C) \cup Hom(C).

Proof.
  Take an element X of CAT_{1} such that C = Cat_{1}(X) (by CatCat155). Then we can take classes O,H
  and functions i,d,c,o such that X = (O,H,i,d,c,o) (by CatCat090). dom(C) = O \cup H (by
  CatCat100). Indeed (C,X) satisfies CAT1 (by CatCat150). range(C) = C[dom(C)] = C[O \cup H] (by
  FoundMap185). Indeed C is a map. C[O \cup H] = C[O] \cup C[H] (by FoundMap226). Indeed C is a map.
  C[O] = Obj(C) and C[H] = Hom(C) (by CatCat110). Indeed (C,X) satisfies CAT2 (by CatCat150).
qed.


Proposition CatCat175. Let C be a category. id_{A} \in Hom(C) for all A \in Obj(C).

Proof.
  Take an element X of CAT_{1} such that C = Cat_{1}(X) (by CatCat155). Then we can take classes O,H
  and functions i,d,c,o such that X = (O,H,i,d,c,o) (by CatCat090). Let A \in Obj(C). Then
  C^{-1}(A) \in O (by CatCat157). C is a bijective map and A \in range(C). Take a \in dom(C) such
  that a = C^{-1}(A) (by FoundMap178). Hence C(i(a)) = id_{C(a)} (by CatCat120). Indeed (C,X)
  satisfies CAT3. Thus id_{A} = C(i(a)). Indeed C is a bijective map. a \in O.
  Thus i(a) is an element of H (by CatCat045). Indeed X satisfies Cat2 (by CatCat090). dom(C) =
  O \cup H (by CatCat100). Indeed (C,X) satisfies CAT1. Therefore i(a) \in dom(C). Then
  i(a) \in H \cap dom(C). Hence C(i(a)) \in C[H]. Indeed C[H] = {C(x) | x \in H \cap dom(C)} (by
  FoundMap180). C[H] = Hom(C) (by CatCat110). Indeed (C,X) satisfies CAT2. Thus id_{A} \in Hom(C).
qed.


Proposition CatCat180. Let C be a category. dom(id_{X}) = X = codom(id_{X}) for all X \in Obj(C).

# This statement follows immediately from the fact that id_{X} is the identity map for arbitrary
# objects X. But we do not have to worry about it since the identity map and the identity morphism
# have the same behaviour with regard to composition.


Proposition CatCat185. Let C be a category. For all f \in Hom(C) we have id_{codom(f)} \circ f = f.

Proof. [prove off] qed.


Proposition CatCat190. Let C be a category. For all f \in Hom(C) we have f \circ id_{dom(f)} = f.

Proof. [prove off] qed.


Proposition CatCat195. Let C be a category. For all f,g \in Hom(C) such that codom(f) = dom(g) we
have g \circ f \in Hom(C).

Proof. [prove off] qed.


Proposition CatCat200. Let C be a category. For all f,g \in Hom(C) such that codom(f) = dom(g) we
have dom(g \circ f) = dom(f) and codom(g \circ f) = codom(g).

Proof. [prove off] qed.


Proposition CatCat205. Let C be a category. For all f,g,h \in Hom(C) such that codom(f) = dom(g)
and codom(g) = dom(h) we have (h \circ g) \circ f = h \circ (g \circ f).

Proof. [prove off] qed.


Proposition CatCat210. Let C be a category. For all f \in Hom(C) we have dom(f),codom(f) \in Obj(C).

Proof. [prove off] qed.


# 5. Another way of constructing categories

Signature CatCat215. Hom1 is an axiom.

Axiom CatCat220. Let O,H be classes. (O,H) satisfies Hom1 iff every element of H is a map from some
element of O to some element of O.


Signature CatCat225. Hom2 is an axiom.

Axiom CatCat230. Let O,H be classes. (O,H) satisfies Hom2 iff for all X \in O we have id_{X} \in H
and dom(id_{X}) = X = codom(id_{X}).


Signature CatCat235. Hom3 is an axiom.

Axiom CatCat240. Let O,H be classes. (O,H) satisfies Hom3 iff for all f,g \in H such that codom(f) =
dom(g) we have g \circ f \in H and dom(g \circ f) = dom(f) and codom(g \circ f) = codom(g).


Signature CatCat245. Hom4 is an axiom.

Axiom CatCat250. Let O,H be classes. (O,H) satisfies Hom4 iff for all f \in H we have
id_{codom(f)} \circ f = f = f \circ id_{dom(f)}.


Signature CatCat255. Hom5 is an axiom.

Axiom CatCat260. Let O,H be classes. (O,H) satisfies Hom5 iff for all f,g,h \in H such that
codom(f) = dom(g) and codom(g) = dom(h) we have (h \circ g) \circ f = h \circ (g \circ f).


Signature CatCat280. Hom6 is an axiom.

Axiom CatCat285. Let O,H be classes. (O,H) satisfies Hom6 iff dom(f) and codom(f) lie in O for all
f \in H.


Definition CatCat290. Let O be a class. A homomorphism class over O is a class H such that

  (O,H) satisfies Hom1 and

  (O,H) satisfies Hom2 and

  (O,H) satisfies Hom3 and

  (O,H) satisfies Hom4 and

  (O,H) satisfies Hom5 and

  (O,H) satisfies Hom6.


Axiom CatCat295. CAT_{2} is a class such that CAT_{2} = {(O,H) | O,H are classes such that H is a
homomorphism class over O}.


Definition CatCat300. Let O be a class. identity_{O} is a function of O such that identity_{O}(X) =
id_{X} for all X \in O.

Definition CatCat305. Let H be a class. domain_{H} is a function of H such that domain_{H}(f) =
dom(f) for all f \in H.

Definition CatCat310. Let H be a class. codomain_{H} is a function of H such that codomain_{H}(f) =
codom(f) for all f \in H.

Definition CatCat315. Let H be a class. composition_{H} is a function such that dom(composition_{H})
= {(f,g) | f,g \in H and dom(g) = codom(f)} and composition_{H}(f,g) = g \circ f for all f,g \in H
such that dom(g) = codom(f).


Proposition CatCat320. Let O,H be classes such that H is a homomorphism class over O. Then
(O, H, identity_{O}, domain_{H}, codomain_{H}, composition_{H}) lies in the domain of Cat_{1}.

Proof. [prove off] qed.


Signature CatCat330. Cat_{2} is a map from CAT_{2} to CAT.

Axiom CatCat335. Let O,H be classes such that H is a homomorphism class over O. Then Cat_{2}(O,H) =
Cat_{1}(O, H, identity_{O}, domain_{H}, codomain_{H}, composition_{H}).


Lemma CatCat340. Cat_{2} is injective.

Proof. [prove off] qed.


Axiom CatCat345. Let O,H be classes such that H is a homomorphism class over O. Then (O,H)_{CAT} =
Cat_{2}(O,H).


Lemma CatCat350. Let O,H be classes such that H is a homomorphism class over O. Then O \cup H is the
domain of (O,H)_{CAT}.

Proof. [prove off] qed.


Lemma CatCat355. Let O,H be classes such that H is a homomorphism class over O. Let x \in O. Then
(O,H)_{CAT}(x) \in Obj((O,H)_{CAT}).

Proof. [prove off] qed.


Lemma CatCat360. Let O,H be classes such that H is a homomorphism class over O. Let f \in H. Then
(O,H)_{CAT}(f) \in Hom((O,H)_{CAT}).

Proof. [prove off] qed.


Lemma CatCat365. Let O,H be classes such that H is a homomorphism class over O. Let
X \in Obj((O,H)_{CAT}). Then there is an element x of O such that X = (O,H)_{CAT}(x).

Proof. [prove off] qed.


Lemma CatCat370. Let O,H be classes such that H is a homomorphism class over O. Let
F \in Hom((O,H)_{CAT}). Then there is an element f of H such that F = (O,H)_{CAT}(f).

Proof. [prove off] qed.
