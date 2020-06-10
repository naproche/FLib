#
# Functors
# (Marcel Schütz, 2020)
#

#[prove off]
[read ForTheLib/Categories/morphisms.ftl]
[read ForTheLib/Foundations/maps.ftl]
#[prove on]


# 1. Functors

# 1.1 Maps between categories

Definition CatFun000. A map between categories is a map from some category to some category.


Lemma CatFun005. Let F be a map between categories and X \in Obj(dom(F)). Then X \in dom(F).


Lemma CatFun010. Let F be a map between categories and f \in Hom(dom(F)). Then f \in dom(F).


Lemma CatFun015. Let F be a map between categories and f,g \in Hom(dom(F)). Assume that codom(f) =
dom(g). Then g \circ f \in dom(F).

Proof.
  g \circ f is a morphism between dom(f) and codom(g).
qed.


# 1.1 Axioms for functors

Signature CatFun020. Fun1 is an axiom.

Axiom CatFun025. Let F be a map between categories. F satisfies Fun1 iff for all X \in Obj(dom(F))
we have F(X) \in Obj(codom(F)).


Signature CatFun030. Fun2 is an axiom.

Axiom CatFun035. Let F be a map between categories. F satisfies Fun2 iff for all f \in Hom(dom(F))
we have F(f) \in Hom(codom(F)).


Signature CatFun040. Fun3 is an axiom.

Axiom CatFun045. Let F be a map between categories. F satisfies Fun3 iff for all X \in Obj(dom(F))
we have F(id_{X}) = id_{F(X)}.


# Convariance

Signature CatFun050. Fun4 is an axiom.

Axiom CatFun055. Let F be a map between categories. F satisfies Fun4 iff for all f \in Hom(dom(F))
we have dom(F(f)) = F(dom(f)) and codom(F(f)) = F(codom(f)).


Signature CatFun060. Fun5 is an axiom.


Axiom CatFun065. Let F be a map between categories. F satisfies Fun5 iff for all f,g \in Hom(dom(F))
such that codom(f) = dom(g) we have F(g \circ f) = F(g) \circ F(f).


# Contravariance

Signature CatFun070. Fun6 is an axiom.

Axiom CatFun075. Let F be a map between categories. F satisfies Fun6 iff for all f \in Hom(dom(F))
we have dom(F(f)) = F(codom(f)) and codom(F(f)) = F(dom(f)).


Signature CatFun080. Fun7 is an axiom.

Axiom CatFun085. Let F be a map between categories. F satisfies Fun7 iff for all f,g \in Hom(dom(F))
such that codom(f) = dom(g) we have F(g \circ f) = F(f) \circ F(g).


# 1.2 Definitions of functors

# NOTE: We cannot write "a map F between categories" instead of "a map between categories F".

Definition CatFun090. A covariant functor is a map between categories F such that F satisfies Fun1
and Fun2 and Fun3 and Fun4 and Fun5.

Definition CatFun095. A contravariant functor is a map between categories F such that F satisfies
Fun1 and Fun2 and Fun3 and Fun6 and Fun7.

Definition CatFun100. A functor is a covariant functor.


Definition CatFun102. Let C,D be categories. A functor between C and D is a functor F such that
dom(F) = C and codom(F) = D.


# 2. Full, faithful, fully faithful and essentially surjective

Axiom CatFun105. Let F be a functor and X,Y \in Obj(dom(F)). F_{X,Y} is a map from Hom(X,Y) to
Hom(F(X),F(Y)).


Lemma CatFun107. Let F be a functor and X,Y \in Obj(dom(F)). Then F_{X,Y} is a map.

Proof.
  F_{X,Y} is a map from Hom(X,Y) to Hom(F(X),F(Y)) (by CatFun105).
qed.


Lemma CatFun110. Let F be a functor and X,Y \in Obj(dom(F)). Let f \in Hom(X,Y). Then f lies in the
domain of F_{X,Y}.

Proof.
  dom(F_{X,Y}) = Hom(X,Y). Indeed F_{X,Y} is a map from Hom(X,Y) to Hom(F(X),F(Y)) (by CatFun105).
qed.


Axiom CatFun115. Let F be a functor and X,Y \in Obj(dom(F)). Let f \in Hom(X,Y). F_{X,Y}(f) = F(f).


Definition CatFun120. Let F be a functor. F is full iff F_{X,Y} is surjective for all
X,Y \in Obj(dom(F)).

Definition CatFun125. Let F be a functor. F is faithful iff F_{X,Y} is injective for all
X,Y \in Obj(dom(F)).

Definition CatFun130. Let F be a functor. F is fully faithful iff F is full and faithful.


Proposition CatFun135. Let F be a functor. F is fully faithful iff F_{X,Y} is bijective for all
X,Y \in Obj(dom(F)).

Proof.
  If F is fully faithful then F_{X,Y} is bijective for all X,Y \in Obj(dom(F)).
  proof.
    Assume that F is fully faithful. Then F is full and faithful. Let X,Y \in Obj(dom(F)). F_{X,Y}
    is injective (by CatFun125). F_{X,Y} is surjective (by CatFun120). Hence F_{X,Y} is bijective
    (by FoundMap110). Indeed F_{X,Y} is a map (by CatFun107).
  end.

  If F_{X,Y} is bijective for all X,Y \in Obj(dom(F)) then F is fully faithful.
  proof.
    Assume that F_{X,Y} is bijective for all X,Y \in Obj(dom(F)). F_{X,Y} is injective and
    surjective For all X,Y \in Obj(dom(F)) (by FoundMap110). Indeed F_{X,Y} is a map for all
    X,Y \in Obj(dom(F)) (by CatFun107). F is full and faithful (by CatFun120,CatFun125).
  end.
qed.


Definition CarFun140. Let F be a functor. F is essentially surjective iff For all objects y of
codom(F) there is an object x of dom(F) such that F(x) \cong y.


# 3. Isomorphic categories

Axiom CatFun150. Let C,D be categories. C and D are isomorphic iff there are functors F,G such that
F \circ G = id_{D} and G \circ F = id_{C}.
