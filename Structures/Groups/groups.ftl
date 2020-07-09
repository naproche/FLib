#
# Groups
# (Marcel Schütz, 2020)
#

#[prove off][check off]
[read FLib/Structures/Foundations/structures.ftl]
[read FLib/Structures/Sets/cardinality.ftl]
#[prove on][check on]


# 1. The group axioms

Signature GrpGrp000. GRP1 is an axiom.

Axiom GrpGrp005. Let X be a set and mul,inv be entities and e be an element of X. (X, mul, inv, e)
satisfies GRP1 iff mul is a function from X \times X to X and inv is a function from X to X.


Signature GrpGrp010. GRP2 is an axiom.

Axiom GrpGrp015. Let X be a set and mul,inv be entities and e be an element of X. (X, mul, inv, e)
satisfies GRP2 iff for all x,y,z \in X we have mul(x,mul(y,z)) = mul(mul(x,y),z).


Signature GrpGrp020. GRP3 is an axiom.

Axiom GrpGrp025. Let X be a set and mul,inv be entities and e be an element of X. (X, mul, inv, e)
satisfies GRP3 iff for all x \in X we have mul(x,e) = x = mul(e,x).


Signature GrpGrp030. GRP4 is an axiom.

Axiom GrpGrp035. Let X be a set and mul,inv be entities and e be an element of X. (X, mul, inv, e)
satisfies GRP4 iff for all x \in X we have mul(inv(x),x) = e = mul(x,inv(x)).


# 2. Groups

Signature GrpGrp040. GRP is a class.

Definition GrpGrp045. A group is an element of GRP.


Axiom GrpGrp050. Every group is a structure.


# 3. Constructing groups

Axiom GrpGrp055. GRP_{1} is a class such that GRP_{1} = {(X, mul, inv, e) | X is a set and mul,inv
are entities and e \in X and

  (X, mul, inv, e) satisfies GRP1 and

  (X, mul, inv, e) satisfies GRP2 and

  (X, mul, inv, e) satisfies GRP3 and

  (X, mul, inv, e) satisfies GRP4
}.


Signature GrpGrp060. Grp_{1} is a bijection between GRP_{1} and GRP.

Axiom GrpGrp065. Let G be an element of GRP_{1}. G_{GRP} = Grp_{1}(G).


Axiom GrpGrp070. Let X be a set and mul,inv be entities and e \in X. Assume that (X, mul, inv, e)
lies in GRP_{1}. Then

  X is the domain of (X, mul, inv, e)_{GRP}.


Lemma GrpGrp075. Let X be a set and mul,inv be entities and e \in X. Assume that (X, mul, inv, e)
lies in GRP_{1}. Then (X, mul, inv, e)_{GRP} is a group.

Proof.
  (X, mul, inv, e)_{GRP} = Grp_{1}(X, mul, inv, e). (X, mul, inv, e) is an element of the domain of
  Grp_{1}. GRP is the codomain of Grp_{1}. Hence (X, mul, inv, e)_{GRP} lies in GRP.
qed.


Lemma GrpGrp080. Let X be a set and mul,inv be entities and e \in X. Assume that (X, mul, inv, e)
lies in GRP_{1}. Let x \in X. Then (X, mul, inv, e)_{GRP}(x) \in (X, mul, inv, e)_{GRP}.

Proof.
  (X, mul, inv, e)_{GRP} is a group. Hence (X, mul, inv, e)_{GRP} is a structure. x lies in the
  domain of (X, mul, inv, e)_{GRP}. Indeed X is the domain of (X, mul, inv, e)_{GRP}. Then we have
  the thesis (by FoundStr020).
qed.


Axiom GrpGrp090. Let X be a set and mul,inv be entities and e \in X. Assume that (X, mul, inv, e)
lies in GRP_{1}. Then

  1_{(X, mul, inv, e)_{GRP}} = (X, mul, inv, e)_{GRP}(e).


Axiom GrpGrp095. Let X be a set and mul,inv be entities and e \in X. Assume that (X, mul, inv, e)
lies in GRP_{1}. Let x,y \in X. Then

  (X, mul, inv, e)_{GRP}(x) \cdot (X, mul, inv, e)_{GRP}(y) = (X, mul, inv, e)_{GRP}(mul(x,y)).


Axiom GrpGrp100. Let X be a set and mul,inv be entities and e \in X. Assume that (X, mul, inv, e)
lies in GRP_{1}. Let x \in X. Then

  ((X, mul, inv, e)_{GRP}(x))^{-1} = (X, mul, inv, e)_{GRP}(inv(x)).


# 4. Consequences of these axioms

Proposition GrpGrp105. Every group is a set.

Proof. [prove off] qed.


Proposition GrpGrp110. Let G be a group. Then 1_{G} is an element of G.

Proof. [prove off] qed.


Proposition GrpGrp115. Let G be a group. Let x,y \in G. Then x \cdot y is an element of G.

Proof. [prove off] qed.


Proposition GrpGrp120. Let G be a group. Let x \in G. Then x^{-1} is an element of G.

Proof. [prove off] qed.


Proposition GrpGrp125. Let G be a group. Let x,y,z \in G. Then

  x \cdot (y \cdot z) = (x \cdot y) \cdot z.

Proof. [prove off] qed.


Proposition GrpGrp130. Let G be a group. Let x \in G. Then

  x \cdot 1_{G} = x = 1_{G} \cdot x.

Proof. [prove off] qed.


Proposition GrpGrp135. Let G be a group. Let x \in G. Then

  x \cdot x^{-1} = 1_{G} = x^{-1} \cdot x.

Proof. [prove off] qed.


# 5. Basic properties of groups

Proposition GrpGrp140. Let G be a group. Let e \in G. Assume that e \cdot x = x for all x \in G.
Then e = 1_{G}.


Proposition GrpGrp145. Let G be a group. Let e \in G. Assume that x \cdot e = x for all x \in G.
Then e = 1_{G}.


Proposition GrpGrp150. Let G be a group. Let x,y \in G. Assume that x \cdot y = 1_{G}. Then y =
x^{-1}.

Proof.
  (x^{-1} \cdot x) \cdot y = x^{-1} \cdot (x \cdot y) (by GrpGrp125). Indeed x^{-1} \in G. Thus we
  have

  y
  = 1_{G} \cdot y
  = (x^{-1} \cdot x) \cdot y
  = x^{-1} \cdot (x \cdot y)
  = x^{-1} \cdot 1_{G}
  = x^{-1}.
qed.


Proposition GrpGrp155. Let G be a group. Let x,y \in G. Assume that y \cdot x = 1_{G}. Then y =
x^{-1}.

Proof.
  y \cdot (x \cdot x^{-1}) = (y \cdot x) \cdot x^{-1} (by GrpGrp125). Indeed x^{-1} \in G. Thus we
  have

  y
  = y \cdot 1_{G}
  = y \cdot (x \cdot x^{-1})
  = (y \cdot x) \cdot x^{-1}
  = 1_{G} \cdot x^{-1}
  = x^{-1}.
qed.


Proposition GrpGrp160. Let G be a group and x,y,z \in G. If x \cdot y = x \cdot z then y = z.

Proof.
  Assume that x \cdot y = x \cdot z. Then x^{-1} \cdot (x \cdot y) = x^{-1} \cdot (x \cdot z).
  x^{-1} \in G.

  x^{-1} \cdot (x \cdot y) = (x^{-1} \cdot x) \cdot y (by GrpGrp125). 
  x^{-1} \cdot (x \cdot z) = (x^{-1} \cdot x) \cdot z (by GrpGrp125).

  (x^{-1} \cdot x) \cdot y = 1_{G} \cdot y = y and (x^{-1} \cdot x) \cdot z = 1_{G} \cdot z = z.
qed.


Corollary GrpGrp162. Let G be a group and x,y \in G. If x = x \cdot y then y = 1_{G}.

Proof.
  Assume that x = x \cdot y. Then x \cdot 1_{G} = x \cdot y. Hence the thesis (by GrpGrp160). Indeed
  1_{G} \in G.
qed.


Proposition GrpGrp165. Let G be a group and x,y,z \in G. If x \cdot z = y \cdot z then x = y.

Proof.
  Assume that x \cdot z = y \cdot z. Then (x \cdot z) \cdot z^{-1} = (y \cdot z) \cdot z^{-1}.
  z^{-1} \in G.

  (x \cdot z) \cdot z^{-1} = x \cdot (z \cdot z^{-1}) (by GrpGrp125).
  (y \cdot z) \cdot z^{-1} = y \cdot (z \cdot z^{-1}) (by GrpGrp125).

  x \cdot (z \cdot z^{-1}) = x \cdot 1_{G} (by GrpGrp135). y \cdot (z \cdot z^{-1}) = y \cdot 1_{G}
  (by GrpGrp135). Hence x \cdot (z \cdot z^{-1}) = x and y \cdot (z \cdot z^{-1}) = y (by
  GrpGrp130).
qed.


Corollary GrpGrp167. Let G be a group and x,y \in G. If y = x \cdot y then x = 1_{G}.

Proof.
  Assume that y = x \cdot y. Then 1_{G} \cdot y = x \cdot y. Hence the thesis (by GrpGrp165). Indeed
  1_{G} \in G.
qed.


Proposition GrpGrp170. Let G be a group and x \in G. (x^{-1})^{-1} = x.

Proof.
  x \cdot x^{-1} = 1_{G}. Hence the thesis (by GrpGrp155). Indeed x^{-1} \in G.
qed.


Proposition GrpGrp175. Let G be a group and x,y \in G. (x \cdot y)^{-1} = y^{-1} \cdot x^{-1}.

Proof.
  x^{-1}, y^{-1}, x \cdot y \in G.
  
  (y^{-1} \cdot x^{-1}) \cdot (x \cdot y) = y^{-1} \cdot (x^{-1} \cdot (x \cdot y)) (by GrpGrp125).
  y^{-1} \cdot (x^{-1} \cdot (x \cdot y)) = y^{-1} \cdot ((x^{-1} \cdot x) \cdot y) (by GrpGrp125).
  y^{-1} \cdot ((x^{-1} \cdot x) \cdot y) = y^{-1} \cdot (1_{G} \cdot y) = y^{-1} \cdot y = 1_{G}.

  Thus (y^{-1} \cdot x^{-1}) \cdot (x \cdot y) = 1_{G}. Hence the thesis (by GrpGrp155). Indeed
  y^{-1} \cdot x^{-1}, x \cdot y \in G.
qed.


Proposition GrpGrp180. Let G be a group. 1_{G}^{-1} = 1_{G}.

Proof.
  1_{G} \cdot 1_{G}^{-1} = 1_{G}.
qed.


# 6. The trivial group

Proposition GrpGrp200. There is a group that has exactly one element.

Proof. [prove off] qed.


Axiom GrpGrp205. 1_{GRP} is a group that has exactly one element.

Let the trivial group stand for 1_{GRP}.
