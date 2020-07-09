#
# Group homomorphisms
# (Marcel Schütz, 2020)
#

#[prove off][check off]
[read FLib/Structures/Groups/abelian-groups.ftl]
#[prove on][check on]


# 1. Homomorphisms

Definition GrpHom000. Let G,H be groups. A group homomorphism between G and H is a map phi from G to
H such that phi(x \cdot y) = phi(x) \cdot phi(y) for all x,y \in G.


Lemma GrpHom002. Let G,H be groups and phi be a group homomorphism between G and H. Then phi is a
map.


# 1.1 Properties of homomorphisms between groups

Proposition GrpHom005. Let G,H be groups and phi be a group homomorphism between G and H. Let
x \in G. Then phi(x) \in H.


Proposition GrpHom010. Let G,H be groups and phi be a group homomorphism between G and H. Then
phi(1_{G}) = 1_{H}.

Proof.
  phi(1_{G}) = phi(1_{G}) = phi(1_{G} \cdot 1_{G}). phi(1_{G} \cdot 1_{G}) =
  phi(1_{G}) \cdot phi(1_{G}) (by GrpHom000). Indeed 1_{G} is an element of G. Hence the thesis (by
  GrpGrp162). Indeed phi(1_{G}) \in H.
qed.


Proposition GrpHom015. Let G,H be groups and phi be a group homomorphism between G and H. Let
x \in G. Then phi(x^{-1}) = phi(x)^{-1}.

Proof.
  phi(x^{-1}) \cdot phi(x) = phi(x^{-1} \cdot x) (by GrpHom000). Indeed x^{-1} \in G.
  phi(x^{-1} \cdot x) = phi(1_{G}) = 1_{H}. Hence the thesis (by GrpGrp155). Indeed phi(x^{-1}) and
  phi(x) are elements of H.
qed.


Proposition GrpHom020. Let G be a group. id_{G} is a group homomorphism between G and G.

Proof.
  id_{G} is a map from G to G. For all x,y \in G we have id_{G}(x \cdot y) =
  id_{G}(x) \cdot id_{G}(y). Indeed x \cdot y \in G for all x,y \in G.
qed.


Proposition GrpHom025. Let G,H,K be groups. Let phi be a group homomorphism between G and H and psi
be a group homomorphism between H and K. Then psi \circ phi is a group homomorphism between H and K.

Proof. [prove off] qed.


# 1.2 Properties of homomorphisms between abelian groups

Proposition GrpHom030. Let G,H be abelian groups and phi be a group homomorphism between G and H.
Let x,y \in G. Then phi(x + y) = phi(x) + phi(y).

Proof.
  phi(x + y) = phi(x \cdot y) = phi(x) \cdot phi(y) = phi(x) + phi(y) (by GrpAb005, GrpHom000,
  GrpHom005).
qed.


Proposition GrpHom035. Let G,H be abelian groups and phi be a group homomorphism between G and H.
Then phi(0_{G}) = 0_{H}.


Proposition GrpHom040. Let G,H be abelian groups and phi be a group homomorphism between G and H.
Let x \in G. Then phi(-x) = -phi(x).

Proof.
  phi(-x) = phi(x^{-1}). phi(x^{-1}) = phi(x)^{-1} (by GrpHom015). phi(x)^{-1} = -phi(x). Indeed
  phi(x) \in H.
qed.


Proposition GrpHom050. Let G,H be abelian groups and phi be a group homomorphism between G and H.
Let x,y \in G. Then phi(x - y) = phi(x) - phi(y).

Proof.
  phi(x - y) = phi(x + (-y)) = phi(x) + phi(-y) (by GrpAb015, GrpHom030). Indeed -y \in G.
  phi(-y) = -phi(y) (by GrpHom040). phi(x) + (-phi(y)) = phi(x) - phi(y) (by GrpAb015). Indeed
  phi(x),phi(y) \in H.
qed.


# 2. Endo, mono, epi, iso, auto

# 2.1 Definitions

Definition GrpHom070. Let G be a group. A group endomorphism on G is a group homomorphism between G
and G.

Definition GrpHom075. Let G,H be groups. A group monomorphism between G and H is an injective group
homomorphism between G and H.

Definition GrpHom080. Let G,H be groups. A group epimorphism between G and H is a surjective group
homomorphism between G and H.

Definition GrpHom085. Let G,H be groups. A group isomorphism between G and H is an invertible group
homomorphism f between G and H such that f^{-1} is a group homomorphism between H and G.

Definition GrpHom090. Let G be a group. A group automorphism on G is a group isomorphism between G
and G.


# 2.2 Properties

Proposition GrpHom095. Let G be a group. id_{G} is a group automorphism on G.

Proof. [prove off] qed.


Proposition GrpHom100. Let G,H be groups and f be a group homomorphism between G and H. f is a group
isomorphism between G and H iff f is bijective.

Proof. [prove off] qed.


Proposition GrpHom105. Let G,H be groups and f be a group isomorphism between G and H. Then f^{-1}
is a group isomorphism between H and G.

Proof. [prove off] qed.


Proposition GrpHom110. Let G,H,K be groups. Let phi be a group monomorphism between G and H and psi
be a group monomorphism between H and K. Then psi \circ phi is a group monomorphism between G and K.

Proof. [prove off] qed.


Proposition GrpHom115. Let G,H,K be groups. Let phi be a group epimorphism between G and H and psi
be a group epimorphism between H and K. Then psi \circ phi is a group epimorphism between G and K.

Proof. [prove off] qed.


Proposition GrpHom120. Let G,H,K be groups. Let phi be a group isomorphism between G and H and psi
be a group isomorphism between H and K. Then psi \circ phi is a group isomorphism between G and K.

Proof. [prove off] qed.


# 2.3 Isomorphic groups

Axiom GrpHom140. Let G,H be groups. G and H are isomorphic iff there is a group isomorphism between
G and H.


Proposition GrpHom145. Let G be a group. G and G are isomorphic.

Proof. [prove off] qed.


Proposition GrpHom150. Let G,H be groups. If G and H are isomorphic then H and G are isomorphic.

Proof. [prove off] qed.


Proposition GrpHom155. Let G,H,K be groups. If G and H are isomorphic and H and K are isomorphic
then G and K are isomorphic.

Proof. [prove off] qed.


Proposition GrpHom160. Let G be a group that has exactly one element. Then G and the trivial group
are isomorphic.

Proof. [prove off] qed.
