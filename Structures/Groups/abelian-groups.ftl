#
# Abelian groups
# (Marcel Schütz, 2020)
#

#[prove off][check off]
[read FLib/Structures/Groups/groups.ftl]
#[prove on][check on]


# 1. Definition

Axiom GrpAb000. Let G be a group. G is abelian iff x \cdot y = y \cdot x for all x,y \in G.


Axiom GrpAb005. Let G be an abelian group. Then x \cdot y = x + y for all x,y \in G.

Axiom GrpAb010. Let G be an abelian group and x \in G. Then x^{-1} = -x.

Axiom GrpAb015. Let G be an abelian group and x,y \in G. Then x - y = x + (-y).

Axiom GrpAb020. Let G be an abelian group. 1_{G} = 0_{G}.


# 2. Basic properties

Proposition GrpAb023. Let G be an abelian group. Then 0_{G} is an element of G.

Proposition GrpAb025. Let G be an abelian group. Let x,y \in G. Then x + y is an element of G.

Proposition GrpAb030. Let G be an abelian group. Let x \in G. Then -x is an element of G.


Proposition GrpAb033. Let G be an abelian group. Let x,y \in G. Then x - y is an element of G.

Proof.
  x - y = x + (-y).
qed.


Proposition GrpAb034. Let G be an abelian group. Let x,y \in G. Then x + y = y + x.

Proof.
  x + y = x \cdot y = y \cdot x = y + x.
qed.


Proposition GrpAb035. Let G be an abelian group. Let x,y,z \in G. Then x + (y + z) = (x + y) + z.

Proof.
  x + (y + z) = x \cdot (y \cdot z) and (x \cdot y) \cdot z = (x + y) + z (by GrpAb005, GrpAb025).
  x \cdot (y \cdot z) = (x \cdot y) \cdot z (by GrpGrp125).
qed.


Proposition GrpAb040. Let G be an abelian group. Let x \in G. Then x + 0_{G} = x = 0_{G} + x.

Proof.
  0_{G} = 1_{G}. Hence 0_{G} \in G. Thus x + 0_{G} = x \cdot 1_{G} and 0_{G} + x = 1_{G} \cdot x (by
  GrpAb005).
qed.


Proposition GrpAb045. Let G be an abelian group. Let x \in G. Then x + (-x) = 0_{G} = -x + x.

Proof.
  -x \in G. 0_{G} = 1_{G}. -x = x^{-1}. Hence x + (-x) = x \cdot x^{-1} and -x + x = x^{-1} \cdot x
  (by GrpAb005).
qed.


Proposition GrpAb050. Let G be an abelian group and x \in G. Then x - x = 0_{G}.

Proof.
  x - x = x + (-x).
qed.


Proposition GrpAb060. Let G be an abelian group. Let e \in G. Assume that e + x = x for all x \in G.
Then e = 0_{G}.


Proposition GrpAb065. Let G be an abelian group. Let e \in G. Assume that x + e = x for all x \in G.
Then e = 0_{G}.


Proposition GrpAb070. Let G be an abelian group. Let x,y \in G. Assume that x + y = 0_{G}. Then y =
-x.

Proof.
  x \cdot y = 1_{G}. Hence y = x^{-1} (by GrpGrp150). x^{-1} = -x.
qed.


Proposition GrpAb075. Let G be an abelian group. Let x,y \in G. Assume that y + x = 0_{G}. Then y =
-x.

Proof.
  y \cdot x = 1_{G}. Hence y = x^{-1} (by GrpGrp155). x^{-1} = -x.
qed.


Proposition GrpAb080. Let G be an abelian group and x,y,z \in G. If x + y = x + z then y = z.

Proof.
  Assume x + y = x + z. Then x \cdot y = x \cdot z. Hence y = z (by GrpGrp160).
qed.


Proposition GrpAb085. Let G be an abelian group and x,y,z \in G. If x + z = y + z then x = y.

Proof.
  Assume x + z = y + z. Then x \cdot z = y \cdot z. Hence x = y (by GrpGrp165).
qed.


Proposition GrpAb090. Let G be an abelian group and x \in G. -(-x) = x.

Proof.
  -x = x^{-1}. Hence -(-x) = (x^{-1})^{-1}.
qed.


Proposition GrpAb095. Let G be an abelian group and x,y \in G. -(x + y) = (-y) + (-x) = -y - x.

Proof.
  x + y = x \cdot y. x + y \in G. Hence -(x + y) = (x \cdot y)^{-1}. (x \cdot y)^{-1} =
  y^{-1} \cdot x^{-1} (by GrpGrp175). y^{-1} \cdot x^{-1} = (-y) \cdot (-x). (-y) \cdot (-x) =
  (-y) + (-x). Indeed -x,-y \in G.
qed.


Proposition GrpAb100. Let G be an abelian group and x,y \in G. x - y = -y + x.

Proof.
  x - y = x + (-y).
qed.
