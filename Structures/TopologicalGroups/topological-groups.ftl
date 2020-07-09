#
# Topological groups
# (Marcel Schütz, 2020)
#

#[prove off][check off]
[read FLib/Structures/Foundations/operations.ftl]
[read FLib/Structures/Groups/groups.ftl]
[read FLib/Structures/TopologicalSpaces/product-spaces.ftl]
#[prove on][check on]


# 1. Topological groups

# 1.1 Axioms for topological groups

Axiom TgTg000. Let G be a group. \cdot_{G} is a map from G \times G to G.

Axiom TgTg005. Let G be a group. ^{-1}_{G} is a map from G to G.


Signature TgTg010. TG1 is an axiom.

Axiom TgTg015. Let G be a group and T be a topological space such that dom(G) = dom(T). Let i be the
inclusion of G into T and j be the inclusion of T \times T into G \times G. (G,T) satisfies TG1 iff
(i \circ \cdot_{G}) \circ j is continuous.


Signature TgTg020. TG2 is an axiom.

Axiom TgTg025. Let G be a group and T be a topological space such that dom(G) = dom(T). Let i be the
inclusion of G into T and j be the inclusion of T into G. (G,T) satisfies TG1 iff
(i \circ ^{-1}_{G}) \circ j is continuous.


# 1.2 Constructing topological groups

Signature TgTg030. TOPGRP is a class.

Definition TgTg035. A topological group is an element of TOPGRP.

Axiom TgTg040. Every topological group is a structure.


Axiom TgTg045. TOPGRP_{1} = {(G,T) | G is a group and T is a topological space such that dom(G) =
dom(T) and

  (G,T) satisfies TG1 and

  (G,T) satisfies TG2
}.

Signature TgTg050. TopGrp_{1} is a bijection between TOPGRP_{1} and TOPGRP.

Axiom TgTg055. Let G be a group and T be a topological space such that (G,T) \in TOPGRP_{1}. Then
(G,T)_{TOPGRP} = TOPGRP_{1}(G,T).


Axiom TgTg060. Let G be a group and T be a topological space such that (G,T) \in TOPGRP_{1}. Then
the domain of G is the domain of (G,T)_{TOPGRP}.


Lemma TgTg065. Let G be a group and T be a topological space such that (G,T) \in TOPGRP_{1}. Then
the domain of T is the domain of (G,T)_{TOPGRP}.

Proof. [prove off] qed.


Lemma TgTg070. Let G be a group and T be a topological space such that (G,T) \in TOPGRP_{1}. Let x
be an element of dom(G). Then (G,T)_{TOPGRP}(x) is an element of (G,T)_{TOPGRP}.

Proof. [prove off] qed.


Lemma TgTg075. Let G be a group and T be a topological space such that (G,T) \in TOPGRP_{1}. Let x
be an element of dom(T). Then (G,T)_{TOPGRP}(x) is an element of (G,T)_{TOPGRP}.

Proof. [prove off] qed.


Lemma TgTg080. Every topological group is a set.

Proof. [prove off] qed.


Axiom TgTg085. Let G be a group and T be a topological space such that (G,T) \in TOPGRP_{1}. Let
x,y \in dom(G). Then (G,T)_{TOPGRP}(x) \cdot (G,T)_{TOPGRP}(y) = G(x) \cdot G(y).

Axiom TgTg090. Let G be a group and T be a topological space such that (G,T) \in TOPGRP_{1}. Let
x \in dom(G). Then ((G,T)_{TOPGRP}(x))^{-1} = G(x)^{-1}.

Axiom TgTg095. Let G be a group and T be a topological space such that (G,T) \in TOPGRP_{1}. Then
1_{(G,T)_{TOPGRP}} = (G,T)_{TOPGRP}(G^{-1}(1_{G})).

Axiom TgTg100. Let G be a group and T be a topological space such that (G,T) \in TOPGRP_{1}. Let
A be a subset of T. Then (G,T)_{TOPGRP}[A] is open iff T[A] is open.


# 1.3 Identifying topological groups with groups and topological spaces

Axiom TgTg105. Every topological group is a group.

Axiom TgTg110. Every topological group is a topological space.


# 2. Consequences of the axioms

Proposition TgTg115. Let G be a topological group. Then \cdot_{G} is continuous.

Proof. [prove off] qed.


Proposition TgTg120. Let G be a topological group. Then ^{-1}_{G} is continuous.

Proof. [prove off] qed.
