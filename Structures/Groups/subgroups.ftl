#
# Subgroups
# (Marcel Schütz, 2020)
#

#[prove off][check off]
[read FLib/Structures/Groups/homomorphisms.ftl]
#[prove on][check on]


# 1. Subgroups

Definition GrpSub000. Let G be a group. A subgroup of G is a substructure H of G that is a group
such that the inclusion of H into G is a group homomorphism between H and G.


Axiom GrpSub005. Let G,H be groups. G < H iff G is a subgroup of H.


# 1.1 Constructing subgroups

Proposition GrpSub010. Let G be a group and A be a nonempty subset of G. Assume that for all
x,y \in A we have x \cdot y \in A. Assume that for all x \in A we have x^{-1} \in A. Then there is a
subgroup H of G such that A is the image of H under the inclusion of H into G.

Proof. [prove off] qed.


Proposition GrpSub015. Let G be a group and A be a nonempty subset of G. Assume that for all
x,y \in A we have x \cdot y^{-1} \in A. Then there is a subgroup H of G such that A is the image of
H under the inclusion of H into G.

Proof.
  1_{G} \in A.
  proof.
    Take an element x of A. Then x \cdot x^{-1} \in A. x and x^{-1} are elements of G. Hence
    x \cdot x^{-1} = 1_{G}.
  end.

  For all x \in A we have x^{-1} \in A.
  proof.
    Let x \in A. Then 1_{G} \cdot x^{-1} \in A. x^{-1} lies in G. Thus 1_{G} \cdot x^{-1} = x^{-1}.
  end.

  For all x,y \in A we have x \cdot y \in A.
  proof.
    Let x,y \in A. Then y^{-1} \in A. Hence x \cdot (y^{-1})^{-1} is an element of A. (y^{-1})^{-1}
    = y. Indeed y lies in G.
  end.

  Then we have the thesis (by GrpSub010).
qed.


# 2. The inclusion map

Lemma GrpSub020. Let G be a group and H be a subgroup of G. The inclusion of H into G is an
injective map.

Proof.
  G is a structure and H is a substructure of G. Hence the thesis (by FoundStr050).
qed.


Lemma GrpSub025. Let G be a group and H be a subgroup of G. Let i be the inclusion of H into G.
Then i(x) \in G for all x \in H.


Lemma GrpSub030. Let G be a group and H be a subgroup of G. Let i be the inclusion of H into
G. Then i(x \cdot y) = i(x) \cdot i(y) for all x,y \in H.

Proof.
  Let x,y \in H. G and H are groups and i is a group homomorphism between H and G. Hence the thesis
  (by GrpHom000).
qed.


Lemma GrpSub035. Let G be a group and H be a subgroup of G. Let i be the inclusion of H into G.
Then i(x^{-1}) = i(x)^{-1} for all x \in H.

Proof.
  Let x \in H. G and H are groups and i is a group homomorphism between H and G. Hence the thesis
  (by GrpHom015).
qed.


Lemma GrpSub040. Let G be a group and H be a subgroup of G. Let i be the inclusion of H into G. Then
i(1_{H}) = 1_{G}.

Proof.
  G and H are groups and i is a group homomorphism between H and G. Hence the thesis (by GrpHom010).
qed.


Lemma GrpSub045. Let G be a group and H be a subgroup of G. Let i be the inclusion of H into G. Then
i[H] = {i(x) | x \in H}.


Proposition GrpSub050. Every subgroup of any abelian group is abelian.

Proof.
  Let G be an abelian group and H be a subgroup of G. Then g \cdot h = h \cdot g for all g,h \in G.

  For all x,y \in H we have x \cdot y = y \cdot x.
  proof.
    Let x,y \in H. Take a map i from H to G that is the inclusion of H into G. i(x) and i(y) are
    elements of G. Hence i(x \cdot y) = i(x) \cdot i(y) = i(y) \cdot i(x) = i(y \cdot x) (by
    GrpSub030). i is injective. Hence the thesis (by FoundMap092). Indeed i is a map and x \cdot y,
    y \cdot x are elements of the domain of i.
  end.

  H is a group. Hence the thesis (by GrpAb000).
qed.


Proposition GrpSub055. Let G be a group. Then the inclusion of G into G is the identity map on G.

Proof.
  Take a map i that is the inclusion of G into G. G is the domain of i and G is the codomain of G.
  For all x \in G we have i(x) = x. Moreover for all x \in G we have id_{G}(x) = x. G is the domain
  of id_{G} and G is the codomain of G. Hence i and id_{G} are maps such that dom(i) = dom(id_{G})
  and codom(i) = codom(id_{G}). Furthermore for all x \in dom(i) we have i(x) = id_{G}(x). Then we
  have the thesis (by FoundMap040).
qed.


# 2.1 Abuse of notation

Axiom GrpSubxxx. Let G be a group and H be a subgroup of G. Let i be the inclusion of H into G. Then
g \cdot h = g \cdot i(h) for all g \in G and all h \in H.

Axiom GrpSubxxx. Let G be a group and H be a subgroup of G. Let i be the inclusion of H into G. Then
h \cdot g = i(h) \cdot g for all g \in G and all h \in H.


# 3. The trivial subgroups

Proposition GrpSub060. Every group G is a subgroup of G.

Proof.
  Let G be a group. G is a structure. Hence G is a substructure of G (by FoundStr055). Take a map i
  from G to G that is the inclusion of G into G.

  For all x,y \in G we have i(x \cdot y) = i(x) \cdot i(y).
  proof.
    Let x,y \in G. i(x \cdot y) = G(G^{-1}(x \cdot y)) = x \cdot y.
  end.

  Hence i is a group homomorphism between G and G (by GrpHom000).
qed.


Proposition GrpSub065. Let G be a group. There is a subgroup H of G such that H = {1_{H}}.

Proof.
  Define A = {1_{G}}. A is a set (by SetSet077). Indeed 1_{G} is an element. Hence A is a nonempty
  subset of G. Indeed every element of A lies in G. 1_{G}^{-1} = 1_{G}. Hence 1_{G} \cdot 1_{G}^{-1}
  = 1_{G}. Thus for all x,y \in A we have x \cdot y^{-1} \in A. Therefore we can take a subgroup H
  of G such that A is the image of H under the inclusion of H into G (by GrpSub015). Take a map i
  from H to G that is the inclusion of H into G.

  Every element of H is equal to 1_{H}.
  proof.
    Let x \in H. 1_{H} is an element of H and i[H] = {1_{G}}. Hence i(1_{H}) = i(x) (by GrpSub045).
    i is an injective map. Thus x = 1_{H} (by FoundMap092). Indeed x and 1_{H} are elements of the
    domain of i.
  end.
qed.


Corollary GrpSub070. Every group has a subgroup H such that H and the trivial group are isomorphic.

Proof.
  Let G be a group. Take a subgroup H of G such that H = {1_{H}} (by GrpSub065). Then H has exactly
  one element (by SetCard081b). Indeed H is a set. Hence the thesis (by GrpHom160). Indeed H is a
  group.
qed.


# 4. Kernel and image

# 4.1 The kernel of a group homomorphism 

Proposition GrpSub080. Let G,H be groups and phi be a group homomorphism between G and H. There is a
subgroup ker of G such that the image of ker under the inclusion of ker into G is a set K such that
K = {x in G | phi(x) = 1_{H}}.

Proof.
  Define K = {x in G | phi(x) = 1_{H}}. K is a subset of G. phi(1_{G}) = 1_{H}. Hence 1_{G} lies in
  K. Thus K is nonempty.

  For all x,y \in K we have x \cdot y^{-1} \in K.
  proof.
    Let x,y \in K. Then phi(x) = 1_{H} = phi(y). phi(x \cdot y^{-1}) = phi(x) \cdot phi(y)^{-1} (by
    GrpHom000, GrpHom015). Indeed y^{-1} lies in G. 1_{H}^{-1} = 1_{H}. Hence phi(x \cdot y^{-1}) =
    1_{H}. Thus x \cdot y^{-1} \in K.
  end.

  Hence the thesis (by GrpSub015). Indeed K is a set.
qed.


Axiom GrpSub085. Let G,H be groups and phi be a group homomorphism between G and H. ker(phi) is a
subgroup of G such that the image of ker(phi) under the inclusion of ker(phi) into G is a set K such
that K = {x in G | phi(x) = 1_{H}}.


Proposition GrpSub090. Let G,H be groups and phi be a group homomorphism between G and H. Assume
that G is abelian. Then the kernel of phi is abelian.

Proof.
  ker(phi) is a subgroup of G. Hence the thesis (by GrpSub050).
qed.


# 4.1.1 Abuse of notation

Proposition GrpSub095. Let G,H be groups and phi be a group homomorphism between G and H. Let x be
an element of the kernel of phi. Then phi(x) = 1_{H}.

Proof.
  Take a map i that is the inclusion of ker(phi) into G. phi is a map such that dom(phi) = G. Hence
  phi(x) = phi(i(x)) (by FoundStr070). Indeed G is a structure and ker(phi) is a substructure of G.
  i[ker(phi)] = {g in G | phi(g) = 1_{H}} (by GrpSub085). i(x) is an element of i[ker(phi)] (by
  GrpSub045). Indeed ker(phi) is a subgroup of G.
qed.


Corollary GrpSub100. Let G,H be groups. Assume that H is abelian. Let phi be a group homomorphism
between G and H. Let x be an element of the kernel of phi. Then phi(x) = 0_{H}.

Proof.
  phi(x) = 1_{H} (by GrpSub095). Hence the thesis (by GrpAb020).
qed.


# 4.1.2 Characterization of injective group homomorphisms

Proposition GrpSub105. Let G,H be groups and phi be a group homomorphism between G and H. phi is
injective iff for all x \in G if phi(x) = 1_{H} then x = 1_{G}.

Proof. [prove off] qed.


Corollary GrpSub110. Let G,H be groups and phi be a group homomorphism between G and H. phi is
injective iff the kernel of phi and the trivial group are isomorphic.

Proof. [prove off] qed.


# 4.2 The image of a group homomorphism

Proposition GrpSub120. Let G,H be groups and phi be a group homomorphism between G and H. There is a
subgroup im of H such that the image of im under the inclusion of im into H is a set I such that
I = range(phi).

Proof. [prove off] qed.


Axiom GrpSub125. Let G,H be groups and phi be a group homomorphism between G and H. im(phi) is a
subgroup of H such that the image of im(phi) under the inclusion of im(phi) into H is a set I such
that I = range(phi).


Proposition GrpSub130. Let G,H be groups and phi be a group homomorphism between G and H. Assume
that H is abelian. Then im(phi) is abelian.

Proof.
  im(phi) is a subgroup of H. Hence the thesis (by GrpSub050).
qed.


# 5. Normal subgroups

# 5.1 Definition

Signature GrpSub150. Let G be a group. A normal subgroup of G is a notion.

Axiom GrpSub155. Let G be a group and N be a subgroup of G. Let i be the inclusion of N into G. N is
a normal subgroup of G iff for all g \in G we have g \cdot N = N \cdot g.

Axiom GrpSub160. Let N,G be groups. N \triangleleft G iff N is a normal subgroup of G.


# 5.2 Equivalent definitions

Proposition GrpSubxxx. Let G be a group and N be a subgroup of G. Let i be the inclusion of N into
G. N is a normal subgroup of G iff (g \cdot N) \cdot g^{-1} is a subset of i[N] for all g \in G.

Proof. [prove off] qed.


Proposition GrpSubxxx. Let G be a group and N be a subgroup of G. Let i be the inclusion of N into
G. N is a normal subgroup of G iff (g \cdot n) \cdot g^{-1} \in i[N] for all g \in G and all
n \in N.

Proof. [prove off] qed.


# 5.3 Basic facts about normal subgroups

Proposition GrpSub165. Every group G is a normal subgroup of G.

Proof. [prove off] qed.


Proposition GrpSub170. Let G be a group and H be a subgroup of G. If H = {1_{H}} then H is a normal
subgroup of G.

Proof. [prove off] qed.


Proposition GrpSub175. Every subgroup of any abelian group G is a normal subgroup of G.

Proof. [prove off] qed.


Proposition GrpSub180. Let G,H be groups and phi be a group homomorphism between G and H. The kernel
of phi is a normal subgroup of G.

Proof. [prove off] qed.
