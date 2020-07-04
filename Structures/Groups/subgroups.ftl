#
# Subgroups
# (Marcel Schütz, 2020)
#

[prove off][check off]
[read FLib/Structures/Groups/homomorphisms.ftl]
[prove on][check on]


# 1. Subgroups

Definition GrpSub000. Let G be a group. A subgroup of G is a group H such that the domain of H is a
subset of G.


# 1.1 Constructing subgroups

Proposition GrpSub001. Let G be a group and A be a nonempty subset of G. Assume that for all
x,y \in A we have x \cdot y \in A. Assume that for all x \in A we have x^{-1} \in A. Then A is the
domain of some subgroup of G.

Proof.
  A is a set.

  1_{G} is an element of A.
  proof.
    Take an element a of A. Then a^{-1} \in A. Hence a \cdot a^{-1} \in A. a \cdot a^{-1} = 1_{G}.
    Indeed a and a^{-1} are elements of G.
  end.

  Define mul((x,y)) = x \cdot y for (x,y) in A \times A.
  Define inv(x) = x^{-1} for x in A.

  For all z \in A \times A we have mul(z) \in A.
  proof.
    Let z \in A \times A. Take x,y \in A such that z = (x,y) (by FoundFam380). Indeed A is a class.
    Then mul(z) = mul(x,y) = x \cdot y.
  end.

  Hence mul is a function from A \times A to A (by FoundMap266). Moreover for all x \in A we have
  inv(x) \in A. Thus inv is a function from A to A (by FoundMap266). Then (A, mul, inv, 1_{G})
  satisfies GRP1 (by GrpGrp005).

  For all x,y,z \in A we have mul(x,mul(y,z)) = mul(mul(x,y),z).
  proof.
    Let x,y,z \in A. mul(x,mul(y,z)) = x \cdot (y \cdot z). mul(mul(x,y),z) = (x \cdot y) \cdot z.
    x \cdot (y \cdot z) = (x \cdot y) \cdot z (by GrpGrp125). Indeed x,y,z \in G.
  end.

  Hence (A, mul, inv, 1_{G}) satisfies GRP2 (by GrpGrp015).
  proof. [prove off] end. # Naproche-SAD cannot prove it...

  For all x \in A we have mul(x,1_{G}) = x = mul(1_{G},x).
  proof.
    Let x \in A. mul(x,1_{G}) = x \cdot 1_{G} and mul(1_{G},x) = 1_{G} \cdot x.
  end.

  Hence (A, mul, inv, 1_{G}) satisfies GRP3 (by GrpGrp025).
  proof. [prove off] end. # Naproche-SAD cannot prove it...

  For all x \in A we have mul(x,inv(x)) = 1_{G} = mul(inv(x),x).
  proof.
    Let x \in A. mul(x,inv(x)) = x \cdot x^{-1}. mul(inv(x),x) = x^{-1} \cdot x. x \in G. Hence the
    thesis (by GrpGrp135).
  end.

  Thus (A, mul, inv, 1_{G}) satisfies GRP4 (by GrpGrp035).

  Then (A, mul, inv, 1_{G}) lies in GRP_{1} (by GrpGrp055). Hence we can take a group H such that
  H = (A, mul, inv , 1_{G})_{GRP} (by GrpGrp075). Then A is the domain of H.
qed.


Proposition GrpSub002. Let G be a group and A be a nonempty subset of G. Assume that for all
x,y \in A we have x \cdot y^{-1} \in A. Then A is the domain of some subgroup of G.

Proof. [prove off] qed.


# 1.2 The inclusion map of subgroups

Axiom GrpSub005. Let G be a group and H be a subgroup of G. Let i be the inclusion of H. Then i is a
map from H to G such that i(x) = H^{-1}(x) for all x \in H.


Proposition GrpSub007. Let G be a group and H be a subgroup of G. Let i be the inclusion of H. Let
x \in H. Then i(x) \in dom(H).

Proof.
  i(x) = H^{-1}(x) (by GrpSub005). x is an element of dom(H^{-1}).
qed.


Proposition GrpSub010. Let G be a group and H be a subgroup of G. Then the inclusion of H is a group
monomorphism between H and G.

Proof.
  Let us show that H^{-1}(x \cdot y) = H^{-1}(x) \cdot H^{-1}(y) for all x,y \in H.
    [prove off]
  end.

  Take a map i from H to G that is the inclusion of H. Then i(x) = H^{-1}(x) for all x \in H (by
  GrpSub005). i(x \cdot y) = i(x) \cdot i(y) for all x,y \in H (by GrpSub000). Indeed x \cdot y is
  an element of H for all x,y \in H. Hence i is a group homomorphism between H and G (by GrpHom000,
  GrpSub005). Indeed H is a group.

  For all x,y \in dom(i) if i(x) = i(y) then x = y.
  proof.
    Let x,y \in dom(i). Then x,y \in H. Assume that i(x) = i(y). Then H^{-1}(x) = H^{-1}(y) (by
    GrpSub005). H^{-1} is an injective map. Hence the thesis (by FoundMap092). Indeed x and y are
    elements of dom(H^{-1}).
  end.

  Thus i is injective (by FoundMap092). Indeed i is a map.
qed.


Corollary GrpSub015. Let G be a group and H be a subgroup of G. Let i be the inclusion of H. Let
x \in H. Then i(x) \in G.

Proof.
  G and H are groups. i is a group homomorphism between H and G (by GrpSub010, GrpHom075). Hence the
  thesis (by GrpHom005).
qed.


Corollary GrpSub020. Let G be a group and H be a subgroup of G. Let i be the inclusion of H. Let
x,y \in H. Then i(x \cdot y) = i(x) \cdot i(y).

Proof.
  G and H are groups. i is a group homomorphism between H and G (by GrpSub010, GrpHom075). Hence the
  thesis (by GrpHom000).
qed.


Corollary GrpSub025. Let G be a group and H be a subgroup of G. Let i be the inclusion of H. Then
i(1_{H}) = 1_{G}.

Proof.
  G and H are groups. i is a group homomorphism between H and G (by GrpSub010, GrpHom075). Hence the
  thesis (by GrpHom010).
qed.


Corollary GrpSub030. Let G be a group and H be a subgroup of G. Let i be the inclusion of H. Let
x \in H. Then i(x^{-1}) = i(x)^{-1}.

Proof.
  G and H are groups. i is a group homomorphism between H and G (by GrpSub010, GrpHom075). Hence the
  thesis (by GrpHom015).
qed.


Proposition GrpSub050. Every subgroup of any abelian group is abelian.

Proof.
  Let G be an abelian group and H be a subgroup of G. Then g \cdot h = h \cdot g for all g,h \in G.

  For all x,y \in H we have x \cdot y = y \cdot x.
  proof.
    Let x,y \in H. Take a map i from H to G that is the inclusion of H. i(x) and i(y) lie in G.
    Hence i(x \cdot y) = i(x) \cdot i(y) = i(y) \cdot i(x) = i(y \cdot x) (by GrpSub020). i is
    injective. Hence the thesis (by FoundMap092). Indeed i is a map and x \cdot y, y \cdot x are
    elements of the domain of i.
  end.
qed.


# 3. Abuse of notation.

Proposition GrpSub070. Let G be a group and H be a subgroup of G. Let phi be a map such that
dom(phi) = G. Let i be the inclusion of H. Then phi(x) = phi(i(x)) for all x \in H.

Proof.
  Let x \in H. G and H are structures. dom(H) \subseteq G. Hence phi(x) = phi(H^{-1}(x)) (by
  FoundStr047). i(x) = H^{-1}(x) (by GrpSub005).
qed.


Corollary GrpSub075. Let G,K be groups and H be a subgroup of G. Let phi be a group homomorphism
between G and K. Let i be the inclusion of H. Then phi(x) = phi(i(x)) for all x \in H.

Proof.
  phi is a map such that dom(phi) = G. Hence the thesis (by GrpSub070).
qed.


# 4. Kernel and image

# 4.1 Kernel

Lemma GrpSub090. Let G,H be groups and phi be a group homomorphism between G and H. Let K be a class
such that K = {x in G | phi(x) = 1_{H}}. Then K is the domain of some subgroup of G.

Proof.
  For all x,y \in K we have x \cdot y^{-1} \in K.
  proof.
    Let x,y \in K. Then phi(x) = 1_{H} = phi(y). phi(x \cdot y^{-1}) = phi(x) \cdot phi(y)^{-1} (by
    GrpHom000, GrpHom015). Indeed y^{-1} \in G. Hence phi(x \cdot y^{-1}) = 1_{H} \cdot 1_{H} =
    1_{H}. Indeed 1_{H}^{-1} = 1_{H} (by GrpGrp180). x \cdot y^{-1} lies in G.
  end.

  K is nonempty. Indeed phi(1_{G}) = 1_{H}. Hence the thesis (by GrpSub002). Indeed K is a subset of
  G.
qed.


Axiom GrpSub095. Let G,H be groups and phi be a group homomorphism between G and H. ker(phi) is a
subgroup of G such that dom(ker(phi)) = {x in G | phi(x) = 1_{H}}.


Proposition GrpSub100. Let G,H be groups and phi be a group homomorphism between G and H. Then
phi(x) = 1_{H} for all x \in ker(phi).

Proof.
  Take a map i from ker(phi) to G that is the inclusion of ker(phi). Let x \in ker(phi). ker(phi) is
  a subgroup of G. Hence phi(x) = phi(i(x)) (by GrpSub075). i(x) lies in the domain of ker(phi) (by
  GrpSub007). Thus we have the thesis (by GrpSub095).
qed.
