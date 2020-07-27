#
# Groups
# (Marcel Schütz, 2020)
#

[prove off][check off]
[read FLib/Structures/NumberTheory/integers.ftl]
[read FLib/Structures/Foundations/4-tuples.ftl]
[check on][prove on]


Signature. Let X,f be entities. f is associative on X is a statement.

Signature. Let X,f be entities. A neutral element of X wrt f is a notion.

Signature. Let X,f,e be entities. An inverse mapping of X wrt f and e is a notion.


Let G denote a class.


Axiom CLOSED1. Let carr be a subset of G. Let mul be a function from G \times G to G. mul is closed
in carr iff for all x,y \in carr we have mul(x,y) \in carr.

Axiom CLOSED2. Let carr be a subset of G. Let inv be a function from G to G. inv is closed in carr
iff for all x \in carr we have inv(x) \in carr.

Axiom ASSO. Let carr be a subset of G. Let mul be a function from G \times G to G. mul is
associative on carr iff for all x,y,z \in carr we have mul(x,mul(y,z)) = mul(mul(x,y),z).

Axiom NEUTR. Let carr be a subset of G. Let mul be a function from G \times G to G and e be an
element of G. e is a neutral element of carr wrt mul iff e \in carr and for all x \in carr we have
mul(x,e) = x = mul(e,x).

Axiom INV. Let carr be a subset of G. Let mul be a function from G \times G to G and inv be a
function from G to G and e be an element of G. inv is an inverse mapping of carr wrt mul and e iff
for all x \in carr we have mul(inv(x),x) = e = mul(x,inv(x)).


Definition GROUP. Group(G) = {(carr, mul, inv, e) |

  carr is a subset of G and

  mul is a function from G \times G to G and

  inv is a function from G to G and

  e is an element of G
}.


Signature. A group is a notion.

Axiom GROUPDEF. Let carr, mul, inv, e be entities. Assume that (carr, mul, inv, e) is an element of
Group(G). (carr, mul, inv, e) is a group iff

  mul is closed in carr and

  mul is associative on carr and

  e is a neutral element of carr wrt mul and

  inv is closed in carr and

  inv is an inverse mapping of carr wrt mul and e.


Definition. add is the function from \mathbb{Z} \times \mathbb{Z} to \mathbb{Z} such that add(n,m) =
n + m for all n,m \in \mathbb{Z}.

Definition. neg is the function from \mathbb{Z} to \mathbb{Z} such that neg(n) = -n for all
n \in \mathbb{Z}.

Definition TRIVGRP. The trivial group is (`{0}`, add, neg, 0).


Theorem. The trivial group is a group.

Proof.
  `{0}` = {0}. Moreover \mathbb{Z} and `{0}` are classes.

  `{0}` is a subset of \mathbb{Z}.
  proof.
    Every element of `{0}` belongs to \mathbb{Z}. Hence `{0}` \subseteq \mathbb{Z} (by FoundCl000).
    Furthermore `{0}` is a set.
  end.

  The trivial group is an element of Group(\mathbb{Z}).
  proof.
    [ontored on]
    # Without ontological reduction the following statements would both be translated to "truth" in
    # the following proof tasks.
    add is a function from \mathbb{Z} \times \mathbb{Z} to \mathbb{Z}. Moreover neg is a function
    from \mathbb{Z} to \mathbb{Z}.
    [ontored off]

    Furthermore 0 is an element of \mathbb{Z}. Hence the thesis (by GROUP, TRIVGRP).
  end.

  add is a function from \mathbb{Z} \times \mathbb{Z} to \mathbb{Z}. Moreover neg is a function from
  \mathbb{Z} to \mathbb{Z}.

  add is closed in `{0}` (by CLOSED1). Indeed For all n,m \in `{0}` we have add(n,m) \in `{0}`.

  add is associative on `{0}` (by ASSO). Indeed For all n,m,k \in `{0}` we have add(n,add(m,k)) =
  add(add(n,m),k).

  Hence 0 is a neutral element of `{0}` wrt add (by NEUTR). Indeed 0 \in \mathbb{Z} and 0 \in `{0}`
  and for all n \in `{0}` we have add(n,0) = n = add(0,n).

  Hence neg is closed in `{0}` (by CLOSED2). Indeed For all n \in `{0}` we have neg(n) \in `{0}`.

  neg is an inverse mapping of `{0}` wrt add and 0 (by INV). Indeed 0 \in \mathbb{Z} and for all
  n \in `{0}` we have add(neg(n),n) = 0 = add(n,neg(n)).

  Then we have the thesis (by GROUPDEF, TRIVGRP).
qed.
