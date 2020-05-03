# This is a ForTheL version of some example text
# for a CNL for Lean by Tom Hales

# Preliminaries on Types

[synonym type/-s]
Signature. A type is a set.
Let C stand for a set.
Let A stand for a type.
Let a : t stand for a is an element of t.
Let a \in t stand for a is an element of t.

Signature. C is finite is an atom.

# Preliminaries on Numbers

[synonym number/-s]
Signature. A number is a notion.
let m,n,p,q denote numbers.

Signature. m * n is a number.

Signature. m - 1 is a number.

Definition. A divisor of n is a number m such that n = m * a for some number a.
Let m divides n stand for m is a divisor of n.

# Let m divides n stand for there is a number a such that n = m * a.

Signature. p^m is a number.

Signature. Assume C is finite. |C| is a number.
Let the order of C stand for |C|.
Let the size of C stand for |C|.

Signature. p is prime is an atom.

Signature. The multiplicity of p in n is a number.

# Preliminaries on Groups

[synonym group/-s]
Signature. A group is a type.
Let G,H denote groups.
Signature. Let x,y : G. x *^{G} y is an element of G.
Signature. Let x : G. x^{-1,G} is an element of G.

Definition. A subgroup of G is a group H such that
every element of H is an element of G.

Axiom. Let G be a finite group. Every subgroup of G is finite.

# Sylow Subgroups

Definition conjugate. Assume g : G. Assume that H is a subgroup of G.
The conjugate of H by g in G is the subgroup K of G such that for
all elements x of G x \in K <=> (g *^{G} x) *^{G} g^{-1,G} \in K.

Definition normalizer. Assume that H is a subgroup of G.
The normalizer of H in G is the subgroup N of G such that for all
elements x of G x \in N iff
for all elements h of H (x^{-1,G} *^{G} h) *^{G} x \in H.

Let G,P,Q denote finite groups.
Let p denote a prime number.

[synonym subgroup/-s]
Definition Sylow. A Sylow subgroup of G for p is a subgroup P of G such
that |P| = p^m where m is the multiplicity of p in |G|.

Definition. Syl(p,G) = { R | R is a Sylow subgroup of G for p}.

Axiom. Syl(p,G) is finite.

Definition. n(p,G) is the size of Syl(p,G).

Axiom Sylow1. There exists a Sylow subgroup of G for p.

Axiom Sylow2. If P,Q are Sylow subgroups of G for p then there
exists g : G such that Q is the conjugate of P by g in G.

Axiom Sylow3a. Assume that |G| = q * (p^m). Then n(p,G) divides q.

Axiom Sylow3b. p divides n(p,G)-1.

Axiom Sylow3c. Let Norm be the normalizer of P in G where P is a Sylow subgroup
of G for p. Then  n(p,G) * |Norm| = |G|.



