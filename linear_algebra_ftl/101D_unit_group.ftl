[read linear_algebra_ftl/A_Props/100A_ring.ftl]


Definition. A group is a structure G such that
     (G has carr,one,mul,inv)
 and (|G| is a set)
 and (1{G} < G)
 and (mul{G} is a function from Prod(|G|,|G|) to |G|)
 and (inv{G} is a function from |G| to |G|)
 and (for all a < G     :       a *{G} 1{G} = a)
 and (for all a < G     :          a /{G} a = 1{G})
 and (for all a,b,c < G : a *{G} (b *{G} c) = (a *{G} b) *{G} c).


Let R denote a ring.

Signature. Un(R) is a structure.
Axiom. (Un(R) has carr).
Axiom. |Un(R)| is a set.
Axiom. |Un(R)| = {r | r < R and there is s < R such that (r *{R} s = 1{R} and s *{R} r = 1{R})}.


# For every r < Un(R) there is exactly one s < R such that r*s = 1 = s*r. (see P_unit_group)
# This allows the following definition.

Signature. ringInv(R) is a function.
Axiom. Dom(ringInv(R)) = |Un(R)|.
Axiom. For all r < Un(R) : ringInv(R)[r] < R.
Axiom. For all r < Un(R) : r *{R} ringInv(R)[r] = 1{R}.
Axiom. For all r < Un(R) : ringInv(R)[r] *{R} r = 1{R}.


Axiom. (Un(R) has one,mul,inv).
Axiom. 1{Un(R)}   = 1{R}.
Axiom. mul{Un(R)} = mul{R}|{Prod(|Un(R)|,|Un(R)|)}.
Axiom. inv{Un(R)} = ringInv(R).
