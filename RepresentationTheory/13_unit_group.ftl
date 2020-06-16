[read RepresentationTheory/11_group.ftl]
[read RepresentationTheory/12_ring.ftl]

Let R denote a Ring.

Axiom. |Un(R)| is a set.
Axiom. |Un(R)| = {r | r < R and there is s < R such that (r *{R} s = 1{R} and s *{R} r = 1{R})}.

Theorem. Let r,s,t < Un(R).
 Assume r *{R} s = 1{R} and s *{R} r = 1{R}. Assume r *{R} t = 1{R} and t *{R} r = 1{R}.
 Then s = t.

# The theorem above allows the following definition.

Axiom. Let r < Un(R). inv{R} r < R.
Axiom. Let r < Un(R). r *{R} (inv{R} r) = 1{R}.
Axiom. Let r < Un(R). (inv{R} r) *{R} r = 1{R}.

Axiom. 1{Un(R)} = 1{R}.
Axiom. Let a,b < Un(R). a *{Un(R)} b = a *{R} b.
Axiom. Let a < Un(R).   inv{Un(R)} a = inv{R} a.

Theorem. Un(R) is a group.
Proof.
 1{Un(R)} < Un(R).
 Let us show that for all a,b < Un(R): a *{Un(R)} b < Un(R).
  Let a,b < Un(R).
  Take s < R such that (a *{R} s = 1{R} and s *{R} a = 1{R}).
  Take t < R such that (b *{R} t = 1{R} and t *{R} b = 1{R}).
  t *{R} s < R.
  (a *{Un(R)} b) *{R} (t *{R} s) = (a *{R} (b *{R} t)) *{R} s = (a *{R} 1{R}) *{R} s
  = a *{R} s = 1{R}.
  (t *{R} s) *{R} (a *{Un(R)} b) = (t *{R} (s *{R} a)) *{R} b = (t *{R} 1{R}) *{R} b
  = t *{R} b = 1{R}.
 qed.
 For all a < Un(R)     : inv{Un(R)} a < Un(R).
 For all a < Un(R)     :       a *{Un(R)} 1{Un(R)} = a.
 For all a < Un(R)     :              a /{Un(R)} a = 1{Un(R)}.
 For all a,b,c < Un(R) : a *{Un(R)} (b *{Un(R)} c) = (a *{Un(R)} b) *{Un(R)} c.
Qed.