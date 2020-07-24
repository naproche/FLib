[read RepresentationTheory/00_introduction.ftl]

Definition AbelianGroup. An abelian group is an object G such that
     (|G| is a set)
 and (0{G} < G)
 and (for all a,b < G   : a +{G} b < G)
 and (for all a < G     :   ~{G} a < G)
 and (for all a < G     :       a +{G} 0{G} = a)
 and (for all a < G     :          a -{G} a = 0{G})
 and (for all a,b,c < G : a +{G} (b +{G} c) = (a +{G} b) +{G} c)
 and (for all a,b < G   :          a +{G} b = b +{G} a).

Theorem NegZero. Let G be an abelian group.
 Then ~{G} 0{G} = 0{G}.

Theorem ZeroAdd. Let G be an abelian group. Let a < G.
 Then 0{G} +{G} a = a.

Theorem NegAdd. Let G be an abelian group. Let a,b < G.
 Then ~{G} (a +{G} b) = (~{G} a) -{G} b.
Proof.
 ~{G} (a +{G} b) = (~{G} (a +{G} b)) +{G} ((a -{G} a) +{G} (b -{G} b)).
 (~{G} (a +{G} b)) +{G} ((a -{G} a) +{G} (b -{G} b))
 = ((~{G} (a +{G} b)) +{G} (a +{G} b)) +{G} ((~{G} a) -{G} b).
 ((~{G} (a +{G} b)) +{G} (a +{G} b)) +{G} ((~{G} a) -{G} b) = (~{G} a) -{G} b.
Qed.