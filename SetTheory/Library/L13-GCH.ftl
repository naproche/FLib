[read Forthel-Dateien/SetTheory/Library/L12-Cardinal_Exponentiation.ftl]

[prove off]

## Pretyped Variables

Let w,x,y,z,W,X,Y,Z stand for zfsets.
Let a,b,c,d,A,B,C,D,M stand for sets.
Let o,o1,o2 stand for objects.
Let alpha, beta, gamma stand for ordinals.
Let f,g,h,F,G,H stand for zffunction.
Let kappa, lambda stand for cardinals.




## Generalized Continuum Hypothesis


Signature. GCH is an atom.

Axiom. GCH iff forall kappa /in /Card 2 ^3 kappa = Plus[kappa].

Lemma. Assume GCH. Then forall kappa /in /Card Gimel[kappa] = Plus[kappa].

Lemma. Assume GCH. Let kappa, lambda /in /Card. Let lambda /in cof(kappa). Then kappa ^3 lambda = kappa.

Lemma. Assume GCH. Let kappa, lambda /in /Card. Let cof(kappa) /subset lambda /\ lambda /subset kappa. Then kappa ^3 lambda = Plus[kappa].

Lemma. Assume GCH. Let kappa, lambda /in /Card. Let kappa /in lambda. Then kappa ^3 lambda = Plus[lambda].



[prove on]
