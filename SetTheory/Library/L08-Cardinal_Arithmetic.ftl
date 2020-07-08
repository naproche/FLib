[read Forthel-Dateien/SetTheory/Library/L07-Cardinals_Part_2.ftl]

[prove off]

## Pretyped Variables

Let w,x,y,z,W,X,Y,Z stand for zfsets.
Let a,b,c,d,A,B,C,D,M stand for sets.
Let o,o1,o2 stand for objects.
Let alpha, beta, gamma, delta stand for ordinals.
Let f,g,h,F,G,H stand for zffunction.
Let kappa, lambda stand for cardinals.



## Cardinal Arithmetic

Axiom. Let f be a zffunction. Let Dom(f) /in /VV. Then f is a zfset.

Lemma. Let A,B /in /VV. Then ^{A}B /in /VV.

Lemma. Forall x1,x2,y1,y2 /in /VV ( x1 /tilde x2 /\ y1 /tilde y2 => ^{x1}y1 /tilde ^{x2}y2 ).

Signature. kappa +3 lambda is a cardinal.
Signature. kappa *3 lambda is a cardinal.
Signature. kappa ^3 lambda is a cardinal.

Definition. Let kappa, lambda /in /Cd. Let x,y /in /VV. (kappa,lambda) IsAdditionCompatibleWith (x,y) iff (Card(x) = kappa /\ Card(y) = lambda /\ x /cap y = /emptyset).
Let (a,b) /sim (x, y) stand for (a,b) IsAdditionCompatibleWith (x, y).

Axiom. Let kappa, lambda /in /Cd. Let x,y /in /VV. Let (kappa,lambda) /sim (x, y).
Then kappa +3 lambda = Card(x /cup y).

Axiom. Let kappa, lambda /in /Cd. Let x,y /in /VV. Let Card(x) = kappa. Let Card(y) = lambda. Let x /cap y = /emptyset.
Then kappa +3 lambda = Card(x /cup y).

Axiom. Let kappa, lambda /in /Cd. Then kappa *3 lambda = Card(kappa /times lambda).

Axiom. Let kappa, lambda /in /Cd. Then kappa ^3 lambda = Card(^{lambda}kappa).

Lemma. Forall kappa, lambda /in /Cd exists x,y ((kappa,lambda) /sim (x,y)).


## Algebraic rules for Sum and Product

Lemma. Forall kappa, lambda /in /Cd (kappa +3 lambda = lambda +3 kappa).

Lemma. Forall kappa, lambda /in /Cd (kappa *3 lambda = lambda *3 kappa).

Lemma. Let alpha, beta /in /Cd. Let x be a zfset. Let Card(x) = alpha. Then exists y (alpha,beta) /sim (x,y).

Lemma. Forall alpha, beta, gamma /in /Cd ((alpha +3 beta) +3 gamma = alpha +3 (beta +3 gamma)).


## Basic Facts

Lemma. Forall kappa, lambda /in /Cd (kappa /subset kappa +3 lambda).

Lemma. Forall kappa /in /Cd (kappa ^3 0 = 1).

Lemma. Forall kappa /in /Cd (kappa /neq 0 => 0 ^3 kappa = 0).

Lemma. Forall kappa /in /Cd (1 ^3 kappa = 1).


## Cardinal = Ordinal Arithmetic for finite sets.

Lemma. Forall n /in /NN (n + 1 = n +3 1).

Lemma. Forall alpha /in /Cd (alpha +3 0 = alpha).

Lemma. Forall alpha, beta /in /NN (alpha + beta = alpha +3 beta).

Lemma. Forall alpha, beta /in /NN (alpha * beta = alpha *3 beta).

Lemma. Forall alpha, beta /in /NN (alpha ^ beta = alpha ^3 beta).


## Calculation Rules

Lemma. Let alpha, beta, gamma /in /Cd. Then alpha *3 (beta +3 gamma) = (alpha *3 beta) +3 (alpha *3 gamma).

Lemma. Let alpha, beta, gamma /in /Cd. Then (alpha ^3 (beta +3 gamma) = (alpha ^3 beta) *3 (alpha ^3 gamma)).

Definition. Let alpha, beta, gamma /in /VV. Let f /in ^{beta /times gamma}alpha. Let F be a zffunction.
F /partial (f,alpha,beta,gamma) iff (Dom(F) = gamma /\ forall b /in gamma ((F[b] is a zffunction) /\ Dom(F[b]) = beta /\ forall a /in beta (F[b])[a] = f[(a,b)])).

Lemma. Let alpha, beta, gamma /in /VV. Let f /in ^{beta /times gamma}alpha. Let F be a zffunction. Let F /partial (f,alpha,beta,gamma).
Then F /in ^{gamma}(^{beta}alpha).

Lemma. Let alpha, beta, gamma /in /Cd. Then (alpha ^3 (beta *3 gamma) = (alpha ^3 beta) ^3 gamma).

Lemma. Forall kappa /in /Card (kappa *3 kappa = kappa).

Lemma. Let kappa /in /Card. Let lambda /in /Cd. Let lambda /neq 0. Then kappa *3 lambda = kappa /cup lambda.

Lemma. Let kappa /in /Card. Let lambda /in /Cd. Then kappa +3 lambda = kappa /cup lambda.

Lemma. Forall n /in /NN forall kappa /in /Card (n /neq 0 => kappa ^3 n = kappa).

Lemma ExpEq. Let kappa /in /Card. Let lambda /in /Cd. Let 2 /subset lambda. Let lambda /subset (2 ^3 kappa).
Then lambda ^3 kappa = 2 ^3 kappa.


[prove on]
