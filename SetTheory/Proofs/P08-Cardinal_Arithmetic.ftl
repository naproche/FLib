[read Forthel-Dateien/SetTheory/Library/L07-Cardinals_Part_2.ftl]

## Pretyped Variables

Let w,x,y,z,W,X,Y,Z stand for zfsets.
Let a,b,c,d,A,B,C,D,M stand for sets.
Let o,o1,o2 stand for objects.
Let alpha, beta, gamma, delta stand for ordinals.
Let f,g,h,F,G,H stand for zffunction.
Let kappa, lambda stand for cardinals.



## Cardinal Arithmetic

Signature. 2 is an ordinal.

Axiom. 2 = 1 + 1.

Axiom. Let f be a zffunction. Let Dom(f) /in /VV. Then f is a zfset.


Lemma. Let A,B /in /VV. Then ^{A}B /in /VV.
Proof.
  Forall f /in ^{A}B (f : A /rightarrow B).
  Let M = /PP (A /times B).
  Define inc[f] = {(a,f[a]) | a /in A} for f in ^{A}B.
  Then inc is a zffunction.
  Proof.
    Let f /in ^{A}B.
    Then forall a /in A (a,f[a]) /in /VV.
    Define g[a] = (a,f[a]) for a in A.
    Then g is a zffunction.
    Proof.
      Let a /in A.
      Then g[a] /in /VV.
    end.
    inc[f] /subset g^[A].
    Proof.
      Let x /in inc[f]. Take a zfset a such that a /in A /\ x = (a,f[a]).
      Then x /in g^[A].
    end.
    Then inc[f] /in /VV.
  end.
  Then inc : ^{A}B /rightarrow M.
  Proof.
    Let f /in ^{A}B.
    Then forall a /in A (a,f[a]) /in /VV.
    Define g[a] = (a,f[a]) for a in A.
    Then g is a zffunction.
    Proof.
      Let a /in A.
      Then g[a] /in /VV.
    end.
    inc[f] /subset g^[A].
    Proof.
      Let x /in inc[f]. Take a zfset a such that a /in A /\ x = (a,f[a]).
      Then x /in g^[A].
    end.
    g^[A] /subset A /times B.
    Proof.   
      Let x /in g^[A]. Take a zfset a such that a /in A /\ x = g[a].
      Then x = (a,f[a]).
      f : A /rightarrow B.
      f[a] /in B.
      Then x /in A /times B.
    end.
    Then inc[f] /subset A /times B.
    Then inc[f] /in M.
  end.
  
  inc is injective.
  Proof.
    Let f,g /in ^{A}B. Let f /neq g. Then inc[f] /neq inc[g].
    Proof.
      Dom(f) = Dom(g).
      Exists a /in A (f[a] /neq g[a]).
      Proof by contradiction. Assume the contrary.
        f,g are functions.
        Forall a /in Dom(f) (f[a] = g[a]).
        Then f = g.
        Contradiction.
      end.
      Take a zfset a such that a /in A /\ f[a] /neq g[a].
      Then (a,f[a]) /in inc[f].
      (a,f[a]) /notin inc[g].
      Proof by contradiction. Assume the contrary.
        Then (a,f[a]) /in inc[g].
        Take a zfset b such that b /in A /\ (a,f[a]) = (b,g[b]).
        Take zfsets c1,c2 such that c1 = f[a] /\ c2 = g[b].
        Then (a,c1) = (b,c2).
        Then a = b /\ c1 = c2.
        Contradiction.
      end.
      Then inc[f] /neq inc[g].
    end.
  end.
  
  Then inc : ^{A}B /leftrightarrow ran(inc).
  Then inc^{-1} : ran(inc) /leftrightarrow ^{A}B.
  ran(inc) /subset M.
  M /in /VV.
  Then ran(inc) /in /VV.
  
  ^{A}B = (inc^{-1})^ [ran(inc)].
  Then ^{A}B /in /VV.

qed.


Lemma. Forall x1,x2,y1,y2 /in /VV ( x1 /tilde x2 /\ y1 /tilde y2 => ^{x1}y1 /tilde ^{x2}y2 ).
Proof.  
  Forall x1,x2,y1,y2 /in /VV ( x1 /tilde x2 /\ y1 /tilde y2 => ^{x1}y1 <= ^{x2}y2).
  Proof.
    Let x1,x2,y1,y2 /in /VV.
    Let x1 /tilde x2.
    Let y1 /tilde y2.
    Take a zffunction f such that f : x2 /leftrightarrow x1.
    Take a zffunction g such that g : y1 /leftrightarrow y2.
  
    Forall h /in ^{x1}y1 (ran(f) /subset Dom(h) /\ ran(h) /subset Dom(g)).
    Define bij[h] = g /circ (h /circ f) for h in ^{x1}y1.
    Then bij is a zffunction.
    Proof.
      Let h /in ^{x1}y1. Then h /circ f is a zffunction.
      Then g /circ (h /circ f) is a zffunction.
      Dom(g /circ (h /circ f)) /in /VV.
      Then bij[h] /in /VV.
    end.
    bij : ^{x1}y1 /rightarrow ^{x2}y2.
    Proof.
      Let h /in ^{x1}y1.
      Then h /circ f : x2 /rightarrow y1.
      Then g /circ (h /circ f) : x2 /rightarrow y2.
      g /circ (h /circ f) is a zffunction.
      Then bij[h] /in ^{x2}y2.
    end.
  
    bij is injective.
    Proof.
      Let h1,h2 /in ^{x1}y1.
      Let h1 /neq h2.
      Then exists a /in x1 (h1[a] /neq h2[a]).
      Proof by contradiction. Assume the contrary.
        h1,h2 are functions.
        Dom(h1) = Dom(h2).
        Forall a /in Dom(h1) h1[a] = h2[a].
        Then h1 = h2.
        Contradiction.
      end.
      Take a zfset a such that a /in x1 /\ h1[a] /neq h2[a].
      Take a zfset b such that b /in x2 /\ f[b] = a.
      Then (h1 /circ f)[b] /neq (h2 /circ f)[b].
      ran(h1 /circ f), ran(h2 /circ f) /subset Dom(g).
      (h1 /circ f)[b], (h2 /circ f)[b] /in Dom(g).
      g is injective.
      (g /circ (h1 /circ f))[b] = g[(h1 /circ f)[b]].
      (g /circ (h2 /circ f))[b] = g[(h2 /circ f)[b]].
      Then (g /circ (h1 /circ f))[b] /neq (g /circ (h2 /circ f))[b].
      Then (g /circ (h1 /circ f)) /neq (g /circ (h2 /circ f)).
      Then bij[h1] /neq bij[h2].
    end.
    
    Then ^{x1}y1 <= ^{x2}y2.
  end.
  
  Let x1,x2,y1,y2 /in /VV.
  Let x1 /tilde x2.
  Let y1 /tilde y2.
  
  Then ^{x1}y1 <= ^{x2}y2.
  Then ^{x2}y2 <= ^{x1}y1.
  Then ^{x1}y1 /tilde ^{x2}y2.
qed.

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
Proof.
  Let kappa, lambda /in /Cd.
  Define x = {(z,0) | z /in kappa}.
  Define y = {(z,1) | z /in lambda}.
  (x is a zfset) /\ x /tilde kappa.
  Proof.
    Define f[z] = (z,0) for z in kappa.
    f is a zffunction.
    Proof.
      Let z /in kappa. Then f[z] /in /VV.
    end.
    Then f : kappa /rightarrow x.
    f is injective.
    Proof.
      Let z1,z2 /in kappa. Let z1 /neq z2.
      Then f[z1] /neq f[z2].
    end.
    ran(f) = x.
    Then x = f^[kappa].
    Then x /in /VV.
    f : kappa /leftrightarrow x.
  end.
  
  (y is a zfset) /\ y /tilde lambda.
  Proof.
    Define f[z] = (z,1) for z in lambda.
    f is a zffunction.
    Proof.
      Let z /in lambda. Then f[z] /in /VV.
    end.
    Then f : lambda /rightarrow y.
    f is injective.
    Proof.
      Let z1,z2 /in lambda. Let z1 /neq z2.
      Then f[z1] /neq f[z2].
    end.
    ran(f) = y.
    Then y = f^[lambda].
    Then y /in /VV.
    f : lambda /leftrightarrow y.
  end.
  
  x /cap y = /emptyset.
  Then (kappa, lambda) /sim (x,y).
qed.


## Algebraic rules for Sum and Product

Lemma. Forall kappa, lambda /in /Cd (kappa +3 lambda = lambda +3 kappa).
Proof.
  Let kappa, lambda /in /Cd.
  Take zfsets x,y such that (kappa,lambda) /sim (x,y).
  Then (lambda, kappa) /sim (y,x).
  x /cup y, y /cup x are zfsets.
  kappa +3 lambda = Card(x /cup y).
  lambda +3 kappa = Card(y /cup x).
  x /cup y = y /cup x.  
qed.


Lemma. Forall kappa, lambda /in /Cd (kappa *3 lambda = lambda *3 kappa).
Proof.
  Let kappa, lambda /in /Cd.
  Define f[(a,b)] = (b,a) for (a,b) in kappa /times lambda.
  Then f : kappa /times lambda /rightarrow lambda /times kappa.
  Proof.
    Dom(f) = kappa /times lambda.
    Let pair /in kappa /times lambda.
    Take zfsets a,b such that a /in kappa /\ b /in lambda /\ pair = (a,b).
    Then (b,a) /in lambda /times kappa.
    f[pair] = (b,a).
    Then f[pair] /in lambda /times kappa.
  end.
  f is injective.
  Proof.
    Let pair1, pair2 /in Dom(f).
    Let pair1 /neq pair2.
    pair1, pair2 /in kappa /times lambda.
    Take ordinals a1,a2 such that a1 /in kappa /\ a2 /in lambda /\ pair1 = (a1,a2).
    Take ordinals b1,b2 such that b1 /in kappa /\ b2 /in lambda /\ pair2 = (b1,b2).
    Then (a1,a2) /neq (b1,b2).
  end.
  ran(f) = lambda /times kappa.
  Proof.
    Let pair /in lambda /times kappa.
    Take zfsets a,b such that a /in lambda /\ b /in kappa /\ pair = (a,b).
    Then (b,a) /in kappa /times lambda.
    f[(b,a)] = (a,b).
    Then pair /in ran(f).
  end.
  Then f : kappa /times lambda /leftrightarrow lambda /times kappa.
  Then Card(kappa /times lambda) = Card(lambda /times kappa).
  kappa *3 lambda = Card(kappa /times lambda).
  lambda *3 kappa = Card(lambda *3 kappa).
qed.


Lemma. Let alpha, beta /in /Cd. Let x be a zfset. Let Card(x) = alpha. Then exists y (alpha,beta) /sim (x,y).
Proof.
  Forall z /in beta ((z,0) is a zfset).
  Define y = {<(z,0),x> | z /in beta}.
  (y is a zfset) /\ y /tilde beta.
  Proof.
    Forall z /in beta (<(z,0),x> is a zfset).
    Define f[z] = <(z,0),x> for z in beta.
    f is a zffunction.
    Proof.
      Let z /in beta. Then f[z] /in /VV.
    end.
    Then f : beta /rightarrow y.
    f is injective.
    Proof.
      Let z1,z2 /in beta. Let z1 /neq z2.
      Then f[z1] /neq f[z2].
    end.
    ran(f) = y.
    Then y = f^[beta].
    Then y /in /VV.
    f : beta /leftrightarrow y.
  end.
  x /cap y = /emptyset.
  Proof by contradiction. Assume the contrary.
    Take a zfset z such that z /in x /cap y.
    Take a zfset zz such that zz /in beta /\ z = <(zz,0),x>.
    z /in x.
    x /in z.
    Let a = <x,z>.
    Then a /in a.
    Contradiction.
  end.
qed.


Lemma. Forall alpha, beta, gamma /in /Cd ((alpha +3 beta) +3 gamma = alpha +3 (beta +3 gamma)).
Proof.
  Let alpha, beta, gamma /in /Cd.
  Take zfsets x,y such that (alpha,beta) /sim (x,y).
  Take zfsets z such that (alpha +3 beta,gamma) /sim (x /cup y, z).
  Then (alpha +3 beta) +3 gamma = Card((x /cup y) /cup z).
  y /cap z = /emptyset.
  Then (beta,gamma) /sim (y,z).
  x /cap (y /cup z) = /emptyset.
  Then (alpha, beta +3 gamma) /sim (x, y /cup z).
  Then alpha +3 (beta +3 gamma) = Card(x /cup (y /cup z)).
  (x /cup y) /cup z = x /cup (y /cup z).
qed.



## Basic Facts


Lemma. Forall kappa, lambda /in /Cd (kappa /subset kappa +3 lambda).
Proof.
  Let kappa, lambda /in /Cd.
  Take zfsets x,y such that (kappa,lambda) /sim (x,y).
  Then kappa +3 lambda = Card(x /cup y).
  x /subset x /cup y.
  Then Card(x) /subset Card(x /cup y).
qed.

Lemma. Forall kappa /in /Cd (kappa ^3 0 = 1).
Proof.
  Let kappa /in /Cd.
  Forall f,g /in ^{0}kappa (f = g).
  Define f[n] = 0 for n in 0.
  Then f : 0 /rightarrow kappa.
  f is a zffunction.
  Then f /in ^{0}kappa.
  Then ^{0}kappa = {f}.
  Then ^{0}kappa /tilde 1.
  Proof.
    Define g[n] = f for n in 1.
    Then g is a zffunction.
    g : 1 /leftrightarrow ^{0}kappa.
  end.
qed.


Lemma. Forall kappa /in /Cd (kappa /neq 0 => 0 ^3 kappa = 0).
Proof.
  Let kappa /in /Cd. Let kappa /neq 0.
  Then ^{kappa}0 = /emptyset.
  qed.
  
  Lemma. Forall kappa /in /Cd (kappa ^3 1 = kappa).
  Proof.
  Let kappa /in /Cd.
  Forall g /in ^{1}kappa 0 /in Dom(g).
  Define f[g] = g[0] for g in ^{1}kappa.
  f is a zffunction.
  Proof.
    Let g /in Dom(f).
    Then g[0] /in /VV.
    Then f[g] /in /VV.
  end.
  Then f : ^{1}kappa /rightarrow kappa.
  Proof.
    Let g /in ^{1}kappa.
    0 /in Dom(g).
    Then g[0] /in kappa.
    Then f[g] /in kappa.
  end.
  f is injective.
  Proof.
    Let g1,g2 /in ^{1}kappa.
    Let f[g1] = f[g2].
    g1,g2 are functions.
    Dom(g1) = Dom(g2).
    Forall x /in Dom(g1) (g1[x] = g2[x]).
    Then g1 = g2.
  end.
  ran(f) = kappa.
  Proof.
    Let x /in kappa.
    Define g[n] = x for n in 1.
    Then g /in ^{1}kappa.
    f[g] = x.
    Then x /in ran(f).
  end.
  Then f : ^{1}kappa /leftrightarrow kappa.
qed.


Lemma. Forall kappa /in /Cd (1 ^3 kappa = 1).
Proof.
  Let kappa /in /Cd.
  Forall f,g /in ^{kappa}1 (f = g).
  Proof.
    Let f,g /in ^{kappa}1.
    Then f,g are functions.
    Dom(f) = Dom(g).
    Forall x /in kappa f[x] = 0.
    Forall x /in kappa g[x] = 0.
    Then forall x /in Dom(f) f[x] = g[x].
    Then f = g.
  end.
  Define f[n] = 0 for n in kappa.
  Then f : kappa /rightarrow 1.
  f is a zffunction.
  Then f /in ^{kappa}1.
  Then ^{kappa}1 = {f}.
  Then ^{kappa}1 /tilde 1.
  Proof.
    Define g[n] = f for n in 1.
    Then g is a zffunction.
    g : 1 /leftrightarrow ^{kappa}1.
  end.
qed.



## Cardinal = Ordinal Arithmetic for finite sets.


Lemma. Forall n /in /NN (n + 1 = n +3 1).
Proof.
  Let n /in /NN.
  Let y = <n>.
  Card(n) = n.
  Card(y) = 1.
  Proof.
    Define f[x] = n for x in 1.
    Then f : 1 /leftrightarrow y.
  end.
  n /cap y = /emptyset.
  Then (n,1) /sim (n,y).
  Then n +3 1 = Card(n /cup y).
  n /cup y = n+1.
end.


Lemma. Forall alpha /in /Cd (alpha +3 0 = alpha).
Proof.
  Let alpha /in /Cd.
  Take zfsets x,y such that (alpha,0) /sim (x,y).
  Card(y) = 0.
  Then y = /emptyset.
  alpha +3 0 = Card(x /cup y).
  x /cup y = x.
  Card(x) = alpha.
qed.


Lemma. Forall alpha, beta /in /NN (alpha + beta = alpha +3 beta).
Proof.
  Let alpha /in /NN.
  Forall beta /in /NN (alpha + beta = alpha +3 beta).
  Proof by induction.
    Let beta /in /NN.
    Case beta = 0.      
    end.
    Case beta /neq 0.
      Let gamma = beta --.
      alpha + beta = (alpha + gamma) + 1.
      alpha + beta = (alpha +3 gamma) + 1.
      alpha + beta = (alpha +3 gamma) +3 1.
      Then alpha + beta = alpha +3 (gamma +3 1).
    end.
  end.
qed.


Lemma. Forall alpha, beta /in /NN (alpha * beta = alpha *3 beta).


Lemma. Forall alpha, beta /in /NN (alpha ^ beta = alpha ^3 beta).
Proof.
  Let alpha /in /NN.
  Forall beta /in /NN (alpha ^ beta = alpha ^3 beta).
  Proof by induction.
    Let beta /in /NN.
    Case beta = 0.
    end.
    Case beta /neq 0.
      Let gamma = beta --.
      alpha ^ beta = (alpha ^3 gamma) *3 alpha.
      (alpha ^3 gamma) *3 alpha = Card(^{gamma}alpha /times alpha).
      Proof.
        (alpha ^3 gamma) *3 alpha = Card((alpha ^3 gamma) /times alpha).
        alpha ^3 gamma /tilde ^{gamma}alpha.
        Then (alpha ^3 gamma) /times alpha /tilde ^{gamma}alpha /times alpha.
      end.
      Forall f /in ^{beta}alpha (gamma /subset Dom(f)).
      Forall f /in ^{beta}alpha (f /upharpoonright gamma is a zfset).
      Forall f /in ^{beta}alpha (gamma /in Dom(f)).
      Define split[f] = ((f /upharpoonright gamma),f[gamma]) for f in ^{beta}alpha.
      split : ^{beta}alpha /rightarrow ^{gamma}alpha /times alpha.
      Proof.
        Let f /in ^{beta}alpha.
        f /upharpoonright gamma : gamma /rightarrow alpha.
        Then f /upharpoonright gamma /in ^{gamma}alpha.
        f[gamma] /in ran(f).
        ran(f) /subset alpha.
        Then f[gamma] /in alpha.
        Then split[f] /in ^{gamma}alpha /times alpha.
      end.
      split is injective.
      Proof.
        Let f,g /in ^{beta}alpha.
        Let f /neq g.
        Exists x /in Dom(f) f[x] /neq g[x].
        Proof by contradiction. Assume the contrary.
          f,g are functions.
          Dom(f) = Dom(g).
          Forall x /in Dom(f) f[x] = g[x].
          Then f = g.
          Contradiction.
        end.
        Take a zfset x such that x /in Dom(f) /\ f[x] /neq g[x].
        Then split[f] /neq split[g].
        Proof.
          Case x /in gamma.
            Then f /upharpoonright gamma /neq g /upharpoonright gamma.
          end.
          Case x = gamma.
            Then f[gamma] /neq g[gamma].
          end.
        end.
      end.
      ran(split) = ^{gamma}alpha /times alpha.
      Proof.
        Let pair /in ^{gamma}alpha /times alpha.
        Take zfsets f,a such that f /in ^{gamma}alpha /\ a /in alpha /\ pair = (f,a).
        f : gamma /rightarrow alpha.
        Define g[n] =
          Case n /in gamma -> f[n],
          Case n = gamma -> a
        for n in beta.
        Then g : beta /rightarrow alpha.
        Proof.
          Let n /in beta.
          Then g[n] /in alpha.
          Proof.
            Case n /in gamma. 
              Then g[n] = f[n].
              f[n] /in ran(f).
              ran(f) /subset alpha.
              Then f[n] /in alpha.
            end.
            Case n = gamma. 
              Then g[n] = a.
              a /in alpha.
            end.
          end.
        end.
        Then g /in ^{beta}alpha.
        g /upharpoonright gamma = f.
        Proof.
          Dom(f) = Dom(g /upharpoonright gamma).
          Forall x /in gamma f[x] = (g /upharpoonright gamma)[x].
        end.
        g[gamma] = a.
        Then split[g] = (f,a).
        Then pair /in ran(split).
      end.
      Then split : ^{beta}alpha /leftrightarrow ^{gamma}alpha /times alpha.
      alpha ^3 beta = Card(^{beta}alpha).
      Then alpha ^3 beta = Card(^{gamma}alpha /times alpha).
    end.
  end.
qed.



## Calculation Rules


Lemma. Let alpha, beta, gamma /in /Cd. Then alpha *3 (beta +3 gamma) = (alpha *3 beta) +3 (alpha *3 gamma).
Proof.
  alpha *3 (beta +3 gamma) = Card( alpha /times (beta +3 gamma)).
  Take zfsets xx,yy such that Card(xx) = beta /\ Card(yy) = gamma.
  Define x = {(z,0) | z /in xx}.
  Define y = {(z,1) | z /in yy}.
  (x is a zfset) /\ x /tilde xx.
  Proof.
    Define f[z] = (z,0) for z in xx.
    f is a zffunction.
    Proof.
      Let z /in xx. Then f[z] /in /VV.
    end.
    Then f : xx /rightarrow x.
    f is injective.
    Proof.
      Let z1,z2 /in xx. Let z1 /neq z2.
      Then f[z1] /neq f[z2].
    end.
    ran(f) = x.
    Then x = f^[xx].
    Then x /in /VV.
    f : xx /leftrightarrow x.
  end.
  
  (y is a zfset) /\ y /tilde yy.
  Proof.
    Define f[z] = (z,1) for z in yy.
    f is a zffunction.
    Proof.
      Let z /in yy. Then f[z] /in /VV.
    end.
    Then f : yy /rightarrow y.
    f is injective.
    Proof.
      Let z1,z2 /in yy. Let z1 /neq z2.
      Then f[z1] /neq f[z2].
    end.
    ran(f) = y.
    Then y = f^[yy].
    Then y /in /VV.
    f : yy /leftrightarrow y.
  end.
  
  x /cap y = /emptyset /\ Card(x) = beta /\ Card(y) = gamma.
  Then (beta,gamma) /sim (x,y).
  x /cup y is a zfset.
  Then beta +3 gamma = Card(x /cup y).
  alpha /times Card(x /cup y) is a zfset.
  Then alpha *3 (beta +3 gamma) = Card( alpha /times Card(x /cup y)).
  alpha, alpha /times (x /cup y) are zfsets.
  alpha /times (x /cup y) /tilde Card(alpha) /times Card(x /cup y).
  Then alpha *3 (beta +3 gamma) = Card(alpha /times (x /cup y)).
  
  alpha /times (x /cup y) = (alpha /times x) /cup (alpha /times y).
  
  (alpha /times x) /cap (alpha /times y) = /emptyset.
  Proof by contradiction. Assume the contrary.
    Take a zfset pair such that pair /in (alpha /times x) /cap (alpha /times y).
    pair /in alpha /times x.
    Take zfsets a1,b1 such that a1 /in alpha /\ b1 /in x /\ pair = (a1,b1).
    pair /in alpha /times y.
    Take zfsets a2,b2 such that a2 /in alpha /\ b2 /in y /\ pair = (a2,b2).
    Then (a1,b1) = (a2,b2).
    Then b1 = b2.
    Then b1 /in x /cap y.
    Contradiction.
  end.
  alpha /times x is a zfset.
  (alpha /times x) /tilde (alpha /times beta).
  Then (alpha *3 beta) = Card(alpha /times x).
  alpha /times y is a zfset.
  (alpha /times y) /tilde (alpha /times gamma).
  Then (alpha *3 gamma) = Card(alpha /times y).
  Then ((alpha *3 beta), (alpha *3 gamma)) /sim ((alpha /times x), (alpha /times y)).
  
  Then (alpha *3 beta) +3 (alpha *3 gamma) = Card((alpha /times x) /cup (alpha /times y)).
qed.


Lemma. Let alpha, beta, gamma /in /Cd. Then (alpha ^3 (beta +3 gamma) = (alpha ^3 beta) *3 (alpha ^3 gamma)).
Proof.
  Take zfsets xx,yy such that Card(xx) = beta /\ Card(yy) = gamma.
  Define x = {(z,0) | z /in xx}.
  Define y = {(z,1) | z /in yy}.
  (x is a zfset) /\ x /tilde xx.
  Proof.
    Define f[z] = (z,0) for z in xx.
    f is a zffunction.
    Proof.
      Let z /in xx. Then f[z] /in /VV.
    end.
    Then f : xx /rightarrow x.
    f is injective.
    Proof.
      Let z1,z2 /in xx. Let z1 /neq z2.
      Then f[z1] /neq f[z2].
    end.
    ran(f) = x.
    Then x = f^[xx].
    Then x /in /VV.
    f : xx /leftrightarrow x.
  end.
  
  (y is a zfset) /\ y /tilde yy.
  Proof.
    Define f[z] = (z,1) for z in yy.
    f is a zffunction.
    Proof.
      Let z /in yy. Then f[z] /in /VV.
    end.
    Then f : yy /rightarrow y.
    f is injective.
    Proof.
      Let z1,z2 /in yy. Let z1 /neq z2.
      Then f[z1] /neq f[z2].
    end.
    ran(f) = y.
    Then y = f^[yy].
    Then y /in /VV.
    f : yy /leftrightarrow y.
  end.
  
  x /cap y = /emptyset /\ Card(x) = beta /\ Card(y) = gamma.
  Then (beta,gamma) /sim (x,y).
  beta +3 gamma /tilde x /cup y.
  Then ^{beta +3 gamma}alpha /tilde ^{x /cup y}alpha.
  
  ^{x /cup y}alpha /tilde ^{x}alpha /times ^{y}alpha.
  Proof.
    Define phi[f] = (f /upharpoonright x, f /upharpoonright y) for f in ^{x /cup y}alpha.
    Then phi : ^{x /cup y}alpha /rightarrow ^{x}alpha /times ^{y}alpha.
    Proof.
      Dom(phi) = ^{x /cup y}alpha.
      phi is a zffunction.
      Proof.
        Let f /in ^{x /cup y}alpha.
        Then f /upharpoonright x /in /VV.
        Proof.
          Let z /in x. Then (f /upharpoonright x)[z] /in /VV.
          Then f /upharpoonright x is a zffunction.
          Dom(f /upharpoonright x) = x.
          Then Dom(f /upharpoonright x) /in /VV.
        end.
        f /upharpoonright y /in /VV.
        Proof.
          Let z /in y. Then (f /upharpoonright y)[z] /in /VV.
          Then f /upharpoonright y is a zffunction.
          Dom(f /upharpoonright y) = y.
          Then Dom(f /upharpoonright y) /in /VV.
        end.
        Then phi[f] /in /VV.
      end.
      ran(phi) /subset ^{x}alpha /times ^{y}alpha.
      Proof.
        Let f /in ^{x /cup y}alpha.
        Then f /upharpoonright x /in ^{x}alpha.
        Proof.
          Dom(f /upharpoonright x) = x.
          Forall z /in x (f /upharpoonright x)[z] = f[z].
          f : x /cup y /rightarrow alpha.
          Forall z /in x f[z] /in alpha.
          Then forall z /in x (f /upharpoonright x)[z] /in alpha.
          Then ran(f /upharpoonright x) /subset alpha.
        end.
        Then f /upharpoonright y /in ^{y}alpha.
        Proof.
          Dom(f /upharpoonright y) = y.
          Forall z /in y (f /upharpoonright y)[z] = f[z].
          f : x /cup y /rightarrow alpha.
          Forall z /in y f[z] /in alpha.
          Then forall z /in y (f /upharpoonright y)[z] /in alpha.
          Then ran(f /upharpoonright y) /subset alpha.
        end.
        Then phi[f] /in ^{x}alpha /times ^{y}alpha.
      end.
    end.
    
    Forall f, g /in ^{x /cup y}alpha (f /neq g => phi[f] /neq phi[g]).
    Proof.
      Let f,g /in ^{x /cup y}alpha. Let f /neq g.
      Then exists z /in x /cup y (f[z] /neq g[z]).
      Proof by contradiction. Assume the contrary.
        f,g are functions.
        Dom(f) = Dom(g).
        Forall z /in Dom(f) f[z] = g[z].
        Then f = g.
        Contradiction.
      end.
      Take a zfset z such that z /in x /cup y /\ f[z] /neq g[z].
      Take zfsets a1,b1 such that a1 = (f /upharpoonright x) /\ b1 = (f /upharpoonright y).
      Take zfsets a2,b2 such that a2 = (g /upharpoonright x) /\ b2 = (g /upharpoonright y).
      Then phi[f] = (a1,b1).
      Then phi[g] = (a2,b2).     
      Then phi[f] /neq phi[g].
      Proof.
        Case z /in x.
          Then (f /upharpoonright x)[z] /neq (g /upharpoonright x)[z].
          Then (f /upharpoonright x) /neq (g /upharpoonright x).
          Then (f /upharpoonright x) /neq (g /upharpoonright x).
          Then a1 /neq a2. 
          Then (a1,b1) /neq (a2,b2).
        end.
        Case z /in y. Then (f /upharpoonright y) /neq (g /upharpoonright y).
          Then b1 /neq b2. 
          Then (a1,b1) /neq (a2,b2).
        end.
      end.
    end.
    Then phi is injective.
    
    ran(phi) = ^{x}alpha /times ^{y}alpha.
    Proof.
      Let pair /in ^{x}alpha /times ^{y}alpha.
      Take a set A such that A = ^{x}alpha.
      Take a set B such that B = ^{y}alpha.
      Then pair /in A /times B.
      Take zfsets f1,f2 such that f1 /in A /\ f2 /in B /\ pair = (f1,f2).
      Then f1 : x /rightarrow alpha.
      Then f2 : y /rightarrow alpha.
      Define f[n] =
        Case n /in x -> f1[n],
        Case n /in y -> f2[n]
      for n in x /cup y.
      Then f : x /cup y /rightarrow alpha.
      Proof.
        f is a zffunction.
        Proof.
          let z /in x /cup y. Then f[z] /in /VV.
        end.
        ran(f) /subset alpha.
        Proof.
          Let z /in x /cup y. Then f[z] /in alpha.
          Proof.
            Case z /in x. 
              Then f[z] = f1[z].
              f1[z] /in alpha.
            end.
            Case z /in y. 
              Then f[z] = f2[z].
              f2[z] /in alpha.
            end.
          end.
        end.
      end.
      
      f /upharpoonright x = f1.
      Proof.
        f1,(f /upharpoonright x) are functions.
        Dom(f1) = Dom(f /upharpoonright x).
        Forall z /in Dom(f1) f1[z] = (f /upharpoonright x)[z].
      end.  
      f /upharpoonright y = f2.
      Proof.
        f2,(f /upharpoonright y) are functions.
        Dom(f2) = Dom(f /upharpoonright y).
        Forall z /in Dom(f2) f2[z] = (f /upharpoonright y)[z].
      end.   
      Then phi[f] = (f1,f2).
      Then pair /in ran(phi).
    end.
    
    Then phi : ^{x /cup y}alpha /leftrightarrow ^{x}alpha /times ^{y}alpha.
  end.
  
  ^{beta +3 gamma}alpha /tilde ^{x}alpha /times ^{y}alpha.
  Proof.
    Take zfsets A,B,C such that A = ^{beta +3 gamma}alpha /\ B = ^{x /cup y}alpha /\ C = ^{x}alpha /times ^{y}alpha.
    ^{beta +3 gamma}alpha /tilde ^{x /cup y}alpha.
    ^{x /cup y}alpha /tilde ^{x}alpha /times ^{y}alpha.
    Then A /tilde B /\ B /tilde C.
    Then A /tilde C.
  end.
  
  x /tilde beta.
  ^{x}alpha is a zfset.
  Then ^{x}alpha /tilde ^{beta}alpha.
  Then alpha ^3 beta = Card(^{x}alpha).
  
  y /tilde gamma.
  ^{y}alpha is a zfset.
  Then ^{y}alpha /tilde ^{gamma}alpha.
  Then alpha ^3 gamma = Card(^{y}alpha).
  
  Card(^{x}alpha) /times Card(^{y}alpha) is a zfset.
  (alpha ^3 beta) *3 (alpha ^3 gamma) = Card(Card(^{x}alpha) /times Card(^{y}alpha)).
  Card(^{x}alpha) /times Card(^{y}alpha) /tilde ^{x}alpha /times ^{y}alpha.
  Then (alpha ^3 beta) *3 (alpha ^3 gamma) /tilde ^{x}alpha /times ^{y}alpha.
  ^{x}alpha /times ^{y}alpha /tilde (alpha ^3 beta) *3 (alpha ^3 gamma).
  
  Then (alpha ^3 (beta +3 gamma) /tilde (alpha ^3 beta) *3 (alpha ^3 gamma)).
  Proof.
    Forall A,B,C /in /VV (A /tilde B /\ B /tilde C => A /tilde C).
    Take a zfset A such that A = (alpha ^3 (beta +3 gamma)).
    Take a zfset B such that B = ^{x}alpha /times ^{y}alpha.
    Take a zfset C such that C = (alpha ^3 beta) *3 (alpha ^3 gamma).
    Then A /tilde B /\ B /tilde C.
    Then A /tilde C.
  end.
qed.


Definition. Let alpha, beta, gamma /in /VV. Let f /in ^{beta /times gamma}alpha. Let F be a zffunction.
F /partial (f,alpha,beta,gamma) iff (Dom(F) = gamma /\ forall b /in gamma ((F[b] is a zffunction) /\ Dom(F[b]) = beta /\ forall a /in beta (F[b])[a] = f[(a,b)])).


Lemma. Let alpha, beta, gamma /in /VV. Let f /in ^{beta /times gamma}alpha. Let F be a zffunction. Let F /partial (f,alpha,beta,gamma).
Then F /in ^{gamma}(^{beta}alpha).
Proof.
  Forall b /in gamma F[b] /in ^{beta}alpha.
  Proof.
    Let b /in gamma.
    Then (F[b] is a zffunction) /\ Dom(F[b]) = beta.
    ran(F[b]) /subset alpha.
    Proof.
      Let a /in beta.
      Then f[(a,b)] /in alpha.
      Then (F[b])[a] /in alpha.
    end.
  end.
qed.


Lemma. Let alpha, beta, gamma /in /Cd. Then (alpha ^3 (beta *3 gamma) = (alpha ^3 beta) ^3 gamma).
Proof.
  Forall f /in ^{beta /times gamma}alpha forall a /in beta forall b /in gamma (a,b) /in Dom(f).
  Forall f /in ^{beta /times gamma}alpha exists F (F /partial (f,alpha,beta,gamma)).
  Proof.
    Let f /in ^{beta /times gamma}alpha.
    Forall b /in gamma exists g ( Dom(g) = beta /\ forall a /in beta g[a] = f[(a,b)]).
    Proof.
      Let b /in gamma.
      Define g[a] = f[(a,b)] for a in beta.
      Then Dom(g) = beta.
      g is a zffunction.
      Proof.
        Let a /in beta. Then g[a] /in /VV.
      end.
      Forall a /in beta g[a] = f[(a,b)].
    end.
    Define F[b] = (Choose a zffunction g such that ( Dom(g) = beta /\ forall a /in beta g[a] = f[(a,b)]) in g) for b in gamma.
    Then F is a zffunction.
    Proof.
      Let b /in gamma.
      Then F[b] is a zffunction.
      Dom(F[b]) /in /VV.
      Then F[b] /in /VV.
    end.
    Dom(F) = gamma.
    Forall b /in gamma ((F[b] is a zffunction) /\ Dom(F[b]) = beta /\ forall a /in beta (F[b])[a] = f[(a,b)]).
    Then F /partial (f,alpha,beta,gamma).
  end.
  Define phi[f] = (Choose a zffunction F such that (F /partial (f,alpha,beta,gamma)) in F) for f in ^{beta /times gamma}alpha.
  
  phi is a zffunction.
  Proof.
    Let f /in ^{beta /times gamma}alpha.
    Then phi[f] is a zffunction.
    Dom(phi[f]) /in /VV.
    Then phi[f] /in /VV.
  end.
  phi : ^{beta /times gamma}alpha /rightarrow ^{gamma}(^{beta}alpha).
  Proof.
    Let f /in ^{beta /times gamma}alpha.
    Then phi[f] is a zffunction.
    Take a zffunction F such that F = phi[f].
    Then F /partial (f,alpha,beta,gamma).
    Then F /in ^{gamma}(^{beta}alpha).
  end.
  
  phi is injective.
  Proof.
    Let f1,f2 /in Dom(phi).
    Let f1 /neq f2.
    f1,f2 /in ^{beta /times gamma}alpha.
    Then exists pair /in beta /times gamma (f1[pair] /neq f2[pair]).
    Proof by contradiction. Assume the contrary.
      f1,f2 are functions.
      Dom(f1) = Dom(f2).  
      Forall pair /in Dom(f1) f1[pair] = f2[pair].
      Then f1 = f2. 
      Contradiction.
    end.
    Take a zfset pair such that pair /in beta /times gamma /\ f1[pair] /neq f2[pair].
    Take zfsets a,b such that a /in beta /\ b /in gamma /\ pair = (a,b).
    Then phi[f1] /neq phi[f2].
  end.
    
  ran(phi) = ^{gamma}(^{beta}alpha).
  Proof.
    Let F /in ^{gamma}(^{beta}alpha).
    Forall b /in gamma F[b] /in ^{beta}alpha.
    Forall o1,o2 ((o1,o2) /in beta /times gamma => o1 /in beta /\ o2 /in gamma).
    Define f[(a,b)] = (F[b])[a] for pair in beta /times gamma.
    Then f : beta /times gamma /rightarrow alpha.
    Proof.
      Dom(f) = beta /times gamma.
      Let pair /in beta /times gamma.
      Take zfsets a,b such that a /in beta /\ b /in gamma /\ pair = (a,b).
      Then f[pair] = (F[b])[a].
      Then F[b] /in ^{beta}alpha.
      Then (F[b])[a] /in alpha.
      Then f[pair] /in alpha.
    end.
    F /partial (f,alpha,beta,gamma).
    Proof.
      Dom(F) = gamma.
      Forall b /in gamma ((F[b] is a zffunction) /\ Dom(F[b]) = beta /\ forall a /in beta (F[b])[a] = f[(a,b)]).
      Proof.
        Let b /in gamma.
        Then F[b] is a zffunction.
        Dom(F[b]) = beta.
        Forall a /in beta (F[b])[a] = f[(a,b)].
        Proof.
          Let a /in beta.
          Then (a,b) /in beta /times gamma.
          Take zfsets aa,bb such that aa /in beta /\ bb /in gamma /\ (a,b) = (aa,bb) /\ f[(a,b)] = (F[bb])[aa].
          Then a = aa /\ b = bb.
          Then f[(a,b)] = (F[b])[a].
        end.
      end.
    end.
    Then phi[f] = F.
    Proof.
      Take a zffunction G such that G = phi[f].
      Then G /partial (f,alpha,beta,gamma).
      Then F = G.
      Proof.
        F,G are functions.
        Then (F = G iff Dom(F) = Dom(G) /\ forall val /in Dom(F) F[val] = G[val]).
        Dom(F) = Dom(G).
        Forall b /in gamma F[b] = G[b].
        Proof.
          Let b /in gamma.
          Then F[b] = G[b].
          Proof.
            F[b], G[b] are functions.
            Then (F[b] = G[b] iff Dom(F[b]) = Dom(G[b]) /\ forall val /in Dom(F[b]) F[b][val] = G[b][val]).
            Dom(F[b]) = beta /\ Dom(G[b]) = beta.
            Forall a /in beta (F[b])[a] = (G[b])[a].
            Proof.
              Let a /in beta.
              Then (F[b])[a] = f[(a,b)].
              (G[b])[a] = f[(a,b)].
            end.
          end.
        end.
      end.
    end.
    Then F /in ran(phi).
  end.
  
  Then phi : ^{beta /times gamma}alpha /leftrightarrow ^{gamma}(^{beta}alpha).
  
  Then ^{beta /times gamma}alpha /tilde ^{gamma}(^{beta}alpha).
  
  beta *3 gamma /tilde beta /times gamma.
  alpha ^3 (beta *3 gamma) /tilde ^{beta *3 gamma}alpha.
  Then alpha ^3 (beta *3 gamma) /tilde ^{beta /times gamma}alpha.
  Proof.
    Take zfsets x1,x2 such that x1 = beta *3 gamma /\ x2 = beta /times gamma.
    Then ^{x1}alpha /tilde ^{x2}alpha.
    alpha ^3 (x1) /tilde ^{x1}alpha.
    Then alpha ^3 (x1) /tilde ^{x2}alpha.
  end.
  
  ^{beta}alpha /tilde alpha ^3 beta.
  Then ^{gamma}(^{beta}alpha) /tilde ^{gamma}(alpha ^3 beta).
  ^{gamma}(alpha ^3 beta) /tilde (alpha ^3 beta) ^3 gamma.
  Then ^{gamma}(^{beta}alpha) /tilde (alpha ^3 beta) ^3 gamma.
  
  Then (alpha ^3 (beta *3 gamma) = (alpha ^3 beta) ^3 gamma).
  Proof.
    Take a zfset x1 such that x1 = (alpha ^3 (beta *3 gamma)).
    Take a zfset x2 such that x2 = ^{beta /times gamma}alpha.
    Take a zfset x3 such that x3 = ^{gamma}(^{beta}alpha).
    Take a zfset x4 such that x4 = (alpha ^3 beta) ^3 gamma.
    Then x1 /tilde x2 /\ x2 /tilde x3 /\ x3 /tilde x4.
    Then x1 /tilde x4.
  end.
qed.


Lemma. Forall kappa /in /Card (kappa *3 kappa = kappa).
Proof.
  Let kappa /in /Card.
  Then kappa /tilde kappa /times kappa.
qed.


Lemma. Let kappa /in /Card. Let lambda /in /Cd. Let lambda /neq 0. Then kappa *3 lambda = kappa /cup lambda.
Proof.
  Forall a,b /in /Ord (a /subset b \/ b /subset a).
  kappa /subset lambda \/ lambda /subset kappa.
  Case kappa /subset lambda.
    Then kappa /cup lambda = lambda.
    lambda <= kappa /times lambda.
    Proof.
      Define f[n] = (0,n) for n in lambda.
      Then f : lambda /rightarrow kappa /times lambda.
      Proof.
        Let n /in lambda. 0 /in kappa.
        Then (0,n) /in kappa /times lambda.
        Then f[n] /in kappa /times lambda.
      end.
      f is injective.
      Proof.
        Let m,n /in lambda.
        Let m /neq n.
        Then (0,m) /neq (0,n).
        Then f[m] /neq f[n].
      end.
    end.
    kappa /times lambda /subset lambda /times lambda.
    /NN /subset lambda.
    lambda /times lambda /tilde lambda.
    Then kappa /times lambda <= lambda.
    Then kappa *3 lambda = lambda.
  end.
  Case lambda /subset kappa.
    Then kappa /cup lambda = kappa.
    kappa <= kappa /times lambda.
    Proof.
      Define f[n] = (n,0) for n in kappa.
      Then f : kappa /rightarrow kappa /times lambda.
      Proof.
        Let n /in kappa. 0 /in lambda.
        Then (n,0) /in kappa /times lambda.
        Then f[n] /in kappa /times lambda.
      end.
      f is injective.
      Proof.
        Let m,n /in kappa.
        Let m /neq n.
        Then (m,0) /neq (n,0).
        Then f[m] /neq f[n].
      end.
    end.
    kappa /times lambda /subset kappa /times kappa.
    kappa /times kappa /tilde kappa.
    Then kappa /times lambda <= kappa.
    Then kappa *3 lambda = kappa.
  end.
qed.


Lemma. Let kappa /in /Card. Let lambda /in /Cd. Then kappa +3 lambda = kappa /cup lambda.
Proof.
  Define x = {(z,0) | z /in kappa}.
  Define y = {(z,1) | z /in lambda}.
  (x is a zfset) /\ x /tilde kappa.
  Proof.
    Define f[z] = (z,0) for z in kappa.
    f is a zffunction.
    Proof.
      Let z /in kappa. Then f[z] /in /VV.
    end.
    Then f : kappa /rightarrow x.
    f is injective.
    Proof.
      Let z1,z2 /in kappa. Let z1 /neq z2.
      Then f[z1] /neq f[z2].
    end.
    ran(f) = x.
    Then x = f^[kappa].
    Then x /in /VV.
    f : kappa /leftrightarrow x.
  end.
  (y is a zfset) /\ y /tilde lambda.
  Proof.
    Define f[z] = (z,1) for z in lambda.
    f is a zffunction.
    Proof.
      Let z /in lambda. Then f[z] /in /VV.
    end.
    Then f : lambda /rightarrow y.
    f is injective.
    Proof.
      Let z1,z2 /in lambda. Let z1 /neq z2.
      Then f[z1] /neq f[z2].
    end.
    ran(f) = y.
    Then y = f^[lambda].
    Then y /in /VV.
    f : lambda /leftrightarrow y.
  end.
  x /cap y = /emptyset /\ Card(x) = kappa /\ Card(y) = lambda.
  Then (kappa,lambda) /sim (x,y).
  kappa +3 lambda /tilde x /cup y.
  
  Forall a,b /in /Ord (a /subset b \/ b /subset a).
  kappa /subset lambda \/ lambda /subset kappa.
  Case kappa /subset lambda.
    Then kappa /cup lambda = lambda.
    lambda <= kappa +3 lambda.
    x /cup y /subset lambda /times 2.
    Then kappa +3 lambda <= lambda /times 2.
    lambda *3 2 = lambda /cup 2.
    Then lambda /times 2 /tilde lambda.
    Then kappa +3 lambda <= lambda.
    Then kappa +3 lambda /tilde lambda.
  end.
  Case lambda /subset kappa.
    Then kappa /cup lambda = kappa.
    kappa <= kappa +3 lambda.
    x /cup y /subset kappa /times 2.
    Then kappa +3 lambda <= kappa /times 2.
    kappa *3 2 = kappa /cup 2.
    Then kappa /times 2 /tilde kappa.
    Then kappa +3 lambda <= kappa.
    Then kappa +3 lambda /tilde kappa.
  end.
qed.


Lemma. Forall n /in /NN forall kappa /in /Card (n /neq 0 => kappa ^3 n = kappa).
Proof by induction.
  Let n /in /NN.
  Let kappa /in /Card.
  Then n /neq 0 => kappa ^3 n = kappa.
  Proof.
    Case n = 0.
    end.
    Case n /neq 0.
      Let m = n--.
      Case m = 0.
        Then n = 1.
      end.
      Case m /neq 0.
        kappa ^3 n = kappa ^3 (m +3 1).
        Then kappa ^3 n = (kappa ^3 m) *3 (kappa ^3 1).
        kappa ^3 m = kappa.
        kappa ^3 1 = kappa.
        kappa *3 kappa = kappa.
      end.
    end.
  end.
qed.


Lemma. Let kappa /in /Card. Let lambda /in /Cd. Let 2 /subset lambda. Let lambda /subset (2 ^3 kappa).
Then lambda ^3 kappa = 2 ^3 kappa.
Proof.
  2 ^3 kappa /subset lambda ^3 kappa.
  Proof.
    2 /subset lambda.
    Then ^{kappa}2 /subset ^{kappa}lambda.
    Then Card(^{kappa}2) /subset Card(^{kappa}lambda).
  end.
  lambda ^3 kappa /subset (2 ^3 kappa) ^3 kappa.
  Proof.
    ^{kappa}lambda /subset ^{kappa}(2 ^3 kappa).
    Take zfsets x1,x2 such that x1 = ^{kappa}lambda /\ x2 = ^{kappa}(2 ^3 kappa).
    Then lambda ^3 kappa = Card(x1).
    Then (2 ^3 kappa) ^3 kappa = Card(x2).
  end.
  (2 ^3 kappa) ^3 kappa = 2 ^3 (kappa *3 kappa).
  kappa *3 kappa = kappa.
  Then 2 ^3 (kappa *3 kappa) = 2 ^3 kappa.
  Then lambda ^3 kappa /subset 2 ^3 kappa.
qed.


