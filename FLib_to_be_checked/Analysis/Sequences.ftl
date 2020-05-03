[read Forster/Naturals.ftl]
[sequence/-s]
Let n : nat stand for n is a natural number.


Definition Seq.
A sequence f is a function such that every element of Dom(f) is a natural number and every natural number is an element of Dom(f) and for every natural number n f[n] is a real number.

Axiom SequenceEq.
Let a, b be sequences. a = b <=> (for every natural number n a[n] = b[n]).

Let a denote a sequence.



Definition Convergence.
Let a be a sequence. Let x be a real number. a converges to x iff for every positive real number eps
there exists a natural number N such that for every natural number n such that N < n dist(a[n],x) < eps.

Definition Conv.
Let a be a sequence. a converges iff there exists a real number x such that a converges to x.


Let a is convergent stand for a converges.

Signature Limit.
Let a be a sequence. Assume a converges. lim a is a real number such that a converges to lim a.



### Sequence 1/n converges to 0

Lemma.
Let a be a sequence such that for every positive natural number n a[n] = inv(n). Then a converges to 0.
Proof.
Assume eps is a positive real number. Take a natural number N such that 1 < N * eps (by ArchimedeanAxiom, OnePos).
Let us show that for every natural number n such that N < n dist(a[n],0) < eps.
  Assume n is a natural number such that N < n. n is positive. [ontored on]
  1 < n * eps. [/ontored] inv(n) < eps.
  end.
qed.


### A convergent sequence is bounded

Definition BoundedSequence.
Let a be a sequence. a is bounded iff there exists a real number K such that
for every natural number n abs(a[n]) =< K.

Definition BoundedBy.
Let a be a sequence. Let K be a real number. a is bounded by K iff for every
natural number n abs(a[n]) =< K.


#Lemma Bounded.
#Let a be a sequence. (There exists a real number K such that a is bounded by K)
#iff a is bounded.

Signature Max.
Let a be a sequence. Let N be a natural number. maxN(a,N) is a real number such that
(there exists a natural number n such that n =< N and maxN(a,N) = a[n]) and
for every natural number n (n =< N => a[n] =< maxN(a,N)).


Lemma ConvergentImpBounded.
Every convergent sequence is bounded.
Proof.
Let a be a convergent sequence. Take a real number x such that a converges to x.
Take a natural number N such that for every natural number n such that N < n dist(a[n],x) < 1 (by Convergence, OnePos).
For any natural number n such that N < n we have abs(a[n]) =< abs(x) + 1. proof.
	Let n be a natural number such that N < n. abs(a[n]) =< abs(x) + dist(a[n],x). abs(x) + dist(a[n],x) < abs(x) + 1.
	end.
Define a2 = \n in NAT. abs(a[n]).
Define b = \n in NAT. case n = N + 1 -> abs(x) + 1, case not n = N + 1 -> a2[n].
Then b is a sequence.
Take a real number K such that K = maxN(b, N + 1).
Let us show that for every natural number n abs(a[n]) =< K.
	Let n be a natural number.
	Case N < n. abs(a[n]) =< b[N + 1] =< K. [ontored on] end. [/ontored]
	Case n =< N. abs(a[n]) = b[n] =< K. end.
 	end.
qed.


Lemma LimitUnique.
Let a be a sequence. Let x,y be real numbers. If a converges to x and a converges to y then x = y.
Proof.[ontored on]
Assume a converges to x and a converges to y. Assume  x != y. Take a real number eps such that eps = dist(x,y) * inv(2).Then pos(eps).
Take a natural number N1 such that for every natural number n such that N1 < n dist(a[n],x) < eps (by Convergence).
Take a natural number N2 such that for every natural number n such that N2 < n dist(a[n],y) < eps (by Convergence).
Take a natural number N3 such that N3 = max(N1,N2) + 1.
Then N1 < N3 and N2 < N3.
Hence dist(a[N3],x) < eps and dist(a[N3],y) < eps.
Therefore dist(x,a[N3]) + dist(a[N3],y) < eps + eps (by AddInvariance, DistSymm).
We have dist(x,y) =< dist(x,a[N3]) + dist(a[N3],y) (by DistTriangleIneq).
Therefore dist(x,y) < eps + eps (by MixedTransitivity).
eps + eps = dist(x,y).
Hence dist(x,y) < dist(x,y). A contradiction.
qed.
[/ontored]
### Sum and Product of sequences

Definition SequenceSum.
Let a, b be sequences. a +' b is a sequence such that for every natural number n (a +' b)[n] = a[n] + b[n].

Signature SequenceProd.
Let a,b be sequences. a *' b is a sequence such that for every natural number n (a *' b)[n] = a[n] * b[n].

Lemma SumConv.
Let a,b be sequences. Let x,y be real numbers. Assume a converges to x and b converges to y.
Then a +' b converges to x + y.
Proof.
Let eps be a positive real number. We have not 2 = 0.
Take a real number eps2 such that eps2 = eps * inv(2). Then pos(eps2).
Take a natural number N1 such that for all natural numbers n such that N1 < n dist(a[n],x) < eps * inv(2) (by Convergence).
Take a natural number N2 such that for all natural numbers n such that N2 < n dist(b[n],y) < eps * inv(2) (by Convergence).
Take a natural number N3 such that N3 = max(N1,N2) + 1. Then N1 < N3 and N2 < N3.
Let us show that for every natural number n such that N3 < n dist((a +' b)[n],x + y) < eps.
  Let n be a natural number such that N3 < n. Then N1 < n and N2 < n (by TransitivityOfOrder).
  Therefore dist(a[n],x) < eps * inv(2) and dist(b[n],y) < eps * inv(2).
  Let us show that dist((a +' b)[n], x + y) < (eps * inv(2)) + (eps * inv(2)). [ontored on]
      dist((a +' b)[n], x + y) = abs((a[n] - x) + (b[n] - y)) =< dist(a[n],x) + dist(b[n],y).[/ontored]
      Therefore the thesis (by MixedTransitivity, AddInvariance).
      end.
  (eps * inv(2)) + (eps * inv(2)) = eps.
  Therefore dist((a +' b)[n], x + y) < eps.
  end.
qed.


Lemma SumConvRewrite.
Let a,b be convergent sequences. Then a +'b is convergent and lim (a +'b) = lim a + lim b.
Proof.
Take real numbers x,y such that a converges to x and b converges to y.
a +' b converges to x + y (by SumConv). Therefore a +' b is convergent.
lim (a +' b) = x + y = lim a + lim b (by LimitUnique, Limit ).
qed.


[prove off]
### The following proof is not yet finished
Lemma ProdConv.
Let a,b be sequences. Let x,y be real numbers. Assume a converges to x and b converges to y.
Then a *' b converges to x * y.
Proof.
a is bounded (by ConvergentImpBounded).
Take a real number K2 such that for every natural number n abs(a[n]) =< K2 (by BoundedSequence).
Take a real number K3 such that K3 = max(K2,abs(y)).
(For every natural number n abs(a[n]) =< K3) and abs(y) =< K3 (by MaxIneq, MaxSym, LeqTransitivity).
Take a real number K such that K = max(K3, 1) + 1.
Then for every natural number n abs(a[n]) < K and abs(y) < K. Then pos(K).
Let eps be a positive real number. (1) Take a real number eps2 such that eps2 = eps * inv(2 * K).
Let us show that pos(eps2).
  pos(inv(2 * K)).
  end.
Take a natural number N1 such that for all natural numbers n such that N1 < n dist(a[n],x) < eps2 (by Convergence).
Take a natural number N2 such that for all natural numbers n such that N2 < n dist(b[n],y) < eps2 (by Convergence).
Take a natural number N3 such that N3 = max(N1,N2) + 1.
Let us show that N1 < N3 and N2 < N3.
    We have max(N1, N2) < max(N1,N2) + 1.
    We have N1 =< max(N1,N2) (by MaxIneq). Therefore N1 < max(N1,N2) + 1 (by MixedTransitivity).
    We have N2 =< max(N1,N2) (by MaxIneq, MaxSym). Therefore N1 < max(N1,N2) + 1 (by MixedTransitivity).
    end.
Let us show that for every natural number n such that N3 < n dist((a*'b)[n], x*y) < eps.
  Let n be a natural number such that N3 < n. Then N1 < n and N2 < n (by TransitivityOfOrder).
  Let us show that dist((a*'b)[n], x * y) < eps.
  Let us show that dist ((a *' b)[n], x * y) =< (abs(a[n]) * dist(b[n], y)) + (dist(a[n],x) * abs(y)).
      dist((a *' b)[n] , x *y) .= abs(((a[n] * b[n]) + 0) - (x * y))                                          (by SequenceProd, DistDefinition, Zero)
                              .= abs(((a[n] * b[n]) + ((-(a[n] * y)) + (a[n] * y))) - (x * y))                (by Neg, ComAdd)
                              .= abs(((a[n] * b[n]) - (a[n] * y)) + ((a[n] * y) - (x * y)))                   (by AssAdd)
                              .= abs(((a[n] * b[n]) + ((-1) * (a[n] * y))) + ((a[n] * y) + ((-1) * (x * y)))) (by MinusRule4)
                              .= abs(((a[n] * b[n]) +  (a[n] * ((-1) * y))) + ((a[n] * y) + (((-1)* x) * y))) (by AssMult,ComMult, BubbleMult)
                              .= abs(((a[n] * b[n]) + (a[n] * (-y))) + ((a[n] * y) + ((-x) * y)))             (by MinusRule4)
                              .= abs((a[n] * (b[n] - y)) + ((a[n] - x) * y))                                  (by Distrib, DistribDummy).
      abs((a[n] * (b[n] - y)) + ((a[n] - x) * y)) =< abs((a[n] * (b[n] - y))) + abs(((a[n] - x) * y))         (by AbsTriangleIneq).
      abs((a[n] * (b[n] - y))) + abs(((a[n] - x) * y)) .= (abs(a[n]) * abs(b[n] - y)) + (abs(a[n] - x) * abs(y)) (by AbsMult)
                                                       .= (abs(a[n]) * dist(b[n], y)) + (dist(a[n], x) * abs(y)) (by DistDefinition).
      end.
      K is nonnegative (by BoundNonNeg).
      (abs(a[n]) * dist(b[n], y)) + (dist(a[n], x) * abs(y)) < eps.
    end.
    end.
qed.
[/prove]

### Taking limits is weakly monotone

Lemma LimMon.
Let a,b be sequences. Assume a and b are convergent.
If a[n] =< b[n] for every natural number n then lim a =< lim b.
Proof.
Assume for every natural number n a[n] =< b[n].
Let us show that for every convergent sequence c if for every natural number n 0 =< c[n] then 0 =< lim c.
    Let c be a convergent sequence. Assume for every natural number n 0 =< c[n].
    Assume (not 0 =< lim c). Then lim c < 0. Take a real number eps such that
    eps = - lim c. Then pos(eps).
    Take a natural number N such that for every natural number n such that N < n
    dist(c[n], lim c) < eps. Take a natural number n such that N < n. Then
          dist(c[n], lim c) < eps.
          abs(c[n] - lim c) < eps (by DistDefinition).
          c[n] < 0.
    A contradiction.
    end.
(1) Define a2 = \n in NAT. - a[n]. Then a2 is a sequence.
Let us show that (5) a2 converges and lim(a2) = - lim(a).
    Define d = \n in NAT. -1. Then d converges to -1. Then d is a sequence.
    For every natural number n a2[n] = d[n] * a[n] (by MinusRule4). Therefore a2 = d *' a (by SequenceEq).
    Therefore d *' a converges to - lim a (by MinusGr, ProdConv).[unfoldlow on]
    end.[/unfoldlow]
(2) Take a sequence c such that c =  b +' a2. Then c is convergent and lim c = lim b + lim a2 (by SumConvRewrite).
Let us show that for every natural number n 0 =< c[n].
    Let n be a natural number. n is an element of Dom(a2) and a[n] is a real number.## These trivialities are conditions for rewriting
    (3) Case a[n] = b[n].  
    				c[n] .= (b +' a2)[n] (by 2)
                 .= b[n] + a2[n]     (by SequenceSum)
                 .= b[n] - a[n]      (by 1)
                 .= 0                (by 3, Neg).
    end.
    Case a[n] < b[n]. c[n] .= (b +' a2)[n] .= b[n] + a2[n] (by SequenceSum) .= b[n] - a[n] (by 1). b[n] - a[n] > 0. end.
    end.
lim c .= lim b - lim a (by 5,2,SumConvRewrite).
Therefore lim a =< lim b.
qed.
