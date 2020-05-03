
[number/-s]
Signature Real. A real number is a notion.
Signature. RR is the set of real numbers.

Let x,y,z denote real numbers.

Signature A1. x + y is a real number. 
Let the sum of x and y denote x + y.
Signature M1. x * y is a real number.
Let the product of x and y denote x * y.

Axiom A2. x + y = y + x.
Axiom A3. (x + y) + z = x + (y + z).
Signature A4. 0 is a real number such that 
for every real number x x + 0 = x.
Signature A5. -x is a real number such that x + (-x) = 0.

Axiom M2. x * y = y * x.
Axiom M3. (x * y) * z = x * (y * z).
Signature M4. 1 is a real number such that 1 !=0 for every real number x x * 1 = x.
Signature Inverse. Assume not x = 0. inv(x) is a real number such that x * inv(x) = 1.

Lemma OneDummy.
1 * x = x.

Lemma InvDummy.
Assume not x = 0. Then inv(x) * x = 1.





Axiom BubbleAdd. x + (y + z) = y + (x + z).

Lemma ZeroUnique.
Let a be a real number. (1) Assume that for all real numbers x x + a = x. Then a = 0.
Proof.
a .= a + 0 (by Zero)
  .= 0 + a (by ComAdd)
  .= 0     (by 1).
qed.

Lemma NegUnique.
Let a, x be real numbers. (1) Assume that x + a = 0. Then a = -x.
Proof.
a .= (x + a) + (-x) (by ComAdd, AssAdd, BubbleAdd, Neg, Zero)
  .= 0 + (-x) (by 1)
  .= (-x) + 0  (by ComAdd)
  .= (-x) (by Zero).
qed.
Lemma NegOfZero. -0 = 0.
Proof. 0 + 0 = 0 (by Zero). Hence 0 = -0 (by NegUnique). qed.

Let x - y stand for x + (-y).

Lemma MinusRule1.
- (x + y) = (-x) + (-y).
Proof.
    (x + y) + ((-x) + (-y)) .= ( x + (-x)) + (y + (-y)) (by AssAdd, ComAdd, BubbleAdd)
                            .= 0 (by Zero, Neg).
Hence the thesis (by NegUnique).
qed.

Lemma MinusRule2.
-(-x) = x.
Proof.
(-x) + x = 0.
Hence the thesis (by NegUnique).
qed.

Lemma MinusRule3.
-(y - x) = (x - y).
Proof.
- (y - x) .= (-y) + x (by MinusRule1, MinusRule2)
          .= x - y (by ComAdd).
qed.

[group AddGr Add AssAdd ComAdd Zero Neg MinusRule1 MinusRule2 MinusRule3]

Axiom BubbleMult. x * (y * z) = y * (x * z).


Axiom ZeroNotOne. not 1 = 0.
Axiom Distrib. (x * y) + (x * z) = x * (y + z).
Axiom DistribDummy. (y * x) + (z * x) = (y + z) * x.

Lemma OneUnique.
Let a be a real number. Assume for all real numbers x x * a = x. Then a = 1.
Proof. a = a * 1 = 1 * a = 1. qed.


Lemma ZeroMult.
0 * x = 0.
Proof.
(1) 0 * x .= (0 + 0) * x            (by Zero)
          .= x * (0 + 0)            (by ComMult)
          .= (x * 0) + (x * 0)      (by Distrib)
          .= (0 * x) + (0 * x)      (by ComMult).
0 .= (0 * x) - (0 * x)              (by Neg)
  .= ((0 * x) + (0 * x)) - (0 * x)  (by 1)
  .= (0 * x) + ((0 * x) - (0 * x))  (by AssAdd)
  .= (0 * x)                        (by Zero,Neg).
qed.

Lemma InvNotZero.
Assume not x = 0. Then not inv(x) = 0.
Proof.
(1) Assume inv(x) = 0.
1 .= inv(x) * x (by Inverse, ComMult)
  .= 0 * x (by 1, ZeroMult).
qed.

Lemma InvUnique.
Let a be a real number. (1) Assume x * a = 1. Then (not x = 0) and a = inv(x).
Proof.
Let us show that not x = 0.
    Assume x = 0. Then 1 = x * a = 0 * a = 0. A contradiction. end.
a .= a * 1 (by One)
  .= a * (x * inv(x)) (by Inverse)
  .= (a * x) * inv(x) (by AssMult)
  .= (x * a) * inv(x) (by ComMult)
  .= 1 * inv(x)       (by 1)
  .= inv(x) * 1       (by ComMult)
  .= inv(x)           (by One).
qed.

Lemma NoZeroDivisors.
Assume x != 0 and y != 0. Then x * y != 0.
Proof.
(1) Assume the contrary.
 0 .= 0 * inv(x) (by ZeroMult)
   .= inv(x) * 0 (by ComMult)
   .= inv(x) * (x * y) (by 1)
   .= (inv(x) * x) * y (by AssMult)
   .= (x * inv(x)) * y (by ComMult)
   .= 1 * y (by Inverse)
   .= y * 1 (by ComMult)
   .= y (by One).
qed.

Lemma InvRule1.
Assume not x = 0. then inv(inv(x)) = x.
Proof.
inv(x) * x = x * inv(x) = 1. Therefore the thesis (by InvUnique). qed.

Lemma InvRule2.
Assume x != 0 and y !=0. Then x * y != 0 and inv(x * y) =  inv(x) * inv(y).
Proof.
(x * y) * (inv(x) * inv(y)) .= (x * inv(x)) * (y * inv(y)) (by AssMult, ComMult, BubbleMult)
                            .= 1 (by Inverse, One).
Hence the thesis (by InvUnique).
qed.


Lemma MinusRule4.
-x = (-1) * x.
Proof.
0 .= x * 0                (by ComMult, ZeroMult)
  .= x * (1 + (-1))       (by Neg)
  .= (x * 1) + (x * (-1)) (by Distrib)
  .= x + (x * (-1))       (by One)
  .= x + ((-1) * x)       (by ComMult).
Hence the thesis (by NegUnique).
qed.

Lemma InvSwap. Let a,b,c,d be real numbers. Assume c != d. (a - b) * inv(c - d) = (b - a) * inv( d - c).
Proof. d - c != 0 and - (d - c) != 0 and -1 != 0.
(a - b) * inv(c - d) .= (- (b - a)) * inv (- (d - c))            (by MinusRule3)
										 .= ((-1) * (b - a)) * inv((-1)*(d - c))     (by MinusRule4)
										 .= ((-1) * (b - a)) * (inv(-1) * inv(d - c))(by InvRule2)
										 .= ((b - a) * inv(d - c)) * ((-1) * inv(-1))(by AssMult, ComMult, BubbleMult)
										 .= (b - a) * inv(d - c)                     (by Inverse, One).
qed.
[group MultGr Mult AssMult ComMult One Inverse ZeroNotOne Distrib ZeroMult InvNotZero NoZeroDivisors InvRule1 InvRule2 MinusRule4]

[group MinusGr MinusRule1 MinusRule2 MinusRule3 MinusRule4]
[group FieldGr AddGr MultGr]

###Ordering

Signature positive.
Let x be a real number. pos(x) is an atom.

Let x is positive stand for pos(x).

Definition nonnegativeAdj.
Let x be a real number. x is nonnegative iff x = 0 \/ pos(x).

Lemma PosIsNonNeg.
Every positive real number is nonnegative.

Axiom TrichExi. pos(x) \/ x = 0 \/ pos(-x).
Axiom TrichUnique. not (pos(x) /\ pos(-x)) /\ not pos(0).
Axiom AddClosed. (pos(x) /\ pos(y)) => pos(x + y).
Axiom MultClosed. (pos(x) /\ pos(y)) => pos(x * y).

#Lemma. pos(x) => x != 0.

Definition less. x < y iff pos(y - x).
Let x > y stand for y < x.

Definition leq. x =< y iff (x < y \/ x = y).
Let x >= y stand for y =< x.



Lemma TotalityOfOrderExi.
(x < y \/ y < x \/ y = x).
Proof.
Case pos (x - y). Obvious.
Case pos (-(x - y)).
  We have - (x - y) = y - x (by MinusRule3).
  Therefore pos(y - x).
  end.
Case x - y = 0.
  Then y = y + 0 = y + (x - y) = x.
  end.
qed.

Lemma LargerMult.
Assume x is positive and a is a real number such that 1 < a. Then x < a * x.
Proof.
a - 1 is positive. Therefore (a - 1) * x is positive (by MultClosed).
(a - 1) * x .= (a * x) - x (by DistribDummy, MinusRule4).
qed.


Lemma SmallerMult.
Assume x is positive and a is a real number such that a < 1. then a * x < x.
Proof.
1 - a is positive. Therefore (1 - a) * x is positive (by MultClosed).
(1 - a) * x .= (x * 1) + (x * (-a)) (by DistribDummy, ComMult)
            .= x - (a * x) (by One, MinusRule4, ComMult, AssMult, BubbleMult ).
qed.


Lemma TotalityOfOrderUnique.
not((x < y /\ y < x) \/ (x < y /\ y = x) \/ (y < x /\ y = x)).
Proof.
Assume the contrary.
Case (x < y /\ y < x).
  We have y - x = - (x - y) (by MinusRule3).
  Therefore pos(x - y) and pos(-(x - y)).
  Contradiction (by TrichUnique).
  end.
Case (x < y /\ y = x).
  We have pos(y - x). We have y = x.
  Therefore y - x = 0.
  Contradiction (by TrichUnique).
  end.
Case (y < x /\ y = x).
  We have y - x = - (x - y) (by MinusRule3).
  Therefore pos(x - y) and pos(-(x - y)).
  Contradiction (by TrichUnique).
  end.
qed.

Lemma TransitivityOfOrder.
x < y /\ y < z => x < z.
Proof.
Assume x < y /\ y < z. Then pos(y - x) and pos (z - y).
We have
    (y - x) + (z - y) = (y - y) + (z - x) = 0 + (z - x) = z - x (by AssAdd, ComAdd, Neg, Zero).
Hence pos(z - x) (by AddClosed).
qed.


Lemma TranslationInvariance.
x < y => x + z < y + z.
Proof.
Assume x < y. Then pos(y - x).
    (y + z) - (x + z) .= (y + z) + ((-x) + (-z)) (by MinusRule1)
                      .= (y - x) + (z - z)       (by AssAdd, ComAdd, BubbleAdd)
                      .= y - x                   (by Neg, Zero).
qed.


Lemma AddInvariance.
Let a,b be real numbers. x < a /\ y < b => x + y < a + b.
Proof.
Assume x < a /\ y < b. We have x + y < a + y and y + a < b + a (by TranslationInvariance).
Therefore we have the thesis (by ComAdd, TransitivityOfOrder).
qed.

Lemma PosAdd.
Assume pos(y). Then x < x + y.
Proof.
x = x + 0 (by Zero).
We have 0 < y.
x + 0 < x + y (by TranslationInvariance, ComAdd).
qed.


Lemma LeqAddInvariance.
Let a,b be real numbers. x =< a /\ y =< b => x + y =< a + b.
Proof.
Assume x =< a /\ y =< b.
Case x = a /\ y = b. Obvious.
(1) Case x = a /\ y < b.
  x + y .= a + y (by 1) .= y + a (by ComAdd).
  b + a .= a + b (by ComAdd).
  y + a < b + a (by TranslationInvariance).
  Therefore x + y < a + b.
  end.
Case x < a /\ y = b.
  x + y = x + b < a + b (by TranslationInvariance).
  end.
Case x < a /\ y < b.
  x + y < a + b (by AddInvariance).
  end.
qed.

Lemma OrdMirror.
x < y => -y < -x.
Proof.
Assume x < y. We have
    -x - -y = -x + (-(-y)) = -x + y = y - x.
Hence pos(-x - (-y)).
qed.

Lemma OrdMirrorLeq.
x =< y => -y =< -x.
Proof.
Assume x =< y.
Case x = y. Obvious.
Case x < y. -y < -x (by OrdMirror). end.
qed.


Lemma MultInvariance.
(x < y /\ pos (z)) => z * x < z * y.
Proof.
Assume (x < y /\ pos(z)). We have pos(z * (y - x)) (by MultClosed).
We have z * (y - x) = (z * y) + (- (z * x)) (by Distrib, ComMult, MinusRule4, AssMult).
qed.






Lemma OnePos.
pos(1).
Proof.
Assume the contrary. Then pos(-1) (by TrichExi, ZeroNotOne).
We have (-1)*(-1) = -(-1) = 1. Hence pos(1) (by MultClosed).
A contradiction.
qed.


Lemma PosMono.
(pos(x) /\ x < y) => pos(y).
Proof.
Assume (pos(x) /\ x < y). We have y = y + (x - x) = (y - x) + x.
Therefore pos(y) (by AddClosed).
qed.

Lemma NonNegMono.
Assume x is nonnegative. Assume x =< y. Then y is nonnegative.
Proof.
Case y = 0. Obvious.
Case y != 0.
  Case x = y. Obvious.
  Case x < y. Obvious.
  end.
qed.

Lemma NonNegMultInvariance.
Assume x,y,a,b are nonnegative real numbers. Assume x < a /\ y < b. x * y < a * b.
Proof.
(1) Case x = 0.
  x * y .= 0 (by 1, ZeroMult).
  pos(a).
  Let us show that pos(b).
    Case y = 0. Obvious.
    Case pos(y). Then the thesis (by PosMono). end.
    end.
  Therefore pos(a * b) (by MultClosed).
  end.
Case y = 0.
  x * y = 0.
  pos(b).
  Let us show that pos(a).
    Case x = 0. Obvious.
    Case pos(x). Then the thesis (by PosMono). end.
    end.
  Therefore pos(a * b) (by MultClosed).
  end.
Case not x = 0 /\ not y = 0.
  We have (x = 0 \/ pos(x)) and (y = 0 \/ pos(y)) (by nonnegativeAdj).
  Then pos(x) /\ pos(y) (by TrichUnique).
  Then pos(a) /\ pos(b) (by PosMono).
  x * y < a * y < a * b (by ComMult, MultInvariance).
  Then x * y < a * b (by TransitivityOfOrder).
  end.
qed.


Lemma MinusAndMinus.
Assume pos(-x) and pos(-y). Then pos(x*y).
Proof.
(1) We have (-1)*(-1) = 1.
x*y .= (x * y) * ((-1) * (-1)) (by 1, One)
    .= ((-1) * x) * ((-1) * y) (by AssMult, ComMult, BubbleMult)
    .=(-x) * (-y)              (by MinusRule4).
Therefore the thesis (by MultClosed).
qed.


Lemma PosSquare.
Assume not x = 0. Then pos(x*x).
Proof.
Case pos(x). Obvious (by MultClosed).
Case pos(-x). Obvious (by MinusAndMinus).
qed.


Lemma InvMono.
If pos(x) then pos(inv(x)).
Proof.
Assume pos(x). Then x != 0 (by TrichUnique).
We have not inv(x) = 0. Therefore pos(inv(x) * inv(x)) (by PosSquare).
We have
    inv(x) = inv(x) * 1 = inv(x) * (x * inv(x)) = (inv(x) * inv(x)) * x.
Hence the thesis (by MultClosed).
qed.

Lemma InvIneq.
Assume x is positive.
inv(x) < 1 <=> 1 < x.
Proof.
x != 0 (by TrichUnique). 
inv(x) < 1 => 1 < x.
  proof.
  assume inv(x) < 1.
  Then 1 - inv (x) is positive.
  Therefore x * (1 - inv(x)) is positive.
  x * (1 - inv(x)) .= (x * 1) +(x * (-inv(x))) (by MinusRule4, Distrib)
                   .= x - 1 (by One, MinusRule4, ComMult, AssMult, BubbleMult, Inverse).
  end.
inv(x) is positive (by InvMono).
1 < x => inv(x) < 1.
  proof.
  assume 1 < x.
  Then x - 1 is positive.
  Therefore inv(x) * (x - 1) is positive.
  inv(x) * (x - 1) .= (inv(x) * x) + (inv (x) * (-1)) (by Distrib)
                   .= 1 - inv(x) (by Inverse, MinusRule4, ComMult, AssMult, BubbleMult, One).
  end.
qed.


Lemma MixedTransitivity.
x =< y /\ y < z => x < z.
Proof.
Assume x =< y /\ y < z.
Case x = y. Obvious.
Case x < y. Then x < z (by TransitivityOfOrder). end.
qed.

Lemma LeqTransitivity.
(x =< y) /\ (y =< z) => x =< z.
Proof.
Assume x =< y and y =< z.
Case x = y and y = z. Obvious.
Case x = y and y < z. Obvious.
Case x < y and y = z. Obvious.
Case x < y and y < z. Obvious (by TransitivityOfOrder).
qed.




###Absolute Value
Signature Abs.
abs(x) is a real number.

Axiom AbsValue.
(pos(x) => abs(x) = x) /\ (pos(-x) => abs(x) = -x) /\ abs(0) = 0.

Lemma DummyAbsValue.
abs(0) = 0.




Lemma NonNegAbsValue.
If x is nonnegative then abs(x) = x.

Lemma NonNegAbs.
abs(x) is nonnegative.


Lemma AbsIneq1.
x =< abs(x).
Proof.
Case not pos(-x). Obvious.
Case pos(-x).
    Then abs(x) = -x. We have abs(x) - x = (-x) - x. Therefore pos(abs(x) - x) (by AddClosed).
    end.
qed.

Lemma AbsPosNeg.
abs(x) = abs(-x).
Proof.
(1) Case x = 0.
    -x .= 0 (by NegOfZero, 1).
    end.
Case pos(x).
    Then abs(x) = x (by AbsValue).
    We have -(-x) = x (by MinusRule2).
    Therefore pos(-(-x)). Therefore abs(-x) = -(-x) = x.
    end.
Case pos(-x).
    Then abs(x) = -x and abs(-x) = -x (by AbsValue).
    end.
qed.

Lemma AbsIneqCharac1.
(abs(x) =< y) <=> -y =< x =< y.
Proof.
Let us show that (-y =< x =< y => abs(x) =< y).
  Assume -y =< x =< y.
  Let us show that (abs(x) =< y).
      Case not pos(-x). Obvious.
      Case pos(-x).
          We have -y =< x. Therefore -x =< y (by OrdMirror, MinusRule2).
          We have abs(x) = -x.
          end.
      end.
  end.
Let us show that (abs(x) =< y => -y =< x =< y).
  Assume abs(x) =< y.
  Let us show that x =< y.
    We have x =< abs(x) (by AbsIneq1). Therefore x =< y (by TransitivityOfOrder).
  end.
  Let us show that -y =< x.
    We have abs(x) = abs(-x) (by AbsPosNeg).
    Therefore abs(-x) =< y.
    We have -x =< abs(-x) (by AbsIneq1). Therefore -x =< y (by TransitivityOfOrder).
    Hence -y =< x (by OrdMirror, MinusRule2).
  end.
end.
qed.

Lemma AbsIneqCharac2.
(abs(x) =< y) <=> (x =< y /\ -x =< y).
Proof.
Let us show that (abs(x) =< y => x =< y /\ -x =< y).
  Assume abs(x) =< y. Let us show that (x =< y /\ -x =< y).
      We have x =< abs(x) (by AbsIneq1).
      Therefore x =< y (by TransitivityOfOrder).
      We have -x =< abs(x) (by AbsIneq1, AbsPosNeg).
      Therefore -x =< y (by TransitivityOfOrder).
      end.
  end.
Let us show that (x =< y /\ -x =< y => abs(x) =< y).
  Assume (x =< y /\ -x =< y). Let us show that (abs(x) =< y).
      Case not pos(-x). Obvious.
      Case pos(-x). Then abs(x) = -x. end.
      end.
  end.
qed.

Lemma AbsStrongIneqCharac1.
(abs(x) < y) <=> (-y < x < y).
Proof.
Let us show that (-y < x < y => abs(x) < y).
  Assume -y < x < y.
  Let us show that (abs(x) < y).
      Case not pos(-x). Obvious.
      Case pos(-x).
          We have -y < x. Therefore -x < y (by OrdMirror, MinusRule2).
          We have abs(x) = -x.
          end.
      end.
  end.
Let us show that (abs(x) < y => -y < x < y).
  Assume abs(x) < y.
  Let us show that x < y.
    We have x =< abs(x) (by AbsIneq1).
    Therefore x < y (by MixedTransitivity).
    end.
  end.
qed.

Lemma AbsStrongIneqCharac2.
(abs(x) < y) <=> (x < y /\ -x < y).
Proof.
Let us show that abs(x) < y => x < y /\ -x < y.
  Assume abs(x) < y.
  Let us show that (x < y /\ -x < y).
    We have x =< abs(x) (by AbsIneq1).
    Therefore x < y (by MixedTransitivity).
    We have -x =< abs(x) (by AbsIneq1, AbsPosNeg).
    Therefore -x < y (by MixedTransitivity).
    end.
  end.
Let us show that x < y /\ -x < y => abs(x) < y.
  Assume (x < y /\ -x < y).
  Let us show that (abs(x) < y).
    Case not pos(-x). Obvious.
    Case pos(-x). Then abs(x) = -x. end.
    end.
  end.
qed.


Lemma AbsTriangleIneq.
abs(x + y) =< abs(x) + abs(y).
Proof.
We have x =< abs(x) and y =< abs(y) (by AbsIneq1).
Therefore x + y =< abs(x) + abs(y) (by LeqAddInvariance).
We have -x =< abs(x) and -y =< abs(y) (by AbsIneq1, AbsPosNeg).
Therefore
    - (x + y) = (-x) - y =< abs(x) + abs(y) (by LeqAddInvariance, MinusRule1).
Hence the thesis (by AbsIneqCharac2).
qed.



Lemma AbsPos.
If not x = 0 then pos(abs(x)).
Proof.
Case pos(x). Obvious.
Case pos(-x). Then abs(x) = -x. Therefore pos(abs(x)). end.
qed.


Lemma AbsMult.
abs(x * y) = abs(x) * abs(y).
Proof.
(1) Case x = 0.
  abs(x * y) .= abs(0 * y) (by 1)
             .= abs(0)     (by ZeroMult)
             .= 0 (by DummyAbsValue)
             .= 0 * abs(y) (by ZeroMult)
             .= abs(0) * abs(y) (by DummyAbsValue)
             .= abs(x) * abs(y) (by 1).
  end.
(2) Case y = 0.
  abs(x * y) .= abs(x * 0) (by 2)
             .= abs(0 * x) (by ComMult)
             .= abs(0)     (by ZeroMult)
             .= 0 (by DummyAbsValue)
             .= 0 * abs(x) (by ZeroMult)
             .= abs(x) * 0 (by ComMult)
             .= abs(x) * abs(0) (by DummyAbsValue)
             .= abs(x) * abs(y) (by 2).
  end.
Case pos(x) /\ pos(y).
  We have pos(x * y) (by MultClosed).
  abs(x * y) = x * y = abs(x) * abs(y) (by AbsValue).
  end.
Case pos(-x) /\  pos(-y).
  (-x) * (-y) .= ((-1) * x) * ((-1) * y) (by MinusRule4)
              .= (-1) * (x * (y * (-1))) (by ComMult, AssMult, BubbleMult)
              .= (-1) * ((-1) * (x * y)) (by ComMult, AssMult, BubbleMult)
              .= ((-1) * (-1)) * (x * y) (by AssMult)
              .= (-(-1)) * (x * y)       (by MinusRule4)
              .= 1 * (x * y)             (by MinusRule2)
              .= x * y                   (by OneDummy).
  We have pos ((-x) * (-y)) (by MultClosed).
  abs(x * y) = abs((-x) * (-y)) = (-x) * (-y) = abs(-x) * abs(-y) = abs(x) * abs(y) (by AbsValue, AbsPosNeg).
  end.
Case pos(x) /\ pos(-y).
  pos(x * (-y)) (by MultClosed).
   x * (-y) .= x * ((-1) * y) (by MinusRule4)
            .= (-1) * (x * y) (by AssMult, ComMult, BubbleMult)
            .= -(x * y)       (by MinusRule4).
  abs(x * y) = abs(-(x * y)) = -(x * y) = x * (-y) = abs(x) * abs(-y) = abs(x) * abs(y) (by AbsValue, AbsPosNeg).
  end.
Case pos(-x) /\ pos(y).
  pos((-x) * y) (by MultClosed).
  (-x) * y .= ((-1) * x) * y (by MinusRule4)
           .= (-1) * (x * y) (by AssMult)
           .= -(x * y)       (by MinusRule4).
  abs(x * y) = abs(-(x * y)) = -(x * y) = (-x) * y = abs(-x) * abs(y) = abs(x) * abs(y) (by AbsValue, AbsPosNeg).
  end.
qed.

[group AbsGr Abs AbsValue NonNegAbsValue NonNegAbs AbsIneq1 AbsMult AbsTriangleIneq AbsPosNeg] 
###Distance

Signature Dist.
dist(x,y) is a nonnegative real number.

Axiom DistDefinition. dist(x,y) = abs(x - y).

Lemma IdOfInd.
dist(x,y) = 0 <=> x = y.
Proof.
Let us show that (x = y => dist(x,y) = 0).
    Assume x = y. Then dist(x,y) = 0.
    end.
Let us show that dist(x,y) = 0 => x = y.
    Assume dist(x,y) = 0.
    Then not pos(abs(x - y)). Hence x - y = 0 (by AbsPos).
    Hence x = x + 0 = x + (y - y) = (x - y) + y  = 0 + y = y.
    end.
qed.

Lemma DistSymm. dist(x,y) = dist(y,x).
Proof.
dist(x,y) .= abs(x - y)    (by DistDefinition)
          .= abs(-(x - y)) (by AbsPosNeg)
          .= abs(y - x)    (by MinusRule3)
          .= dist(y,x)     (by DistDefinition).
qed.

Lemma DistTriangleIneq. dist(x,z) =< dist(x,y) + dist(y,z).
Proof.
    abs(x - z) .= abs((x + 0) - z)        (by Zero)
               .= abs((x + (y - y)) - z)  (by Neg)
               .= abs((x - y) + (y - z))  (by AssAdd, ComAdd, BubbleAdd).
We have abs((x - y) + (y - z)) =< abs(x - y) + abs(y - z) (by AbsTriangleIneq).
Therefore the thesis (by DistDefinition).
qed.



[group DistGr Dist DistDefinition IdOfInd DistSymm DistTriangleIneq]

[group AbsDist AbsGr DistGr]
###Some Operations

Signature Maximum.
max(x,y) is a real number such that (x =< y => max(x,y) = y) /\ (y =< x => max(x,y) = x).



Lemma MaxIneq.
x =< max(x,y).
Proof.
Case x =< y. Then max(x,y) = y (by Maximum). Hence x =< max(x,y). end.
Case y =< x. Then max(x,y) = x (by Maximum). Hence x =< max(x,y). end.
qed.

Lemma MaxSym.
max(x,y) = max(y,x).
Proof.
Case x =< y. max(x,y) .= y (by Maximum) .= max(y,x) (by Maximum). end.
Case y =< x. max(x,y) .= x (by Maximum) .= max(y,x) (by Maximum). end.
qed.

[group MaxGr Maximum MaxIneq MaxSym]

[group RealGr FieldGr AbsDist MaxGr]
