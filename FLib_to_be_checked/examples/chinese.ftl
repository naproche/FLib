[element/-s]

Signature ElmSort. An element is a notion.

Let a,b,c,x,y,z,u,v,w denote elements.

Signature SortsC.  0 is an element.
Signature SortsC.  1 is an element.
Signature SortsU.  -x is an element.
Signature SortsB.  x + y is an element.
Signature SortsB.  x * y is an element.

Let x is nonzero stand for x != 0.
Let x - y stand for x + -y.

Axiom AddComm.  x + y = y + x.
Axiom AddAsso.  (x + y) + z = x + (y + z).
Axiom AddZero.  x + 0 = x = 0 + x.
Axiom AddInvr.  x + -x = 0 = -x + x.

Axiom MulComm.  x * y = y * x.
Axiom MulAsso.  (x * y) * z = x * (y * z).
Axiom MulUnit.  x * 1 = x = 1 * x.

Axiom AMDistr.  x * (y + z) = (x * y) + (x * z) and
                (y + z) * x = (y * x) + (z * x).

Lemma MulMnOne. -1 * x = -x = x * -1.

Lemma MulZero.  x * 0 = 0 = 0 * x.

Axiom Cancel.  If x * y = 0 then x = 0 or y = 0.

Axiom UnNeZr.  1 != 0.

[set/-s] [belong/-s]

Signature SetSort.  A set is a notion.

Let X,Y,Z,U,V,W denote sets.

Signature EOfElem.  An element of W is an element.

Let x << W denote x is an element of W.
Let x belongs to W denote x is an element of W.

Axiom SetEq.    If every element of X belongs to Y
        and every element of Y belongs to X then X = Y.

Definition DefSSum. X + Y = { x + y | x << X and y << Y }.

Definition DefSInt. X ** Y = { h | h << X and h << Y }.

[ideal/-s]

Definition DefIdeal.
    An ideal is a set X such that for every x << X
        forall y << X (x + y) << X and
        forall z (z * x) << X.

Let I,J denote ideals.

Lemma IdeSum.   I + J is an ideal.
Proof.
    Let x, y belong to I + J and z be an element.
    Take k << I and l << J such that x = k + l.
    Take m << I and n << J such that y = m + n.
    k + m belongs to I and l + n belongs to J.
    z * k belongs to I and z * l belongs to J.
    We have x + y = (k + m) + (l + n) (by AddComm, AddAsso).
    We have z * x = (z * k) + (z * l) (by AMDistr).
    Hence (x + y), (z * x) belong to I + J.
qed.

Lemma IdeInt.   I ** J is an ideal.

Definition DefMod.  x = y (mod I)  iff  x - y << I.

Theorem ChineseRemainder.
    Suppose that every element belongs to I + J.
    Let x, y be elements.
    There exists an element w such that
        w = x (mod I) and w = y (mod J).
Proof.
    Take a << I and b << J such that a + b = 1.
    Take w = (y * a) + (x * b).

    w - x belongs to I.
    proof.
        w - x = (y * a) + ((x * b) - x) (by AddAsso).
        x * (b - 1) belongs to I.
    end.

    w - y belongs to J.
    proof.
        w - y = (x * b) + ((y * a) - y) (by AddAsso,AddComm).
        y * (a - 1) belongs to J.
    end.
qed.


[number/-s]

Signature NatSort.  A natural number is a notion.

Signature EucSort.  Let x be a nonzero element.
    |x| is a natural number.

Signature NatLess.  Let i,j be natural numbers.
    i -<- j is a relation.

Axiom Division.
    Let x, y be elements and y != 0.
    There exist elements q,r such that
        x = (q * y) + r and (r != 0 => |r| -<- |y|).


[divisor/-s] [divide/-s]

Definition DefDiv.
    x divides y  iff  for some z (x * z = y).

Let x | y stand for x divides y.
Let x is divided by y stand for y | x.

Definition DefDvs.
    A divisor of x is an element that divides x.

Definition DefGCD.
    A gcd of x and y is a common divisor c of x and y
        such that any common divisor of x and y divides c.

Definition DefRel.
    x, y are relatively prime iff 1 is a gcd of x and y.


Definition DefPrIdeal.
    <c> is { c * x | x is an element }.

Lemma PrIdeal.  <c> is an ideal.
Proof.
    Let x,y belong to <c> and z be an element.
    Take an element u such that c * u = x.
    Take an element v such that c * v = y.
    We have x + y = c * (u + v) (by AMDistr).
    We have z * x = c * (u * z) (by MulComm,MulAsso).
    Hence (x + y), (z * x) belong to <c>.
qed.


Theorem GCDin.  Let a, b be elements.
    Assume that a is nonzero or b is nonzero.
    Let c be a gcd of a and b. Then c belongs to <a> + <b>.
Proof.
    Take an ideal I equal to <a> + <b>.
    We have 0,a << <a> and 0,b << <b>.
    Hence there exists a nonzero element of <a> + <b>.

    Take a nonzero u << I
        such that for no nonzero v << I (|v| -<- |u|).
    Indeed we can show by induction on |w| that
        for every nonzero w << I there exists nonzero u << I
            such that for no nonzero v << I (|v| -<- |u|).
        Obvious.

    u is a common divisor of a and b.
    proof.
        Assume the contrary.
        For some elements x,y  u = (a * x) + (b * y).
        proof.
            Take k << <a> and l << <b> such that u = k + l.
            Hence the thesis.
        end.

        Case u does not divide a.
            Take elements q,r such that a = (q * u) + r
                and (r = 0 \/ |r| -<- |u|).
            r is nonzero.
            - (q * u) belongs to I.
            a belongs to I.
            r = - (q * u) + a.
            Hence r belongs to I.
        end.

        Case u does not divide b.
            Take elements q,r such that b = (q * u) + r
                and (r = 0 \/ |r| -<- |u|).
            r is nonzero.
            - (q * u) belongs to I.
            b belongs to I.
            r = - (q * u) + b.
            Hence r belongs to I.
        end.
    end.

    Hence u divides c.
    Hence the thesis.
qed.

