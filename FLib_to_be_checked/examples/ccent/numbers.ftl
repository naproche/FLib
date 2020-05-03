# We need a number ontology (ordered field, etc.) out of which
# we would select e.g. integers as natural numbers.

# REAL NUMBERS

[prove off]

[number/-s][integer/-s]

Signature Numbers.  A number is a notion.

Let r,u,v,w,x,y,z denote numbers.

Signature Null.  0 is a number.

Let u is nonzero stand for u != 0.

Signature One.  1 is a nonzero number.

Signature Addition.  u + v is a number.
Signature Negative. -u is a number.
Signature Difference. u - v is a number.
Signature Multiplication.  u * v is a number.

Axiom AddComm.   u + v = v + u.
Axiom AddAsso.  (u + v) + w = u + (v + w).
Axiom _AddZero.  u + 0 = u = 0 + u.

Axiom. u - v = -(v-u). 
Axiom. u - u = 0.
Axiom. u - w = (u-v)+(v-w).
Axiom. u-0=u.

Axiom MulComm.   u * v = v * u.
Axiom MulAsso.  (u * v) * w = u * (v * w).
Axiom _MulUnit.  u * 1 = u = 1 * u.
Axiom _MulZero.  u * 0 = 0 = 0 * u.

Axiom AMDistr.  u * (v + w) = (u * v) + (u * w) and
                (u + v) * w = (u * w) + (v * w).

Axiom. -(u*v) = (-u)*v = u*(-v).
Axiom. (u+v)-(w+x)=(u-w)+(v-x).
Axiom. (u-v)-(w-x)=(u-w)-(v-x).
Axiom. (u-v)+v=u.

Axiom DiffDistr. u * (v - w) = (u * v) - (u * w) and
                (u - v) * w = (u * w) - (v * w).

Axiom AddCanc.  If (u + v = u + w \/ v + u = w + u) then v = w.

Axiom MulCanc.  Assume that u is nonzero.
                If (u * v = u * w \/ v * u = w * u) then v = w.

Lemma ZeroMul.  If u * v = 0 then u = 0 \/ v = 0.

Signature SOrder. u < v is an atom.
Signature Order. u <= v is an atom.
Let v > u stand for u < v.

Axiom. u<v<w => u<w.
Axiom. u < v iff (u<=v and u != v).
Axiom. u <= v iff (u < v or u = v).
Axiom. u <= v => u+w <= v+w.
Axiom. (u <= v and 0 <= w) => u*w <= v*w.
Axiom. u != 0 => u*u > 0.

# INTEGERS

Signature Integer. u is whole is an atom.

Let an integer denote a whole number.
Let a,b,c,d,e denote integers.

Axiom Closure0. 0 is an integer.
Axiom. 1 is an integer.
Axiom Closure1. a+b is an integer.
Axiom Closure2. -a is an integer.
Axiom Closure3. a-b is an integer.
Axiom Closure4. a*b is an integer.

Axiom. 0 < 1.
Axiom. Let a < b. Then a+1 <= b.
Axiom. a <= -1 or 0 <= a.

# NATURAL NUMBERS

Signature Natural. u is natural is an atom.
Axiom. Every natural number is an integer.

Let k,l,m,n denote natural numbers.

Axiom ClosureA0. 1 is a natural number.
Axiom ClosureA1. k+l is a natural number.
Axiom ClosureA4. k*l is a natural number.

Axiom. If k != 1 then there is l such that k=l+1.
Axiom. 1 <= k.

Signature. k -<- l is an atom.
Axiom. l -<- l+1. 


# 2. DIVISIBILITY

[divide/-s] [divisor/-s]

Definition 1_divisibility. Let b,c be integers. 
b divides c iff (there is an integer d such that c = b * d).

Let a | b denote a divides b.
Let a -| b denote a does not divide b.

Proposition 2_transitivity_of_divisibility. Let a,b and c be integers such that (a | b and b | c). Then a | c.
Proof. Take d such that b=a*d. 
Take e such that c=b*e.
Then c=b*e=(a*d)*e=a*(d*e).
Hence a | c. 
qed.

Proposition 2_1. Let n be an integer. Then n divides n and 1 divides n.

# Definition 2_2. quotients? Should also be there as basic operation
# with axioms.

Proposition 3_1. Let a,b,c be integers such that (a | b and a | c). Then a divides b+c.

Proposition 3_2. Let a,b,c be integers such that (a | b and a | c). Then a divides b-c.

# Certified without proof.
# Proof. Take d such that b=a*d. Take e such that c=a*e.
# Then b-c=(a*d)-(a*e)=a*(d-e).
# qed.

Proposition 3_3. Let a,b be integers such that a | b. 
Then a divides (b*e).

Proof. Take c such that b=a*c. 
Then b*e=a*(c*e).
qed.

Definition 5. Let a and b be integers. Let c be a natural number such that c > 1. a == b mod c iff (c divides a - b).

Let a is congruent b modulo c stand for a == b mod c.

Proposition 6_a. Let a,b,c be integers. Let d be a natural number such that d > 1. Then a == a mod d.
Proof. a - a = 0 = d *0.
qed.

Proposition 6_b. Let a,b,c be integers. Let d be a natural number such that d > 1. Then if a == b mod d then b == a mod d.
Proof. Suppose that a == b mod d. 
Take an integer e such that a - b = d * e.
b-a=-(a-b)=-(d*e)=d*(-e).
qed.

Proposition 6_c. Let a,b,c be integers. Let d be a natural number such that d > 1. Then if a == b mod d and b == c mod d then a == c mod d.
Proof. Suppose that a == b mod d and b == c mod d. 
Take an integer e such that a - b = d * e. 
Take an integer f such that b - c = d * f.
a-c=(a-b)+(b-c)=(d*e)+(d*f)=d*(e+f).
qed.

Proposition 6_1_a. Assume that a,b,c and d are integers. Assume that n is a natural number such that n > 1. Assume that a == c mod n and b == d mod n. Then a + b == c + d mod n.
Proof. Take an integer e such that a - c = n * e. 
Take an integer f such that b - d = n * f.
(a+b)-(c+d)=(a-c)+(b-d).
qed.

Proposition 6_1_b. Assume that a,b,c and d are integers. Assume that n is a natural number such that n > 1. Assume that a == c mod n and b == d mod n. Then a * b == c * d mod n.
Proof. n divides a*(b-d). 
n divides (a*b)-(a*d).
n divides (a-c)*d.
n divides (a*d)-(c*d).
(a*b)-(c*d)=((a*b)-(a*d))+((a*d)-(c*d)).
n divides (a*b)-(c*d) (by 3_1). 
qed.

Proposition 6_1_c. Assume that a,b,c and d are integers. Assume that n is a natural number such that n > 1. Assume that a == c mod n and b == d mod n. Then a - b == c - d mod n.
Proof. n divides a-c.
n divides b-d.
(a-b)-(c-d)=(a-c)-(b-d).

Take an integer e such that a - c = n * e. 
Take an integer f such that b - d = n * f.
(a+b)-(c+d)=(a-c)+(b-d).
qed.

Proposition 6_3. For all natural numbers a such that a>1 we have 
a == 0 mod a.

Proposition 6_2. 
Let b be a natural number such that b > 1. 
Then for every natural number a there is a natural number c such that 
(c <= b and a == c mod b).
Proof by induction on a. 
Let a be a natural number.
Case a=1. Obvious.
Case a!=1. Take a natural number d such that a=d+1.
d -<- a.
Take a natural number e such that 
e<=b and d == e mod b (by IH).
Case e < b. Then e+1 <= b. 
d+1 == e+1 mod b (by 6_a, 6_1_a). end.
Case e=b. Then 1 <= b. d == 0 mod b. d+1 == 0+1 mod b (by 6_a, 6_1_a). end.
end.  
qed.

# Problem: Wir muessen die Voraussetzungen anders formulieren.
# Hier sind wir Carl zu treu gefolgt. Hat das Problem auch mit
# den "Praesuppositionen" von mod zu tun?

Lemma 6_4. Let a,b be natural numbers such that b > 1.
Then there are integers n,r such that (
  0 <= n, 
  1 <= r <= b,
  a = (n*b)+r).
Proof.
Take a natural number r such that r <= b and a == r mod b.
1 <= r. 
Take an integer n such that a-r = n*b.
a=(a-r)+r=(n*b)+r.
Assume that not 0 <= n.
Then n <= -1. 
n*b <= (-1)*b = -b. 
a = (n*b)+r <= (-b)+r <= 0.
Contradiction.
qed.
[/prove]


# 3. PRIMES

Proposition 9__1. Let a and b be integers such that a > b. Let c be a natural number. Then a*c > b*c.
Proof. 1 <= c. 0<c. qed.

Proposition 9__2. Let a and b be integers such that b <= a. Let c be a natural number. Then b*c <= a*c.

Corollary 9_1. Let a,b,n be natural numbers such that (n=a*b and b>1). Then a<n.

Lemma 10. Let n,a,b be natural numbers such that (a>1, b>1 and a*b=n). Then a<n and b<n.

Lemma 10_1. Let a and b be natural numbers such that a divides b.
Then a <= b.

Proposition 11. If a is an integer such that a != 0 then a*a > 0.


