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

Axiom DiffDistr. u * (v - w) = (u * v) - (u * w) and
                (u - v) * w = (u * w) - (v * w).

Axiom AddCanc.  If (u + v = u + w \/ v + u = w + u) then v = w.

Axiom MulCanc.  Assume that u is nonzero.
                If (u * v = u * w \/ v * u = w * u) then v = w.

Lemma ZeroMul.  If u * v = 0 then u = 0 \/ v = 0.

Signature SOrder. u < v is an atom.
Signature Order. u <= v is an atom.
Let v > u stand for u < v.

Axiom. u < v iff u<=v and u != v.

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

Axiom. Let a < b. Then a+1 <= b.

# NATURAL NUMBERS

#Signature Natural. u is natural is an atom.
#Axiom. Every natural number is an integer.

#Let k,l,m,n denote natural numbers.

#Axiom ClosureA0. 1 is a natural number.
#Axiom ClosureA1. k+l is a natural number.
#Axiom ClosureA4. a*b is a natural number.

# Axiom. If k != 1 then there is l such that k=l+1.

#Signature. k -<- l is an atom.
#Axiom. l -<- l+1. 

Lemma. 0=1.



