# This file is a ForTheL version of 
# https://github.com/leanprover/lean/blob/master/library/init/algebra/group.lean

[synonym type/-s]
Signature. A type is a set.
Let alpha stand for a type.
Let a : t stand for a is an element of t.

Signature. A type with multiplication is a type.
Signature. Let alpha be a type with multiplication and a,b : alpha. 
a *^{alpha} b is an element of alpha.
  

[synonym semigroup/-s]
Definition. A semigroup is a type with multiplication alpha
such that for all a,b,c : alpha
(a *^{alpha} b) *^{alpha} c = a *^{alpha} (b *^{alpha} c). 

Definition. A commutative semigroup is a semigroup alpha
such that for all a,b : alpha
a *^{alpha} b = b *^{alpha} a.

Definition. A semigroup with left cancellation is a semigroup
alpha such that for all a,b,c : alpha
a *^{alpha} b = a *^{alpha} c => b = c.

Definition. A semigroup with right cancellation is a semigroup
alpha such that for all a,b,c : alpha
a *^{alpha} b = c *^{alpha} b => a = c.

Signature. A type with one is a type.
Signature. Assume alpha is a type with one. 1^{alpha} is an
element of alpha.

Definition. A monoid is a semigroup alpha such that alpha is a type
with one and
forall a : alpha 1^{alpha} *^{alpha} a = a and
forall a : alpha a *^{alpha} 1^{alpha} = a.

Definition. A commutative monoid is a monoid that
is a commutative semigroup.

Signature. A type with inverses is a type.
Signature. Assume alpha is a type with inverses and a : alpha.
a^{-1,alpha} is an element of alpha.

Definition. A group is a monoid alpha such that alpha is a type 
with inverses and 
for all a : alpha a^{-1,alpha} *^{alpha} a = 1^{alpha}.

Definition. A commutative group is a group that is a commutative
monoid.

Lemma mul_left_comm. Let alpha be a commutative semigroup.
Then for all a,b,c : alpha
a *^{alpha} (b *^{alpha} c) = b *^{alpha} (a *^{alpha} c).

Lemma mul_right_comm. Let alpha be a commutative semigroup.
Then for all a,b,c : alpha
a *^{alpha} (b *^{alpha} c) = a *^{alpha} (c *^{alpha} b).

Lemma mul_left_cancel_iff. Let alpha be a 
semigroup with left cancellation. Then for all a,b,c : alpha
a *^{alpha} b = a *^{alpha} c <=> b = c.

Lemma mul_right_cancel_iff. Let alpha be a 
semigroup with right cancellation. Then for all a,b,c : alpha
b *^{alpha} a = c *^{alpha} a <=> b = c.

Let alpha denote a group.

Lemma inv_mul_cancel_left. For all a,b : alpha
a^{-1,alpha} *^{alpha} (a *^{alpha} b) = b.

Lemma inv_mul_cancel_right. For all a,b : alpha
a *^{alpha} (b^{-1,alpha} *^{alpha} b) = a.

Lemma inv_eq_of_mul_eq_one. Let a, b : alpha and
a *^{alpha} b = 1^{alpha}. Then a^{-1,alpha} = b.

Lemma one_inv. (1^{alpha})^{-1,alpha} = 1^{alpha}.

Lemma inv_inv. Let a : alpha. Then
(a^{-1,alpha})^{-1,alpha} = a.

Lemma mul_right_inv. Let a : alpha. Then 
a *^{alpha} a^{-1,alpha} = 1^{alpha}.

Lemma inv_inj. Let a,b : alpha and a^{-1,alpha} = b^{-1,alpha}.
Then a = b.

Lemma group_mul_left_cancel. Let a,b,c : alpha and
a *^{alpha} b = a *^{alpha} c. Then b = c.

Lemma group_mul_right_cancel. Let a,b,c : alpha and
a *^{alpha} b = c *^{alpha} b. Then a = c.
Proof. a = (a *^{alpha} b) *^{alpha} b^{-1,alpha}
= (c *^{alpha} b) *^{alpha} b^{-1,alpha} = c.
qed.

Lemma mul_inv_cancel_left. Let a,b : alpha. Then
a *^{alpha} (a^{-1,alpha} *^{alpha} b) = b.

Lemma mul_inv_cancel_right. Let a,b : alpha. Then
(a *^{alpha} b) *^{alpha} b^{-1,alpha} = a.


Lemma mul_inv_rev. Let a,b : alpha. Then
(a *^{alpha} b)^{-1,alpha} = b^{-1,alpha} *^{alpha} a^{-1,alpha}.
Proof. 
(a *^{alpha} b) *^{alpha} (b^{-1,alpha} *^{alpha} a^{-1,alpha})
= 1^{alpha}.
qed.

Lemma eq_inv_of_eq_inv. Let a,b : alpha and a = b^{-1,alpha}.
Then b = a^{-1,alpha}.

Lemma eq_inv_of_mul_eq_one. Let a,b : alpha and
a *^{alpha} b = 1^{alpha}. Then a = b^{-1,alpha}.

Lemma eq_mul_inv_of_mul_eq. Let a,b,c : alpha and
a *^{alpha} c = b. Then a = b *^{alpha} c^{-1,alpha}.

Lemma eq_inv_mul_of_mul_eq. Let a,b,c : alpha and
b *^{alpha} a = c. Then a = b^{-1,alpha} *^{alpha} c.

Lemma inv_mul_eq_of_eq_mul. Let a,b,c : alpha and
b = a *^{alpha} c. Then a^{-1,alpha} *^{alpha} b = c.

Lemma mul_inv_eq_of_eq_mul. Let a,b,c : alpha and
a = c *^{alpha} b. Then a *^{alpha} b^{-1,alpha} = c.

Lemma eq_mul_of_mul_inv_eq. Let a,b,c : alpha and
a *^{alpha} c^{-1,alpha} = b. Then a = b *^{alpha} c.

Lemma eq_mul_of_inv_mul_eq. Let a,b,c : alpha and
b^{-1,alpha} *^{alpha} a = c . Then a = b *^{alpha} c.

Lemma mul_eq_of_eq_inv_mul. Let a,b,c : alpha and
b = a^{-1,alpha} *^{alpha} c. Then a *^{alpha} b = c.

Lemma mul_eq_of_eq_mul_inv. let a,b,c : alpha and
a = c *^{alpha} b^{-1,alpha}. Then a *^{alpha} b = c.

Lemma mul_inv. Let alpha be a commutative group. 
Let a,b : alpha. Then
(a *^{alpha} b)^{-1,alpha} = a^{-1,alpha} *^{alpha} b^{-1,alpha}.



