[synonym member/-s]
[synonym map/-s]
[synonym space/-s]
[synonym homomorphism/-s]
[synonym algebra/-s]
[synonym algebrahom/-s]
[synonym module/-s]
[synonym modulehom/-s]
[synonym category/categories]
[synonym functor/-s]
[synonym vertex/vertices]
[synonym arrow/-s]

Signature. Let A,a be objects. A\{a} is an object.
Signature. Let A be an object. A member of A is a notion.   # "element" is already used for sets
Let x << A stand for x is a member of A.

Signature. Let f,x be objects. f(x) is an object.
Signature. Let f be an object. Dmn(f) is an object.   # Dom(f) would lead to ambiguity errors.
Signature. Let A be an object. id{A} is an object.
Signature. Let f,g be objects. f*g is an object.
Signature. Let f be an object. f^(-1) is an object.

Signature. Let S be an object.   |S| is an object.
Signature. Let S be an object.   0{S} is an object.
Signature. Let S be an object.   1{S} is an object.
Signature. Let a,b,S be objects. a +{S} b is an object.
Signature. Let a,b,S be objects. a *{S} b is an object.
Signature. Let a,S be objects.   ~{S} a is an object.
Signature. Let a,S be objects.   inv{S} a is an object.
Signature. Let a,b,S be objects. a @{S} b is an object.
Signature. Let a,b,S be objects. a @@{S} b is an object.
Let a < S stand for a << |S|.
Let a < S* stand for a << |S|\{0{S}}.
Let a -{S} b stand for a +{S} (~{S} b).
Let a /{S} b stand for a *{S} (inv{S} b).

Signature. Let K,V,W be objects. Hom(K,V,W) is an object.
Signature. Let f,x,y be objects. f(x,y) is an object.
Signature. Let K,V be objects.   dual(K,V) is an object.
Signature. Let K,V be objects.   V2ddV(K,V) is an object.
Signature. Let R be an object.   Un(R) is an object.
Signature. Let K,V be objects.   Endo(K,V) is an object.   #"End" can cause problems in proofs.
Signature. Let K,V be objects.   Aut(K,V) is an object.
Signature. Let f be an object.   Ker(f) is an object.

Signature. Let p,K,A,V be objects. rep2mod(p,K,A,V) is an object.
Signature. Let K,A,V be objects.   mod2rep(K,A,V) is an object.
Signature. Let K,A,M,N be objects. Hom(K,A,M,N) is an object.
Signature. Let X,C be objects.     1{X,C} is an object.
Signature. Let K,A be objects.     Mod(K,A) is an object.
Signature. Let K,A,x be objects.   Hom(K,A,x,-) is an object.
Signature. Let K,A,x be objects.   Hom(K,A,-,x) is an object.
Signature. id is an object.

Signature. 0 is an object.
Signature. 1 is an object.
Signature. Let Q be an object. Q(st) is an object.
Signature. Let Q be an object. Q(tl) is an object.


Axiom. Let A be a set. Let x be an object. x << A iff x is an element of A.

Definition Subset. Let B be an object. A subset of B is a set A such that
 for all x << A : x << B.

Axiom SetExt. Let A,B be sets. Assume A is subset of B. Assume B is subset of A. Then A = B.

Axiom. Let A be a set. Let a << A. A\{a} is a set.
Axiom. Let A be a set. Let a << A. A\{a} = {x | x << A and x != a}.