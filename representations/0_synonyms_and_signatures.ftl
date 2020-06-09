[synonym member/-s]
[synonym map/-s]
[synonym space/-s]
[synonym algebra/-s]
[synonym module/-s]
[synonym category/categories]
[synonym functor/-s]
[synonym vertex/vertices]
[synonym arrow/-s]

Signature. Let A,a be objects. A\{a} is an object.
Signature. Let A be an object. A member of A is a notion.   # "element" is already used for sets
Let x << A stand for x is a member of A.

Signature. Let f,x be objects. f(x) is an object.
Signature. Dmn is an object.   # Dom(f) would lead to ambiguity errors.
Signature. Let A be an object. id{A} is an object.
Signature. Let f,A be objects. f|A is an object.
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

# Constructions with one or two parameters shall be introduced by their prefix being an object.
# Constructions with more than two parameters are introduced individually.
Signature. Let K,V,W be objects. Hom(K,V,W) is an object.
Signature. Let f,x,y be objects. f(x,y) is an object.
Signature. dual is an object.
Signature. V2ddV is an object.
Signature. Un is an object.
Signature. End is an object.
Signature. Aut is an object.
Signature. Ker is an object.

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
Signature. st is an object.
Signature. tl is an object.