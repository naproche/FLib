# Lawvere's elementary theory of abstract categories

Let x \neq y stand for x is not equal to y.


# 1. Morphisms

[synonym morphism/-s]

Signature. A morphism is a notion.

Let f,g,h,u,v,x,y denote morphisms.

Signature. dom(f) is a morphism.
Signature. codom(f) is a morphism.

Axiom. dom(dom(f))     = dom(f).
Axiom. dom(codom(f))   = codom(f).
Axiom. codom(dom(f))   = dom(f).
Axiom. codom(codom(f)) = codom(f).

# We can interpret dom(f) as the identity on dom(f) and codom(f) as the identity
# on codom(f).


Signature. g \circ f is an object.

Axiom. codom(f) = dom(g) iff g \circ f is a morphism.

Axiom. If g \circ f is a morphism then dom(g \circ f) = dom(f) and
codom(g \circ f) = codom(g).

Axiom. f \circ dom(f) = f = codom(f) \circ f.


Lemma. If g \circ f and h \circ g are morphisms then h \circ (g \circ f) and
(h \circ g) \circ f are morphisms.

Axiom. If g \circ f and h \circ g are morphisms then h \circ (g \circ f) =
(h \circ g) \circ f.


# 2. Mono-, epi-, endo- and isomorphisms

Definition. A monomorphism is a morphism f such that for all morphisms x,y if
dom(f) = codom(x) and dom(f) = codom(y) then (f \circ x = f \circ y  =>  x = y).

Definition. An epimorphism is a morphism f such that for all morphisms x,y if
dom(x) = codom(f) and dom(y) = codom(f) then (x \circ f = y \circ f  =>  x = y).

Definition. An endomorphism is a morphism f such that dom(f) = codom(f).

Definition. An Isomorphism is a morphism f such that there is a morphism g such
that codom(f) = dom(g) and dom(f) = codom(g) and g \circ f = dom(f) and
f \circ g = codom(f).


# 3. Objects

[synonym object/-s]

Definition. A categorical object is a morphism A such that dom(A) = A =
codom(A).

# Since the word 'object' is used by Naproche to denote unspecified mathematical
# entities we use the notion 'categorical object' to denote objects in the
# categorical sense.

Proposition. Let A be a morphism. A is a categorical object iff A = dom(f) for
some morphism f or A = codom(g) for some morphism g.

Proposition. Let A be a morphism. A is a categorical object iff (for all
morphisms f,g if A \circ f = g then f = g) and (for all morphisms h,k if
h \circ A = k then h = k).


Let A,B denote categorical objects.


Definition. A morphism from A to B is a morphism f such that dom(f) = A and
codom(f) = B.

Let f: A --> B stand for f is a morphism from A to B.


Definition. A monomorphism from A to B is a monomorphism f such that dom(f) = A
and codom(f) = B.

Let f: A >--> B stand for f is a monomorphism from A to B.


Definition. An epimorphism from A to B is an epimorphism f such that dom(f) = A
and codom(f) = B.

Let f: A -->> B stand for f is a monomorphism from A to B.


Definition. An isomorphism between A and B is an isomorphism f such that
dom(f) = A and codom(f) = B.


Definition. An automorphism on A is an isomorphism between A and A.

Definition. A and B are isomorphic iff there is an isomorphism between A and B.

Let A ~~ B stand for A and B are isomorphic.


Definition. A retract of B is an categorical object A such that A = f \circ g
for some morphism g and some f: A --> B.

Definition. A generator is an categorical object G such that for all morphisms
f,g if dom(f) = dom(g) and codom(f) = codom(g) and f \neq g then there is a
morphism x from G to dom(f) such that x \circ f \neq x \circ g.


# 5. Categories and functors

[synonym category/categories]
[synonym functor/-s]
[synonym endofunctor/-s]

Signature. A category is a categorical object.

Let A,B,C,I,J denote categories.


Definition. A functor is a morphism F such that dom(F) and codom(F) are
categories.

Let F,G,H denote functors.


Definition. A functor from A to B is a functor F such that dom(F) = A and
codom(F) = B.

Definition. An endofunctor on A is a functor from A to A.

Definition. An endofunctor is an endofunctor on some category.


Signature. 0 is a category.

Signature. 1 is a category such that for all categories C there is a functor F
from C to 1 such that every functor G from C to 1 is equal to F.

# I.e. there is a unique functor from 1 to any category C.


Definition. F factors through C iff F = G \circ H for some functors G,H such
that codom(G) = C = dom(H).

Definition. F is constant iff F factors through 1.


Axiom Partial skeletal axiom 1. Any automorphism on A is equal to A.

Axiom Partial skeletal axiom 2. If A and B are isomorphic then A and B are
equal.


# 6. The category 2

Signature. 2 is a category.

Signature. Let I = 0 or I = 1. \partial{I} is a functor from 2 to 2.


Axiom. \partial{0} and \partial{1} are constant.

Axiom. \partial{J} \circ \partial{I} = \partial{J} where (I = 0 or I = 1) and
(J = 0 or J = 1).

Axiom. \partial{0} \neq \partial{1}.

Axiom. \partial{I} \neq 2 where I = 0 or I = 1.

Axiom. Let x be an endofunctor on 2. Then x = \partial{0} or x = \partial{1} or
x = 2.

Axiom. 2 is a generator.

Axiom. 2 is a retract of any generator.


Proposition. Let C be a generator and F,G,H be endofunctors on C such that
F \neq G and G \neq H and H \neq F. Assume that for any endofunctor K on C we
have K = F or K = G or K = H. Suppose that F and G are constant and C is a
retract of any generator. Then C = 2.


Definition. x \in A iff x is a functor from 2 to A.

Let a morphism in A stand for a morphism x such that x \in A.
