#
# Lawvere's elementary theory of abstract categories
# (Marcel Schütz, 2019-2020)
#

Let x \neq y stand for x is not equal to y.


# 1. Morphisms

[synonym morphism/-s]

Signature. A morphism is a notion.

Signature. Let f be a morphism. dom(f) is a morphism.
Signature. Let f be a morphism. codom(f) is a morphism.

Axiom. Let f be a morphism. dom(dom(f))     = dom(f).
Axiom. Let f be a morphism. dom(codom(f))   = codom(f).
Axiom. Let f be a morphism. codom(dom(f))   = dom(f).
Axiom. Let f be a morphism. codom(codom(f)) = codom(f).

# We can interpret dom(f) as id_{dom(f)} and codom(f) as id_{codom(f)}.


Signature. Let g,f be morphisms. g \circ f is an entity.

Axiom. Let f,g be morphisms. codom(f) = dom(g) iff g \circ f is a morphism.

Axiom. Let f,g be morphisms. If g \circ f is a morphism then dom(g \circ f) = dom(f) and
  codom(g \circ f) = codom(g).

Axiom. Let f be a morphism. f \circ dom(f) = f = codom(f) \circ f.


Lemma. Let f,g,h be morphisms. If g \circ f and h \circ g are morphisms then h \circ (g \circ f) and
(h \circ g) \circ f are morphisms.

Axiom. Let f,g,h,u,v,x,y be morphisms. If g \circ f and h \circ g are morphisms then
  h \circ (g \circ f) = (h \circ g) \circ f.


Let f: A --> B stand for dom(f) = A and codom(f) = B.


# 2. Mono-, epi-, endo- and isomorphisms

Definition. A monomorphism is a morphism f such that for all morphisms x,y if dom(f) = codom(x) and
  dom(f) = codom(y) then (f \circ x = f \circ y => x = y).

Definition. An epimorphism is a morphism f such that for all morphisms x,y if dom(x) = codom(f) and
  dom(y) = codom(f) then (x \circ f = y \circ f => x = y).

Definition. An endomorphism is a morphism f such that dom(f) = codom(f).

Definition. An Isomorphism is a morphism f such that there is a morphism g such that
  codom(f) = dom(g) and dom(f) = codom(g) and g \circ f = dom(f) and f \circ g = codom(f).


# 3. Objects

[synonym object/-s]

Definition. An object is a morphism A such that dom(A) = A = codom(A).

Proposition. Let A be a morphism. A is an object iff A = dom(f) for some morphism f or A = codom(g)
  for some morphism g.

Proposition. Let A be a morphism. A is an object iff (for all morphisms f,g if A \circ f = g then
  f = g) and (for all morphisms h,k if h \circ A = k then h = k).


Definition. Let A,B be objects. A and B are isomorphic iff there is an isomorphism f such that
  f: A --> B.

Definition. Let B be an object. A retract of B is an object A such that there are morphisms f,g such
  that f: A --> B and f \circ g = A.

Definition. A generator is an object G such that for all morphisms f,g we have dom(f) = dom(g) and
  codom(f) = codom(g) and if f \neq g then there is a morphism x such that dom(x) = G and
  codom(x) = dom(f) and x \circ f \neq x \circ g.


# 4. Categories

[synonym category/categories] [synonym functor/-s]

Signature. A category is an object.

Definition. A functor is a morphism F such that F: C --> D for some categories C,D.


Definition. 1 is a category such that for all categories A there is a functor F such that F: A --> 1
  and for all functors G if G: A --> 1 then F = G.

Definition. Let F be a functor. F is constant iff there are functors G,H such that F = H \circ G and
  dom(H) = 1.


Axiom. Let A be an object and f be an isomorphism. Assume that f: A --> A. Then f = A.

Axiom. Let A,B be objects. If A and B are isomorphic then A = B.
