#
# Maps
# (Marcel Schütz, 2020)
#

#[prove off]
[read ForTheLib/Foundations/classes.ftl]
#[prove on]


# 1. Maps

Signature FoundMap000. A map is a notion.


# Range

Axiom FoundMap005. Let f be a map. range(f) is a class such that range(f) = {f(x) | x \in dom(f)}.

Proposition FoundMap010. Let f be a map and x be an element of the domain of f. Then the value of f
at x lies in the range of f.


# Values

Axiom FoundMap015. Let f be a map and y be an object. y is a value of f iff y lies in the range of
f.

Proposition FoundMap020. Let f be a map and y be an object. y is a value of f iff y is equal to the
value of f at x for some element x of the domain of f.


# Codomain

Axiom FoundMap025. Let f be a map. range(f) \subseteq codom(f).

Proposition FoundMap030. Let f be a map and x be an element of the domain of f. Then the value of f
at x lies in the codomain of f.


# Maps from ... to ...

Definition FoundMap035. Let X,Y be objects. A map from X to Y is a map f such that X is the domain
of f and Y is the codomain of f.


# Extensionality

Axiom FoundMap040. Let f,g be maps. Assume that the domain of f is equal to the domain of g and the
codomain of f is equal to the codomain of g. Assume that the value of f at x is equal to the value
of g at x for all elements x of the domain of f. Then f is equal to g.


# Composition

Axiom FoundMap045. Let f and g be maps. Assume that the domain of g is the codomain of f. Then the
composition of g and f is a map from the domain of f to the codomain of g.

Lemma FoundMap047. Let f and g be maps. Assume that the domain of g is the codomain of f. Then the
composition of g and f is a map.

Lemma FoundMap050. Let f and g be maps. Assume that the domain of g is the codomain of f. Then the
domain of the composition of g and f is the domain of f.

Lemma FoundMap055. Let f and g be maps. Assume that the domain of g is the codomain of f. Then the
codomain of the composition of g and f is the codomain of g.

Axiom FoundMap060. Let f and g be maps. Assume that the domain of g is the codomain of f. Then
(g \circ f)(x) = g(f(x)) for all elements x of the domain of f.


# Identity

Axiom FoundMap065. Let X be an object. id_{X} is a map from X to X.

Lemma FoundMap070. Let X be an object. The domain of id_{X} is equal to X.

Lemma FoundMap075. Let X be an object. The codomain of id_{X} is equal to X.

Axiom FoundMap080. Let X be an object. id_{X}(x) = x for all x \in X.


# Injectivity

Axiom FoundMap085. Let f be a map. f is injective iff for all elements x,y of the domain of f if
f(x) = f(y) then x = y.


Proposition FoundMap090. Let f,g be injective maps. Assume that the codomain of f is the domain of
g. Then the composition of g and f is injective.

Proof.
  For all x,y \in dom(g \circ f) if (g \circ f)(x) = (g \circ f)(y) then x = y.
  proof.
    Let x,y \in dom(g \circ f). Then x,y \in dom(f). Assume that (g \circ f)(x) = (g \circ f)(y).
    Then g(f(x)) = g(f(y)). Hence f(x) = f(y). Indeed f(x),f(y) \in dom(g). Thus x = y.
  end.

  Hence the thesis (by FoundMap085). Indeed g \circ f is a map.
qed.


# Surjectivity

Axiom FoundMap095. Let f be a map. f is surjective iff every element of the codomain of f is a value
of f.


Proposition FoundMap100. Let f be a map. f is surjective iff for all y \in codom(f) there is an
x \in dom(f) such that y = f(x).


Proposition FoundMap105. Let f,g be surjective maps. Assume that the codomain of f is the domain of
g. Then the composition of g and f is surjective.

Proof.
  For all z \in codom(g \circ f) there is an x \in dom(g \circ f) such that (g \circ f)(x) = z.
  proof.
    Let z \in codom(g \circ f). Then z \in codom(g). Take y \in dom(g) such that g(y) = z. Then
    y \in codom(f). Take x \in dom(f) such that f(x) = y. Then z = g(f(x)) = (g \circ f)(x).
  end.

  Hence the thesis (by FoundMap100). Indeed g \circ f is a map.
qed.


# Bijectivity

Axiom FoundMap110. Let f be a map. f is bijective iff f is injective and surjective.


Proposition FoundMap115. Let f,g be bijective maps. Assume that the domain of g is the codomain of
f. Then the composition of g and f is bijective.

Proof.
  f and g are injective and surjective. Hence g \circ f is injective and surjective. Then we have
  the thesis (by FoundMap110). Indeed g \circ f is a map.
qed.


Proposition FoundMap120. Let X be an object. Then id_{X} is bijective.

Proof.
  For all x,y \in X if id_{X}(x) = id_{X}(y) then x = y. Hence id_{X} is injective. For all y \in X
  there is an x \in X such that y = id_{X}(x). Hence id_{X} is surjective.
qed.


# Invertible maps

Axiom FoundMap125. Let f be a map. f is invertible iff there is a map g from codom(f) to dom(f) such
that f \circ g = id_{dom(g)} and g \circ f = id_{dom(f)}.


# Constant maps

Axiom FoundMap130. Let f be a map. f is constant iff range(f) = {a} for some object a.

Proposition FoundMap135. Let f be a map. Assume that the domain of f has an element. f is constant
iff there is an object a such that f(x) = a for all elements x of the domain of f.


# 2. Homomorphisms

Signature FoundMap150. A homomorphism is a map.
