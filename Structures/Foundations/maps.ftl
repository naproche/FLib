#
# Maps and functions
# (Marcel Schütz, 2020)
#

#[prove off][check off]
[read FLib/Structures/Foundations/classes.ftl]
#[prove on][check on]


# 1. Maps

Signature FoundMap000. A map is a notion.


# 1.1 Range

Definition FoundMap005. Let f be a map. range(f) = {f(x) | x \in dom(f)}.

Let the range of f stand for range(f).


# 1.2 Values

Definition FoundMap015. Let f be a map. A value of f is an element of the range of f.

Proposition FoundMap020. Let f be a map and y be an entity. y is a value of f iff y is equal to the
value of f at x for some element x of the domain of f.


# 1.3 Codomain

Axiom FoundMap025. Let f be a map. range(f) \subseteq codom(f).

Proposition FoundMap030. Let f be a map and x be an element of the domain of f. Then the value of f
at x lies in the codomain of f.

Proof. [prove off] qed.


# 1.4 Maps from ... to ...

Definition FoundMap035. Let X,Y be entities. A map from X to Y is a map f such that X is the domain
of f and Y is the codomain of f.


# 1.5 Extensionality

Axiom FoundMap040. Let f,g be maps. Assume that the domain of f is equal to the domain of g and the
codomain of f is equal to the codomain of g. Assume that the value of f at x is equal to the value
of g at x for all elements x of the domain of f. Then f is equal to g.


# 1.6 Composition

Axiom FoundMap045. Let f and g be maps. Assume that range(f) \subseteq dom(g). Then the composition
of g and f is a map from the domain of f to the codomain of g.


Corollary FoundMap046. Let x,y,z be entities. Let f be a map from x to y and g be a map from y to z.
Then g \circ f is a map from x to z.


Lemma FoundMap047. Let f and g be maps. Assume that range(f) \subseteq dom(g). Then the
composition of g and f is a map.

Proof. [prove off] qed.


Lemma FoundMap050. Let f and g be maps. Assume that range(f) \subseteq dom(g). Then the
domain of the composition of g and f is the domain of f.

Proof. [prove off] qed.


Lemma FoundMap055. Let f and g be maps. Assume that range(f) \subseteq dom(g). Then the
codomain of the composition of g and f is the codomain of g.

Proof. [prove off] qed.


Axiom FoundMap056. Let f and g be maps. Assume that range(f) \subseteq dom(g). Then
(g \circ f)(x) = g(f(x)) for all elements x of the domain of f.


Lemma FoundMap057. Let f and g be maps. Assume that range(f) \subseteq dom(g). Then range(g \circ f)
\subseteq range(g).

Proof.
  The range of g \circ f and the range of g are classes. range(g \circ f) =
  {(g \circ f)(x) | x \in dom(f)}. {(g \circ f)(x) | x \in dom(f)} = {g(f(x)) | x \in dom(f)}. Hence
  every element of range(g \circ f) lies in range(g).
qed.


Proposition FoundMap060. Let f,g,h be maps. Assume that range(f) \subseteq dom(g) and
range(g) \subseteq dom(h). Then h \circ (g \circ f) = (h \circ g) \circ f.

Proof.
  g \circ f is a map. range(g \circ f) \subseteq dom(h). Indeed range(g \circ f) \subseteq range(g).
  h \circ g is a map such that range(f) \subseteq dom(h \circ g).

  (1) dom(h \circ (g \circ f)) = dom(g \circ f) = dom(f) = dom((h \circ g) \circ f).

  (2) codom(h \circ (g \circ f)) = codom(h) = codom(h \circ g) = codom((h \circ g) \circ f).

  (3) For all x \in dom(f) we have (h \circ (g \circ f))(x) = ((h \circ g) \circ f)(x).
  proof.
    Let x \in dom(f). (h \circ (g \circ f))(x) = h((g \circ f)(x)) = h(g(f(x))).
    h(g(f(x))) = (h \circ g)(f(x)). Indeed f(x) lies in the domain of g. (h \circ g)(f(x)) =
    ((h \circ g) \circ f)(x) (by FoundMap056).
  end.

  Then we have the thesis (by FoundMap040, 1, 2, 3). Indeed Take maps a,b such that
  a = h \circ (g \circ f) and b = (h \circ g) \circ f.
qed.


# 1.7 Identity

Axiom FoundMap065. Let X be an entity. id_{X} is a map from X to X.
Let the identity map on X stand for id_{X}.


Lemma FoundMap070. Let X be an entity. The domain of id_{X} is equal to X.

Lemma FoundMap075. Let X be an entity. The codomain of id_{X} is equal to X.


Axiom FoundMap080. Let X be an entity. id_{X}(x) = x for all x \in X.


Lemma FoundMap085. Let X be an entity. range(id_{X}) = {x | x \in X}.


Proposition FoundMap090. Let f be a map. Then f \circ id_{dom(f)} = f = id_{codom(f)} \circ f.

Proof.
  Take entities x,y such that x = dom(f) and y = codom(f). range(id_{x}) \subseteq x and
  range(f) \subseteq y.

  (1) dom(f \circ id_{x}) = x = dom(id_{y} \circ f).

  (2) codom(f \circ id_{x}) = y = codom(id_{y} \circ f).

  (3) For all u \in x we have (f \circ id_{x})(u) = f(u) = (id_{y} \circ f)(u).
qed.


# 1.8 Injectivity

Definition FoundMap092. Let f be a map. f is injective iff for all elements x,y of the domain of f
if f(x) = f(y) then x = y.


Proposition FoundMap093. Let f,g be injective maps. Assume that range(f) \subseteq dom(g). Then the
composition of g and f is injective.

Proof.
  Let x,y \in dom(g \circ f). Then x,y \in dom(f). Assume that (g \circ f)(x) = (g \circ f)(y).
  Then g(f(x)) = g(f(y)). Hence f(x) = f(y). Indeed f(x),f(y) \in dom(g). Thus x = y (by
  FoundMap092).
qed.


# 1.9 Surjectivity

Definition FoundMap095. Let f be a map. f is surjective iff every element of the codomain of f is a
value of f.


Proposition FoundMap100. Let f be a map. f is surjective iff for all y \in codom(f) there is an
x \in dom(f) such that y = f(x).


Proposition FoundMap105. Let f,g be surjective maps. Assume that codom(f) = dom(g). Then the
composition of g and f is surjective.

Proof.
  Let z \in codom(g \circ f). Then z \in codom(g). Take y \in dom(g) such that z = g(y). y is an
  element of codom(f). Take x \in dom(f) such that y = f(x). Then z = g(f(x)). Hence
  z = (g \circ f)(x). x \in dom(g \circ f). Thus z is a value of g \circ f.
qed.


# 1.10 Bijectivity

Definition FoundMap110. Let f be a map. f is bijective iff f is injective and surjective.


Proposition FoundMap115. Let f,g be bijective maps. Assume that the domain of g is the codomain of
f. Then the composition of g and f is bijective.

Proof.
  f and g are injective and surjective. Hence g \circ f is injective and surjective. Then we have
  the thesis (by FoundMap110). Indeed g \circ f is a map.
qed.


Proposition FoundMap120. Let X be an entity. Then id_{X} is bijective.

Proof.
  For all x,y \in X if id_{X}(x) = id_{X}(y) then x = y. Hence id_{X} is injective. For all y \in X
  there is an x \in X such that y = id_{X}(x). Hence id_{X} is surjective.
qed.


Definition FoundMap125. Let x,y be entities. A bijection between x and y is a bijective map from x
to y.


Proposition FoundMap130. Let x,y be entities and f be a bijection between x and y. Then dom(f) = x.

Proposition FoundMap135. Let x,y be entities and f be a bijection between x and y. Then codom(f) = y.


Proposition FoundMap140. Let x,y,z be classes. Let f be a bijection between x and y and g be a
bijection between y and z. Then g \circ f is a bijection between x and z.

Proof.
  f and g are bijective. Hence g \circ f is bijective. dom(g \circ f) = x. codom(g \circ f) = z.
qed.


Proposition FoundMap145. Let x be an entity. id_{x} is a bijection between x and x.


# 1.11 Invertible maps

Axiom FoundMap150. Let x,y be entities and f be a map from x to y. Let g be an entity. g is an
inverse of f iff g is a map from y to x such that f \circ g = id_{y} and g \circ f = id_{x}.

Axiom FoundMap130. Let f be a map. f is invertible iff f has an inverse.


Proposition FoundMap155. Let x,y be entities and f be an invertible map. Let g,h be inverses of f.
Then g = h.

Proof. [prove off] qed.


Axiom FoundMap160. Let f be an invertible map. Then f^{-1} is the inverse of f.


Lemma FoundMap165. Let f be an invertible map. Then f^{-1} is a map.

Proof.
  Take entities x,y such that f is a map from x to y. Then f^{-1} is the inverse of f. Hence the
  thesis.
qed.


Proposition FoundMap170. Let f be a map. Then f is invertible iff f is bijective.

Proof. [prove off] qed.


Proposition FoundMap175. Let f be an invertible map. Then f^{-1} is bijective.

Proof. [prove off] qed.


Proposition FoundMap177. Let f be a bijective map and x \in dom(f). Then f^{-1}(f(x)) = x.

Proof. [prove off] qed.


Proposition FoundMap178. Let f be a bijective map and y \in range(f). Then f^{-1}(y) \in dom(f).

Proof. [prove off] qed.


Proposition FoundMap179. Let x,y be entities and f be a bijection between x and y. Then f^{-1} is a
bijection between y and x.

Proof. [prove off] qed.


Proposition FoundMap179a. Let f be a bijective map. Then (f^{-1})^{-1} = f.

Proof. [prove off] qed.


Proposition FoundMap179b. Let X,Y be entities and f be a bijection between X and Y. Let x,y \in Y.
If x \neq y then f^{-1}(x) \neq f^{-1}(y).

Proof. [prove off] qed.


Proposition FoundMap179c. Let X,Y be entities and f be a bijection between X and Y. Let y \in Y.
f(f^{-1}(y)) = y.

Proof. [prove off] qed.

Proposition FoundMap179d. Let X,Y be entities and f be a bijection between X and Y. Let x \in X.
f^{-1}(f(x)) = x.

Proof. [prove off] qed.

# 1.12 Image

Axiom FoundMap180. Let f be a map and x be an entity. f[x] is a class such that f[x] = {f(u) |
u \in x \cap dom(f)}.


Proposition FoundMap185. Let f be a map. f[dom(f)] = range(f).

Proof.
  f[dom(f)] = {f(u) | u \in dom(f)} (by FoundMap180). Indeed {f(u) | u \in dom(f)} =
  {f(u) | u \in dom(f) \cap dom(f)}. Moreover {f(u) | u \in dom(f)} = range(f).
qed.


Corollary FoundMap186. Let f be a map. f[dom(f)] = {f(x) | x \in dom(f)}.

Proof. [prove off] qed.


Proposition FoundMap187. Let x be an entity and a be a subclass of x. id_{x}[a] = a.

Proof. [prove off] qed.


Proposition FoundMap188. Let f be a map and a be a subclass of dom(f). Then f[a] = {f(x) | x \in a}.

Proof. [prove off] qed.


# 1.13 Preimage

Proposition FoundMap190. Let f be an invertible map and y be a class. f^{-1}[y] = {u in dom(f) |
f(u) \in y}.

Proof. [prove off] qed.


Axiom FoundMap195. Let f be a map and y be a class. f^{-1}[y] is a class such that f^{-1}[y] =
{u in dom(f) | f(u) \in y}.


Proposition FoundMap197. Let x be an entity and a be a subclass of x. id_{x}^{-1}[a] = a.

Proof. [prove off] qed.


Proposition FoundMap198. Let x,y,z be entities. Let f be a map from x to y and g be a map from y to
z. Let a be a subclass of z. Then (g \circ f)^{-1}[a] = f^{-1}[g^{-1}[a]].

Proof. [prove off] qed.


Proposition FoundMap199. Let x,y be entities and a be a subclass of y. Let f be a surjective map
from x to y. Then f[f^{-1}[a]] = a.

Proof. [prove off] qed.


Proposition FoundMap200. Let x,y be entities and a be a subclass of x. Let f be an injective map
from x to y. Then f^{-1}[f[a]] = a.

Proof. [prove off] qed.


# 1.14 Constant maps

Definition FoundMap204. Let f be a map. f is constant iff range(f) = {a} for some entity a.


Proposition FoundMap205. Let f be a map. Assume that the domain of f has an element. f is constant
iff there is an entity a such that f(x) = a for all elements x of the domain of f.

Proof.
  If f is constant then there is an entity a such that f(x) = a for all elements x of the domain of
  f.
  proof.
    Assume that f is constant. Take an entity a such that range(f) = {a}.
  end.

  If there is an entity a such that f(x) = a for all elements x of the domain of f then f is
  constant.
  proof.
    Assume that there is an entity a such that f(x) = a for all elements x of the domain of f. Take
    an entity a such that f(x) = a for all elements x of the domain of f. range(f) =
    {f(x) | x \in dom(f)}. {f(x) | x \in dom(f)} = {a}. Hence range(f) = {a}.
  end.
qed.


# 1.15 Restriction

Definition FoundMap210. Let f be a map and x be an entity. Assume that every element of x lies in
the domain of f. restr(f,x) is a map from x to codom(f) such that restr(f,x)(u) = f(u) for all
u \in x.

Let x \restr y stand for restr(x,y).
Let the restriction of x to y stand for restr(x,y).


Proposition FoundMap215. Let f be a map and x be a subclass of dom(f). range(f \restr x) = f[x].

Proof. [prove off] qed.


Proposition FoundMap220. Let f be a bijective map and z be a subclass of dom(f). Then the
restriction of f to z is a bijection between z and f[z].

Proof. [prove off] qed.


# 1.16 Zeroes

Definition FoundMap225. Let f be a map. A zero of f is an element x of the domain of f such that
f(x) = 0.


# 2. Maps and operations on classes

Proposition FoundMap226. Let x,y be entities and f be a map. Then

  f[x \cup y] = f[x] \cup f[y].

Proof. [prove off] qed.


Proposition FoundMap227. Let x,y be entities and f be a map. Then

  f[x \cap y] \subseteq f[x] \cap f[y].

Proof. [prove off] qed.


Proposition FoundMap228. Let x,y be entities and f be an injective map. Then

  f[x \cap y] = f[x] \cap f[y].

Proof. [prove off] qed.


Proposition FoundMap230. Let x,y be entities and f be a map. Assume that y = {f[u] | u \in x}. Then

  f[\bigcup x] = \bigcup y.

Proof. [prove off] qed.


Proposition FoundMap231. Let x,y be entities and f be a map. Assume x is nonempty and  y =
{f[u] | u \in x}. Then

  f[\bigcap x] \subseteq \bigcup y.

Proof. [prove off] qed.


Proposition FoundMap232. Let x,y be entities and f be an injective map. Assume that x is nonempty
and y = {f[u] | u \in x}. Then

  f[\bigcap x] = \bigcap y.

Proof. [prove off] qed.


Proposition FoundMap234. Let x,y be entities and f be a map. Assume that every element of x lies
in y. Then

  f^{-1}[x] \subseteq f^{-1}[y].

Proof. [prove off] qed.


Proposition FoundMap235. Let x,y be entities and f be a map. Then

  f^{-1}[x \cup y] = f^{-1}[x] \cup f^{-1}[y].

Proof. [prove off] qed.


Proposition FoundMap240. Let x,y be entities and f be a map. Then

  f^{-1}[x \cap y] = f^{-1}[x] \cap f^{-1}[y].

Proof. [prove off] qed.


Proposition FoundMap245. Let x,y be entities and f be a map. Assume that y = {f^{-1}[u] | u \in x}.
Then

  f^{-1}[\bigcup x] = \bigcup y.

Proof. [prove off] qed.


Lemma FoundMap250. Let x,y be entities and f be a map. Assume that x is nonempty. Assume that y =
{f^{-1}[u] | u \in x}. Then y is nonempty.

Proof. [prove off] qed.


Proposition FoundMap255. Let x,y be entities and f be a map. Assume that x is nonempty. Assume that
y = {f^{-1}[u] | u \in x}. Assume that x is nonempty. Then

  f^{-1}[\bigcap x] = \bigcap y.

Proof. [prove off] qed.


Proposition FoundMap256. Let x,y be entities and f be a map from x to y. Let a be a subclass of y.
Then

  f^{-1}[y \setminus a] = x \setminus f^{-1}[a].

Proof. [prove off] qed.


Proposition FoundMap257. Let f be a map and x \in dom(f). Then f[`{x}`] = `{f(x)}`.

Proof. [prove off] qed.


# 3. Functions

Axiom FoundMap260. Any function is a map f such that codom(f) = range(f).

Definition FoundMap265. Let x,y be entities. A function from x to y is a function f such that
dom(f) = x and range(f) \subseteq y.


Proposition FoundMap266. Let x,y be an entity and f be a function. f is a function from x to y iff
dom(f) = x and f(u) \in y for all u \in x.

Proof. [prove off] qed.


Definition FoundMap270. Let x be an entity. A function of x is a function f such that the domain of
f is equal to x.

Definition FoundMap275. Let x be an entity. A function on x is a function from x to x.


# 3.2 Extensionality

Proposition FoundMap290. Let f,g be functions. Assume that dom(f) = dom(g) and f(x) = g(x) for all
x \in dom(f). Then f = g.

Proof.
  f and g are maps. range(f) = {f(x) | x \in dom(f)} and range(g) = {f(x) | x \in dom(f)}. Hence
  range(f) = range(g). Thus codom(f) = codom(g). Then we have the thesis (by FoundMap040).
qed.


# 3.3 Composition

Axiom FoundMap295. Let f,g be functions. Assume that range(f) \subseteq dom(g). Then
g \circ f is a function of dom(f).


Proposition FoundMap300. Let f,g be functions. Assume that codom(f) \subseteq dom(g). Then
range(g \circ f) \subseteq range(g).


# 3.4 Bijections

Proposition FoundMap305. Let x be an entity and f be an injective function of x. Then f is a
bijection between x and range(f).
