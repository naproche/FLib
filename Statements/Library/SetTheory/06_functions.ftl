# 6 Functions

[read FLib/Statements/Library/SetTheory/02_elementary-set-theory.ftl]


Let W,X,Y,Z denote collections. Let f,g,h denote functions.


# Functions from X to Y

Definition 0601. A function of X is a function f such that Dom(f) = X. Let a
functions of X stand for a function of X.

Definition 0602. A function from X to Y is a function f of X such that every
value of f at any element of X is an element of Y. Let f: X \to Y stand for f is
a function from X to Y.

Definition 0603. A function on X is a function from X to X. Let a functions on X
stand for a function on X.


# Extensionality

Lemma 0604. If Dom(f) = Dom(g) and f[x] = g[x] for all x \in Dom(f) then f = g.


# Constructing functions

Definition 0605. Let F be a predicate. F is functional iff F has two free
variables and for all objects x,y,z if F(x,y) and F(x,z) then y = z.

Definition 0606. Let F be a predicate. F is functional on X iff F is functional
and for all x \in X there is an object y such that F(x,y).


Axiom 0607. Let F be a predicate that is functional on X. Then there is a
function f of X such that for all x \in X and all objects y we have f[x] = y iff
F(x,y).


# The identity function

Lemma 0608. There is a function f of X such that f[x] = x for all x \in X.

Proof.
  Define f[x] = x for x in X.
  proof.
    [prove off]
    Define F = {(x,y) | y = x}. F has two free variables.
    [prove on]

    F is functional on X. Hence we can take a function f of X such that for all
    x \in X and all objects y we have f[x] = y iff F(x,y). Then f[x] = x for all
    x \in X.
  end.
qed.


Lemma 0609. Let f,g be functions of X such that f[x] = x = g[x] for all x \in X.
Then f = g.


Definition 0610. id--{X} is the function of X such that id--{X}[x] = x for all
x \in X.


# The empty function

Lemma 0611. There is a function of \emptyset. Indeed we can take
f = id--{\emptyset}.


Lemma 0612. Let f,g be functions of \emptyset. Then f = g.

Proof.
  We have Dom(f) = \emptyset = Dom(g). For all x \in Dom(f) we have f[x] = g[x].
  Thus f = g.
qed.


Definition 0613. The empty function is the function on \emptyset.


# Constant functions

Definition 0614. f is constant iff there is an object a such that f[x] = a for
all x \in Dom(f).


# Composition

Lemma 0615. Assume f[x] \in Dom(g) for all x \in Dom(f). Then there is a
function h of Dom(f) such that h[x] = g[f[x]] for all x \in Dom(h).

Proof.
  Define h[x] = g[f[x]] for x in Dom(f).
  proof.
    Take X = Dom(f).

    [prove off]
    Define H = {(x,y) | x \in X and y = g[f[x]]}. H has two free variables.
    [prove on]

    H is functional on X. Hence we can take a function h of X such that for all
    x \in X and all objects y we have h[x] = y iff H(x,y) (by 0607). Indeed X is
    a collection.
  end.
qed.


Definition 0616. Assume f[x] \in Dom(g) for all x \in Dom(f). g \circ f is the
function of Dom(f) such that (g \circ f)[x] = g[f[x]] for all x \in Dom(f).


Lemma 0617. Let f: X \to Y and g: Y \to Z. g \circ f is the function from X to Z
such that (g \circ f)[x] = g[f[x]] for all x \in X.


Proposition 0618. Let f: X \to Y. id--{Y} \circ f = f = f \circ id--{X}.

[prove off][check off]
Proposition 0619. Let f: W \to X and g: X \to Y and h: Y \to Z. Then
f \circ (g \circ h) = (f \circ g) \circ h.
[/prove][/check]


# Function restriction

Lemma 0620. Assume X \subseteq Dom(f). Then there is a function g of X such that
g[x] = f[x] for all x \in X.

Proof.
  Define g[x] = f[x] for x in X.
  proof.
    [prove off]
    Define G = {(x,y) | x \in X and y = f[x]}. G has two free variables.
    [prove on]

    G is functional on X. Thus we can take a function g of X such that for all
    x \in X and all objects y we have g[x] = y iff G(x,y) (by 0607). Then
    g[x] = f[x] for all x \in X.
  end.
qed.


Definition 0621. Assume X \subseteq Dom(f). f \restr X is the function of X such
that (f \restr X)[x] = f[x] for all x \in X.
