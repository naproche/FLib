#
# Set Theory
# (Alexander Holz, Marcel Schütz, 2019)
#


# \section{Preliminaries} % chapter 1

[synonym subset/-s]

Let a \neq b stand for a != b.

Let a,b,c,i,j,x,y,z denote sets.

Let x \in y stand for x is an element of y.
Let x \notin y stand for not x \in y.

Let f,g,h stand for functions.

Let the value of f at x stand for f[x].
Let f is defined on x stand for Dom(f) = x.
Let the domain of f stand for Dom(f).

Axiom. Every element of a is a set.
Axiom. If a is an element of b then a -<- b.


# \subsection{Class terms} % chapter 1.1

Definition. The empty set is the set that has no elements.
Let \emptyset stand for the empty set.
Let x is nonempty stand for x is not the empty set.
Let x is empty stand for x is the empty set.

Definition. A subset of y is a set x such that every element of x is an element of y.
Let x \subseteq y stand for x is a subset of y.
Let x \subset y stand for x is a subset of y and x \neq y.

Definition. The union of x and y is {u | u \in x \/ u \in y}.
Let x \cup y stand for the union of x and y.

Definition. The union of x is {u | exists y \in x: u \in y}.
Let \bigcup x stand for the union of x.

Definition. The intersection of x and y is {u | u \in x /\ u \in y}.
Let x \cap y stand for the intersection of x and y.

Definition. Assume x is nonempty. The intersection of x is {u | forall y \in x: u \in y}.
Let \bigcap x stand for the intersection of x.

Definition. The difference of x and y is {u | u \in x /\ u \notin y}.
Let x \setminus y stand for the difference of x and y.

Definition. The powerset of x is the set of subsets of x.
Let \Pow(x) stand for the powerset of x.

Definition. The singleton set of x is {u | u = x}.
Let \{ x \} stand for the singleton set of x.

Definition. The unordered pair of x and y is {u | u = x \/ u = y}.
Let \{ x,y \} stand for the unordered pair of x and y.


# \subsectioin{Functions} % chapter 1.2

Definition. Let f be a function. \range(f) = {f[x] | x \in Dom(f)}.
Let the range of f stand for \range(f).

Definition. A function from a to b is a function f such that Dom(f) = a and \range(f) \subseteq b.
Let f : a \rightarrow b stand for f is a function from a to b.

Definition. A partial function from a to b is a function f such that Dom(f) \subseteq a and
\range(f) \subseteq b.

Definition. Let x be a subset of Dom(f). f^[x] = {f[y] | y \in x}.
Let the image of x under f stand for f^[x].

Definition. Let y \subseteq Dom(f). f^{-1}(y) = {x \in Dom(f) | f[x] \in y}.
Let the preimage of y under f stand for f^{-1}(y).

Definition. Let f be a function and x \subseteq Dom(f). f \upharpoonright x is a function such that
Dom(f \upharpoonright x) = x and (f \upharpoonright x)[i] = f[i] for every i \in x.
Let the restriction of f to x stand for f \upharpoonright x.

Definition. Let f,g be functions such that \range(f) \subseteq Dom(g). g \circ f is a
function such that Dom(g \circ f) = Dom(f) and (g \circ f)[i] = g[f[i]] for every i \in Dom(f).
Let the composition of g and f stand for g \circ f.

Definition. Let f be a function such that for all u,v \in Dom(f) if u \neq v then f[u] \neq f[v].
f^{-1} is a function such that Dom(f^{-1}) = \range(f) and \range(f^{-1}) = Dom(f) and f^{-1}[f[i]]
= i for every i \in Dom(f).
Let the inverse of f stand for f^{-1}.

Definition. A surjective function from a to b is a function f such that Dom(f) = a and \range(f) = b.
Let f: a \twoheadrightarrow b stand for f is a surjective function from a to b.

Definition. An injective function from a to b is a function f such that f: a \rightarrow b and for
all x,y \in a if x \neq y then f[x] \neq f[y].
Let f: a \hookrightarrow b stand for f is an injective function from a to b.

Definition. A bijective function from a to b is a function f such that f is a surjective function
from a to b and f is an injective function from a to b.
Let f : a \leftrightarrow b stand for f is a bijective function from a to b.

Definition. \id--{x} is a function from x to x such that \id--{x}[i] = i for every i \in x.

Definition. 0--{x} is a function such that Dom(0--{x}) = x and 0--{x}[i] = \emptyset for all i \in x.


# \subsectioin{Inductive sets} % chapter 1.3

Let 0 stand for \emptyset.

Definition. The successor of x is {u | u \in x \/ u = x}.
Let x + 1 stand for the successor of x.

Definition. 1 = 0 + 1.
Definition. 2 = 1 + 1.
Definition. 3 = 2 + 1.

Definition. x is inductive iff 0 \in x and for all n \in x n + 1 \in x.


# \subsection{The Cartesian Product} % chapter 1.4

Definition. The cartesian product of x and y is {(a,b) | a \in x /\ b \in y}.
Let x \times y stand for the cartesian product of x and y.

Axiom 1401. For any objects x,y,i,j (x,y) = (i,j) iff x = i and y = j.

Lemma 1402. Let s,t be objects. (s,t) \in x \times y iff s \in x and t \in y.
Proof.
  Let us show that if (s,t) \in x \times y then s \in x and t \in y.
    Assume (s,t) \in x \times y. Take a \in x and b \in y such that (s,t) = (a,b). a,b are sets.
    Then s = a and t = b (by 1401). Thus (s,t) \in x \times y.
  end.

  If s \in x and t \in y then (s,t) \in x \times y.
qed.


# \subsection{The ZF Axioms} % chapter 1.5

Axiom EX. There is x such that there is no element of x.

Axiom EXT. If for all z z \in x iff z \in y then x = y.

Axiom PAIR. For all x,y there is a set z such that z = \{ x,y \}.

Axiom UNION. For all x there is a set y such that y is the union of x.

Axiom POW. For all x there is a set y such that y is the set of subsets of x.

Axiom SEP. For all x,y there is a set z such that z is the intersection of x and y.

Axiom REP. Let f be a function. The value of f at any element of Dom(f) is a set.

Axiom FOUND. Assume x is nonempty. There exists y \in x such that there is no element of y \cap x.

Axiom INF. There is an inductive set.


# \subsection{Some easy lemmas} % chapter 1.6

Lemma 1601. \id--{x} is an injective function from x to x.
Proof.
  \id--{x} is a function from x to x.
  Let us show that for all u,v \in x if u \neq v then \id--{x}[u] \neq \id--{x}[v].
    Let u,v \in x. Assume u \neq v. \id--{x}[u] = u and \id--{x}[v] = v.
  end.
qed.

Lemma 1602. \id--{x} is a bijective function from x to x.
Proof.
  \id--{x} is an injective function from x to x (by 1601).

  Let us show that \range(\id--{x}) = x.
    For all u \in x \id--{x}[u] = u. Thus for all u \in x u \in \range(\id--{x}).
    For all u \in \range(\id--{x}) \id--{x}[u] = u. Thus for all u \in \range(\id--{x}) u \in x.
  end.

  Hence \id--{x} is a surjective function from x to x.
qed.

Lemma 1603. If f is a function from x to y and g is a function from y to z then g \circ f is a
function from x to z.
Proof.
  Assume that f is a function from x to y and g is a function from y to z.

  Let us show that for all u \in x (g \circ f)[u] \in z.
    Let u \in x. f[u] \in y. g[f[u]] \in z.
  end.

  For all v \in \range(g \circ f) v = (g \circ f)[u] for some u \in x. Indeed Dom(g \circ f) = x.
  Thus for all v \in \range(g \circ f) v \in z. Hence \range(g \circ f) is a subset of z.
qed.

Lemma 1604. If f is an injective function from x to y and g is an injective function from y to z
then g \circ f is an injective function from x to z.
Proof.
  Assume that f is an injective function from x to y and g is an injective function from y to z. g
  \circ f is a function from x to z (by 1603).

  Let us show that for all u,v \in x if u \neq v then (g \circ f)[u] \neq (g \circ f)[v].
    Let u,v \in x. Assume u \neq v. f[u] \neq f[v]. Indeed f is an injective function from x to y.
    f[u],f[v] \in y. Thus g[f[u]] \neq g[f[v]]. Indeed g is an injective function from y to z.
  end.
qed.

Lemma 1605. If f is a bijective function from x to y and g is a bijective function from y to z then
g \circ f is a bijective function from x to z.
Proof.
  Assume that f is a bijective function from x to y and g is a bijective function from y to z.
  g \circ f is an injective function from x to z (by 1604).
  Let us show that for all w \in z  w \in \range(g \circ f).
    Let w \in z. Take v \in y such that g[v] = w. Indeed g is a surjective function from y to z.
    Take u \in x such that f[u] = v. Indeed f is a surjective function from x to y. (g \circ f)[u] =
    w.
  end.

  Thus z \subseteq \range(g \circ f). Therefore \range(g \circ f) = z (by EXT). Hence g \circ f is a
  surjective function from x to z.
qed.

Lemma 1606. If f is an injective function from x to y and g is a bijective function from y to z
then g \circ f is an injective function from x to z (by 1604).
Indeed If g is a bijective function from y to z then g is an injective function from y to z.

Lemma 1607. If f is a bijective function from x to y and g is an injective function from y to z
then g \circ f is an injective function from x to z (by 1604).
Indeed If f is a bijective function from x to y then f is an injective function from x to y.

Lemma 1608. If f is a bijective function from x to y then f^{-1} is a bijective function from y to
x.
Proof.
  Assume that f is a bijective function from x to y. \range(f) = y. Indeed f is a surjective
  function from x to y. Thus Dom(f^{-1}) = y. Dom(f) = x. Thus \range(f^{-1}) = x. x is a subset of
  x. Hence f^{-1} is a function from y to x.

  For all u,v \in y if u \neq v then f^{-1}[u] \neq f^{-1}[v].
  proof.
    Let u,v \in y. Assume that u \neq v. Take a,b \in x such that f[a] = u and f[b] = v. Indeed
    \range(f) = y. a \neq b. Indeed f is an injective function from x to y. f^{-1}[u] = f^{-1}[f[a]]
    = a and f^{-1}[v] = f^{-1}[f[b]] = b.
  end.

  Hence f^{-1} is an injective function from y to x. Indeed f^{-1} is a function from y to x.

  For all u \in x u \in \range(f^{-1}).
  proof.
    Let u \in x. Take v \in y such that f[u] = v. f^{-1}[v] = f^{-1}[f[u]] = u.
  end.

  Thus x \subseteq \range(f^{-1}). Hence \range(f^{-1}) = x (by EXT). Therefore f^{-1} is a
  surjective function from y to x.
qed.

Lemma 1609. Let f be a function such that Dom(f) = x. f^[x] = \range(f).
Proof.
  For all v \in f^[x] v \in \range(f). Indeed for all v \in f^[x] there is u \in x such that f[u] =
  v. Thus f^[x] is a subset of \range(f). For all v \in \range(f) v \in f^[x]. Indeed for all v \in
  \range(f) there is u \in x such that f[u] = v. Thus \range(f) is a subset of f^[x]. Hence the
  thesis (by EXT).
qed.

Lemma 1610. Let f be an injective function from x to y. Then f is a bijective function from x to
f^[x].
Proof.
  f^[x] is a subset of \range(f). Indeed f^[x] = \range(f) (by 1609). Thus f is a function from x to
  f^[x]. For all u,v \in x if u \neq v then f[u] \neq f[v]. Indeed f is an injective function from x
  to y. Thus f is an injective function from x to f^[x]. Indeed f is a function from x to f^[x]. f
  is a surjective function from x to f^[x]. Indeed f^[x] = \range(f) (by 1609).
qed.

Lemma 1611. Let f be an injective function from x to y. Dom(f^{-1}) \subseteq y.
Indeed Dom(f^{-1}) = \range(f).

Lemma 1612. Let f be a bijective function from x to y and g be an injective function from y to z.
Then g \circ f is a bijective function from x to g^[y].
Proof.
  g is a bijective function from y to g^[y] (by 1610). Indeed g is an injective function from y to
  z. Hence the thesis (by 1605).
qed.

Lemma 1613. Let f be a function from x to y. Let z be a subset of x. Then the restriction of f to z
is a function from z to y.
Proof.
  Dom(f \upharpoonright z) = z.

  Let us show that for all u \in z (f \upharpoonright z)[u] \in y.
    Let u \in z. (f \upharpoonright z)[u] = f[u]. Thus (f \upharpoonright z)[u] \in \range(f).
    If (f \upharpoonright z)[u] \in \range(f) then (f \upharpoonright z)[u] \in y. Indeed \range(f)
    is a subset of y.
  end.

  Thus for all v \in \range(f \upharpoonright z) v \in y.  Hence (f \upharpoonright z)^[z] is a
  subset of y.
qed.

Lemma 1614. Let f be a bijective function from x to y. Let z be a subset of x. Then the restriction
of f to z is a bijective function from z to f^[z].
Proof.
  f \upharpoonright z is a function from z to y (by 1613). Indeed f is a function from x to y.

  Let us show that for all u,v \in z if u \neq v then (f \upharpoonright z)[u] \neq
  (f \upharpoonright z)[v].
    Let u,v \in z. Assume u \neq v. f[u] \neq f[v]. Indeed f is an injective function from x to y.
    (f \upharpoonright z)[u] = f[u] and (f \upharpoonright z)[v] = f[v].
  end.

  (1) Thus f \upharpoonright z is an injective function from z to y. Indeed f \upharpoonright z is a
  function from z to y.

  f^[z] = (f \upharpoonright z)^[z].
  proof.
    For all u \in f^[z] u \in (f \upharpoonright z)^[z]. Indeed for all u \in f^[z] there is v \in z
    such that u = f[v] = (f \upharpoonright z)[v]. Thus f^[z] is a subset of
    (f\upharpoonright z)^[z]. For all u \in (f \upharpoonright z)^[z] u \in f^[z]. Indeed for all u
    \in (f \upharpoonright z)^[z] there is v \in z such that u = (f \upharpoonright z)[v] = f[v].
    Thus (f \upharpoonright z)^[z] is a subset of f^[z]. Hence the thesis (by EXT).
  end.

  Therefore the thesis (by 1610).
qed.

Lemma 1615. x \notin x.
Proof.
  Assume x \in x. Define y = {u | u = x}. y is nonempty. Take z \in y such that z \cap y is empty
  (by FOUND). Then x \in z \cap y. Contradiction.
qed.

Lemma 1616. x \setminus y is a subset of x.
Indeed for all u \in x \setminus y u \in x.

Lemma 1617. If x is nonempty then 0--{x} is a surjective function from x to 1.
Proof.
  Assume that x is nonempty.
  Let us show that for all u \in x 0--{x}[u] \in 1.
    Let u \in x. 0--{x}[u] = 0. 0 \in 1.
  end.

  Hence \range(0--{x}) \subseteq 1. Thus 0--{x} is a function from x to 1.

  Let us show that for all u \in 1 u \in \range(0--{x}).
    Let u \in 1.For all v \in x 0--{x}[v] = 0. Take v \in x such that 0--{x}[v] = u.
  end.

  Thus \range(0--{x}) = 1.
qed.


# \section{Ordinal Numbers} % chapter 2

[synonym ordinal/-s]


Definition. x is transitive iff every element of every element of x is an element of x.
Let Trans(x) stand for x is transitive.

Definition. An ordinal is a set x such that x is transitive and every element of x is transitive.
Let \Ord(x) stand for x is an ordinal.

Let x \in \Ord stand for \Ord(x).
Let x \subseteq \Ord stand for for all y \in x y is an ordinal.


Let alpha, beta, gamma denote ordinals.


[prove off]

Lemma 2001. 0 is an ordinal.

Lemma 2002. alpha + 1 is an ordinal.

Lemma 2003. Every element of alpha is an ordinal.

Lemma 2004. If alpha \in beta and beta \in gamma then alpha \in gamma.

Lemma 2005. alpha \notin alpha.

Lemma 2006. alpha \in beta or alpha = beta or beta \in alpha.


Definition. alpha < beta iff alpha \in beta.

Definition. alpha > beta iff beta < alpha.

Definition. alpha \leq beta iff alpha < beta or alpha = beta.

Definition. alpha \geq beta iff beta \leq alpha.


Lemma 2007. alpha \leq beta iff alpha \subseteq beta.

Lemma 2008. If alpha \in beta then alpha \subseteq beta.

Lemma 2009. alpha < alpha +1.

Lemma 2010. If beta < alpha +1 then beta = alpha or beta < alpha.

Lemma 2011. beta < alpha or beta = alpha or alpha < beta.

Lemma 2012. alpha < beta iff alpha -<- beta.

Lemma 2013. Let x \subseteq alpha. \bigcup x is an ordinal.

Lemma 2014. alpha > 0 iff alpha is nonempty.


Definition. A successor ordinal is an ordinal alpha such that exists beta alpha = beta + 1.
Let \Succ(x) stand for x is a successor ordinal.

Definition. A limit ordinal is an ordinal alpha such that alpha \neq 0 and alpha is not a successor
ordinal.

Let x \in \Succ stand for \Succ(x).
Let x \subseteq \Succ stand for for every y \in x \Succ(y).

Let x \in \Lim stand for x is a limit ordinal.
Let x \subseteq \Lim stand for for every y \in x y is a limit ordinal.

Definition. Let alpha be a successor ordinal. \pred(alpha) is an ordinal such that \pred(alpha) + 1
= alpha.
Let the predecessor of x stand for \pred(x).
Let x - 1 stand for \pred(x).


Lemma 2015. Let lambda be a limit ordinal. Assume alpha \in lambda. Then alpha + 1 \in lambda.

[/prove]


# \subsection{Natural Numbers} % chapter 2.1
[/prove][/check]
[synonym number/-s]

Definition. omega is a set such that for all x x \in omega iff x is an element of every inductive
set.


[prove off]

Lemma 2101. omega \subseteq \Ord.

Lemma 2102. Let x be inductive and a subset of omega. Then x = omega.

Lemma 2103. omega \in \Ord.

Lemma 2104. omega \in \Lim.


Definition. A natural number is an ordinal n such that n < omega.

Let m,n,k denote natural numbers.


Lemma 2105. 0 is a natural number.

Lemma 2106. n + 1 is a natural number.

Lemma 2107. Let n \neq 0. Then n is a successor ordinal.

[/prove]

# \subsection{The Axiom of Choice} % chapter 2.2

Axiom 2201. For all x there exists alpha such that there is a bijective function from x to alpha.


# \section{The order type} % chapter 3

Definition. Let x,y \subseteq \Ord. An order isomorphism from x to y is a bijective function f from
x to y such that for all u,v \in x u < v iff f[u] < f[v].

Definition. Let x \subseteq \Ord. \otp(x) is an ordinal such that there is an order isomorphism from
x to \otp(x).

Lemma 3001. Let x \subseteq alpha. Let f be an order isomorphism from x to \otp(x). For all y \in x
f[y] is an ordinal.

Lemma 3002. Let x \subseteq \Ord. There is an order isomorphism from \otp(x) to x.
Proof.
  Take an order isomorphism f from x to \otp(x). f^{-1} is a bijective function from \otp(x) to x
  (by 1608).

  Let us show that for all u,v \in \otp(x) (u < v iff f^{-1}[u] < f^{-1}[v]).
    Let u,v \in \otp(x).

    If u < v then f^{-1}[u] < f^{-1}[v].
    proof.
      Assume u < v.
      Take p,q \in x such that f[p] = u and f[q] = v.
      p < q.
      f^{-1}[u] = p and f^{-1}[v] = q.
    end.

    If f^{-1}[u] < f^{-1}[v] then u < v.
    proof.
      Assume f^{-1}[u] < f^{-1}[v].
      Take p,q \in x such that f^{-1}[u] = p and f^{-1}[v] = q.
      u = f[p] and v = f[q].
    end.
  end.

  Hence f^{-1} is an order isomorphism from \otp(x) to x.
qed.

Lemma 3003. Let f be an order isomorphism from alpha to beta. Then alpha = beta and f = \id--{alpha}.
Proof.
  Let us show by induction on x that for all x \in alpha f[x] = x.
    Let x \in alpha.

    Case x = 0. Obvious.

    Case x \neq 0.
      For all y \in x y -<- x. Thus for all y \in x f[y] = y \in f[x]. Hence x \subseteq f[x].

      Let us show that for all v \in f[x] v \in x.
        Let v \in f[x]. Take u \in alpha such that v = f[u]. Indeed beta is transitive. u \in x.
        Thus v = f[u] = u \in x.
      end.

      Hence f[x] \subseteq x. Therefore x = f[x] (by EXT).
    end.
  end.
qed.

Lemma 3004. Let x \subseteq alpha. Let f be an order isomorphism from x to \otp(x). For all y \in x
y \geq f[y].
Proof by induction on y.
qed.

Lemma 3005. Let x \subseteq alpha. \otp(x) \leq alpha.
Proof.
  Let us show that for all y \in \otp(x) y \in alpha.
    Let y \in \otp(x). Take an order isomorphism f from x to \otp(x). Take z \in x such that y =
    f[z]. z \geq f[z] (by 3004). Hence z < alpha.
  end.
qed.


# \section{Cardinalities} % chapter 4

Definition. x and y are equipollent iff there is a bijective function from x to y.
Let x and y are equipotent stand for x and y are equipollent.
Let x and y have same cardinality stand for x and y are equipollent.
Let x \sim y stand for x and y are equipollent.
Let x \nsim y stand for not x \sim y.

Definition. x has cardinality at most that of y iff there is f such that f
is an injective function from x to y.
Let x \preccurlyeq y stand for x has cardinality at most that of y.

Definition. x has cardinality less than y iff x \preccurlyeq y and x \nsim y.
Let x \prec y stand for x has cardinality less than y.

Lemma 4001. x \sim x.
Indeed \id--{x} is a bijective function from x to x (by 1602).


Lemma 4002. If x \sim y then y \sim x.
Proof.
  Assume x \sim y. Take f: x \leftrightarrow y. The inverse of f is a bijective function from y to x
  (by 1608).
qed.

Lemma 4003. If x \sim y and y \sim z then x \sim z.
Proof.
  Assume x \sim y and y \sim z. Take f: x \leftrightarrow y and g: y \leftrightarrow z. The
  composition of g and f is a bijective function from x to z (by 1605).
qed.

Lemma 4004. If x \sim y then x \preccurlyeq y and y \preccurlyeq x.

Lemma 4005. x \preccurlyeq x.

Lemma 4006. If x \preccurlyeq y and y \preccurlyeq z then x \preccurlyeq z.
Proof.
  Assume x \preccurlyeq y and y \preccurlyeq z. Take f: x \hookrightarrow y and g: y \hookrightarrow
  z. The composition of g and f is an injective function from x to z (by 1604).
qed.

Lemma 4007. If x \subseteq y then x \preccurlyeq y.
Proof.
  Assume x \subseteq y. \id--{x} is an injective function from x to x (by 1601). Thus \id--{x} is an
  injective function from x to y.
qed.

# Knaster-Tarski
Lemma 4008. Let h: \Pow(z) \rightarrow \Pow(z). Assume for all x,y \subseteq z if x \subseteq y
then h[x] \subseteq h[y]. Then there is w \subseteq z such that h[w] = w.
Proof.
  Define A = {u \subseteq z | u \subseteq h[u]}. \bigcup A \in \Pow(z). Take x \in A. x \subseteq
  \bigcup A. Then h[x] \subseteq h[\bigcup A]. Hence \bigcup A \subseteq h[\bigcup A]. Thus we have
  \bigcup A \in A. Then h[\bigcup A] \in A. Therefore h[\bigcup A] \subseteq \bigcup A \subseteq
  \bigcup A. Hence h[\bigcup A] = \bigcup A.
qed.

# Cantor-Bernstein
Theorem 4009. If x \preccurlyeq y and y \preccurlyeq x then x \sim y.
Proof.
  Assume x \preccurlyeq y and y \preccurlyeq x. Take an injective function f from x to y. Take an
  injective function g from y to x. y \setminus f^[u] \subseteq y for any u \in \Pow(x). Define h[u]
  = x \setminus g^[y \setminus f^[u]] for u in \Pow(x).

  For all u,v \in \Pow(x) if u \subseteq v then h[u] \subseteq h[v].
  proof.
    Let u,v \in \Pow(x). Assume u \subseteq v. f^[u] \subseteq f^[v]. Then y \setminus f^[v]
    \subseteq y \setminus f^[u]. Hence g^[y \setminus f^[v]] \subseteq g^[y \setminus f^[u]]. Thus
    x \setminus g^[y \setminus f^[u]] \subseteq x \setminus g^[y \setminus f^[v]]. Therefore h[u]
    \subseteq h[v].
  end.

  (1) For all u,v \subseteq x if u \subseteq v then h[u] \subseteq h[v].
  (2) h is a function from \Pow(x) to \Pow(x).

  There is w \subseteq x such that h[w] = w.
  proof. [timelimit 10] The thesis (by 4008,1,2). end.

  Take w \subseteq x such that h[w] = w.

  (3) w = h[w] iff x \setminus w = g^[y \setminus f^[w]].

  Define F[u] = f[u] for u in w. g^{-1} is a bijective function from \range(g) to y. x \setminus w =
  g^[y \setminus f^[w]] \subseteq \range(g) (by 3). Define G[u] = g^{-1}[u] for u in x \setminus w.
  F is a bijective function from w to \range(F). G is a bijective function from x \setminus w to
  \range(G).

  Define H[u] =
    case u \in w -> F[u],
    case u \in x \setminus w -> G[u]
  for u in x.

  Let us show that for all u \in \range(H) u \in y.
    Let u \in \range(H). Take v \in x such that H[v] = u. If v \in w then u = H[v] = F[v] = f[v]
    \in y. If v \notin w then u = H[v] = G[v] = g^{-1}[v] \in y.
  end.

  Hence H is a function from x to y.

  Let us show that for all u,v \in x if u \neq v then H[u] \neq H[v].
    Let u,v \in x. Assume u \neq v.

    Case u,v \in w.
      H[u] = F[u] and H[v] = F[v].
    end.

    Case u,v \in x \setminus w.
      H[u] = G[u] and H[v] = G[v].
    end.

    Case u \in w and v \in x \setminus w.
      H[u] = F[u] and H[v] = G[v]. v \in g^[y \setminus f^[w]] (by 3). We have G[v] \in y \setminus
      F^[w]. Hence G[v] \neq F[u].
    end.

    Case u \in x \setminus w and v \in w.
      H[u] = G[u] and H[v] = F[v]. u \in g^[y \setminus f^[w]] (by 3). We have G[u] \in y \setminus
      f^[w]. Hence G[u] \neq F[v].
    end.
  end.

  Therefore H is an injective function from x to y.

  Let us show that for all v \in y: v \in \range(H).
    Let v \in y.

    Case v \in f^[w].
      There is u \in w such that f[u] = v. Thus there is u \in w such that F[u] = v.
    end.

    Case v \notin f^[w].
      v \in y \setminus f^[w]. g[v] \in g^[y \setminus f^[w]]. Then g[v] \in x \setminus h[w]. We
      have g[v] \in x \setminus w. Thus  there is u \in x \setminus w such that G[u] = v.
    end.
  end.

  H is a surjective function from x to y.
qed.


[synonym cardinal/-s]


Lemma 4010. Let x be nonempty and x \subseteq \Ord. Then there is y \in x such that for all z \in x
y \leq z.
Proof.
  Take y \in x such that there is no element z of x \cap y. There is z \in x such that z \subseteq
  y.

  There is no element z of x such that z \subset y.
  proof by contradiction.
    Assume z \in x and z \subset y. Then z is an ordinal. Thus z \in y. Hence z \in x \cap y.
  end.

  For all z \in x: y \subseteq z. Indeed for all z \in x z is an ordinal.
qed.


Definition. Assume x is nonempty and x \subseteq \Ord. The minimum of x is the ordinal beta such
that beta \in x and for all gamma \in x beta \leq gamma.
Let \min(x) stand for the minimum of x.

Definition. EquipotOrd(x) = {u | u \in \Ord /\ u \sim x}.

Definition. \card(x) = \min(EquipotOrd(x)).
Let the cardinality of x stand for \card(x).
Let \bar{\bar{x}} stand for \card(x).

Definition. A cardinal is an ordinal kappa such that there is a set x such that kappa = \card(x).

Let x \in \Cd stand for x is a cardinal.
Let x \subseteq \Cd stand for for every y \in x y \in \Cd.
Let x \in \Card stand for x is a cardinal and omega \leq x.
Let x \subseteq \Card stand for for every y \in x y \in \Card.


Let kappa, mu, nu stand for cardinals.

Lemma 4011. x \sim \card(x) and \card(x) \sim x.

Lemma 4012. \card(alpha) \leq alpha.

Lemma 4013. \card(\card(x)) = \card(x).

Lemma 4014. \card(kappa) = kappa.

Lemma 4015. Let f be an injective function from x to y. Then \card(x) = \card(f^[x]).
Proof.
  f is a bijective function from x to f^[x] (by 1610). Take a bijective function g from \card(x) to
  x (by 4011). Take a bijective function h from f^[x] to \card(f^[x]) (by 4011). Then f \circ g is a
  bijective function from \card(x) to f^[x] (by 1605). Indeed \card(x) is a set. Hence h \circ (f
  \circ g) is a bijective function from \card(x) to \card(f^[x]) (by 1605). Indeed \card(x),
  \card(f^[x]) are sets.
qed.

Theorem 4016. x \preccurlyeq y iff \card(x) \leq \card(y).
Proof.
  If x \preccurlyeq y then \card(x) \leq \card(y).
  proof.
    Assume x \preccurlyeq y.

    (1) Take an injective function f from x to y.
    (2) Take a bijective function g from \card(x) to x.

    Take a bijective function h from \card(y) to y.

    (h^{-1} \circ f) \circ g is an injective function from \card(x) to \card(y).
    proof.
      h^{-1} is a bijective function from y to \card(y).

      (3) Then h^{-1} \circ f is an injective function from x to \card(y) (by 1606, 1, 2). Indeed
      \card(y) is a set.
      (4) \card(x), \card(y) are sets.

      Hence the thesis (by 1607, 2, 3, 4).
    end.

    Take z = ((h^{-1} \circ f) \circ g)^[\card(x)]. Then \card(x) = \card(z).

    [timelimit 10] Hence \card(x) \subseteq \card(y).
  end.

  [timelimit 10] If \card(x) \leq \card(y) then x \preccurlyeq y.
qed.

Corollary 4017. x \sim y iff \card(x) = \card(y).

Theorem 4018. For all natural numbers n \card(n) = n.
Proof by induction.
  Let n be a natural number.

  Case n = 0. Obvious.

  Case n \neq 0.
    We have n - 1 -<- n. Hence \card(n - 1) = n - 1. \card(n) \leq n.

    Let us show by contradiction that we have not \card(n) < n.
      Assume \card(n) < n. Take m = \card(n). Take a bijective function f from m to n. Take u \in m
      such that f[u] = n - 1.

      Case u = m - 1.
        The restriction of f to m - 1 is a bijective function from m - 1 to n - 1.
        proof.
          f \upharpoonright m - 1 is a bijective function from m - 1 to f^[m - 1] (by 1614).
          f^[m - 1] \subseteq n - 1. n - 1 \subseteq f^[m - 1]. Thus f^[m - 1] = n - 1.
        end.

        Hence \card(n - 1) \leq m - 1 < n - 1. Contradiction.
      end.

      Case u < m - 1.
        Define g[i] =
          case i \neq u -> f[i],
          case i = u -> f[m - 1]
        for i in m - 1.

        Let us show that for all x \in \range(g) x \in n - 1.
          Let x \in \range(g).

          Case x = g[u].
            Then x = f[m - 1] \neq f[u] = n - 1. Thus x \in n - 1.
          end.

          Case x \neq g[u].
            Take j \in m - 1 such that x = f[j]. Then x \in n - 1.
          end.
        end.

        Thus g is a function from m - 1 to n - 1.

        Let us show that for all x \in n - 1 x \in \range(g).
          Let x \in n - 1. Then x \in \range(f) and x \neq n - 1 = f[u]. Thus x = f[j] for some j
          \in m. Hence x \in \range(g).
        end.

        Thus g is a surjective function from m - 1 to n - 1.

        Let us show that for all i,j \in m - 1 (if i \neq j then g[i] \neq g[j]).
          Let i,j \in m - 1. Assume i \neq j.

          Case i,j \neq u.
            Then g[i] = f[i] \neq f[j] = g[j].
          end.

          Case i = u.
            Then j \neq u. Thus g[i] = g[u] = f[m - 1] \neq f[j] = g[j].
          end.

          Case j = u.
            Then i \neq u. Thus g[i] = f[i] \neq f[m - 1] = g[u] = g[j].
          end.
        end.

        Thus g is an injective function from m - 1 to n - 1.
      end.
    end.
  end.
qed.

Corollary 4019. n \in \Cd.

Theorem 4020. \card(omega) = omega.
Proof.
  \card(omega) \leq omega.
  Let us show by contradiction that not \card(omega) < omega.
    Assume that \card(omega) < omega. Take n such that \card(omega) = n. Contradiction.
  end.
qed.

Corollary 4021. omega \in \Card.

Lemma 4022. Let alpha \geq omega. \card(alpha + 1) = \card(alpha).
Proof.
  Define f[i] =
    case i = alpha -> 0,
    case i < omega -> i + 1,
    case omega \leq i < alpha -> i
  for i in alpha + 1.

  f is a bijective function from alpha + 1 to alpha.
  proof.
    f is a function from alpha + 1 to alpha.
		proof.
      Let us show that for all u \in \range(f) u \in alpha.
        Let u \in \range(f). Take i \in alpha + 1 such that f[i] = u.

        Case i = alpha.
          u = f[i] = 0 \in alpha.
        end.

        Case i < omega.
          u = f[i] = i + 1 < omega. Thus u \in alpha.
        end.

        Case omega \leq i < alpha.
          u = f[i] = i \in alpha.
        end.
      end.
    end.

    f is a surjective function from alpha + 1 to alpha.
    proof.
      Let us show that for all j \in alpha: j \in \range(f).
        Let j \in alpha.

        Case j = 0.
          Then j = f[alpha]. Thus j \in \range(f).
        end.

        Case 0 < j < omega.
          Then j = f[j - 1]. Thus j \in \range(f).
        end.

        Case omega \leq j < alpha.
          Then j = f[j]. Thus j \in \range(f).
        end.
      end.
    end.

    f is an injective function from alpha + 1 to alpha.
    proof.
      Let us show that for all i,j \in alpha + 1 (if i \neq j then f[i] \neq f[j]).
        Let i,j \in alpha + 1. Assume i \neq j.

        Case i = alpha.
          Case j < omega.
            f[i] = 0 < j + 1 = f[j].
          end.

          Case omega \leq j < alpha.
            f[i] = 0 < j = f[j].
          end.
        end.

        Case i < omega.
          Case j = alpha.
            f[i] = i + 1 > 0 = f[j].
          end.

          Case omega \leq j.
            f[i] = i + 1 < omega \leq j = f[j].
          end.
        end.

        Case omega \leq i < alpha.
          Case j = alpha.
            f[i] = i \geq omega > 0 = f[j].
          end.

          Case j < omega.
            f[i] = i \geq omega > j + 1 = f[j].
          end.
        end.
      end.
    end.
  end.
qed.

Lemma 4023. Let kappa \in \Card. Then kappa is a limit ordinal.
Proof by contradiction.
  Assume that kappa is not a limit ordinal. kappa = 0 or kappa is a successor ordinal.

  Case kappa = 0. Obvious.

  Case kappa \neq 0.
    Take alpha such that kappa = alpha + 1. alpha \geq omega. \card(alpha + 1) = \card(alpha).
  end.
qed.

Lemma 4024. Let \card(x),\card(y) > 0. \card(x) \leq \card(y) iff there is a surjective function
from y to x.
Proof.
  If \card(x) \leq \card(y) then there is a surjective function from y to x.
  proof.
    Assume \card(x) \leq \card(y). Take an injective function f from x to y. Take z \in x. f^{-1} is
    a function from \range(f) to x.

    Define g[u] =
      case u \in \range(f) -> f^{-1}[u],
      case u \notin \range(f) -> z
    for u in y.

    g is a surjective function from y to x.
  end.

  If there is a surjective function from y to x then \card(x) \leq \card(y).
  proof.
    Let f be a surjective function from y to x. Define g[u] = choose v \in y such that f[v] = u in v
    for u in x. g is an injective function from x to y.
  end.
qed.

Lemma 4025. Let x \subseteq y. Then \card(x) \leq \card(y).

Lemma 4026. Let x \subseteq alpha. \card(x) \leq \otp(x).

Lemma 4027. Let x = Dom(f). \card(f^[x]) \leq \card(x).
Proof.
  Case \card(x) = 0.
    x = \emptyset.
  end.

  Case \card(x) \neq 0.
    \card(x) > 0. \card(f^[x]) > 0. Indeed There is y such that if y \in x then f[y] \in f^[x]. f is
    a surjective function from x to f^[x]. Hence the thesis (by 4024).
  end.
qed.


# \section{Finite, countable and uncountable sets} % chapter 5

Definition. x is finite iff \card(x) < omega.

Definition. x is infinite iff \card(x) \geq omega.

Definition. x is countable iff \card(x) \leq omega.

Definition. x is countably infinite iff \card(x) = omega.

Definition. x is uncountable iff \card(x) > omega.


Lemma 5001. x is finite iff x is not infinite.

Lemma 5002. x is countable iff x is not uncountable.

Lemma 5003. x is countably infinite iff x is countable and not finite.


# \subsection{Finite sets} % chapter 5.1

Lemma 5101. Let x be finite. Then every subset of x is finite.
Proof.
  Let y \subseteq x. \card(y) \leq \card(x) (by 4025). Hence y is finite.
qed.

Lemma 5102. Let x be finite. Then x + 1 is finite.
Proof.
  Take n such that \card(x) = n. Take a bijective function f from x to n.

  Define g[u] =
    case u \in x -> f[u],
    case u = x -> n
  for u in x + 1.

  g is a bijective function from x + 1 to n + 1.
  proof.
    g is a function from x + 1 to n + 1. \range(g) = n + 1. Thus g is a surjective function from x
    + 1 to n + 1.

    g is an injective function from x + 1 to n + 1.
    proof.
      Let us show that for all u,v \in x + 1 (if u \neq v then g[u] \neq g[v]).
        Let u,v \in x + 1. Assume u \neq v.

        Case u = x.
          g[u] = n > f[v] = g[v].
        end.

        Case v = x.
          g[u] = f[u] < n = g[v].
        end.

        Case u,v \neq x.
          g[u] = f[u] \neq f[v] = g[v].
        end.
      end.
    end.
  end.
qed.

Theorem 5103. Let x be finite. Assume that \card(y) = 1. Then x \cup y is finite.
Proof.
  There is z such that y = {z}.
  proof.
    Take a bijective function f from 1 to y. For all z z \in \range(f) iff z = f[0]. \range(f) = y.
  end.
  Take z such that y = {z}.

  Case z \in x.
    x \cup y = x. Hence \card(x \cup y) = \card(x) < omega.
  end.

  Case z \notin x.
    Define f[u] =
      case u = z -> x,
      case u \neq z -> u
    for u in x \cup y.

    f is a bijective function from x \cup y to x + 1.
    proof.
      f  is a function from x \cup y to x + 1. \range(f) = x + 1. Thus f is a surjective function
      from x \cup y to x + 1.

      f is an injective function from x \cup y to x + 1.
      proof.
        Let us show that for all i,j \in x \cup y (if i \neq j then f[i] \neq f[j]).
          Let i,j \in x \cup y. Assume i \neq j.

          Case i = z.
            Then f[i] = x \notin x (by 1615).
            f[j] = j \in x.
          end.

          Case j = z.
            Then f[i] = i \neq x = f[j].
          end.

          Case i,j \neq z.
            Then f[i] = i \neq j = f[j].
          end.
        end.
      end.
    end.

    Hence \card(x \cup y) = \card(x + 1) < omega.
  end.
qed.

Lemma 5104. Let \card(x) = n \neq 0. Let y \subseteq x and \card(y) = 1. Then \card(x \setminus y) =
n - 1.
Proof.
  There is z such that y = {z}.
  proof.
    Take z \in y.

    Let us show by contradiction that there is no u \in y such that u \neq z.
      Assume there is u \in y such that u \neq z.

      Define g[v] =
        case v = z -> 0,
        case v \neq z -> 1
      for v in y.

      g is a surjective function from y to 2. Thus 2 \leq \card(y) (by 4024).
    end.
  end.

  Take z such that y = {z}. Take a bijective function h from x to n .

  Define f[u] =
    case h[u] = n - 1 -> h[z],
    case u = z -> n - 1,
    case u \neq z and h[u] \neq n -1 -> h[u]
  for u in x.

  f is a bijective function from x to n.
  proof.
    Let us show that for all v \in \range(f) v \in n.
      Let v \in \range(f). Take u \in x such that f[u] = v.

      Case h[u] = n - 1.
        v = f[u] = h[z] \in n.
      end.

      Case u = z.
        v = f[u] = n - 1 \in n.
      end.

      Case u \neq z and u \neq n - 1.
        v = f[u] = h[u] \in n.
      end.
    end.

    Thus \range(f) \subseteq n.

    Let us show that for all v \in n  v \in \range(f).
      Let v \in n. Take u \in x such that v = h[u].

      Case h[u] = n - 1.
        v = h[u] = n - 1 = f[z]. Thus v \in \range(f).
      end.

      Case u = z.
        Take w \in x such that h[w] = n - 1. v = h[u] = f[w]. Thus v \in \range(f).
      end.

      Case h[u] \neq n - 1 and u \neq z.
        v = h[u] = f[u] \in \range(f).
      end.
    end.

    Hence n \subseteq \range(f). Thus \range(f) = n (by EXT). Therefore f is a surjective function
    from x to n.

    f is a injective function from x to n.
    proof.
      Let us show that for all u,v \in x (if u \neq v then f[u] \neq f[v]).
        Let u,v \in x. Assume u \neq v.
      end.
    end.
  end.

  \range(f \upharpoonright (x \setminus y)) = n - 1.
  proof.
    \range(f \upharpoonright (x \setminus y)) \subseteq n - 1.
    Let us show that n - 1 \subseteq \range(f \upharpoonright (x \setminus y)).
      Let us show that for all v \in n - 1 v \in \range(f \upharpoonright (x \setminus y)).
        Let v \in n - 1. Take u \in x such that f[u] = v. v \neq n - 1. u \neq z. u \in
        Dom(f \upharpoonright (x \setminus y)). Hence v = f[u] = (f \upharpoonright
        (x \setminus y))[u] \in \range(f \upharpoonright (x \setminus y)).
      end.
    end.
    Hence the thesis (by EXT).
  end.

  (3) x is a set and n is a set.
  (4) x \setminus y is a subset of x (by 1616).

  f \upharpoonright (x \setminus y) is a bijective function from x \setminus y to n - 1 (by 1614, 1,
  2, 3, 4).
qed.

Theorem 5105. Let x,y be finite. Then x \cup y is finite.
Proof.
  Let us show by induction on n that for all n (for all a (if \card(a) = n then x \cup a is finite)).
    Let n be a natural number. Let a be a set. Assume \card(a) = n.

    Case n = 0.
      a = \emptyset. Hence x \cup a = x.
    end.

    Case n \neq 0.
      (1) Take a bijective function g from a to n.
      Take z \in a such that g[z] = n - 1.
      (2) Take a set w such that w = {z}.

      \card(w) = 1. Indeed 0--{w} is a bijective function from w to 1. \card(a \setminus w) = n - 1
      (by 5104). We have \card(a \setminus w) -<- \card(a). Hence x \cup (a \setminus w) is finite.
      (x \cup (a \setminus w)) \cup w is finite (by 5103). x \cup a = (x \cup (a \setminus w)) \cup
      w. Thus x \cup a is finite.
    end.
  end.
qed.

Theorem 5106. Let x,y be finite. Then x \cap y is finite.

Theorem 5107. Let x,y be finite. Then x \times y is finite.
Proof.
  Let us show by induction on n that for all n (for all a (if \card(a) = n then x \times a is
  finite)).
    Let n be a natural number. Let a be a set. Assume \card(a) = n.

    Case n = 0. Obvious.

    Case n \neq 0.
      (1) Take a bijective function g from a to n.
      Take z \in a such that g[z] = n - 1.
      (2) Take a set w such that w = {z}.

      \card(w) = 1. Indeed 0--{w} is a bijective function from w to 1. \card(a \setminus w) = n - 1
      (by 5104). We have \card(a \setminus w) -<- \card(a). Hence x \times (a \setminus w) is finite.
      x \times a = (x \times (a \setminus w)) \cup (x \times w).

      x \times w is finite.
      proof.
        Take a bijective function f from x to \card(x). Define h[u] = choose v \in x such that u =
        (v,z) in v for u in x \times w.

        h is a bijective function from x \times w to x.
        proof.
          h is a function from x \times w to x.
          Let us show that \range(h) = x.
            \range(h) \subseteq x.

            For all u \in x u \in \range(h).
            proof.
              Let u \in x. Take v \in w such that (u,v) \in x \times w. u = h[(u,v)].
            end.

            Thus x \subseteq \range(h). Hence the thesis (by EXT).
          end.

          Thus h is a surjective function from x \times w to x. h is an injective function from x
          \times w to x.
        end.
      end.

      Hence the thesis (by 5105).
    end.
  end.
qed.

Theorem 5108. Let x,y be finite. Then x \setminus y is finite.

Theorem 5109. Let x be finite. Then the powerset of x is finite.
Proof.
  Let us show by induction on n that for all n (for all a (if \card(a) = n then the powerset of a is
  finite)).
    Let n be a natural number. Let a be a set. Assume \card(a) = n.

    Case n = 0.
      a = \emptyset. \Pow(a) = {\emptyset}.
    end.

    Case n \neq 0.
      (1) Take a bijective function g from a to n.

      Take z \in a such that g[z] = n - 1. Take a set w such that w = {z}.

      \card(w) = 1. Indeed 0--{w} is a bijective function from w to 1. \card(a \setminus w) = n - 1
      (by 5104). We have \card(a \setminus w) -<- \card(a). Hence the powerset of (a \setminus w) is
      finite. Take m such that m = \card(\Pow(a \setminus w)). Take a bijective function f from
      \Pow(a \setminus w) to m. u \setminus w \in \Pow(a \setminus w) for any u \in \Pow(a).

      For all u \in \Pow(a) (if z \notin u then u \in Dom(f)).
      proof.
        Let u \in \Pow(a). Assume z \notin u. u = u \setminus w.
      end.

      Define h[u] =
        case z \notin u -> (f[u],0),
        case z \in u -> (f[u \setminus w],1)
      for u in \Pow(a).

      h is a injective function from \Pow(a) to m \times 2.
      proof.
        Let us show that \range(h) \subseteq m \times 2.
          Let us show that for all v \in \range(h) v \in m \times 2.
            Let v \in \range(h). Take u \in Dom(h) such that h[u] = v.

            Case z \notin u.
              v = h[u] = (f[u],0). f[u] \in \range(f) = m. 0 \in 2. Hence v \in m \times 2.
            end.

            Case z \in u.
              v = h[u] = (f[u \setminus w],1). f[u \setminus w] \in \range(f) = m. 1 \in 2. Hence v
              \in m \times 2.
            end.
          end.
        end.

        Thus h is a function from \Pow(a) to m \times 2.

        Let us show that for all u,v \in \Pow(a) (if u \neq v then h[u] \neq h[v]).
          Let u,v \in \Pow(a). Assume u \neq v.

          Case z \notin u and z \notin v.
						u,v \in \Pow(a \setminus w). f[u] \neq f[v]. Indeed f is an injective function from
						\Pow(a \setminus w) to m. Thus (f[u],0) \neq (f[v],0). Hence h[u] = (f[u],0) \neq
						(f[v],0) = h[v].
          end.

          Case z \in u and z \in v.
            u \setminus w \neq v \setminus w.
            proof by contradiction.
              Assume u \setminus w = v \setminus w. Then (u \setminus w) \cup w = (v \setminus w)
              \cup w. (u \setminus w) \cup w = u. (v \setminus w) \cup w = v. Thus u = v.
              Contradiction.
            end.

            [timelimit 10]
            Therefore f[u \setminus w] \neq f[v \setminus w]. Indeed f is an injective function from
            \Pow(a \setminus w) to m. Thus (f[u \setminus w],1) \neq (f[v \setminus w],1). Hence
            h[u] = (f[u \setminus w],1) \neq (f[v \setminus w],1) = h[v].
          end.

          Case z \notin u and z \in v.
            h[u] = (f[u],0) \neq (f[v \setminus w],1) = h[v].
          end.

          Case z \in u and z \notin v.
            h[u] = (f[u \setminus w],1) \neq (f[v],0) = h[v].
          end.
        end.
      end.

      (6) m is finite.
      (7) 2 is finite.

      m \times 2 is finite (by 5107, 6, 7). \Pow(a) \preccurlyeq m \times 2. Thus \card(\Pow(a))
      \leq \card(m \times 2) (by 4016). Hence \card(\Pow(a)) < omega.
    end.
  end.
qed.

Theorem 5110. Let x be finite. Let every element of x be finite. Then \bigcup x is finite.
Proof.
  Let us show by induction on n that for all n (for all a (if \card(a) = n and every element of a is
  finite then \bigcup a is finite)).
    Let n be a natural number. Let a be an set. Assume that every element of a is finite. Assume
    that \card(a) = n.

    Case n = 0.
      a = \emptyset. \bigcup a = \emptyset. \bigcup a is finite.
    end.

    Case n \neq 0.
      (1) Take a bijective function g from a to n.

      Take b \in a such that g[b] = n - 1. Take a set y  such that y = {b}.

      \card(y) = 1. Indeed 0--{y} is a bijective function from y to 1.

      \card(a \setminus y) = n - 1 (by 5104). Every element of a \setminus y is finite.  We have
      \card(a \setminus y) -<- \card(a). \bigcup(a \setminus y) is finite. b is finite. b \cup
      (\bigcup(a \setminus y)) is finite. \bigcup a = (b \cup (\bigcup(a \setminus y))). \bigcup a
      is finite.
    end.
  end.
qed.

Theorem 5111. Let x be finite. For all f (f: x \hookrightarrow x => f: x \twoheadrightarrow x).
Proof.
 Let us show by induction on n that for all n (for all a for all b (if \card(a) = n and \card(b) = n
 then for all f (f: a \hookrightarrow b => f: a \twoheadrightarrow b))).
    Let n be a natural number. Let a be an set. Let b be an set. Assume \card(a) = n. Assume
    \card(b) = n.

    Case n = 0.
      Take f such that f: a \hookrightarrow b. Dom(f) = a. \range(f) \subseteq b. b = \emptyset.
      \range(f) = \emptyset. \range(f) = b. f: a \twoheadrightarrow b.
    end.

    Case n \neq 0.
      Take c \in a. Let f: a \hookrightarrow b. Take y such that y = {c}.

      \card(y) = 1. Indeed 0--{y} is a bijective function from y to 1. Take z such that z = {f[c]}.
      \card(z) = 1. Indeed 0--{z} is a bijective function from z to 1.

      f \upharpoonright (a \setminus y) is an injective function from  a \setminus y to b. There is
      no d \in a \setminus y such that (f \upharpoonright (a \setminus y))[d] = f[c].

      f \upharpoonright (a \setminus y) is an injective function from  a \setminus y to b \setminus
      z.
      proof.
        Let us show that for all u \in a \setminus y (f \upharpoonright (a \setminus y))[u] \in b
        \setminus z.
          Let u \in a \setminus y. u \neq c. Thus f[u] \neq f[c]. Hence f[u] \notin z.
        end.
        Thus f \upharpoonright (a \setminus y) is a function from a \setminus y to b \setminus z.
      end.

      \card(a \setminus y) = n - 1 (by  5104). \card(b \setminus z) = n - 1 (by  5104). We have
      \card(a \setminus y) -<- \card(a). We have \card(b \setminus z) -<- \card(b). f
      \upharpoonright (a \setminus y) is a surjective function from a \setminus y to b \setminus z.
      \range(f \upharpoonright (a \setminus y)) = b \setminus z.

      \range(f) = b.
      proof.
        \range(f) \subseteq b.

        Let us show that for all u \in b u \in \range(f).
          Let u \in b.

          Case u = f[c]. Obvious.

          Case u \neq f[c].
            u \in b \setminus z. Take v \in a \setminus y such that (f \upharpoonright (a \setminus
            y))[v] = u. (f \upharpoonright (a \setminus y))[v] = f[v].
          end.
        end.
      end.

      Hence f is a surjective function from a to b.
    end.
  end.
qed.

Theorem 5112. Let x be finite. For all f (f: x \twoheadrightarrow x => f: x \hookrightarrow x).
Proof.
  Let f: x \twoheadrightarrow x.  Define g[u] = choose an element i of x such that (f[i] = u) in i
  for u in x. g: x \hookrightarrow x. g: x \twoheadrightarrow x (by 5111). f: x \hookrightarrow x.
qed.

Theorem 5113. If x \subseteq \Ord and x is finite and nonempty then there is y \in x such that y
\geq z for all z \in x.
Proof.
  Let x \subseteq \Ord. Assume that x is finite and nonempty.

	Let us show by induction on n that for all n (for all a (if \card(a) = n and a is nonempty and
	a \subseteq \Ord then (\bigcup(a) \in a and \bigcup(a) \geq z for all z \in a))).
    Let n be a natural number. Let a be an set. Assume a \subseteq \Ord. Assume \card(a) = n. a is
    finite.

    Case n = 1.
			Take c \in a. a \sim 1. Take f : 1 \leftrightarrow a. c = f[0]. \bigcup a = c. Indeed a = {c}.
			\bigcup a \geq c. \bigcup a \geq z for all z \in a.
    end.

    Case n \geq 2.
      Take d \in a. Take b such that b = {d}. \card(b) = 1. Indeed 0--{b} is a bijective function
      from b to 1. \card(a \setminus b) = n - 1 (by  5104). a \setminus b is nonempty. a \setminus b
      is finite. We have \card(a \setminus b) -<- \card(a). \bigcup(a \setminus b) \in a \setminus b.
      \bigcup(a \setminus b) \geq z for all z \in (a \setminus b). \bigcup a = \bigcup(a \setminus
      b) \cup d.

      \bigcup(a) \in a.
      proof.
      	d < \bigcup(a \setminus b) or d = \bigcup(a \setminus b) or d > \bigcup(a \setminus b).

				Case d < \bigcup(a \setminus b).
        	\bigcup(a \setminus b) = \bigcup(a \setminus b) \cup d. \bigcup a = \bigcup(a \setminus b).
        	\bigcup a \geq z for all z \in a. \bigcup a \in a.
       	end.

       	Case d = \bigcup(a \setminus b).
       		\bigcup(a \setminus b) = \bigcup(a \setminus b) \cup d. \bigcup a = \bigcup(a \setminus b).
       	 	\bigcup a \geq z for all z \in a.	\bigcup a \in a.
       	end.

       	Case d > \bigcup (a \setminus b).
       		d = \bigcup(a \setminus b) \cup d. \bigcup a = d.

       		d \geq z for all z \in a \setminus b.
       		proof.
       		 Let z \in a \setminus b. z \neq d.
       		end.

       		\bigcup a \geq z for all z \in (a \setminus b). d \geq z for all z \in b. \bigcup a \geq z
       		for all z \in b. d \geq z for all z \in a. \bigcup a \geq z for all z \in a. d \in a.
       		\bigcup a \in a.
       	end.
      end.
    end.
  end.

	x \subseteq \Ord. \card(x) = n for some n. x is nonempty.	Hence \bigcup x \in x.
qed.


# \subsection{Countable sets} % chapter 5.2

[prove off]

Theorem 5201. Let x be countable. Then every subset of x is countable.

Theorem 5202. Let x be countable. Then x + 1 is countable.

Theorem 5203. Let x be countable. Assume that \card(y) = 1. Then x \cup y is countable.

Theorem 5204. Let x,y be countable. Then x \cup y is countable.

Theorem 5205. Let x,y be countable. Then x \cap y is countable.

Theorem 5206. Let x,y be countable. Then x \times y is countable.

Theorem 5207. Let x,y be countable. Then x \setminus y is countable.

Theorem 5208. Let x be countable. Let every element of x be countable. Then \bigcup x is countable.

[/prove]


# \subsection{Uncountable sets} % chapter 5.3

Theorem 5301. There is an injective function from x to the powerset of x.
Proof.
  Define f[i] = {u | u = i} for i in x. f is an injective function from x to the powerset of x.
qed.

Theorem 5302. There is no injective function from the powerset of x to x.
Proof by contradiction.
  Let g be an injective function from the powerset of x to x. Define c = {u \in Dom(g^{-1}) | u
  \notin g^{-1}[u]}. Dom(g^{-1}) is a subset of x (by 1611). Thus c is a subset of  x. g[c] \in c
  iff g[c] \notin g^{-1}[g[c]] = c. Contradiction.
qed.

# Cantor's Theorem
Theorem 5303. \card(x) < \card(\Pow(x)).
Proof.
  Let us show that \card(x) \leq \card(\Pow(x)).
    There is an injective function f from x to the powerset of x (by 5301).
    (1) Thus x \preccurlyeq \Pow(x).
    Hence the thesis (by 4016, 1).
  end.

  Let us show that \card(x) \neq \card(\Pow(x)).
    Assume the contrary. Take a bijective function f from \card(x) to \card(\Pow(x)).
    (2) Thus there is an injective function from the powerset of x to x.
    Contradiction (by 5302, 2).
  end.
qed.


# \section{The alephs} % chapter 6

Let lambda denote a limit ordinal.


Lemma 6001. For all alpha there is kappa \in \Card such that kappa > alpha.
Proof.
  Let alpha be an ordinal.

  Case alpha < omega. Obvious.

  Case alpha \geq omega.
    Take kappa such that kappa = \card(\Pow(alpha)). kappa > alpha.
  end.
qed.

Lemma 6002. Let x \subseteq \Cd. \bigcup x \in \Cd.
Proof.
  \bigcup x is an ordinal. Take alpha such that alpha = \bigcup x. \card(alpha) \leq alpha.

  Let us show by contradiction that not \card(alpha) < alpha.
    Assume that \card(alpha) < alpha. Take y \in x such that \card(alpha) < y. Then y \leq alpha and
    \card(y) \leq \card(alpha) < y. y is a cardinal. Thus \card(y) = y. Contradiction.
  end.
qed.


# This definition is necessary to define alpha^{+}.
Definition. \CardsGreaterThan(alpha) = {kappa \in \Cd | alpha < kappa \leq \card(\Pow(alpha))}.

# This lemma is necessary to fulfill the assumptions of the definitions of \min in the next
# definition.
Lemma. \CardsGreaterThan(alpha) is nonempty and \CardsGreaterThan(alpha) \subseteq \Ord.

Definition. alpha^{+} = \min(\CardsGreaterThan(alpha)).


Lemma 6003. alpha^{+} \in \Cd.

Lemma 6004. alpha < alpha^{+}.

Lemma 6005. There is no mu such that kappa < mu < kappa^{+}.
Proof by contradiction.
	Assume the contrary. Take mu such that kappa < mu < kappa^{+}. kappa < mu. kappa^{+} \leq
	\card(\Pow(kappa)). mu \leq \card(\Pow(kappa)). mu \in \CardsGreaterThan(kappa). kappa^{+} < mu.
	Contradiction.
qed.



Signature. aleph--{alpha} is a cardinal.

Definition. AlephsLessThan(lambda) = {aleph--{alpha} | alpha \in lambda}.


Axiom. aleph--{0} = omega.

Axiom. aleph--{alpha + 1} = aleph--{alpha}^{+}.

Axiom. aleph--{lambda} = \bigcup AlephsLessThan(lambda).


Definition. A successor cardinal is an infinite cardinal kappa such that kappa = aleph--{alpha + 1}
for some alpha.

Definition. A limit cardinal is an infinite cardinal kappa such that kappa = aleph--{lambda} for
some lambda.


[prove off]

Lemma 6006. x \in \Card iff x = aleph--{alpha} for some alpha.

Lemma 6007. There is kappa such that kappa = aleph--{kappa}.

[/prove]


# \section{Cardinal Arithmetic} % chapter 7

Definition. ^{x}{y} = {function f | f is a function from x to y}.

Definition. ZERO  = {0}.
Definition. ONE   = {1}.
Definition. TWO   = {2}.
Definition. THREE = {3}.

# We cannot use "+" to denote cardinal addition since "+" is already used to denote the "+ 1"
# operation on arbitrary sets.
Definition. kappa \plus mu = \card((kappa \times ZERO) \cup (mu \times ONE)).

Definition. kappa \cdot mu = \card(kappa \times mu).

Definition. kappa^mu = \card(^{mu}{kappa}).


Lemma 7001. kappa \plus mu is a cardinal.

Lemma 7002. kappa \cdot mu is a cardinal.

Lemma 7003. kappa^mu is a cardinal.


[prove off]

Lemma 7004. (kappa \plus mu) \plus nu = kappa \plus (mu \plus nu).

Lemma 7005. kappa \plus mu = mu \plus kappa.

Lemma 7006. kappa \plus 0 = kappa = 0 \plus kappa.


Lemma 7007. (kappa \cdot mu) \cdot nu = kappa \cdot (mu \cdot nu).

Lemma 7008. kappa \cdot mu = mu \cdot kappa.

Lemma 7009. kappa \cdot 1 = kappa = 1 \cdot kappa.


Lemma 7010. kappa \cdot (mu \plus nu) = (kappa \cdot mu) \plus (kappa \cdot nu).

Lemma 7011. (mu \plus nu) \cdot kappa = (mu \cdot kappa) \plus (nu \cdot kappa).


Lemma 7012. kappa^0 = 1.

Lemma 7013. Let kappa \neq 0. Then 0^kappa = 0.

Lemma 7014. kappa^1 = kappa.

Lemma 7015. 1^kappa = 1.

Lemma 7016. kappa^(mu \plus nu) = (kappa^mu) \cdot (kappa^nu).

Lemma 7017. kappa^(mu \cdot nu) = (kappa^mu)^nu.


Lemma 7018. n + 1 = n \plus 1.

Lemma 7019. If mu \leq nu then mu^kappa \leq nu^kappa.

[/prove]


# \subsection{Further cardinal arithmetic} % chapter 7.1

Axiom 7101. Let kappa \in \Card. There is a bijective function from kappa \times kappa to kappa.


Definition. \max(kappa,mu) = kappa \cup mu.

Lemma 7102. \max(kappa,mu) \in \Cd.

Lemma 7103. Let kappa \in \Card. kappa \cdot kappa = kappa.
Proof.
  \card(kappa \times kappa) = \card(kappa). Indeed kappa \times kappa \sim kappa (by 7101).
  Hence the thesis. Indeed \card(kappa) = kappa.
qed.

Lemma 7104. Let kappa \in \Card. Let mu \in \Cd. Assume mu \neq 0. kappa \cdot mu = \max(kappa,mu).
Proof.
  Define f[i] = (i,0) for i in kappa. f is an injective function from kappa to kappa \times mu.
  Hence kappa \leq kappa \cdot mu. Define g[j] = (0,j) for j in mu. g is an injective function from
  mu to kappa \times mu. Hence mu \leq kappa \cdot mu. \max(kappa,mu) \leq kappa \cdot mu.

  kappa \cdot mu \leq \max(kappa,mu) \cdot \max(kappa,mu).
  proof.
    \id--{kappa \times mu} is an injective function from kappa \times mu to kappa \times mu. kappa
    \times mu is a subset of \max(kappa,mu) \times \max(kappa,mu).
  end.

  \max(kappa,mu) \cdot \max(kappa,mu) = \max(kappa,mu).
qed.

Corollary 7105. Let kappa \in \Cd. Let mu \in \Card. Assume kappa \neq 0. kappa \cdot mu =
\max(kappa,mu).
Proof.
  kappa \cdot mu = mu \cdot kappa (by 7008). \max(kappa,mu) = \max(mu,kappa).
qed.

Lemma 7106. Let kappa \in \Card. Let mu \in \Cd. kappa \plus mu = \max(kappa,mu).
Proof.
  (kappa \times ZERO) \cup (mu \times ONE) \subseteq \max(kappa,mu) \times \max(kappa,mu).

  \max(kappa,mu) \leq kappa \plus mu.
  proof.
    Define f[(i,j)] = i for (i,j) in (kappa \times ZERO) \cup (mu \times ONE). kappa \subseteq
    \max(kappa,mu) and mu \subseteq \max(kappa,mu).

    \range(f) \subseteq \max(kappa,mu).
    proof.
      Let us show that for all u \in \range(f) u \in \max(kappa,mu).
        Let u \in \range(f). Take v \in (kappa \times ZERO) \cup (mu \times ONE) such that f[v] = u.

        Case v = (j,0) for some j \in kappa.
          Take j \in kappa such that v = (j,0). u = f[v] = f[(j,0)] = j \in kappa.
        end.

        Case v = (j,1) for some j \in mu.
          Take j \in mu such that v = (j,1). u = f[v] = f[(j,1)] = j \in mu.
        end.
      end.
    end.

    f is a surjective function from (kappa \times ZERO) \cup (mu \times ONE) to \max(kappa,mu).

    (1) \card(\max(kappa,mu)) = \max(kappa,mu) > 0.
    (2) kappa \plus mu > 0.
    proof.
      kappa is nonempty. Take alpha \in kappa. Then (alpha,0) \in (kappa \times ZERO) \cup (mu
      \times ONE). Therefore kappa \plus mu \neq 0.
    end.

    Hence \max(kappa,mu) \leq kappa \plus mu (by 4024, 1, 2).
  end.

  kappa \plus mu \leq \max(kappa,mu) \cdot \max(kappa,mu). \max(kappa,mu) \cdot \max(kappa,mu) =
  \max(kappa,mu).
qed.

Corollary 7107. Let kappa \in \Cd. Let mu \in \Card. kappa \plus mu = \max(kappa,mu).
Proof.
  kappa \cdot mu = mu \cdot kappa (by 7008). \max(kappa,mu) = \max(mu,kappa).
qed.

Lemma 7108. Let kappa \in \Card. Let n be a natural number. Assume 1 \leq n. kappa^n = kappa.
Proof.
  Let us show by induction on m that for all m (if 1 \leq m then kappa^m = kappa).
    Let m be a natural number. Assume 1 \leq m.

    Case m = 0. Obvious.

    Case m = 1. Obvious.

    Case m \geq 1.
      m - 1 -<- m. Hence kappa^(m-1) = kappa.

      (1) m - 1 is a natural number.

      (m - 1) + 1 = (m - 1) \plus 1 (by 7018, 1).

      (2) m - 1 is a cardinal and 1 is a cardinal.

      kappa^m = kappa^((m-1)+1). kappa^((m-1)+1) = kappa^((m-1) \plus 1). kappa^((m-1) \plus 1) =
      (kappa^(m-1)) \cdot (kappa^1) (by 7016, 2). (kappa^(m-1)) \cdot (kappa^1) = (kappa^(m-1))
      \cdot kappa. (kappa^(m-1)) \cdot kappa = (kappa^(m-1)) \cdot kappa = kappa \cdot kappa = kappa.
    end.
  end.
qed.

Lemma 7109. Let kappa \in \Card. Let 2 \leq mu \leq 2^kappa. mu^kappa = 2^kappa.
Indeed 2^kappa \leq mu^kappa \leq (2^kappa)^kappa = 2^(kappa \cdot kappa) = 2^kappa.


# \section{Cofinality} % chapter 8

Definition. Let x \subseteq lambda. x is cofinal in lambda iff for
all alpha \in lambda there is beta \in x such that alpha < beta.

Let a cofinal subset of x stand for a subset of x that is cofinal in x.

# This definition is necessary to define the \cofinality of lambda.
Definition. OtpOfCofSubsets(lambda) = {\otp(x) | x \subseteq lambda and x is cofinal in lambda}.

# This lemma is necessary to fulfill the assumptions of the definitions of \min in the next
# definition.
Lemma. OtpOfCofSubsets(lambda) is nonempty and OtpOfCofSubsets(lambda) \subseteq \Ord.
Proof.
  lambda is cofinal in lambda. Indeed for all alpha \in lambda alpha + 1 \in lambda.
  Hence OtpOfCofSubsets(lambda) is nonempty.
qed.

Definition. The cofinality of lambda is \min(OtpOfCofSubsets(lambda)).
Let \cof(x) stand for the cofinality of x.


#Lemma 8001. \cof(lambda) \in \Card.
#Proof.
#  \cof(lambda) is a cardinal.
#  Let us show that \cof(lambda) \geq omega.
#    Assume the contrary. \cof(lambda) < omega. Take x \subseteq lambda such that (x is cofinal in
#    lambda and x is finite). x \subseteq \Ord.
#
#[depthlimit 1][timelimit 9]
#
#    Take y \in x such that for all z \in x y \geq z (by 5113). Indeed x is nonempty and finite.
#
#[/depthlimit][/timelimit]
#
#    y + 1 \in lambda and there is no z \in x such that z > y + 1. Contradiction.
#  end.
#qed.

#Lemma 8002. \cof(lambda) \leq \card(lambda).

#Lemma 8003. \cof(lambda) \subseteq lambda.
#Proof.
#  \cof(lambda) \subseteq \card(lambda) (by 8002). \card(lambda) \subseteq lambda.
#qed.

Lemma 8004. Let x \subseteq lambda. x is cofinal in lambda iff \bigcup x = lambda.

Lemma 8005. There is a cofinal subset x of lambda such that \cof(lambda) = \card(x).
Proof.
  Take a cofinal subset x of lambda such that \otp(x) = \cof(lambda). \otp(x) \geq \card(x).

  Let us show that \otp(x) \leq \card(x).
    Take a bijective function f from \card(x) to x. Define h[i] = {f[j] | j \in i} for i in \card(x).
    Define g[i] = \bigcup h[i] for i in \card(x). For all i \in \card(x) g[i] is an ordinal. Indeed
    for all i \in \card(x) h[i] \subseteq lambda.

    For all i,j \in \card(x) if i < j then g[i] \leq g[j].
    proof.
      Let i,j \in \card(x). Assume that i < j. \bigcup h[i] \subseteq \bigcup h[j]. Thus g[i]
      \subseteq g[j]. Thus g[i] \leq g[j].
    end.

    g is a function from \card(x) to lambda.
    proof.
      Let us show that for all i \in \card(x) g[i] \in lambda.
        Let i \in \card(x).

        For all j \in \card(x) g[j] \in lambda + 1.
				proof.
          Let j \in \card(x). g[j] \leq lambda. Indeed \bigcup h[j] \subseteq lambda.
          Case g[j] < lambda. Obvious.
          Case g[j] = lambda. Obvious.
        end.

        g[i] \neq lambda.
        proof.
          Let us show by induction on alpha that for all alpha \in \card(x) g[alpha] \neq lambda.
            Let alpha \in \card(x).

            Case alpha = 0. Obvious.

            Case alpha is an successor ordinal.
              Take beta such that alpha = beta + 1. beta -<- alpha. Thus g[beta] \neq lambda. beta
              \in \card(x). \bigcup h[alpha] = (\bigcup h[beta]) \cup f[beta]. Thus g[alpha] =
              g[beta] \cup f[beta]. g[beta] \in lambda and f[beta] \in lambda.
            end.

            Case alpha is a limit ordinal.
              Assume that g[alpha] = lambda. \bigcup h[alpha] = lambda. h[alpha] is cofinal in
              lambda.

              alpha is a subset of lambda.

              alpha is not cofinal in lambda.
              proof.
                Assume the contrary. Then \otp(alpha) < \otp(x). Contradiction.
              end.


              alpha + 1 \in \card(x). Then g[alpha] < g[alpha + 1]. Hence g[alpha] < lambda.

#              \card(h[alpha]) \leq \otp(alpha).
#              proof.
#                alpha \subseteq \otp(x). Define k[beta] = f[beta] for beta in alpha. k is a
#                function from alpha to h[alpha].
#
#                Let us show that for all u \in h[alpha] u \in \range(k).
#                  Let u \in h[alpha]. Take j \in alpha such that u = f[j].
#                end.
#
#                h[alpha] = \range(k). Thus k is a surjective function from alpha to h[alpha].
#                \card(alpha) > 0. Indeed alpha is nonempty. f[beta] \in h[alpha] for some beta \in
#                alpha. Thus h[alpha] is nonempty. Hence \card(h[alpha]) > 0. Indeed \card(h[alpha])
#                \neq 0.Therefore \card(h[alpha]) \leq \card(alpha) (by 4024).
#              end. alpha \subseteq lambda. alpha is cofinal in lambda.
#
#              \otp(alpha) < \otp(x). Indeed alpha < \otp(x). Thus \card(h[alpha]) < \otp(x).
#              Hence \card(h[alpha]) < \otp(x) = \cof(lambda). For all cofinal subsets z of lambda
#              \otp(x) \leq \otp(z). Contradiction. Indeed not \otp(x) \leq \otp(h[alpha]).
            end.
          end.
        end.
      end.
    end.



    For all i \in \card(x) g[i] is an ordinal.

    \range(g) is cofinal in lambda.
    proof.
      Let alpha \in lambda. Take beta \in x such that beta > alpha + 1. Take i \in \card(x) such
      that f[i] = beta. f[i] \in h[i + 1]. alpha \in \bigcup h[i + 1]. g[i + 1] > alpha.
    end.

    Define y = {i \in \card(x) | for all j \in i g[j] < g[i]}. y is a subset of \card(x).

    The restriction of g to y is an order isomorphism from y to \range(g).
    proof.
      g \upharpoonright y is a function from y to \range(g).

      \range(g \upharpoonright y) = \range(g).
      proof.
        Let us show that for all u \in \range(g) u \in \range(g \upharpoonright y).
          Let u \in \range(g). Define z = {v \in \card(x) | g[v] = u}. \min(z) \in \card(x) and
          \min(z) is a ordinal. There is no i \in z such that g[i] < g[\min(z)]. For all j \in
          \min(z) j \in \card(x). Thus for all j \in \card(x) if j < \min(z) then g[j] < g[\min(z)].
          Indeed for all j \in \card(x) if j < \min(z) then j \notin z. g[\min(z)] = u. g[\min(z)]
          \in \range(g \upharpoonright y). Thus u \in \range(g \upharpoonright y).
        end.
      end.

      Thus g \upharpoonright y is a surjective function from y to \range(g). g \upharpoonright y is
      an injective function from y to \range(g). Indeed for all i,j \in y if i \neq j then g[i] \neq
      g[j]. Hence  g \upharpoonright y is a bijective function from y to \range(g). For all i,j \in
      y (i < j iff (g \upharpoonright y)[i] < (g \upharpoonright y)[j]).
    end.

    \otp(y) = \otp(\range(g)).
    proof.
      Take an order isomorphism p from \otp(y) to y. Take an order isomorphism q from \range(g) to
      \otp(\range(g)). (g \upharpoonright y) \circ p is a bijective function from
      \otp(y) to \range(g) (by 1605). (g \upharpoonright y) \circ p is an order isomorphism from
      \otp(y) to \range(g). Thus q \circ ((g \upharpoonright y) \circ p) is a bijective function
      from \otp(y) to \otp(\range(g)) (by 1605). Indeed \otp(y),\otp(\range(g)) are sets and q is a
      bijective function from \range(g) to \otp(\range(g)). (q \circ ((g \upharpoonright y) \circ
      p))[i] is an ordinal for every i \in \otp(y).

      For all i,j \in \otp(y) (i < j iff (q \circ ((g \upharpoonright y) \circ p))[i] < (q \circ ((g
      \upharpoonright y) \circ p))[j]).
      proof.
        Let i,j \in \otp(y).

        Let us show that if i < j then (q \circ ((g \upharpoonright y) \circ p))[i] < (q \circ ((g
        \upharpoonright y) \circ p))[j].
          Assume i < j. Then ((g \upharpoonright y) \circ p)[i] < ((g \upharpoonright y) \circ p)[j].
        end.

        Let us show that if (q \circ ((g \upharpoonright y) \circ p))[i] < (q \circ ((g
        \upharpoonright y) \circ p))[j] then i < j.
          Assume (q \circ ((g \upharpoonright y) \circ p))[i] < (q \circ ((g \upharpoonright y)
          \circ p))[j]. Then q[((g \upharpoonright y) \circ p)[i]] < q[((g \upharpoonright y) \circ
          p)[j]]. Thus ((g \upharpoonright y) \circ p)[i] < ((g \upharpoonright y) \circ p)[j].
        end.
      end.

      Hence q \circ ((g \upharpoonright y) \circ p) is an order isomorphism from \otp(y) to
      \otp(\range(g)).
    end.

    The restriction of g to y is an order isomorphism from y to \range(g).
    \otp(x) \leq \otp(\card(x)).
    [timelimit 3] Hence the thesis.
  end.
qed.


# \subsection{Regularity} % chapter 8.1

Definition. lambda is regular iff \cof(lambda) = lambda.

Definition. lambda is singular iff \cof(lambda) \neq lambda.


Lemma 8101. lambda is regular iff \card(x) = lambda for every cofinal subset x of lambda.

Lemma 8102. \cof(lambda) is regular.
Proof.
  \cof(\cof(lambda)) \leq \cof(lambda).

  Let us show that \cof(lambda) \leq \cof(\cof(lambda)).
    Take x \subseteq lambda such that x is cofinal in lambda and \otp(x) = \cof(lambda). Take an
    order isomorphism f from \cof(lambda) to x. Take y \subseteq \cof(lambda) such that y is cofinal
    in \cof(lambda) and \otp(y) = \cof(\cof(lambda)). Take an order isomorphism g from
    \cof(\cof(lambda)) to y. f \circ g is a function from \cof(\cof(lambda)) to x (by 1603).  Take z
    such that z = (f \circ g)^[\cof(\cof(lambda))]. z = \range(f \circ g). Thus z \subseteq lambda.

    f \circ g is an order isomorphism from \cof(\cof(lambda)) to z.
    proof.
      f \circ g is a surjective function from \cof(\cof(lambda)) to z. f \circ g is an injective
      function from \cof(\cof(lambda)) to z. Hence f \circ g is a bijective function from
      \cof(\cof(lambda)) to z. For all i,j \in \cof(\cof(lambda)) (i < j iff (f \circ g)[i] < (f
      \circ g)[j]).
    end.

    z is cofinal in lambda.
    proof.
      Let alpha \in lambda. Take u \in x such that u > alpha. Take v \in \cof(lambda) such that
      f[v] = u. Take w \in y such that w > v. Take t \in \cof(\cof(lambda)) such that g[t] = w.
      alpha < f[g[t]].
    end.

    \otp(z) \leq \cof(\cof(lambda)). \cof(lambda) \leq \otp(z).
  end.
qed.

Theorem 8103.
Let kappa \in \Card. kappa^{+} is regular.
Proof.
  Assume the contrary. Take a cofinal subset x of kappa^{+} such that \card(x) \neq kappa^{+}.
  \card(x) < kappa^{+}. Then \card(x) \leq kappa. Take a surjective function f from kappa to x (by
  4024). Indeed \card(x),\card(kappa) > 0 and \card(x) \leq \card(kappa).

  Define g[i] =
  	Case i has an element -> Choose a surjective function h from kappa to i in h,
  	Case i has no element -> 0--{kappa}
  for i in kappa^{+}.

  For any xi \in kappa g[f[xi]] is a function and Dom(g[f[xi]]) = kappa.
  proof.
    Let xi \in kappa. g[f[xi]] is a function. Indeed f[xi] \in kappa^{+}.

    Case f[xi] is nonempty.
      Dom(g[f[xi]]) = kappa.
    end.

    Case f[xi] is empty.
      Dom(g[f[xi]]) = kappa.
    end.
  end.

  [checktime 2][checkdepth 3]

  Define h[(xi,zeta)] = g[f[xi]][zeta] for (xi,zeta) in kappa \times kappa.

  [/checktime][/checkdepth]

  Let us show that h is a surjective function from kappa \times kappa to kappa^{+}.
  	Dom(h) = kappa \times kappa. Every element of kappa^{+} is an element of h^[kappa \times kappa].
  	proof.
  		Let n be an element of kappa^{+}. Take an element xi of kappa such that n < f[xi]. Take an
  		element zeta of kappa such that g[f[xi]][zeta] = n. Then n = h[(xi,zeta)]. Therefore the
  		thesis. Indeed (xi,zeta) is an element of kappa \times kappa.
		end.

		Every element of h^[kappa \times kappa] is an element of kappa^{+}.
		proof.
			Let n be an element of h^[kappa \times kappa]. We can take elements a,b of kappa such that n
			= h[(a,b)].

			Case f[a]is nonempty.
			  h[(a,b)]=g[f[a]][b]. \range(g[f[a]]) \in kappa^{+}. g[f[a]][b] \in kappa^{+}.
			end.

			Case f[a]is empty.
			  h[(a,b)]=g[f[a]][b]. g[f[a]][b]=0. 0 \in kappa^{+}.
			end.
		end.
	end.

  kappa^{+} \leq kappa.
	proof.
	  \card(kappa \times kappa)=kappa. \card(kappa^{+}),\card(kappa \times kappa) > 0.
	  \card(kappa^{+}) \leq \card(kappa).
	end.

  Contradiction.
qed.


# \subsection{Cofinality of Aleph Numbers} % chapter 8.2

[prove off]

Lemma 8201. aleph--{0} is regular.

Lemma 8202. \cof(aleph--{lambda}) = \cof(lambda).

Lemma 8203. \cof(aleph--{omega}) = aleph--{0}.

[/prove]


# \subsection{Koenig's Lemma} % chapter 8.3

[synonym sequence/-s]


Definition. A sequence of cardinals on alpha is a function f such that Dom(f) = alpha and f[x] is a
cardinal for every element x of alpha.

Definition. Let kappa be a sequence of cardinals on alpha. SumSet(kappa,alpha) =
{(n,i) | i \in alpha and n \in kappa[i]}.

Definition. Let kappa be a sequence of cardinals on alpha. \Sum(kappa,alpha) =
\card(SumSet(kappa,alpha)).

Definition. Let kappa be a sequence of cardinals on alpha. ProdSet(kappa,alpha) =
{function f | Dom(f) = alpha and (f[i] \in kappa[i] for every element i of alpha)}.

Definition. Let kappa be a sequence of cardinals on alpha. \Prod(kappa,alpha) =
\card(ProdSet(kappa,alpha)).


Lemma 8301. Let kappa be a sequence of cardinals on alpha. \Sum(kappa,alpha) is a cardinal.

Lemma 8302. Let kappa be a sequence of cardinals on alpha. \Prod(kappa,alpha) is a cardinal.

Lemma 8303. Let lambda be a sequence  of cardinals on alpha. Assume that lambda[i] has an element
for every element i of alpha. ProdSet(lambda, alpha) has an element.
Proof.
  Define f[i] = choose an element v of lambda[i] in v for i in alpha. Then f is an element of
  ProdSet(lambda,alpha).
qed.

# Koenig's Theorem
Theorem 8304. Let kappa, lambda be sequences of cardinals on alpha. Assume that for every element i
of alpha kappa[i] < lambda[i]. Then \Sum(kappa,alpha) < \Prod(lambda,alpha).
Proof.
  Assume the contrary. \Sum(kappa,alpha) is an ordinal. \Prod(lambda,alpha)is an ordinal.
  \Prod(lambda,alpha) < \Sum(kappa,alpha) or \Sum(kappa,alpha) < \Prod(lambda,alpha) or
  \Sum(kappa,alpha) = \Prod(lambda,alpha). Thus \Prod(lambda,alpha) \leq \Sum(kappa,alpha).

  Take a function G from SumSet(kappa,alpha) to ProdSet(lambda,alpha).
  proof.
    ProdSet(lambda, alpha) has an element (by 8303). Take x \in ProdSet(lambda, alpha). Define G[i]
    = x for i in SumSet(kappa,alpha).
  end.

  Define Diag[i] = {G[(n,i)][i] | n is an element of kappa[i]} for i in alpha.

  For every element i of alpha \card(Diag[i]) < lambda[i].
  proof.
    Let i \in alpha. Define F[n] = G[(n,i)][i] for n in kappa[i]. F^[kappa[i]] \subseteq Diag[i].
    Diag[i] \subseteq F^[kappa[i]]. Thus F^[kappa[i]] = Diag[i] (by EXT). \card(F^[kappa[i]]) \leq
    \card(kappa[i]) (by 4027). Hence \card(Diag[i]) = \card(F^[kappa[i]]) \leq \card(kappa[i]) =
    kappa[i] < lambda[i].
  end.

  Define f[i] = choose an element v of (lambda[i] \setminus Diag[i]) in v for i in alpha. Then f is
  an element of ProdSet(lambda,alpha). Take an element j of alpha and an element m of kappa[j] such
  that G[(m,j)] = f. Indeed f \in \range(G). G[(m,j)][j] is an element of Diag[j] and f[j] is not an
  element of Diag[j]. Contradiction.
qed.


# \section*{Consistency check}

Lemma. Contradiction.
