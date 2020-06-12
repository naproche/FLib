#
# ZFU (Zermelo-Fraenkel set theory with urelements)
# (Marcel Schütz, 2020)
#

#[prove off]
[read ForTheLib/Foundations/families.ftl]
#[prove on]


# 1. Sets

Signature SetSet000. A set is a notion.

Definition SetSet005. SET = {x | x is a set}.


Definition SetSet010. Let x be an object. A subset of x is a set y such that y \subseteq x.

Definition SetSet015. Let x be an object. A superset of x is a set y such that y \supseteq x.


Proposition SetSet017. Let A be an object. Every subset of A is a subcollection of A.


Definition SetSet020. An element is an object x such that x is an urelement or x is a set.


# 2. The ZFU axioms

Axiom SetSet025. Every set is a class.

Axiom SetSet030. Every element of any set is an element.


# 2.1 The set existence axiom:

Axiom SetSet035. \emptyset is a set.

Let the empty set stand for \emptyset.


# 2.2 The union axiom:

Axiom SetSet040. Let x be a set. \bigcup x is a set.


# 2.3 The powerset axiom:

Axiom SetSet045. Let x be a set. Pow(x) is a set.

Let the powerset of x stand for the power class of x.


# 2.4 The axiom of infinity:

Axiom SetSet050. There exists an inductive set.


# 2.5 The foundation axiom:

Axiom SetSet055. Let x be a nonempty set. Assume that every element of x is a set. Then x has an
element y such that x and y are disjoint.


# 2.6 The replacement axiom:

Axiom SetSet060. Let x be a set and f be a function. Assume that x \subseteq dom(f). If every value
of f is an element then f[x] is a set.


# 3. Consequences of the axioms

Theorem SetSet065. Let x,y be sets. If x \subseteq y and y \subseteq x then x = y.

Theorem SetSet070. Let x,y be elements. `{x,y}` is a set.

Proof.
  \emptyset is a set. Thus Pow(Pow(\emptyset)) is a set. Pow(\emptyset) = `{\emptyset}`. Thus
  Pow(Pow(\emptyset)) = `{\emptyset, `{\emptyset}`}`.

  Define f(u) =
    case u = \emptyset     -> x,
    case u = `{\emptyset}` -> y
  for u in Pow(Pow(\emptyset)).

  f[Pow(Pow(\emptyset))] is a set.
  proof.
    Pow(Pow(\emptyset)) is a set. Every element of Pow(Pow(\emptyset)) is an element of dom(f). f(u)
    is an element for all u \in Pow(Pow(\emptyset)). Thus every value of f is an element. Hence the
    thesis (by SetSet060).
  end.

  f[Pow(Pow(\emptyset))] = `{x,y}`.
  proof.
    f(\emptyset) = x. f(`{\emptyset}`) = y. \emptyset \in dom(f).
  end.
qed.


Proposition SetSet075. Let x be an element. `{x}` = `{x,x}`.

Corollary SetSet080. Let x be an element. `{x}` is a set.


Proposition SetSet080. Let x be a set and y be a class. Assume that y = {a | a is a subset of x}.
Then y is the powerset of x.

Proof. [prove off] qed.


Proposition SetSet082. Let x,y be sets. Assume that every element of y lies in x. Then y is a subset
of x.

Proof. [prove off] qed.


# Separation

Theorem SetSet085. Let x be a set and A be a class. x \cap A is a set.

Proof.
  Define f(u) =
    case u \in A    -> `{u}`,
    case u \notin A -> \emptyset
  for u in x.

  x \subseteq dom(f). f(u) is an element for all u \in x. Indeed `{u}` is a
  set for all u \in x. Thus every value of f is an element. f[x] is a set. Indeed f is a function.
  Hence \bigcup f[x] is a set.

  Every element of \bigcup f[x] is an element of x \cap A.
  proof.
    Let v \in \bigcup f[x]. Take w \in f[x] such that v \in w. Take u \in x such that w = f(u).
  end.

  Every element of x \cap A is an  element of \bigcup f[x].
  proof.
    Let u \in x \cap A. Then f(u) = `{u}`. u \in f(u). f(u) \in f[x]. Indeed f[x] =
    {f(v) | v \in x and v \in dom(f)}.
  end.
  
  Hence \bigcup f[x] = x \cap A.
qed.


Proposition SetSet090. Let x be a set. x \notin x.

Proof.
  Case x = \emptyset. Obvious.
  Case x \neq \emptyset.
    Assume that x \in x. Define A = {y in x | y = x}. A is a nonempty set.
  end.
qed.


Theorem SetSet095. NAT is a set.


Proposition SetSet100. Let n,m be natural numbers. {n, \ldots, m} is a set.

Proof. [prove off] qed.


Proposition SetSet105. Let x,y be sets. Then x \times y is a set.

Proof. [prove off] qed.


Proposition SetSet110. Let x,y be sets. Then x^{y} is a set.

Proof. [prove off] qed.


Proposition SetSet115. Let x be a set and n be a natural number. x^{n} is a set.

Proof. [prove off] qed.


Proposition SetSet120. Let x,y be sets. Then x \uplus y is a set.

Proof. [prove off] qed.


# 4. Proper classes

Definition SetSet125. A proper class is a class that is not a set.

Proposition SetSet130. SET is a proper class.


# 5. The class of sets is closed under the common set operations

Proposition SetSet135. Let x,y be sets. x \cup y is a set.

Proposition SetSet140. Let x,y be sets. x \cap y is a set.


Proposition SetSet145. Let x,y be sets. x \setminus y is a set.

Proof.
  Every element of x \setminus y is an element of x.
end.


Proposition SetSet150. Let x,y be sets. x \triangle y is a set.

Proposition SetSet155. Let x be a set and A be a class. If A \subseteq x then A is a set.


Proposition SetSet160. Let x be a nonempty set. Assume that every element of x is a set. Then
\bigcap x is a set.

Proof.
  Take an element y of x such that every element of \bigcap x is an element of y.
qed.
