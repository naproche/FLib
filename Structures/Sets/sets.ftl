#
# Sets according to ZFU
# (Marcel Schütz, 2020)
#

#[prove off][check off]
[read FLib/Structures/Foundations/families.ftl]
#[prove on][check on]


# 1. Sets

Signature SetSet000. A set is a class.

Definition SetSet005. SET = {x | x is a set}.


Definition SetSet010. Let x be an entity. A subset of x is a set y such that y \subseteq x.

Definition SetSet015. Let x be an entity. A superset of x is a set y such that y \supseteq x.


Definition SetSet020. An element is an entity x such that x is an urelement or x is a set.


# 2. The ZFU axioms

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

Axiom SetSet060. Let f be a function and x be a subset of the domain of f. If every value of f is an
element then f[x] is a set.


# 3. Consequences of the axioms

Theorem SetSet065. Let x,y be sets. If x \subseteq y and y \subseteq x then x = y.

Theorem SetSet070. Let x,y be elements. `{x,y}` is a set.

Proof.
  \emptyset is a set. Thus Pow(Pow(\emptyset)) is a set. Pow(\emptyset) = `{\emptyset}`. Thus
  Pow(Pow(\emptyset)) = `{\emptyset, `{\emptyset}`}`. Indeed Pow(Pow(\emptyset)) = {\emptyset,
  `{\emptyset}`}.

  Define f(u) =
    case u = \emptyset     -> x,
    case u = `{\emptyset}` -> y
  for u in Pow(Pow(\emptyset)).

  f[Pow(Pow(\emptyset))] is a set.
  proof.
    Take a set A such that A = Pow(Pow(\emptyset)). Every element of A is an element of dom(f).
    hence A \subseteq dom(f). f(u) is an element for all u \in A. Thus every value of f is an
    element. Hence f[A] is a set.
  end.

  f[Pow(Pow(\emptyset))] = `{x,y}`.
  proof.
    Pow(Pow(\emptyset)) = {\emptyset, `{\emptyset}`}. f(\emptyset) = x. f(`{\emptyset}`) = y. Hence
    f[Pow(Pow(\emptyset))] = {x,y}. Indeed f[Pow(Pow(\emptyset))] = {f(u) | u = \emptyset or u =
    `{\emptyset}`}.
  end.
qed.


Corollary SetSet072. Let x,y be elements and z be a collection. Assume that z = {x,y}. Then z is a
set.

Proof.
  z = `{x,y}`.
qed.


Proposition SetSet075. Let x be an element. `{x}` = `{x,x}`.

Corollary SetSet080. Let x be an element. `{x}` is a set.


Corollary SetSet077. Let x be an element and y be a class. Assume that y = {x}. Then y is a set.

Proof. [prove off] qed.


Corollary SetSet078. Let x,y be sets and f be a bijection between x and y. Assume that x = {u} for
some entity u. Then y = {v} for some entity v.

Proof. [prove off] qed.


Proposition SetSet080. Let x be a set and y be a class. y is the powerset of x iff y =
{a | a is a subset of x}.

Proof. [prove off] qed.


Proposition SetSet081. Let x,y be sets. x is a subset of y iff every element of x lies in y.

Proof. [prove off] qed.


Proposition SetSet082. Let x,y be sets. Assume that every element of y lies in x. Then y is a subset
of x.

Proof. [prove off] qed.


Proposition SetSet083. Let x,y be sets. If every element of x lies in y and every element of y lies
in x then x = y.

Proof. [prove off] qed.


Proposition SetSet084. Let f be a function. Assume that the domain of f is a set. Then the range of
f is a set.

Proof. [prove off] qed.


# Separation

Theorem SetSet085. Let x be a set and A be a class. x \cap A is a set.

Proof.
  Case x is empty. Obvious.

  Case x is nonempty.

    Define f(u) =
      case u \in A    -> `{u}`,
      case u \notin A -> \emptyset
    for u in x.

    f[x] = {f(u) | u \in x \cap dom(f)} (by FoundMap180). Indeed x is a class and f is a map.

    (1) Hence f[x] = {f(u) | u \in x}.

    x \subseteq dom(f). f(u) is an element for all u \in x. Indeed `{u}` is a
    set for all u \in x. Thus every value of f is an element. f[x] is a set. Indeed f is a function.
    Hence \bigcup f[x] is a set.

    Every element of \bigcup f[x] is an element of x \cap A.
    proof.
      Let v \in \bigcup f[x]. Take w \in f[x] such that v \in w (by FoundCl040).  Take u \in x such
      that w = f(u) (by 1). Indeed f[x] is nonempty.
    end.

    Every element of x \cap A is an  element of \bigcup f[x].
    proof.
      Let u \in x \cap A. Then f(u) = `{u}`. u \in f(u). f(u) \in f[x]. Indeed f[x] =
      {f(v) | v \in x and v \in dom(f)}.
    end.

    Hence \bigcup f[x] = x \cap A.
  end.
qed.


Proposition SetSet090. Let x be a set. x \notin x.

Proof.
  Case x is empty. Obvious.

  Case x is nonempty.
    Assume that x \in x. Define A = {y in x | y = x}. A is a nonempty set. Hence we can take an
    element y of A such that y and A are disjoint. Thus y = x. Then x \in y and x \in A.
    Contradiction.
  end.
qed.


Proposition SetSet091. Let x,y be sets and f be a map from x to y. Let a be a subset of x. Then f[a]
is a subset of y.

Proof. [prove off] qed.


Theorem SetSet095. NAT is a set.


Proposition SetSet100. Let n,m be natural numbers. {n, \ldots, m} is a set.

Proof. [prove off] qed.


Proposition SetSet105. Let x,y be sets. Then x \times y is a set.

Proof. [prove off] qed.


Proposition SetSet110. Let x,y be sets. Then x^{y} is a set.

Proof. [prove off] qed.


Proposition SetSet112. Let x,y be sets. Let F be a class such that F = {f | f is a map from x to y}.
Then F is a set.

Proof. [prove off] qed.


Proposition SetSet115. Let x be a set and n be a natural number. x^{n} is a set.

Proof. [prove off] qed.


Proposition SetSet120. Let x,y be sets. Then x \uplus y is a set.

Proof. [prove off] qed.


Proposition SetSet121. Let x,y be sets and a be a subset of y. Let f be a map from x to y. Then
f^{-1}[a] is a subset of x.


# 4. Proper classes

Definition SetSet125. A proper class is a class that is not a set.

Proposition SetSet130. SET is a proper class.


Definition SetSet131. Let a be an entity. a is setsized iff there is a set x such that
x = {u | u \in a}.

Definition SetSet132. Let a be an entity. a is classsized iff there is a proper class X such that
X = {u | u \in a}.


Lemma SetSet133. Let a be a setsized entity. Let X be a class such that X = {u | u \in a}. Then X is
a set.

Proof.
  Take a set Y such that Y = {u | u \in a} (by SetSet131). Then Y = X.
qed.

Lemma SetSet134. Let a be a classsized entity. Let X be a class such that X = {u | u \in a}. Then X
is a proper class.

Proof.
  Take a proper class Y such that Y = {u | u \in a} (by SetSet132). Then Y = X.
qed.


Proposition SetSet135. Let a be a setsized entity. Then Pow(a) is a set.

Proof.
  Define x = {u | u \in a}. x is a set (by SetSet133). Pow(a) = {b | b is a subclass of a}.
  Pow(x) = {y | y is a subclass of x}. Every subclass of x is a subclass of a.

  Every subclass of a is a subclass of x.
  proof.
    Let b be a subclass of a. Then every element of b lies in a. Hence every element of b lies in x.
  end.

  Thus Pow(a) = Pow(x).
qed.


# 5. The class of sets is closed under the common set operations

Proposition SetSet138. Let x,y be sets. x \cup y is a set.

Proposition SetSet140. Let x,y be sets. x \cap y is a set.


Proposition SetSet145. Let x,y be sets. x \setminus y is a set.

Proof.
  Every element of x \setminus y is an element of x.
end.


Proposition SetSet150. Let x,y be sets. x \triangle y is a set.

Proposition SetSet155. Let x be a set and A be a class such that A \subseteq x. Then A is a set.


Proposition SetSet160. Let x be a nonempty set. Assume that every element of x is a set. Then
\bigcap x is a set.

Proof.
  Take an element y of x such that every element of \bigcap x is an element of y.
qed.
