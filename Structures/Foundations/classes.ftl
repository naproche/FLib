#
# Classes
# (Marcel Schütz, 2020)
#

#[prove off][check off]
[read FLib/Structures/Technicalities/signatures.ftl]
#[prove on][check on]


# 1. Sub- and superclasses

Axiom FoundCl000. Let a be an entity and x be a class. a \subseteq x iff every element of a is an
element of x.

Axiom FoundCl005. Let a be an entity and x be a class. x \subseteq a iff every element of x is an
element of a.


Proposition FoundCl007. Let x,y be classes and a be an entity. Assume that x \subseteq y \subseteq a.
Then x \subseteq a.


Definition FoundCl010. Let a be an entity. A subclass of a is a class x such that x \subseteq a.

Definition FoundCl015. Let a be an entity. A superclass of a is a class x such that x \supseteq a.


Proposition FoundCl020. Let x,y be classes. If x \subseteq y and y \subseteq x then x = y.


# 2. The empty class

Definition FoundCl025. \emptyset = {u | u \neq u}.

Let the empty class stand for \emptyset.


Definition FoundCl027. Let x be an entity. x is empty iff x has no elements.

Let x is nonempty stand for x is not empty.


Proposition FoundCl030. Let x be a class. x is empty iff x = \emptyset.

Proposition FoundCl035. Let x be a class. x is nonempty iff x \neq \emptyset.


# 3. Operations on classes

# 3.1 Union

Definition FoundCl040. Let x be an entity. Union(x) = {u | u \in y for some y \in x}.

Let \bigcup x stand for Union(x).
Let the union of x stand for Union(x).


Definition FoundCl045. Let x,y be entities. union(x,y) = {u | u \in x or u \in y}.

Let x \cup y stand for union(x,y).
Let the union of x and y stand for union(x,y).


# 3.2 Intersections

Definition FoundCl050. Let x be a nonempty entity. Intersec(x) = {u | u \in y for all y \in x}.

Let \bigcap x stand for Intersec(x).
Let the intersection of x stand for Intersec(x).


Definition FoundCl055. Let x,y be entities. intersec(x,y) = {u | u \in x and u \in y}.

Let x \cap y stand for intersec(x,y).
Let the intersection of x and y stand for intersec(x,y).


Definition FoundCl060. Let x,y be entities. x and y are disjoint iff x \cap y = \emptyset.

Proposition FoundCl062. Let x,y be entities. x and y are disjoint iff there is no entity that lies in
x and lies in y.


# 3.3 Complement

Definition FoundCl065. Let x,y be entities. setminus(x,y) = {u | u \in x and u \notin y}.

Let x \setminus y stand for setminus(x,y).
Let the complement of y in x stand for setminus(x,y).


# 3.4 Symmetric difference

Definition FoundCl070. Let x,y be entities. symdiff(x,y) = (x \cup y) \setminus (x \cap y).

Let x \triangle y  stand for symdiff(x,y).
Let the symmetric difference of x and y stand for symdiff(x,y).


Proposition FoundCl072. Let x,y be entities. The symmetric difference of x and y is a class.


# 3.5 Power class

Definition FoundCl075. Let x be an entity. Pow(x) = {u | u is a subclass of x}.

Let the power class of x stand for Pow(x).


# 3.6 Singletons

Definition FoundCl080. Let x be an entity. `{x}` = {x}.

Let the singleton class of x stand for `{x}`.


# 3.7 Unordered pairs

Definition FoundCl085. Let x,y be entities. `{x,y}` = {x,y}.

Let the unordered pair of x and y stand for `{x,y}`.


# 4. Basic properties

Proposition FoundCl090. Let x,y be entities. \bigcup `{x,y}` = x \cup y.

Proof.
  Every element of \bigcup `{x,y}` is an element of x \cup y. Indeed Every element of
  \bigcup `{x,y}` is an element of some element of `{x,y}`. Every element of x \cup y is an element
  of \bigcup `{x,y}`. \bigcup `{x,y}` and x \cup y are classes.
qed.


Proposition FoundCl095. Let x,y be entities. \bigcap `{x,y}` = x \cap y.

Proof.
  Every element of \bigcap `{x,y}` is an element of x \cap y. Every element of x \cap y is an
  element of \bigcap `{x,y}`. Indeed every element of x \cap y is an element of every element of
  `{x,y}`. \bigcap `{x,y}` and x \cap y are classes.
qed.


# 4.1 Commutative laws

Proposition FoundCl100. Let x,y be entities. x \cup y = y \cup x.

Proof.
  Every element of x \cup y is an element of y \cup x. Every element of y \cup x is an element of
  x \cup y. x \cup y and y \cup x are classes.
qed.


Proposition FoundCl105. Let x,y be entities. x \cap y = y \cap x.

Proof.
  Every element of x \cap y is an element of y \cap x. Every element of y \cap x is an element of
  x \cap y. x \cap y and y \cap x are classes.
qed.


# 4.2 Associative laws

Proposition FoundCl110. Let x,y,z be entities. (x \cup y) \cup z = x \cup (y \cup z).

Proof.
  Every element of (x \cup y) \cup z is an element of x \cup (y \cup z). Every element of
  x \cup (y \cup z) is an element of (x \cup y) \cup z. Take classes a,b such that
  a = (x \cup y) \cup z and b = x \cup (y \cup z).
qed.


Proposition FoundCl115. Let x,y,z be entities. (x \cap y) \cap z = x \cap (y \cap z).

Proof.
  Every element of (x \cap y) \cap z is an element of x \cap (y \cap z). Every element of
  x \cap (y \cap z) is an element of (x \cap y) \cap z. Take classes a,b such that
  a = (x \cap y) \cap z and b = x \cap (y \cap z).
qed.


# 4.3 Distributive laws

Proposition FoundCl120. Let x,y,z be entities. x \cap (y \cup z) = (x \cap y) \cup (x \cap z).

Proof.
  Every element of x \cap (y \cup z) is an element of (x \cap y) \cup (x \cap z).
  proof.
    Let u \in x \cap (y \cup z). Then u \in x and u \in y \cup z. Hence u \in x and (u \in y or
    u \in z). (u \in x and u \in y) or (u \in x and u \in z). u \in x \cap y or u \in x \cap z.
    Take classes a,b such that a = x \cap y and b = x \cap z.
  end.

  Every element of (x \cap y) \cup (x \cap z) is an element of x \cap (y \cup z).
  proof.
    Let u \in (x \cap y) \cup (x \cap z). Then u \in x \cap y or u \in x \cap z.
  end.

  Take classes a,b such that a = x \cap (y \cup z) and b = (x \cap y) \cup (x \cap z).
qed.


Proposition FoundCl125. Let x,y,z be entities. x \cup (y \cap z) = (x \cup y) \cap (x \cup z).

Proof.
  Every element of x \cup (y \cap z) is an element of (x \cup y) \cap (x \cup z).
  proof.
    Let u \in x \cup (y \cap z). Then u \in x or u \in y \cap z. Hence u \in x or (u \in y and
    u \in z). Thus (u \in x or u \in y) and (u \in x or u \in z). Therefore u \in x \cup y and
    u \in x \cup z.
  end.

  Every element of (x \cup y) \cap (x \cup z) is an element of x \cup (y \cap z).
  proof.
    Let u \in (x \cup y) \cap (x \cup z). Then u \in x \cup y and u \in x \cup z. Hence (u \in x or
    u \in y) and (u \in x or u \in z).
  end.

  Take classes a,b such that a = x \cup (y \cap z) and b = (x \cup y) \cap (x \cup z).
qed.


# 4.4 Idempocy laws

Proposition FoundCl130. Let x be a class. x \cup x = x.

Proof.
  Every element of x \cup x is an element of x.
qed.


Proposition FoundCl135. Let x be a class. x \cap x = x.

Proof.
  Every element of x \cap x is an element of x. Every element of x is an element of x \cap x.
qed.


# 4.5 De Morgan's laws

Proposition FoundCl140. Let x,y,z be entities. x \setminus (y \cap z) =
(x \setminus y) \cup (x \setminus z).

Proof. [prove off] qed.


Proposition FoundCl145. Let x,y,z be entities. x \setminus (y \cup z) =
(x \setminus y) \cap (x \setminus z).

Proof. [prove off] qed.


# 4.6 Subclass laws

Proposition FoundCl150. Let x,y be entities. x \subseteq x \cup y.


Proposition FoundCl155. Let x,y be entities. x \cap y \subseteq x.
Proof.
  Every element of x \cap y is an element of x.
qed.


Proposition FoundCl160. Let x be an entity and y be a class. x \subseteq y iff x \cup y = y.

Proof. [prove off] qed.


Proposition FoundCl165. Let x be a class and y be an entity. x \subseteq y iff x \cap y = x.

Proof. [prove off] qed.


# 4.7 Symmetric difference

Proposition FoundCl170. Let x,y be entities. x \triangle y = y \triangle x.


Proposition FoundCl175. Let x,y,z be entities. x \cap (y \triangle z) =
(x \cap y) \triangle (x \cap z).

Proof. [prove off] qed.


Proposition FoundCl180. Let x,y be classes. x = y iff x \triangle y is empty.


Proposition FoundCl185. Let x,y,z be classes. If x \triangle y = x \triangle z then y = z.

Proof. [prove off] qed.


Proposition FoundCl190. Let x,y,z be entities. (x \triangle y) \triangle z =
x \triangle (y \triangle z).

Proof. [prove off] qed.


# 4.8 The empty class

Proposition FoundCl195. Let x be an entity. x \setminus x = \emptyset.

Proposition FoundCl200. Let x be a class. x \setminus \emptyset = x.


# 4.9 Complement

Proposition FoundCl205. Let x,y be entities. x \setminus (x \setminus y) = x \cap y.

Proof. [prove off] qed.


Corollary FoundCl210. Let x be an entity and y be a class. Assume that y \subseteq x. Then
x \setminus (x \setminus y) = y.


# 5. Atoms

Definition FoundCl215. An urelement is an entity that is not a class.


# 6. Bounded classes

Axiom FoundCl270. Let x,y be classes and z \in y. z is an upper bound of x in y iff z is greater
than or equal to every element of x.

Axiom FoundCl275. Let x,y be classes and z \in y. z is a lower bound of x in y iff z is less than or
equal to every element of x.

Axiom FoundCl280. Let x,y be classes and z \in y. z is a least upper bound of x in y iff z is an
upper bound of x in y and z is less than or equal to every upper bound of x in y.

Axiom FoundCl285. Let x,y be classes and z \in y. z is a greatest lower bound of x in y iff z is a
lower bound of x in y and z is greater than or equal to every upper bound of x in y.


Proposition FoundCl290. Let x,y be classes and z \in y. Assume that z is a least upper bound of x
in y. Then z is an upper bound of x in y.

Proposition FoundCl295. Let x,y be classes and z \in y. If z is a greatest lower bound of x in y
then z is a lower bound of x in y.


# 7. Initial segment

Axiom FoundCl300. Let x be a class and y be an entity. y is an initial segment of x iff y is a
subclass of x such that for all u \in y and all v \in x if v < u then v \in y.


# 8. Arithmetic with classes

Axiom FoundCl305. Let x,y be classes. x + y = {u + v | u \in x and v \in y}.

Axiom FoundCl310. Let x,y be classes. x - y = {u - v | u \in x and v \in y}.

Axiom FoundCl315. Let x,y be classes. x \cdot y = {u \cdot v | u \in x and v \in y}.
