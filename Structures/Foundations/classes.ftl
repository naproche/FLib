#
# Classes
# (Marcel Schütz, 2020)
#

#[prove off]
[read ForTheLib/Foundations/objects.ftl]
#[prove on]


# 1. Sub- and superclasses

Axiom FoundCl000. Let a be an object and x be a class. a \subseteq x iff every element of a is an
element of x.

Axiom FoundCl005. Let a be an object and x be a class. x \subseteq a iff every element of x is an
element of a.


Definition FoundCl010. Let a be an object. A subclass of a is a class x such that x \subseteq a.

Definition FoundCl015. Let a be an object. A superclass of a is a class x such that x \supseteq a.


Proposition FoundCl020. Let x,y be classes. If x \subseteq y and y \subseteq x then x = y.


# 2. The empty class

Definition FoundCl025. \emptyset = {u | u \neq u}.

Let the empty class stand for \emptyset.


Definition FoundCl030. Let x be a class. x is empty iff x = \emptyset.

Definition FoundCl035. Let x be a class. x is nonempty iff x \neq \emptyset.


# 3. Operations on classes

# 3.1 Union

Axiom FoundCl040. Let x be a class. \bigcup x is a class such that

  \bigcup x = {u | u \in y for some y \in x}.


Axiom FoundCl045. Let x,y be classes. x \cup y is a class such that

  x \cup y = {u | u \in x or u \in y}.


# 3.2 Intersections

Axiom FoundCl050. Let x be a class. \bigcap x is a class such that

  \bigcap x = {u | u \in y for all y \in x}.


Axiom FoundCl055. Let x,y be classes. x \cap y is a class such that

  x \cap y = {u | u \in x and u \in y}.


Definition FoundCl060. Let x,y be classes. x and y are disjoint iff x \cap y = \emptyset.


# 3.3 Complement

Axiom FoundCl065. Let x,y be classes. x \setminus y is a class such that

  x \setminus y = {u | u \in x and u \notin y}.



# 3.4 Symmetric difference

Axiom FoundCl070. Let x,y be classes. x \triangle y is a class such that

  x \triangle y = (x \cup y) \setminus (x \cap y).


# 3.5 Power class

Axiom FoundCl075. Let x be a class. Pow(x) is a class such that

  Pow(x) = {u | u is a subclass of x}.

Let the power class of x stand for Pow(x).


# 3.6 Singletons

Definition FoundCl080. Let x be an object. `{x}` = {x}.

Let the singleton class of x stand for `{x}`.


# 3.7 Unordered pairs

Definition FoundCl085. Let x,y be objects. `{x,y}` = {x,y}.

Let the unordered pair of x and y stand for `{x,y}`.


# 4. Basic properties

Proposition FoundCl090. Let x,y be classes. \bigcup `{x,y}` = x \cup y.

Proof.
  Every element of \bigcup `{x,y}` is an element of x \cup y. Indeed Every element of
  \bigcup `{x,y}` is an element of some element of `{x,y}`. Every element of x \cup y is an element
  of \bigcup `{x,y}`. \bigcup `{x,y}` and x \cup y are classes.
qed.


Proposition FoundCl095. Let x,y be classes. \bigcap `{x,y}` = x \cap y.

Proof.
  Every element of \bigcap `{x,y}` is an element of x \cap y. Every element of x \cap y is an
  element of \bigcap `{x,y}`. Indeed every element of x \cap y is an element of every element of
  `{x,y}`. \bigcap `{x,y}` and x \cap y are classes.
qed.


# 4.1 Commutative laws

Proposition FoundCl100. Let x,y be classes. x \cup y = y \cup x.

Proof.
  Every element of x \cup y is an element of y \cup x. Every element of y \cup x is an element of
  x \cup y. x \cup y and y \cup x are classes.
qed.


Proposition FoundCl105. Let x,y be classes. x \cap y = y \cap x.

Proof.
  Every element of x \cap y is an element of y \cap x. Every element of y \cap x is an element of
  x \cap y. x \cap y and y \cap x are classes.
qed.


# 4.2 Associative laws

Proposition FoundCl110. Let x,y,z be classes. (x \cup y) \cup z = x \cup (y \cup z).

Proof.
  Every element of (x \cup y) \cup z is an element of x \cup (y \cup z). Every element of
  x \cup (y \cup z) is an element of (x \cup y) \cup z. Take classes a,b such that
  a = (x \cup y) \cup z and b = x \cup (y \cup z).
qed.


Proposition FoundCl115. Let x,y,z be classes. (x \cap y) \cap z = x \cap (y \cap z).

Proof.
  Every element of (x \cap y) \cap z is an element of x \cap (y \cap z). Every element of
  x \cap (y \cap z) is an element of (x \cap y) \cap z. Take classes a,b such that
  a = (x \cap y) \cap z and b = x \cap (y \cap z).
qed.


# 4.3 Distributive laws

Proposition FoundCl120. Let x,y,z be classes. x \cap (y \cup z) = (x \cap y) \cup (x \cap z).

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


Proposition FoundCl125. Let x,y,z be classes. x \cup (y \cap z) = (x \cup y) \cap (x \cup z).

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

Proposition FoundCl140. Let x,y,z be classes. x \setminus (y \cap z) =
(x \setminus y) \cup (x \setminus z).

Proof. [prove off] qed.


Proposition FoundCl145. Let x,y,z be classes. x \setminus (y \cup z) =
(x \setminus y) \cap (x \setminus z).

Proof. [prove off] qed.


# 4.6 Subclass laws

Proposition FoundCl150. Let x,y be classes. x \subseteq x \cup y.


Proposition FoundCl155. Let x,y be classes. x \cap y \subseteq x.
Proof.
  Every element of x \cap y is an element of x.
qed.


Proposition FoundCl160. Let x,y be classes. x \subseteq y iff x \cup y = y.

Proof. [prove off] qed.


Proposition FoundCl165. Let x,y be classes. x \subseteq y iff x \cap y = x.

Proof. [prove off] qed.


# 4.7 Symmetric difference

Proposition FoundCl170. Let x,y be classes. x \triangle y = y \triangle x.


Proposition FoundCl175. Let x,y,z be classes. x \cap (y \triangle z) =
(x \cap y) \triangle (x \cap z).

Proof. [prove off] qed.


Proposition FoundCl180. Let x,y be classes. x = y iff x \triangle y is empty.


Proposition FoundCl185. Let x,y,z be classes. If x \triangle y = x \triangle z then y = z.

Proof. [prove off] qed.


Proposition FoundCl190. Let x,y,z be classes. (x \triangle y) \triangle z =
x \triangle (y \triangle z).

Proof. [prove off] qed.


# 4.8 The empty class

Proposition FoundCl195. Let x be a class. x \setminus x = \emptyset.

Proposition FoundCl200. Let x be a class. x \setminus \emptyset = x.


# 4.9 Complement

Proposition FoundCl205. Let x,y be classes. x \setminus (x \setminus y) = x \cap y.

Proof. [prove off] qed.


Corollary FoundCl210. Let x,y be classes. Assume that y \subseteq x. Then
x \setminus (x \setminus y) = y.


# 5. Atoms

Definition FoundCl215. An urelement is an object that is not a class.


# 6. Transitive classes

Axiom FoundCl220. Let x be a class. x is transitive iff every element of x that is not an urelement
is a subclass of x.


Proposition FoundCl225. Let x be a class. Assume that every element of x is a transitive class. Then
\bigcup x is transitive.

Proof. [prove off] qed.


Proposition FoundCl230. Let x be a class. Assume that every element of x is a transitive class. Then
\bigcap x is transitive.

Proof. [prove off] qed.


Proposition FoundCl235. Let x be a class. x is transitive iff \bigcup x \subseteq x.

Proof. [prove off] qed.


Proposition FoundCl240. Let x,y be transitive class. Then (x \cup y) \cup `{x,y}` is transitive.

Proof. [prove off] qed.


Proposition FoundCl245. Let x be a transitive class. Assume that every element of x is a transitive
class. Then x \cup (\bigcup x) is transitive.


Proposition FoundCl250. Let x be a class. Assume that every element of x is a class. If x is
transitive then x \subseteq Pow(x).

Proof. [prove off] qed.


Proposition FoundCl255. Let x be a class. If x \subseteq Pow(x) then x is transitive.


Proposition FoundCl260. Let x be a transitive class. Pow(x) is transitive.

Proof. [prove off] qed.


# 7. Inductive classes

Axiom FoundCl265. Let x be a class. x is inductive iff 0 \in x and succ(y) lies in x for all
y \in x.


# 8. Bounded classes

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


# 9. Initial segment

Axiom FoundCl300. Let x be a class and y be an object. y is an initial segment of x iff y is a
subclass of x such that for all u \in y and all v \in x if v < u then v \in y.


# 10. Arithmetic with classes

Axiom FoundCl305. Let x,y be classes. x + y = {u + v | u \in x and v \in y}.

Axiom FoundCl310. Let x,y be classes. x - y = {u - v | u \in x and v \in y}.

Axiom FoundCl315. Let x,y be classes. x \cdot y = {u \cdot v | u \in x and v \in y}.
