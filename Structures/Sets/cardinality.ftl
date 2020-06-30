#
# Cardinality
# (Marcel Schütz, 2020)
#

#[prove off][check off]
[read ForTheLib/Sets/sets.ftl]
#[prove on][check on]


# 1. Definitions

Definition SetCard000. Let x,y be sets. x \sim y iff there exists a bijection between x and y.

Let x and y are equipollent stand for x \sim y.
Let x and y are equipotent stand for x \sim y.
Let x and y have same cardinality stand for x \sim y.


Definition SetCard005. Let x,y be sets. x \preceq y iff there exists an injective function from x to
y.

Let x \succeq y stand for y \preceq x.

Let x has cardinality at most that of y stand for x \preceq y.
Let x has cardinality at least that of y stand for x \succeq y.

Let x \prec y stand for x \preceq y and not x \sim y.
Let x \succ y stand for x \succeq y and not x \sim y.


# 2. Basic properties

Proposition SetCard010. Let x be a set. x \sim x.

Proof. [prove off] qed.


Proposition SetCard015. Let x,y be sets. If x \sim y then y \sim x.

Proof. [prove off] qed.


Proposition SetCard020. Let x,y,z be sets. If x \sim y \sim z then x \sim z.

Proof. [prove off] qed.


Proposition SetCard025. Let x,y be sets. If x \sim y then x \preceq y and y \preceq x.

Proof. [prove off] qed.


Proposition SetCard030. Let x be a set. x \preceq x.

Proof. [prove off] qed.


Proposition SetCard035. Let x,y,z be sets. If x \preceq y \preceq z then x \preceq z.

Proof. [prove off] qed.


Proposition SetCard040. Let x,y be sets. If x \subseteq y then x \preceq y.

Proof. [prove off] qed.


# 3. The Cantor-Bernstein theorem

Theorem SetCard045. Let x,y be sets. If x \preceq y and y \preceq x then x \sim y.

Proof. [prove off] qed.


# 4. Cantor's theorem

Theorem SetCard050. Let x be a set. x \prec Pow(x).

Proof. [prove off] qed.


# 5. Finite, countable and uncountable sets

Definition SetCard055. Let x be a set. x is finite iff x \sim {1, \ldots, n} for some natural number
n.

Definition SetCard060. Let x be a set. x is infinite iff x is not finite.

Definition SetCard065. Let x be a set. x is countably infinite iff x \sim NAT.

Definition SetCard070. Let x be a set. x is countable iff x is finite or x is countably infinite.

Definition SetCard071. Let x be a set. x is uncountable iff x is not countable.


# 5.1 Finite sets.

Lemma SetCatd074. `{0}` is a set.

Lemma SetCard075. `{0,1}` is a set.


Definition SetCard077. Let x be a set. x has at most one element iff x \preceq `{0}`.

Definition SetCard078. Let x be a set. x has at most two elements iff x \preceq `{0,1}`.


Proposition SetCard079. Let x be an element. `{x}` \sim `{0}`.

Proof. [prove off] qed.


Proposition SetCard080. Let x be a set. x has at most one element iff x = \emptyset or x = `{a}` for
some element a.

Proof. [prove off] qed.


Proposition SetCard081. Let x be a set. x has at most two elements iff x = \emptyset or x = `{a}`
for some element a or x = `{a,b}` for some elements a,b.

Proof. [prove off] qed.


Corollary SetCard082. Let x be an element. `{x}` is a finite set.

Proof. [prove off] qed.


Proposition SetCard085. Let x,y be elements. Assume x \neq y. `{x,y}` \sim `{0,1}`.

Proof. [prove off] end.


Corollary SetCard086. Let x,y be elements. `{x,y}` is a finite set.

Proof. [prove off] qed.


Proposition SetCard090. Let x be a set. If x \sim \emptyset then x = \emptyset.

Proof. [prove off] end.


Proposition SetCard095. Let x be a set. If x \sim `{0}` then x = `{y}` for some element y.

Proof. [prove off] end.


Proposition SetCard100. Every subset of any finite set is finite.

Proof. [prove off] qed.


Proposition SetCard105. Let x be a finite set and a be an element. x \cup `{a}` is finite.

Proof. [prove off] qed.


Proposition SetCard110. Let x,y be finite sets. x \cup y is finite.

Proof. [prove off] qed.


Proposition SetCard115. Let x,y be finite sets. x \cap y is finite.

Proof. [prove off] qed.


Proposition SetCard120. Let x,y be finite sets. x \times y is finite.

Proof. [prove off] qed.


Proposition SetCard125. Let x,y be finite sets. x \setminus y is finite.

Proof. [prove off] qed.


Proposition SetCard130. Let x be a finite set. Pow(x) is finite.

Proof. [prove off] qed.


Proposition SetCard131. Let x,y be sets and f be a bijection between x and y. Assume that x is
finite. Then y is finite.

Proof. [prove off] qed.


# 5.2 Countable sets

Proposition SetCard135. Every subset of any countable set is countable.

Proof. [prove off] qed.


Proposition SetCard140. Let x be a countable set and a be an element. x \cup `{a}` is countable.

Proof. [prove off] qed.


Proposition SetCard145. Let x,y be countable sets. x \cup y is countable.

Proof. [prove off] qed.


Proposition SetCard150. Let x,y be countable sets. x \cap y is countable.

Proof. [prove off] qed.


Proposition SetCard155. Let x,y be countable sets. x \times y is countable.

Proof. [prove off] qed.


Proposition SetCard160. Let x,y be countable sets. x \setminus y is countable.

Proof. [prove off] qed.


Proposition SetCard165. Let x be a countable set. Assume that every set that is an element of x is
countable. \bigcup x is countable.

Proof. [prove off] qed.
