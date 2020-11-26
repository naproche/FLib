# 3 Computation laws for sets

[read FLib/Statements/Library/SetTheory/02_elementary-set-theory.ftl]


Let x,y,z denote zets.


# Commutativity

Proposition 0301. x /cup y = y /cup x.

Proof.
  x /cup y /subseteq y /cup x.
  proof.
    Let u /in x /cup y. Then u /in x or u /in y. Hence u /in y or u /in x. Thus
    u /in y /cup x.
  end.

  y /cup x /subseteq x /cup y.
  proof.
    Let u /in y /cup x. Then u /in y or u /in x. Hence u /in x or u /in y. Thus
    u /in x /cup y.
  end.
qed.


Proposition 0302. x /cap y = y /cap x.

Proof.
  x /cap y /subseteq y /cap x.
  proof.
    Let u /in x /cap y. Then u /in x and u /in y. Hence u /in y and u /in x.
    Thus u /in y /cap x.
  end.

  y /cap x /subseteq x /cap y.
  proof.
    Let u /in y /cap x. Then u /in y and u /in x. Hence u /in x and u /in y.
    Thus u /in x /cap y.
  end.
qed.


# Associativity

Proposition 0303. (x /cup y) /cup z = x /cup (y /cup z).

Proof.
  (x /cup y) /cup z /subseteq x /cup (y /cup z).
  proof.
    Let u /in (x /cup y) /cup z. Then u /in x /cup y or u /in z. Hence u /in x
    or u /in y or u /in z. Thus u /in x or u /in (y /cup z). Therefore
    u /in x /cup (y /cup z).
  end.

  x /cup (y /cup z) /subseteq (x /cup y) /cup z.
  proof.
    Let u /in x /cup (y /cup z). Then u /in x or u /in y /cup z. Hence u /in x
    or u /in y or u /in z. Thus u /in x /cup y or u /in z. Therefore
    u /in (x /cup y) /cup z.
  end.
qed.


Proposition 0304. (x /cap y) /cap z = x /cap (y /cap z).

Proof.
  (x /cap y) /cap z /subseteq x /cap (y /cap z).
  proof.
    Let u /in (x /cap y) /cap z. Then u /in x /cap y and u /in z. Hence u /in x
    and u /in y and u /in z. Thus u /in x and u /in (y /cap z). Therefore
    u /in x /cap (y /cap z).
  end.

  x /cap (y /cap z) /subseteq (x /cap y) /cap z.
  proof.
    Let u /in x /cap (y /cap z). Then u /in x and u /in y /cap z. Hence u /in x
    and u /in y and u /in z. Thus u /in x /cap y and u /in z. Therefore
    u /in (x /cap y) /cap z.
  end.
qed.


# Distributivity

Proposition 0305. x /cap (y /cup z) = (x /cap y) /cup (x /cap z).

Proof.
  x /cap (y /cup z) /subseteq (x /cap y) /cup (x /cap z).
  proof.
    Let u /in x /cap (y /cup z). Then u /in x and u /in y /cup z. Hence u /in x
    and (u /in y or u /in z). Thus (u /in x and u /in y) or (u /in x and
    u /in z). Therefore u /in x /cap y or u /in x /cap z. Hence
    u /in (x /cap y) /cup (x /cap z).
  end.

  (x /cap y) /cup (x /cap z) /subseteq x /cap (y /cup z).
  proof.
    Let u /in (x /cap y) /cup (x /cap z). Then u /in x /cap y or u /in x /cap z.
    Hence (u /in x and u /in y) or (u /in x and u /in z). Thus u /in x and
    (u /in y or u /in z). Therefore u /in x and u /in y /cup z. Hence
    u /in x /cap (y /cup z).
  end.
qed.


Proposition 0306. x /cup (y /cap z) = (x /cup y) /cap (x /cup z).

Proof.
  x /cup (y /cap z) /subseteq (x /cup y) /cap (x /cup z).
  proof.
    Let u /in x /cup (y /cap z). Then u /in x or u /in y /cap z. Hence u /in x
    or (u /in y and u /in z). Thus (u /in x or u /in y) and (u /in x or
    u /in z). Therefore u /in x /cup y and u /in x /cup z. Hence
    u /in (x /cup y) /cap (x /cup z).
  end.

  (x /cup y) /cap (x /cup z) /subseteq x /cup (y /cap z).
  proof.
    Let u /in (x /cup y) /cap (x /cup z). Then u /in x /cup y and u /in x /cup z.
    Hence (u /in x or u /in y) and (u /in x or u /in z). Thus u /in x or
    (u /in y and u /in z). Therefore u /in x or u /in y /cap z. Hence
    u /in x /cup (y /cap z).
  end.
qed.


# Idempocy

Proposition 0307. x /cup x = x.

Proof.
  x /cup x = {u | u /in x or u /in x}. Hence x /cup x = {u | u /in x}. Thus
  x /cup x = x.
qed.


Proposition 0308. x /cap x = x.

Proof.
  x /cap x = {u | u /in x and u /in x}. Hence x /cap x = {u | u /in x}. Thus
  x /cap x = x.
qed.


# De Morgan's laws

Proposition 0309. x /setminus (y /cap z) = (x /setminus y) /cup (x /setminus z).

Proof.
  x /setminus (y /cap z) /subseteq (x /setminus y) /cup (x /setminus z).
  proof.
    Let u /in x /setminus (y /cap z). Then u /in x and u /notin y /cap z. Hence
    we have not (u /in y and u /in z). Thus u /notin y or u /notin z. Therefore
    u /in x and (u /notin y or u /notin z). Then (u /in x and u /notin y) or
    (u /in x and u /notin z). Hence u /in x /setminus y or u /in x /setminus z.
    Thus u /in (x /setminus y) /cup (x /setminus z).
  end.

  (x /setminus y) /cup (x /setminus z) /subseteq x /setminus (y /cap z).
  proof.
    Let u /in (x /setminus y) /cup (x /setminus z). Then u /in x /setminus y or
    u /in x /setminus z. Hence (u /in x and u /notin y) or (u /in x and
    u /notin z). Thus u /in x and (u /notin y or u /notin z). Therefore u /in x
    and not (u /in y and u /in z). Then u /in x and not u /in y /cap z. Hence
    u /in x /setminus (y /cap z).
  end.
qed.


Proposition 0310. x /setminus (y /cup z) = (x /setminus y) /cap (x /setminus z).

Proof.
  x /setminus (y /cup z) /subseteq (x /setminus y) /cap (x /setminus z).
  proof.
    Let u /in x /setminus (y /cup z). Then u /in x and u /notin y /cup z. Hence
    we have not (u /in y or u /in z). Thus u /notin y and u /notin z. Therefore
    u /in x and (u /notin y and u /notin z). Then (u /in x and u /notin y) and
    (u /in x and u /notin z). Hence u /in x /setminus y and u /in x /setminus z.
    Thus u /in (x /setminus y) /cap (x /setminus z).
  end.

  (x /setminus y) /cap (x /setminus z) /subseteq x /setminus (y /cup z).
  proof.
    Let u /in (x /setminus y) /cap (x /setminus z). Then u /in x /setminus y and
    u /in x /setminus z. Hence (u /in x and u /notin y) and (u /in x and
    u /notin z). Thus u /in x and (u /notin y and u /notin z). Therefore u /in x
    and not (u /in y or u /in z). Then u /in x and not u /in y /cup z. Hence
    u /in x /setminus (y /cup z).
  end.
qed.


# Subsets

Proposition 0311. x /subseteq x /cup y.

Proof.
  Let u /in x. Then u /in x or u /in y. Hence u /in x /cup y.
qed.


Proposition 0312. x /cap y /subseteq x.

Proof.
  Let u /in x /cap y. Then u /in x and u /in y. Hence u /in x.
qed.


Proposition 0313. x /subseteq y iff x /cup y = y.

Proof.
  If x /subseteq y then x /cup y = y.
  proof.
    Assume x /subseteq y.

    x /cup y /subseteq y.
    proof.
      Let u /in x /cup y. Then u /in x or u /in y. If u /in x then u /in y.
      Hence u /in y.
    end.

    y /subseteq x /cup y.
    proof.
      Let u /in y. Then u /in x or u /in y. Hence u /in x /cup y.
    end.
  end.

  If x /cup y = y then x /subseteq y.
  proof.
    Assume x /cup y = y. Let u /in x. Then u /in x or u /in y. Hence
    u /in x /cup y = y.
  end.
qed.


Proposition 0314. x /subseteq y iff x /cap y = x.

Proof.
  If x /subseteq y then x /cap y = x.
  proof.
    Assume x /subseteq y.

    x /cap y /subseteq x.
    proof.
      Let u /in x /cap y. Then u /in x and u /in y. Hence u /in x.
    end.

    x /subseteq x /cap y.
    proof.
      Let u /in x. Then u /in y. Hence u /in x and u /in y. Thus u /in x /cap y.
    end.
  end.

  If x /cap y = x then x /subseteq y.
  proof.
    Assume x /cap y = x. Let u /in x. Then u /in x /cap y. Hence u /in x and
    u /in y. Thus u /in y.
  end.
qed.


# The empty set

Proposition 0315. x /setminus x = /emptyset.

Proof.
  x /setminus x has no elements. Indeed x /setminus x = {u | u /in x and
  u /notin x}. Hence the thesis.
qed.


Proposition 0316. x /setminus /emptyset = x.

Proof.
  x /setminus /emptyset = {u | u /in x and u /notin /emptyset}. No object is an
  element of /emptyset. Hence x /setminus /emptyset = {u | u /in x}. Then we
  have the thesis.
qed.


# Complements

Proposition 0317. x /setminus (x /setminus y) = x /cap y.

Proof.
  x /setminus (x /setminus y) /subseteq x /cap y.
  proof.
    Let u /in x /setminus (x /setminus y). Then u /in x and
    u /notin x /setminus y. Hence u /notin x or u /in y. Thus u /in y. Therefore
    u /in x /cap y.
  end.

  x /cap y /subseteq x /setminus (x /setminus y).
  proof.
    Let u /in x /cap y. Then u /in x and u /in y. Hence
    u /notin x or u /in y. Thus u /notin x /setminus y. Therefore
    u /in x /setminus (x /setminus y).
  end.
qed.


Proposition 0318. y is a subset of x iff x /setminus (x /setminus y) = y.

Proof.
  If y is a subset of x then x /setminus (x /setminus y) = y.
  proof.
    Assume that y is a subset of x. Then x /cap y = y. Hence the thesis.
  end.

  If x /setminus (x /setminus y) = y then y is a subset of x.
  proof.
    Assume x /setminus (x /setminus y) = y. Hence every element of y is an
    element of x /setminus (x /setminus y). Thus every element of y is an
    element of x. Then we have the thesis.
  end.
qed.


Proposition 0319. x /cap (y /setminus z) = (x /cap y) /setminus (x /cap z).

Proof.
  x /cap (y /setminus z) /subseteq (x /cap y) /setminus (x /cap z).
  proof.
    Let u /in x /cap (y /setminus z). Then u /in x and u /in y /setminus z.
    Hence u /in x and u /in y. Thus u /in x /cap y and u /notin z.
    Therefore u /notin x /cap z. Then we have u /in (x /cap y) /setminus
    (x /cap z).
  end.

  (x /cap y) /setminus (x /cap z) /subseteq x /cap (y /setminus z).
  proof.
    Let u /in (x /cap y) /setminus (x /cap z). Then u /in x and u /in y.
    u /notin x /cap z. Hence u /notin z. Thus u /in y /setminus z. Therefore
    u /in x /cap (y /setminus z).
  end.
qed.
