# 2 Addition

[read FLib/Statements/Library/Arithmetic/01_peano-axioms.ftl]


Let k,l,m,n denote natural numbers.


# 2.1 Axioms

Axiom 0201. n + 0 = n.

Axiom 0202. n + (m + 1) = (n + m) + 1.


# 2.2 Computation laws

# Associativity

Proposition 0203. n + (m + k) = (n + m) + k.

Proof.
  [prove off]
  # Define P(z) = "x + (y + z) = (x + y) + z for all natural numbers x,y" for
  # any natural number z.
  Define P = {natural number z | x + (y + z) = (x + y) + z for all natural
  numbers x,y}.
  [/prove]

  We have P(0). Indeed x + (y + 0) = x + y = (x + y) + 0 for all natural numbers
  x,y.

  For all natural numbers z if P(z) then P(z + 1).
  proof.
    Let z be a natural number. Assume P(z). Then x + (y + z) = (x + y) + z for
    all natural numbers x,y.

    x + (y + (z + 1)) = (x + y) + (z + 1) for all natural numbers x,y.
    proof.
      Let x,y be natural numbers. Then x + y is a natural number. Thus

        x + (y + (z + 1))
      = x + ((y + z) + 1)   # 2nd addition axiom
      = (x + (y + z)) + 1   # 2nd addition axiom
      = ((x + y) + z) + 1   # P holds for z
      = (x + y) + (z + 1).  # 2nd addition axiom

      Hence the thesis.
    end.
  end.

  Thus P holds for every natural number.
qed.


# Commutativity

Proposition 0204. n + m = m + n.

Proof.
  [prove off]
  # Define P(y) = "x + y = y + x for all natural numbers x" for any natural
  # number y.
  Define P = {natural number y | x + y = y + x for all natural numbers x}.
  [/prove]

  P(0).
  proof.
    [prove off]
    # Define Q(x) = "x + 0 = 0 + x" for any natural number x.
    Define Q = {natural number x | x + 0 = 0 + x}.
    [/prove]

    Q holds for 0.

    For all natural numbers x if Q(x) then Q(x + 1).
    proof.
      Let x be a natural number. Assume Q(x). Then x + 0 = 0 + x. Hence

        (x + 1) + 0
      = x + 1         # 1st addition axiom
      = (x + 0) + 1   # 1st addition axiom
      = (0 + x) + 1   # Q holds for x
      = 0 + (x + 1).  # 2nd addition axiom
    end.

    Thus P holds for 0 (by 0108).
  end.

  P holds for 1.
  proof.
    [prove off]
    # Define Q(x) = "x + 1 = 1 + x" for any natural number x.
    Define Q = {natural number x | x + 1 = 1 + x}.
    [/prove]

    Q holds for 0.

    For all natural numbers x if Q(x) then Q(x + 1).
    proof.
      Let x be a natural number. Assume Q(x). Then x + 1 = 1 + x. Hence

        (x + 1) + 1
      = (1 + x) + 1   # Q holds for x
      = 1 + (x + 1).  # 2nd addition axiom
    end.

    Thus P holds for 1 (by 0108).
  end.

  For all natural numbers x if P(x) then P(x + 1).
  proof.
    Let x be an natural number. Assume P(x).

    (x + 1) + y = y + (x + 1) for all natural numbers y.
    proof.
      Let y be a natural number. Then

        (x + 1) + y
      = x + (1 + y)   # associativity of addition
      = (1 + y) + x   # P holds for x
      = (y + 1) + x   # P holds for 1
      = y + (x + 1).  # associativity of addition, P holds for 1
    end.
  end.

  Hence P holds for every natural number.
qed.


# Cancellation laws

Proposition 0205. If n + k = m + k then n = m.

Proof.
  [prove off]
  # Define P(z) = "for all natural numbers x,y if x + z = y + z then x = y" for
  # any natural number z.
  (1) Define P = {natural number z | for all natural numbers x,y if
  x + z = y + z then x = y}.
  [/prove]

  P holds for 0.

  For all natural numbers z if P(z) then P(z + 1).
  proof.
    Let z be a natural number. Assume P(z).

    For all natural numbers x,y if x + (z + 1) = y + (z + 1) then x = y.
    proof.
      Let x,y be natural numbers. Assume x + (z + 1) = y + (z + 1). Then
      (x + z) + 1 = (y + z) + 1. Hence x + z = y + z (by 0106). Thus
      x = y.
    end.

    Hence the thesis.
  end.

  Therefore P holds for every natural number. Hence the thesis (by 1).
qed.


Corollary 0206. If k + n = k + m then n = m.

Proof.
  Assume k + n = k + m. We have k + n = n + k and k + m = m + k. Hence n + k =
  m + k. Thus n = m.
qed.
