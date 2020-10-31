# 3 Multiplication

[read FLib/Statements/Library/Arithmetic/02_addition.ftl]


Let k,l,m,n denote natural numbers.


# 3.1 Axioms

Axiom 0301. n \cdot 0 = 0.

Axiom 0302. n \cdot (m + 1) = (n \cdot m) + n.


Proposition 0303. n \cdot m is a natural number.

Proof.
  [prove off]
  # Define P(y) iff x \cdot y is a natural number for all natural numbers x.
  Define P = {natural number y | x \cdot y is a natural number for all natural
  numbers x}.
  [prove on]

  P holds for 0.

  For all natural numbers y if P(y) then P(y + 1).
  proof.
    Let y be a natural number. Assume P(y).

    x \cdot (y + 1) is a natural number for all natural numbers x.
    proof.
      Let x be a natural number. Then x \cdot y is a natural number. Thus
      (x \cdot y) + x is a natural number. x \cdot (y + 1) = (x \cdot y) + x.
      Hence the thesis.
    end.
  end.

  Thus P holds for every natural number.
qed.


# 3.2 Computation laws

# Distributivity

Proposition 0304. n \cdot (m + k) = (n \cdot m) + (n \cdot k).

Proof.
  [prove off]
  # Define P(z) iff x \cdot (y + z) = (x \cdot y) + (x \cdot z) for all natural
  # numbers x,y.
  Define P = {natural number z | x \cdot (y + z) = (x \cdot y) + (x \cdot z) for
  all natural numbers x,y}.
  [prove on]

  P holds for 0. Indeed for all natural numbers x,y we have x \cdot (y + 0) =
  x \cdot y = (x \cdot y) + 0 = (x \cdot y) + (x \cdot 0).

  For all natural numbers z if P(z) then P(z + 1).
  proof.
    Let z be a natural number. Assume P(z).

    For all natural numbers x,y we have x \cdot (y + (z + 1)) =
    (x \cdot y) + (x \cdot (z + 1)).
    proof.
      Let x,y be natural numbers. Then

        x \cdot (y + (z + 1))
      = x \cdot ((y + z) + 1)             # 2nd addition axiom
      = (x \cdot (y + z)) + x             # 2nd multiplication axiom
      = ((x \cdot y) + (x \cdot z)) + x   # P holds for z
      = (x \cdot y) + ((x \cdot z) + x)   # associativity of addition
      = (x \cdot y) + (x \cdot (z + 1)).  # 2nd multiplication axiom

      Hence the thesis.
    end.
  end.

  Therefore P holds for every natural number.
qed.


Proposition 0305. (n + m) \cdot k = (n \cdot k) + (m \cdot k).

Proof.
  [prove off]
  # Define P(z) iff (x + y) \cdot z = (x \cdot z) + (y \cdot z) for all natural
  # numbers x,y.
  Define P = {natural number z | (x + y) \cdot z = (x \cdot z) + (y \cdot z) for
  all natural numbers x,y}.
  [prove on]

  P(0). Indeed (x + y) \cdot 0 = 0 = 0 + 0 = (x \cdot 0) + (y \cdot 0) for all
  natural numbers x,y.

  For all natural numbers z if P(z) then P(z + 1).
  proof.
    Let z be a natural number. Assume P(z).

    (x + y) \cdot (z + 1) = (x \cdot (z + 1)) + (y \cdot (z + 1)) for all
    natural numbers x,y.
    proof.
      Let x,y be natural numbers.

      (1) We have ((x \cdot z) + ((y \cdot z) + x)) + y =
      (((x \cdot z) + x) + (y \cdot z)) + y.

      Hence

        (x + y) \cdot (z + 1)
      = ((x + y) \cdot z) + (x + y)             # 2nd multiplication axiom
      = ((x \cdot z) + (y \cdot z)) + (x + y)   # P holds for z
      = (((x \cdot z) + (y \cdot z)) + x) + y   # assoziativity of addition
      = ((x \cdot z) + ((y \cdot z) + x)) + y   # assoziativity of addition
      = (((x \cdot z) + x) + (y \cdot z)) + y   # claim (1)
      = ((x \cdot z) + x) + ((y \cdot z) + y)   # assoziativity of addition
      = (x \cdot (z + 1)) + (y \cdot (z + 1)).  # 2nd multiplication axiom
    end.
  end.

  Thus P holds for every natural number.
qed.


# Neutral element

Proposition 0307. n \cdot 1 = n.

Proof.
    n \cdot 1
  = n \cdot (0 + 1)   # commutativity of addition, 1st addition axiom
  = (n \cdot 0) + n   # 2nd multiplication axiom
  = 0 + n             # 1st multiplication axiom
  = n.                # commutativity of addition, 1st addition axiom
qed.


# Associativity

Proposition 0306. n \cdot (m \cdot k) = (n \cdot m) \cdot k.

Proof.
  [prove off]
  # Define P(z) iff x \cdot (y \cdot z) = (x \cdot y) \cdot z for all natural
  # numbers x,y.
  Define P = {natural number z | x \cdot (y \cdot z) = (x \cdot y) \cdot z for
  all natural numbers x,y}.
  [prove on]

  P(0). Indeed for all natural numbers x,y we have x \cdot (y \cdot 0) =
  x \cdot 0 = 0 = (x \cdot y) \cdot 0.

  For all natural numbers z if P(z) then P(z + 1).
  proof.
    Let z be a natural number. Assume P(z).

    For all natural numbers x,y we have x \cdot (y \cdot (z + 1)) =
    (x \cdot y) \cdot (z + 1).
    proof.
      Let x,y be natural numbers.

      x \cdot (y \cdot (z + 1))
      = x \cdot ((y \cdot z) + y)                     # 2nd multiplication axiom
      = (x \cdot (y \cdot z)) + (x \cdot y)           # left distributivity
      = ((x \cdot y) \cdot z) + (x \cdot y)           # P holds for z
      = ((x \cdot y) \cdot z) + ((x \cdot y) \cdot 1) # 1 is neutral wrt. multiplication
      = (x \cdot y) \cdot (z + 1).                    # left distributivity
    end.
  end.

  Hence P holds for every natural number.
qed.


# Commutativity

Proposition 0308. n \cdot m = m \cdot n.

Proof.
  [prove off]
  # Define P(y) iff x \cdot y = y \cdot x for all natural numbers x.
  Define P = {natural number y | x \cdot y = y \cdot x for all natural numbers
  x}.
  [prove on]

  P holds for 0.
  proof.
    For all natural numbers x we have x \cdot 0 = 0 \cdot x.
    proof.
      [prove off]
      # Define Q(x) iff x \cdot 0 = 0 \cdot x.
      Define Q = {natural number x | x \cdot 0 = 0 \cdot x}.
      [prove on]

      Q holds for 0.

      For all natural numbers x if Q(x) then Q(x + 1).
      proof.
        Let x be a natural number. Assume Q(x). Then

        (x + 1) \cdot 0
        = 0                 # 1st multiplication axiom
        = x \cdot 0         # 1st multiplication axiom
        = 0 \cdot x         # Q holds for x
        = (0 \cdot x) + 0   # 1st addition axiom
        = 0 \cdot (x + 1).  # 2nd multiplication axiom
      end.
    end.
  end.

  P holds for 1.
  proof.
    For all natural numbers x we have x \cdot 1 = 1 \cdot x.
    proof.
      [prove off]
      # Define Q(x) iff x \cdot 1 = 1 \cdot x.
      Define Q = {natural number x | x \cdot 1 = 1 \cdot x}.
      [prove on]

      Q holds for 0.

      For all natural numbers x If Q(x) then Q(x + 1).
      proof.
        Let x be a natural number. Assume Q(x). Then

          (x + 1) \cdot 1
        = (x \cdot 1) + 1   # right-distributivity,
        = (1 \cdot x) + 1   # Q holds for 1 
        = 1 \cdot (x + 1).  # left-distributivity
      end.

      Hence the thesis (by 0107).
    end.
  end.

  For all natural numbers y if P(y) then P(y + 1).
  proof.
    Let y be a natural number. Assume P(y).

    For all natural numbers x we have x \cdot (y + 1) = (y + 1) \cdot x.
    proof.
      Let x be a natural number. Then

      x \cdot (y + 1)
      = (x \cdot y) + (x \cdot 1)   # left distributivity
      = (y \cdot x) + (1 \cdot x)   # P holds for y and for 1
      = (1 \cdot x) + (y \cdot x)   # commutativity of addition
      = (1 + y) \cdot x             # right distributivity
      = (y + 1) \cdot x.            # commutativity of addition
    end.
  end.

  Hence P holds for every natural number (by 0107).
qed.


# There are no zero-divisors

Proposition 0309. If n \cdot m = 0 then n = 0 or m = 0.

Proof.
  Assume n \cdot m = 0.

  If n and m are not equal to 0 then we have a contradiction.
  proof.
    Assume n,m \neq 0. Take natural numbers a,b such that n = (a + 1) and m =
    (b + 1). Then

    0
    = n \cdot m
    = (a + 1) \cdot (b + 1)
    = ((a + 1) \cdot b) + (a + 1)
    = (((a + 1) \cdot b) + a) + 1.

    Hence 0 = k + 1 for some natural number k. Contradiction.
  end.

  Thus n = 0 or m = 0.
qed.


# Cancellation laws

Proposition 0310. Assume k \neq 0. Then if n \cdot k = m \cdot k then n = m.

Proof.
  [prove off]
  # Define P(x) iff for all natural numbers y,z if x \cdot z = y \cdot z and
  # z \neq 0 then x = y.
  Define P = {natural number x | for all natural numbers y,z if x \cdot z =
  y \cdot z and z \neq 0 then x = y}.
  [prove on]

  P holds for 0.
  proof.
    For all natural numbers y,z if 0 \cdot z = y \cdot z and z \neq 0 then 0 = y.
    proof.
      Let y,z be natural numbers. Assume that 0 \cdot z = y \cdot z and z \neq 0.
      Then y \cdot z = 0. Hence y = 0 or z = 0. Thus y = 0.
    end.
  end.

  For all natural numbers x if P(x) then P(x + 1).
  proof.
    Let x be a natural number. Assume P(x).

    For all natural numbers y,z if (x + 1) \cdot z = y \cdot z and z \neq 0 then
    x + 1 = y.
    proof.
      Let y,z be natural numbers. Assume that (x + 1) \cdot z = y \cdot z and
      z \neq 0.

      Case y = 0.
        Then (x + 1) \cdot z = 0. Hence x + 1 = 0. Contradiction.
      end.

      Case y \neq 0.
        Take a natural number p such that y = p + 1. Then (x + 1) \cdot z =
        (p + 1) \cdot z. Hence (x \cdot z) + z = (p \cdot z) + z. Thus
        x \cdot z = p \cdot z (by 0206, 0303). Then we have x = p. Therefore
        x + 1 = p + 1 = y.
      end.
    end.
  end.

  P holds for every natural number.
qed.


Corollary 0311. Assume k \neq 0. Then if k \cdot n = k \cdot m then n = m.

Proof.
  Assume k \cdot n = k \cdot m. We have k \cdot n = n \cdot k and k \cdot m =
  m \cdot k. Hence n \cdot k = m \cdot k. Thus n = m.
qed.
