# 4 Exponentiation

[read FLib/Statements/Library/Arithmetic/03_multiplication.ftl]


Let n,m,k,l denote natural numbers.


# 4.1 Axioms

Signature 0401. n^{m} is a natural number. Let the square of x stand for x^{2}.
Let the cube of x stand for x^{3}.

Axiom 0402. n^{0} = 1.

Axiom 0403. n^{m + 1} = n^{m} /cdot n.


# 4.2 Computation laws

# Powers of 0

Proposition 0404. Assume that n /neq 0. Then 0^{n} = 0.

Proof.
  Take a natural number m such that n = m + 1. Then

    0^{n}
  = 0^{m + 1}       # definition of m
  = 0^{m} /cdot 0   # 2nd exponentiation axiom
  = 0.              # 1st multiplication axiom
qed.


# Powers of 1

Proposition 0405. 1^{n} = 1.

Proof.
  [prove off]
  # Define P(x) = "1^{x} = 1" for any natural number x.
  Define P = {natural number x | 1^{x} = 1}.
  [/prove]

  Then P holds for 0.

  For all natural numbers x if P(x) then P(x + 1).
  proof.
    Let x be a natural number. Assume P(x). Then

      1^{x + 1}
    = 1^{x} /cdot 1   # 2nd exponentiation axiom
    = 1 /cdot 1       # P holds for x
    = 1.              # 1 is neutral wrt. multiplication
  end.

  Hence P holds for every natural number (by 0108).
qed.


# 1 as exponent

Proposition 0406. n^{1} = n.

Proof.
    n^{1}
  = n^{0 + 1}       # 1st addition axiom
  = n^{0} /cdot n   # 2nd exponentiation axiom
  = 1 /cdot n       # 1st exponentiation axiom
  = n.              # 1 is neutral wrt. multiplication
qed.


# 2 as exponent.

Proposition 0407. n^{2} = n /cdot n.

Proof.
    n^{2}
  = n^{1 + 1}       # definition of 2
  = n^{1} /cdot n   # 2nd exponentiation axiom
  = n /cdot n.      # last proposition
qed.


# Sum as exponent

Proposition 0408. k^{n + m} = k^{n} /cdot k^{m}.

Proof.
  [prove off]
  # Define P(z) = "x^{y + z} = x^{y} /cdot x^{z} for all natural numbers x,y"
  # for any natural number z.
  Define P = {natural number z | x^{y + z} = x^{y} /cdot x^{z} for all natural
  numbers x,y}.

  P holds for 0.
  proof.
    For all natural numbers x,y we have x^{y + 0} = x^{y} /cdot x^{0}.
    proof.
      Let x,y be natural numbers. Then

      x^{y + 0}
      = x^{y}               # 1st addition axiom
      = x^{y} /cdot 1       # 1 is neutral wrt. multiplication
      = x^{y} /cdot x^{0}.  # 1st exponentiation axiom
    end.
  end.

  For all natural numbers z if P(z) then P(z + 1).
  proof.
    Let z be a natural number.

    For all natural numbers x,y we have x^{y + (z + 1)} = x^{y} /cdot x^{z + 1}.
    proof.
      Let x,y be natural numbers. Then

        x^{y + (z + 1)}
      = x^{(y + z) + 1}               # 2nd addition axiom
      = x^{y + z} /cdot x             # 2nd exponentiation axiom
      = (x^{y} /cdot x^{z}) /cdot x   # P holds for z
      = x^{y} /cdot (x^{z} /cdot x)   # associativity of multiplication
      = x^{y} /cdot x^{z + 1}.        # 2nd exponentiation axiom
    end.
  end.

  Hence P holds for every natural number.
qed.


# Product as exponent

Proposition 0409. (k^{n})^{m} = k^{n /cdot m}.

Proof.
  [prove off]
  # Define P(z) = "(x^{y})^{z} = x^{y /cdot z} for all natural numbers x,y" for
  # any natural number z.
  Define P = {natural number z | (x^{y})^{z} = x^{y /cdot z} for all natural
  numbers x,y}.
  [/prove]

  P holds for 0. Indeed (x^{y})^{0} = 1 = x^{0} = x^{y /cdot 0} for all natural
  numbers x,y.

  For all natural numbers z if P(z) then P(z + 1).
  proof.
    Let z be a natural number. Assume P(z).

    For all natural numbers x,y we have (x^{y})^{z + 1} = x^{y /cdot (z + 1)}.
    proof.
      Let x,y be natural numbers. Then

        (x^{y})^{z + 1}
      = (x^{y})^{z} /cdot x^{y}   # 2nd exponentiation axiom
      = x^{y /cdot z} /cdot x^{y} # P holds for z
      = x^{(y /cdot z) + y}       # sum-as-exponent-law
      = x^{y /cdot (z + 1)}.      # 2nd multiplication axiom
    end.
  end.

  Therefore P holds for every natural number.
qed.


# Power of product

Proposition 0410. (n /cdot m)^{k} = n^{k} /cdot m^{k}.

Proof.
  [prove off]
  # Define P(z) = "(x /cdot y)^{z} = x^{z} /cdot y^{z} for all natural numbers
  # x,y" for any natural number z.
  Define P = {natural number z | (x /cdot y)^{z} = x^{z} /cdot y^{z} for all
  natural numbers x,y}.
  [/prove]

  P holds for 0. Indeed (x /cdot y)^{0} = 1 = 1 /cdot 1 = x^{0} /cdot y^{0} for
  all natural numbers x,y.

  For all natural numbers z if P(z) then P(z + 1).
  proof.
    Let z be a natural number. Assume P(z).

    For all natural numbers x,y we have (x /cdot y)^{z + 1} =
    x^{z + 1} /cdot y^{z + 1}.
    proof.
      Let x,y be natural numbers.

      (1) We have

        (x^{z} /cdot y^{z}) /cdot (x /cdot y)
      = ((x^{z} /cdot y^{z}) /cdot x) /cdot y  # associativity of multiplication
      = (x^{z} /cdot (y^{z} /cdot x)) /cdot y  # associativity of multiplication
      = (x^{z} /cdot (x /cdot y^{z})) /cdot y  # commutativity of multiplication
      = ((x^{z} /cdot x) /cdot y^{z}) /cdot y  # associativity of multiplication
      = (x^{z} /cdot x) /cdot (y^{z} /cdot y). # associativity of multiplication

      Hence

        (x /cdot y)^{z + 1}
      = (x /cdot y)^{z} /cdot (x /cdot y)       # 2nd exponentiation axiom
      = (x^{z} /cdot y^{z}) /cdot (x /cdot y)   # induction hypothesis
      = (x^{z} /cdot x) /cdot (y^{z} /cdot y)   # claim (1)
      = x^{z + 1} /cdot y^{z + 1}.              # 2nd exponentiation axiom
    end.
  end.

  Therefore P holds for every natural number.
qed.


# Power is zero

Proposition 0411. n^{m} = 0 iff n = 0 and m /neq 0.

Proof.
  If n^{m} = 0 then n = 0 and m /neq 0.
  proof.
    [prove off]
    # Define P(y) = "for all natural numbers x if x^{y} = 0 then x = 0 and
    # y /neq 0" for any natural number y.
    Define P = {natural number y | for all natural numbers x if x^{y} = 0 then
    x = 0 and y /neq 0}.
    [/prove]

    P holds for 0. Indeed for all natural numbers x if x^{0} = 0 then we have a
    contradiction.

    For all natural numbers y if P(y) then P(y + 1).
    proof.
      Let y be a natural number. Assume P(y).

      For all natural numbers x if x^{y + 1} = 0 then x = 0 and y + 1 /neq 0.
      proof.
        Let x be a natural number. Assume x^{y + 1} = 0. Then 0 = x^{y + 1} =
        x^{y} /cdot x. Hence x^{y} = 0 or x = 0. We have y + 1 /neq 0 and if
        x^{y} = 0 then x = 0. Hence the thesis.
      end.
    end.

    Thus P holds for every natural number.
  end.

  If n = 0 and m /neq 0 then n^{m} = 0.
  proof.
    Assume n = 0 and m /neq 0. Take a natural number k such that m = k + 1. Then
    
      n^{m}
    = n^{k + 1}       # definition of m
    = n^{k} /cdot n   # 2nd exponentiation axiom
    = 0^{k} /cdot 0   # n = 0
    = 0.              # 1st multiplication axiom
  end.
qed.
