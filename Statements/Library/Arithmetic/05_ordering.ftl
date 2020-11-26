# 5 Ordering

[read FLib/Statements/Library/Arithmetic/04_exponentiation.ftl]


Let n,m,k,l denote natural numbers.


# 5.1 Definitions and immediate consequences

Definition 0501. n is positive iff n /neq 0.

Definition 0502. n < m iff there exists a positive natural number k such that
m = n + k. Let n is less than m stand for n < m. Let n > m stand for m < n. Let
n is greater than m stand for n > m.

Definition 0503. n /leq m iff there exists a natural number k such that
m = n + k. Let n is less than or equal to m stand for n /leq m. Let n /geq m
stand for m /leq n. Let n is greater than or equal to m stand for n /geq m.


Proposition 0504. n /leq m iff n < m or n = m.

Proof.
  If n /leq m then n < m or n = m.
  proof.
    Assume n /leq m. Take a natural number k such that m = n + k. If k = 0 then
    n = m. If k /neq 0 then n < m.
  end.

  If n < m or n = m then n /leq m.
  proof.
    If n < m then there is a positive natural number k such that m = n + k.
    If n = m then m = n + 0. Thus if n < m then there is a natural number k such
    that m = n + k. Hence the thesis.
  end.
qed.


Proposition 0505. 0 < n iff 0 /neq n.

Proof.
  If 0 < n then 0 /neq n.
  proof.
    Assume 0 < n. Then we can take a positive natural number k such that n =
    0 + k = k. Hence the thesis.
  end.

  If 0 /neq n then 0 < n.
  proof.
    Assume 0 /neq n. Then we can take a natural number k such that n = k + 1.
    Hence n = 0 + (k + 1). k + 1 is positive. Thus 0 < n.
  end.
qed.


# 5.2 Basic properties

# Irreflexivity

Proposition 0506. n is not less than n.

Proof.
  Assume the contrary. Then we can take a positive natural number k such that
  n = n + k. Then we have 0 = k. Contradiction.
qed.


# < implies /neq

Proposition 0507. If n < m then n /neq m.

Proof.
  Assume n < m. Take a positive natural number k such that m = n + k. If n = m
  then k = 0. Hence n /neq m.
qed.


# Antisymmetry of /leq

Proposition 0508. If n /leq m and m /leq n then n = m.

Proof.
  Assume n /leq m and m /leq n. Take natural numbers k,l such that m = n + k and
  n = m + l. Then m = (m + l) + k = m + (l + k). Hence l + k = 0. Therefore
  l = 0 = k. Then we have the thesis.
qed.


# Transitivity of <

Proposition 0509. If n < m < k then n < k.

Proof.
  Assume n < m < k. Take positive natural numbers a,b such that m = n + a and
  k = m + b. Then k = (n + a) + b = n + (a + b). a + b is positive. Hence n < k.
qed.


# Transitivity of /leq

Proposition 0510. If n /leq m /leq k then n /leq k.

Proof.
  Case n = m = k. Obvious.

  Case n = m < k. Obvious.

  Case n < m = k. Obvious.

  Case n < m < k. Obvious.
qed.


# "Semitransitivity" I

Proposition 0511. If n /leq m < k then n < k.

Proof.
  Assume n /leq m < k.

  Case n = m. Obvious.

  Case n < m. Obvious.
qed.


# "Semitransitivity" II

Proposition 0512. If n < m /leq k then n < k.

Proof.
  Assume n < m /leq k.

  Case m = k. Obvious.

  Case m < k. Obvious.
qed.


# < implies /leq for successor

Proposition 0513. If n < m then n + 1 /leq m.

Proof.
  Assume n < m. Take a positive natural number k such that m = n + k.

  Case k = 1.
    Then m = n + 1. Hence n + 1 /leq m.
  end.

  Case k /neq 1.
    Then we can take a natural number l such that k = l + 1. Then
    m = n + (l + 1) = (n + l) + 1 = (n + 1) + l. l is positive. Thus
    n + 1 < m.
  end.
qed.


# Trichotomy

Proposition 0514. n < m or n = m or n > m.

Proof.
  [prove off]
  # Define P(y) = "for all natural numbers x we have x < y or x = y or x > y"
  # for any natural number y.
  (1) Define P = {natural number y | for all natural numbers x we have x < y or
  x = y or x > y}.
  [/prove]

  P holds for 0.

  For all natural numbers y if P(y) then P(y + 1).
  proof.
    Let y be a natural number. Assume P(y).

    (2) For all natural numbers x we have x < y + 1 or x = y + 1 or x > y + 1.
    proof.
      Let x be a natural number.

      Case x < y. Obvious.

      Case x = y. Obvious.

      Case x > y.
        Take a positive natural number k such that x = y + k.

        Case k = 1. Obvious.

        Case k /neq 1.
          Take a natural number l such that x = (y + 1) + l. Hence x > y + 1.
          Indeed l is positive.
        end.
      end.
    end.

    Hence the thesis (by 1). Indeed y + 1 is a natural number.
  end.

  Thus P holds for every natural number.
qed.


# Not less iff geq

Proposition 0515. n is not less than m iff n /geq m.

Proof.
  If n is not less than m then n /geq m.
  proof.
    Assume that n is not less than m. Then n = m or n > m. Hence n /geq m.
  end.

  If n /geq m then n is not less than m.
  proof.
    Assume n /geq m. Assume n < m. Then n /leq m. Hence n = m. Contradiction.
  end.
qed.


# < is stable under addition

Proposition 0516. n < m iff n + k < m + k.

Proof.
  If n < m then n + k < m + k.
  proof.
    Assume n < m. Take a positive natural number l such that m = n + l. Then
    m + k = (n + l) + k = (n + k) + l. Hence the thesis.
  end.

  If n + k < m + k then n < m.
  proof.
    Assume n + k < m + k. Take a positive natural number l such that m + k =
    (n + k) + l. (n + k) + l = n + (k + l) = n + (l + k) = (n + l) + k. Hence
    m + k = (n + l) + k. Thus m = n + l (by 0205). Therefore n < m.
  end.
qed.


Corollary 0517. n < m iff k + n < k + m.

Proof.
  k + n = n + k and k + m = m + k. Hence k + n < k + m iff n + k < m + k.
end.


Corollary 0518. n /leq m iff k + n /leq k + m.


Corollary 0519. n /leq m iff n + k /leq m + k.


# < is stable under multiplication

Proposition 0520. Assume k /neq 0. n < m iff n /cdot k < m /cdot k.

Proof.
  If n < m then n /cdot k < m /cdot k.
  proof.
    Assume n < m. Take a positive natural number l such that m = n + l. Then
    m /cdot k = (n + l) /cdot k = (n /cdot k) + (l /cdot k). l /cdot k is
    positive. Hence the thesis.
  end.

  If n /cdot k < m /cdot k then n < m.
  proof.
    [prove off]
    # Define P(x) = "for all natural numbers y,z if x /cdot z < y /cdot z then
    # x < y" for any natural number x.
    (1) Define P = {natural number x | for all natural numbers y,z if
    x /cdot z < y /cdot z then x < y}.
    [/prove]

    P holds for 0.

    For all natural numbers x if P(x) then P(x + 1).
    proof.
      Let x be a natural number. Assume P(x).

      For all natural numbers y,z if (x + 1) /cdot z < y /cdot z then x + 1 < y.
      proof.
        Let y,z be natural numbers. Assume (x + 1) /cdot z < y /cdot z. Then
        (x /cdot z) + z < y /cdot z. Hence x /cdot z < y /cdot z. Thus x < y.
        Then x + 1 /leq y. If x + 1 = y then (x + 1) /cdot z = y /cdot z. Hence
        the thesis.
      end.

      Hence the thesis (by 1). Indeed x + 1 is a natural number.
    end.

    Therefore P holds for every natural number.
  end.
qed.


Corollary 0521. Assume k /neq 0. n < m iff k /cdot n < k /cdot m.

Proof.
  k /cdot n = n /cdot k and k /cdot m = m /cdot k. Hence k /cdot n < k /cdot m
  iff n /cdot k < m /cdot k.
end.


Proposition 0522. If n,m > k then n /cdot m > k.

Proof.
  [prove off]
  # Define P(x) = "if x,m > k then x /cdot m > k" for any natural number x.
  Define P = {natural number x | if x,m > k then x /cdot m > k}.
  [/prove]

  P holds for 0.

  For all natural numbers x if P(x) then P(x + 1).
  proof.
    Let x be a natural number. Assume P(x).

    If x + 1, m > k then (x + 1) /cdot m > k.
    proof.
      Assume x + 1, m > k. Then (x + 1) /cdot m = (x /cdot m) + m. If x = 0 then
      (x /cdot m) + m = 0 + m = m > k. If x /neq 0 then (x /cdot m) + m > m > k.
      Hence (x + 1) /cdot m > k.
    end.
  end.

  Hence P holds for every natural number.
qed.


Corollary 0523. Assume k /neq 0. n /leq m iff k /cdot n /leq k /cdot m.


Corollary 0524. Assume k /neq 0. n /leq m iff n /cdot k /leq m /cdot k.


# < is stable under exponentiation

Proposition 0525. Assume k /neq 0. n < m iff n^{k} < m^{k}.

Proof.
  If n < m then n^{k} < m^{k}.
  proof.
    Case k = 1. Obvious.

    Case k /neq 1.
      Then k > 1. Indeed k < 1 or k = 1 or k > 1.

      [prove off]
      # Define P(z) = "for all natural numbers x,y if x < y and z > 1 then
      # x^{z} < y^{z}" for any natural number z.
      (1) Define P = {natural number z | for all natural numbers x,y if x < y
      and z > 1 then x^{z} < y^{z}}.
      [/prove]

      P holds for 0.

      P holds for 1.

      P holds for 2.
      proof.
        For all natural numbers x,y if x < y then x^{2} < y^{2}.
        proof.
          Let x,y be natural numbers. Assume x < y.

          Case x = 0 or y = 0. Obvious.

          Case x,y /neq 0.
            Then x /cdot x < x /cdot y < y /cdot y. Hence x^{2} = x /cdot x <
            x /cdot y < y /cdot y = y^{2}.
          end.
        end.
      end.

      For all natural numbers z if P(z) then P(z + 1).
      proof.
        Let z be a natural number. Assume P(z).

        For all natural numbers x,y if x < y and z + 1 > 1 then
        x^{z + 1} < y^{z + 1}.
        proof.
          Let x,y be natural numbers. Assume x < y and z + 1 > 1. (3) Then
          x^{z} < y^{z}.

          Case z /leq 1.
            Then z = 0 or z = 1. Hence z + 1 = 1 or z + 1 = 2. Thus P holds for
            z + 1. Therefore x^{z + 1} < y^{z + 1} (by 1).
          end.

          Case z > 1.
            Case x = 0.
              Then y /neq 0. Hence x^{z + 1} = 0 < y^{z} /cdot y = y^{z + 1}.
              Thus x^{z + 1} < y^{z + 1}.
            end.

            Case x /neq 0.
              Then x^{z} /cdot x < y^{z} /cdot x < y^{z} /cdot y. Indeed
              y^{z} /neq 0. Hence x^{z + 1} = x^{z} /cdot x < y^{z} /cdot x <
              y^{z} /cdot y = y^{z + 1}. Thus x^{z + 1} < y^{z + 1} (by 0511).
            end.
          end.

          Hence the thesis. Indeed z /leq 1 or z > 1.
        end.

        Thus P holds for z + 1 (by 1). Indeed z + 1 is a natural number.
      end.

      Thus P holds for every natural number. Then we have the thesis (by 1).
    end.
  end.

  If n^{k} < m^{k} then n < m.
  proof.
    [prove off]
    # Define P(z) = "for all natural numbers x,y if x /geq y then
    # x^{z} /geq y^{z}" for any natural number z.
    (1) Define P = {natural number z | for all natural numbers x,y if x /geq y
    then x^{z} /geq y^{z}}.
    [/prove]

    P holds for 0.

    For all natural numbers z if P(z) then P(z + 1).
    proof.
      Let z be a natural number. Assume P(z).

      For all natural numbers x,y if x /geq y then x^{z + 1} /geq y^{z + 1}.
      proof.
        Let x,y be natural numbers. Assume x /geq y. Then x^{z} /geq y^{z}.
        Hence x^{z} /cdot x /geq y^{z} /cdot x /geq y^{z} /cdot y. Thus
        x^{z + 1} = x^{z} /cdot x /geq y^{z} /cdot x /geq y^{z} /cdot y =
        y^{z + 1}. Therefore x^{z + 1} /geq y^{z + 1}.
      end.

      Hence the thesis (by 1). Indeed z + 1 is a natural number.
    end.

    Thus P holds for every natural number. Therefore if n /geq m then
    n^{k} /geq m^{k} (by 1). Then we have the thesis.
  end.
qed.


Corollary 0526. Assume k /neq 0. If n^{k} = m^{k} then n = m.

Proof.
  Assume n /neq m. Then n < m or m < n. If n < m then n^{k} < m^{k}. If m < n
  then m^{k} < n^{k}. Thus n^{k} /neq m^{k}. Hence the thesis.
qed.


Corollary 0527. Assume k /neq 0. n^{k} /leq m^{k} iff n /leq m.

Proof.
  If n^{k} < m^{k} then n < m. If n^{k} = m^{k} then n = m.

  If n < m then n^{k} < m^{k}. If n = m then n^{k} = m^{k}.
qed.


Proposition 0528. Assume k > 1. n < m iff k^{n} < k^{m}.

Proof.
  If n < m then k^{n} < k^{m}.
  proof.
    [prove off]
    # Define P(y) = "for all natural numbers x,z if z > 1 and x < y then
    # z^{x} < z^{y}" for any natural number y.
    (1) Define P = {natural number y | for all natural numbers x,z if z > 1 and
    x < y then z^{x} < z^{y}}.
    [/prove]

    P holds for 0.

    For all natural numbers y if P(y) then P(y + 1).
    proof.
      Let y be a natural number. Assume P(y).

      For all natural numbers x,z if z > 1 and x < y + 1 then z^{x} < z^{y + 1}.
      proof.
        Let x,z be natural numbers. Assume z > 1 and x < y + 1. Then x /leq y.
        We have z^{y} /cdot 1 < z^{y} /cdot z. Indeed z^{y} /neq 0.

        Case x = y.
          Then z^{x} = z^{y} < z^{y} /cdot z = z^{y + 1}.
        end.

        Case x < y.
          Then z^{x} < z^{y} < z^{y} /cdot z = z^{y + 1}.
        end.
      end.

      Hence the thesis (by 1). Indeed y + 1 is a natural number.
    end.

    Thus P holds for every natural number (by 0108). Then we have the thesis (by
    1).
  end.

  If k^{n} < k^{m} then n < m.
  proof.
    [prove off]
    # Define P(x) = "for all natural numbers y,z if x /geq y then
    # z^{x} /geq z^{y} or z /leq 1" for any natural number x.
    (2) Define P = {natural number x | for all natural numbers y,z if x /geq y
    then z^{x} /geq z^{y} or z /leq 1}.
    [/prove]

    P holds for 0.

    For all natural numbers x if P(x) then P(x + 1).
    proof.
      Let x be a natural number. Assume P(x).

      For all natural numbers y,z if x + 1 /geq y then z^{x + 1} /geq z^{y} or
      z /leq 1.
      proof.
        Let y,z be natural numbers. Assume x + 1 /geq y.

        Case x + 1 = y. Trivial.

        Case x + 1 > y.
          Then x /geq y. Hence z^{x} /geq z^{y} or z /leq 1 (by 2).

          Case z /leq 1. Trivial.

          Case z^{x} /geq z^{y}.
            We have z^{x} /cdot 1 /leq z^{x} /cdot z. Indeed 1 /leq z and
            z^{x} /neq 0. Hence z^{y} /leq z^{x} = z^{x} /cdot 1 /leq
            z^{x} /cdot z = z^{x + 1}.
          end.
        end.
      end.

      Hence the thesis (by 2). Indeed x + 1 is a natural number.
    end.

    Thus P holds for every natural number. Therefore if n /geq m then
    k^{n} /geq k^{m} or k /leq 1 (by 2). Then we have the thesis.
  end.
qed.


Corollary 0529. Assume k > 1. If k^{n} = k^{m} then n = m.

Proof.
  Assume n /neq m. Then n < m or m < n. If n < m then k^{n} < k^{m}. If m < n
  then k^{m} < k^{n}. Thus k^{n} /neq k^{m}. Hence the thesis.
qed.


Corollary 0530. Assume k > 1. n /leq m iff k^{n} /leq k^{m}.


# succ is immediate successor I

Proposition 0531. If n < m /leq n + 1 then m = n + 1.

Proof.
  Assume n < m /leq n + 1. Take a positive natural number k such that
  m = n + k. Take a natural number l such that n + 1 = m + l. Then n + 1 =
  m + l = (n + k) + l = n + (k + l). Hence k + l = 1.

  We have l = 0.
  proof.
    Assume the contrary. Then k,l > 0.

    Case k,l = 1.
      Then k + l = 2 /neq 1. Contradiction.
    end.

    Case k = 1 and l /neq 1.
      Then l > 1. Hence k + l > 1 + l > 1. Contradiction.
    end.

    Case k /neq 1 and l = 1.
      Then k > 1. Hence k + l > k + 1 > 1. Contradiction.
    end.

    Case k,l /neq 1.
      Take natural numbers a,b such that k = a + 1 and l = b + 1. Indeed
      k,l /neq 0. Hence k = a + 1 and l = b + 1. Thus k,l > 1. Indeed a,b are
      positive.
    end.
  end.

  Then we have n + 1 = m + l = m + 0 = m.
qed.


# succ is immediate successor II

Proposition 0532. If n /leq m < n + 1 then n = m.

Proof.
  Assume n /leq m < n + 1.

  Case n = m. Obvious.

  Case n < m.
    Then n < m /leq n + 1. Hence n = m.
  end.
qed.


# Any successor is /geq 1

Proposition 0533. n + 1 /geq 1.

Proof.
  Case n = 0. Obvious.

  Case n /neq 0.
    Then n > 0. Hence n + 1 > 0 + 1 = 1.
  end.
qed.
