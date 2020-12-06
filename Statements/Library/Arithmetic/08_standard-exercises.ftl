# 8 Standard exercises

[read FLib/Statements/Library/Arithmetic/06_factorial.ftl]
[read FLib/Statements/Library/Arithmetic/07_induction.ftl]


Let k,l,m,n denote natural numbers.


Proposition 0801. (n + 1)^{2} = (n^{2} + (2 /cdot n)) + 1.

Proof.
    (n + 1)^{2}
  = (n + 1) /cdot (n + 1)
  = ((n + 1) /cdot n) + (n + 1)
  = ((n /cdot n) + n) + (n + 1)
  = (n^{2} + n) + (n + 1)
  = ((n^{2} + n) + n) + 1
  = (n^{2} + (n + n)) + 1
  = (n^{2} + (2 /cdot n)) + 1.
qed.


Proposition 0802. Assume n /geq 3. Then n^{2} > (2 /cdot n) + 1.

Proof.
  [prove off]
  # Define P[x] = "x^{2} > (2 /cdot x) + 1" for any natural number x.
  Define P = {natural number x | x^{2} > (2 /cdot x) + 1}.
  [/prove]

  P holds for 3.

  For all natural numbers x such that x /geq 3 we have P(x) => P(x + 1).
  proof.
    Let x be a natural number. Suppose x /geq 3. Assume P(x).

    (x^{2} + (2 /cdot x)) + 1 > (((2 /cdot x) + 1) + (2 /cdot x)) + 1. Indeed
    x^{2} + (2 /cdot x) > ((2 /cdot x) + 1) + (2 /cdot x).

    (2 /cdot (x + x)) + 1 > (2 /cdot (x + 1)) + 1. Indeed 2 /cdot (x + x) >
    2 /cdot (x + 1) (by 0521). Indeed x + x > x + 1 and 2 /neq 0.

    Hence

      (x + 1)^{2}
    = (x^{2} + (2 /cdot x)) + 1
    > (((2 /cdot x) + 1) + (2 /cdot x)) + 1
    > ((2 /cdot x) + (2 /cdot x)) + 1
    = (2 /cdot (x + x)) + 1
    > (2 /cdot (x + 1)) + 1.

    Thus (x + 1)^{2} > (2 /cdot (x + 1)) + 1 (by 0509).
  end.

  Therefore P holds for every natural number x such that x /geq 3 (by 0705).
qed.


Proposition 0803. Assume n /geq 5. Then 2^{n} > n^{2}.

Proof.
  [prove off]
  # Define P[x] = "2^{x} > n^{x}" for any natural number x.
  (1) Define P = {natural number x | 2^{x} > x^{2}}.
  [/prove]

  P holds for 5. Indeed 2^{5} = 2 /cdot (2 /cdot (2 /cdot (2 /cdot 2))) =
  (5 /cdot 5) + 7 > 5 /cdot 5 = 5^{2}.

  For all natural numbers x such that x /geq 5 we have P(x) => P(x + 1).
  proof.
    Let x be a natural number. Suppose x /geq 5. Assume P(x). Then
    2^{x} > x^{2}.

    (2) 2^{x} /cdot 2 > x^{2} /cdot 2 (by 0520). Indeed 2 /neq 0.

    (3) x^{2} /cdot 2 = x^{2} + x^{2}.

    (4) x^{2} + x^{2} > x^{2} + ((2 /cdot x) + 1). Indeed
    x^{2} > (2 /cdot x) + 1.

    (5) x^{2} + ((2 /cdot x) + 1) = (x + 1)^{2} (by 0801, 0203).

    Hence

      2^{x + 1}
    = 2^{x} /cdot 2
    > x^{2} /cdot 2
    = x^{2} + x^{2}
    > x^{2} + ((2 /cdot x) + 1)
    = (x + 1)^{2}.

    Thus 2^{x + 1} > (x + 1)^{2}.
  end.

  Therefore P holds for every natural number x such that x /geq 5 (by 0705).
qed.


Proposition 0804. Assume n /geq 2. Then n^{n} > n!.

Proof.
  [prove off]
  # Define P[x] = "x^{x} > x!" for any natural number x.
  Define P = {natural number x | x^{x} > x!}.
  [/prove]

  P holds for 2.

  For all natural numbers x such that x /geq 2 we have P(x) => P(x + 1).
  proof.
    Let x be a natural number. Suppose x /geq 2. Assume P(x).

    (1) (x + 1)^{x} /cdot (x + 1) > x^{x} /cdot (x + 1) (by 0520, 0107).
    Indeed (x + 1)^{x} > x^{x}. Indeed x + 1 > x and x /neq 0.

    (2) x^{x} /cdot (x + 1) > x! /cdot (x + 1) (by 0520, 0107). Indeed
    x^{x} > x!.

      (x + 1)^{x + 1}
    = (x + 1)^{x} /cdot (x + 1)
    > x^{x} /cdot (x + 1)
    > x! /cdot (x + 1)
    = (x + 1)!.

    Thus (x + 1)^{x + 1} > (x + 1)! (by 0509).
  end.

  Therefore P holds for every natural number x such that x /geq 2 (by 0705).
qed.


Proposition 0805. Assume n /geq 4. Then n! > 2^{n}.

Proof.
  [prove off]
  # Define P[x] = "x! > 2^{x}" for any natural number x.
  Define P = {natural number x | x! > 2^{x}}.
  [/prove]

  P holds for 4.
  proof.
      (4!)
    = 4 /cdot (3 /cdot 2)
    = 2 /cdot (2 /cdot (3 /cdot 2))
    = 3 /cdot (2 /cdot (2 /cdot 2))
    > 2 /cdot (2 /cdot (2 /cdot 2))
    = 2^{4}.
  end.

  For all natural numbers x such that x /geq 4 we have P(x) => P(x + 1).
  proof.
    Let x be a natural number. Suppose x /geq 4. Assume P(x). Then x! > 2^{x}.

    (1) 0 /neq x + 1 > 2. Indeed x > 1.

    (2) x! /cdot (x + 1) > 2^{x} /cdot (x + 1)  (by 0520, 0107).

    (3) 2^{x} /cdot (x + 1) > 2^{x} /cdot 2 (by 0521). Indeed 2^{x} /neq 0.

      ((x + 1)!)
    = x! /cdot (x + 1)
    > 2^{x} /cdot (x + 1)
    > 2^{x} /cdot 2
    = 2^{x + 1}.

    Thus (x + 1)! > 2^{x + 1} (by 0509).
  end.

  Therefore P holds for every natural number x such that x /geq 4 (by 0705).
qed.
