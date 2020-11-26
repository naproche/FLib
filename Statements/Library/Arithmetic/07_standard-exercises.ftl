# 7 Standard exercises

[read FLib/Statements/Library/Arithmetic/06_factorial.ftl]


Let k,l,m,n denote natural numbers.


Proposition 0701. (n + 1)^{2} = (n^{2} + (2 /cdot n)) + 1.

Proof.
    (n + 1)^{2}
  = (n + 1) /cdot (n + 1)
  = ((n + 1) /cdot n) + (n + 1)
  = ((n /cdot n) + n) + (n + 1)
  = (n^{2} + (n + n)) + 1
  = (n^{2} + (2 /cdot n)) + 1.
qed.


Proposition 0702. Assume n /geq 3. Then n^{2} > (2 /cdot n) + 1.

Proof.
  [prove off]
  # Define P(x) = "if x /geq 3 then x^{2} > (2 /cdot x) + 1" for any natural
  # number x.
  Define P = {natural number x | if x /geq 3 then x^{2} > (2 /cdot x) + 1}.
  [/prove]

  P holds for 0.

  For all natural numbers x if P(x) then P(x + 1).
  proof.
    Let x be a natural number. Assume P(x).

    Case x < 2. Trivial.

    Case x = 2. Obvious.

    Case x > 2.
      Then x /geq 3.

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
  end.

  Therefore P holds for every natural number.
qed.


Proposition 0703. Assume n > 4. Then 2^{n} > n^{2}.

Proof.
  [prove off]
  # Define P(x) = "if x > 4 then 2^{x} > n^{x}" for any natural number x.
  (1) Define P = {natural number x | if x > 4 then 2^{x} > x^{2}}.
  [/prove]

  P holds for 0.

  For all natural numbers x if P(x) then P(x + 1).
  proof.
    Let x be a natural number. Assume P(x).

    Case x < 4. Obvious.

    Case x = 4.
      We have 8 /cdot 4 = (5 /cdot 5) + 7. Hence

        2^{x + 1}
      = 2^{4} /cdot 2
      = (2^{3} /cdot 2) /cdot 2
      = 2^{3} /cdot (2 /cdot 2)
      = 2^{3} /cdot 4
      = 8 /cdot 4
      = (5 /cdot 5) + 7.

      (x + 1)^{2}
      = 5 /cdot (4 + 1)
      = (5 /cdot 4) + 5
      = 5 /cdot 5.

      Hence 2^{x + 1} > (x + 1)^{2}.
    end.

    Case x > 4.
      Then 2^{x} > x^{2}.

      2^{x} /cdot 2 > x^{2} /cdot 2.

      x^{2} + x^{2} > x^{2} + ((2 /cdot x) + 1). Indeed x^{2} > (2 /cdot x) + 1.

      Hence

        2^{x + 1}
      = 2^{x} /cdot 2
      > x^{2} /cdot 2
      = x^{2} + x^{2}
      > x^{2} + ((2 /cdot x) + 1)
      = (x + 1)^{2}.

      Thus 2^{x + 1} > (x + 1)^{2}.
    end.
  end.

  Therefore P holds for every natural number.
qed.


Proposition 0704. Assume n > 1. Then n^{n} > n!.

Proof.
  [prove off]
  # Define P(x) = "if x > 1 then x^{x} > x!" for any natural number x.
  Define P = {natural number x | if x > 1 then x^{x} > x!}.
  [/prove]

  P holds for 0.

  For all natural numbers x if P(x) then P(x + 1).
  proof.
    Let x be a natural number. Assume P(x).

    Case x = 0 or x = 1. Obvious.

    Case x > 1.
      (1) (x + 1)^{x} /cdot (x + 1) > x^{x} /cdot (x + 1) (by 0520, 0107).
      Indeed (x + 1)^{x} > x^{x}. Indeed x + 1 > x.

      (2) x^{x} /cdot (x + 1) > x! /cdot (x + 1) (by 0520, 0107). Indeed
      x^{x} > x!.

        (x + 1)^{x + 1}
      = (x + 1)^{x} /cdot (x + 1)
      > x^{x} /cdot (x + 1)
      > x! /cdot (x + 1)
      = (x + 1)!.

      Thus (x + 1)^{x + 1} > (x + 1)! (by 0509).
    end.
  end.

  Therefore P holds for every natural number.
qed.


Proposition 0705. Assume n > 3. Then n! > 2^{n}.

Proof.
  [prove off]
  # Define P(x) = "if x > 3 then x! > 2^{x}" for any natural number x.
  Define P = {natural number x | if x > 3 then x! > 2^{x}}.
  [/prove]

  P holds for 0.

  For all natural numbers x if P(x) then P(x + 1).
  proof.
    Let x be a natural number. Assume P(x).

    Case x < 3. Obvious.

    Case x = 3.
      ((x + 1)!) = (4!)  = ((1 /cdot 2) /cdot 3) /cdot 4.
      2^{x + 1}  = 2^{4} = ((2 /cdot 2) /cdot 2) /cdot 2.

      ((1 /cdot 2) /cdot 3) /cdot 4 > ((2 /cdot 2) /cdot 2) /cdot 2. Hence
      (x + 1)! > 2^{x + 1}. 
    end.

    Case x > 3.
      Then x! > 2^{x}. We have 0 /neq x + 1 > 2.

      x! /cdot (x + 1) > 2^{x} /cdot (x + 1)  (by 0520, 0107).

      2^{x} /cdot (x + 1) > 2^{x} /cdot 2 (by 0521). Indeed 2^{x} /neq 0.

        ((x + 1)!)
      = x! /cdot (x + 1)
      > 2^{x} /cdot (x + 1)
      > 2^{x} /cdot 2
      = 2^{x + 1}.

      Thus (x + 1)! > 2^{x + 1} (by 0509).
    end.
  end.

  Therefore P holds for every natural number.
qed.
