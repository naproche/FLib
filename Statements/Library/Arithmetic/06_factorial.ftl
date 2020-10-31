# 6 Factorial

[read FLib/Statements/Library/Arithmetic/05_ordering.ftl]


Let k,l,m,n denote natural numbers.


# Axioms

Axiom 0601. (0!) = 1.

Axiom 0602. ((n + 1)!) = n! \cdot (n + 1).

# Note that we cannot write "x! = y" since this can be understood as "x! is
# equal to y" or as "x is not equal to y".


Proposition 0603. n! is a natural number.

Proof.
  [prove off]
  # Define P(x) iff x! is a natural number.
  Define P = {natural number x | x! is a natural number}.
  [prove on]

  P holds for 0.

  For all natural numbers x if P(x) then P(x + 1).
  proof.
    Let x be a natural number. Assume P(x). Then x! is a natural number. Thus
    x! \cdot (x + 1) is a natural number. Hence the thesis.
  end.

  Therefore P holds for every natural number.
qed.
