# 8 Alternate forms of induction

[read FLib/Statements/Library/Arithmetic/05_ordering.ftl]


Let P denote a predicate that has at most one free variable.

# 8.1 Induction via least elements

Definition 0801. A least natural number that satisfies P is a natural number n
such that P holds for n and P does not hold for any natural number that is less
than n.

Let a least natural number that satisfy P stand for a least natural number that
satisfies P. # We need this formulation for the next lemma.


Lemma 0802. Let n,m be least natural numbers that satisfy P. Then n = m.

Proof.
  Assume n \neq m. Then n < m or m < n. If n < m then P does not hold for n and
  if m < n then P does not hold for m. Contradiction. Therefore n = m.
qed.


Theorem 0803. Assume that P holds for some natural number. Then there is a least
natural number that satisfies P.

Proof.
  Assume the contrary.

  [prove off]
  # Define Q(n) iff n is a natural number that is less than any natural number m
  # such that P(m).
  Define Q = {n | n is a natural number that is less than any natural number m
  such that P(m)}.
  [prove on]

  Q holds for 0.
  proof.
    If P holds for 0 then 0 is the least natural number that satisfies P. Hence
    0 is less than any natural number m such that P(m). Therefore Q holds for 0.
  end.

  For all natural numbers n if Q(n) then Q(n + 1).
  proof.
    Let n be a natural number. Assume Q(n). Then n is less than any natural
    number m such that P(m). Assume that Q does not hold for n + 1. Then we can
    take a natural number m such that P(m) and n + 1 is not less than m. Hence
    n < m \leq n + 1. Thus m = n + 1. Then n + 1 is the least natural number
    that satisfies P. Contradiction.
  end.

  Therefore Q holds for every natural number. Thus every natural number is less
  than any natural number n such that P(n). Hence there is no natural number n
  such that P(n). Contradiction.
qed.


# 8.2 Induction via predecessors

Theorem 0804. Assume for all natural numbers n if P holds for all natural
numbers that are less than n then P holds for n. Then P holds for all natural
numbers.

Proof.
  Assume the contrary. Take a natural number n such that P does not hold for n.

  [prove off]
  # Define Q(k) iff not P(k).
  Define Q = {k | not P(k)}. Q has one free variable.
  [prove on]

  Then Q holds for n. Thus we can take a least natural number that m satisfies
  Q.                                  # That's a weird position:  ^^^
  Hence Q does not hold for any natural number that is less than m. Therefore P
  holds for all natural numbers that are less than m. Thus P holds for m.
  Contradiction.
qed.
