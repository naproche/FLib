# 7 Alternate forms of induction

[read FLib/Statements/Library/Arithmetic/05_ordering.ftl]


Let P denote a statement that has at most one free variable.

# 7.1 Least elements

Definition 0701. A least natural number satisfying P is a natural number n
such that P holds for n and P does not hold for any natural number that is less
than n.


Lemma 0702. Let n,m be least natural numbers satisfying P. Then n = m.

Proof.
  Assume n /neq m. Then n < m or m < n. If n < m then P does not hold for n and
  if m < n then P does not hold for m. Contradiction. Therefore n = m.
qed.


Theorem 0703. Assume that P holds for some natural number. Then there is a least
natural number satisfying P.

Proof.
  Assume the contrary.

  [prove off]
  # Define Q(n) = "n is a natural number that is less than any natural number m
  # such that P(m)" for any natural number n.
  Define Q = {n | n is a natural number that is less than any natural number m
  such that P(m)}.
  [/prove]

  Q holds for 0.
  proof.
    If P holds for 0 then 0 is the least natural number satisfying P. Hence
    0 is less than any natural number m such that P(m). Therefore Q holds for 0.
  end.

  For all natural numbers n if Q(n) then Q(n + 1).
  proof.
    Let n be a natural number. Assume Q(n). Then n is less than any natural
    number m such that P(m). Assume that Q does not hold for n + 1. Then we can
    take a natural number m such that P(m) and n + 1 is not less than m. Hence
    n < m /leq n + 1. Thus m = n + 1. Then n + 1 is the least natural number
    satisfying P. Contradiction.
  end.

  Therefore Q holds for every natural number. Thus every natural number is less
  than any natural number n such that P(n). Hence there is no natural number n
  such that P(n). Contradiction.
qed.


# 7.2 Induction via predecessors

Theorem 0704. Assume for all natural numbers n if P holds for all natural
numbers that are less than n then P holds for n. Then P holds for all natural
numbers.

Proof.
  Assume the contrary. Take a natural number n such that P does not hold for n.

  [prove off]
  # Define Q(k) = "not P(k)" for any natural number k.
  Define Q = {k | not P(k)}. Q has one free variable.
  [/prove]

  Then Q holds for n. Thus we can take a least natural number m satisfying Q.
  Hence Q does not hold for any natural number that is less than m. Therefore P
  holds for all natural numbers that are less than m. Thus P holds for m.
  Contradiction.
qed.


# 7.3 Induction above a certain number

Theorem 0705. Let k be a natural number. Assume P(k). Suppose for all natural
numbers n such that n /geq k we have P(n) => P(n + 1). Then P(n) for all natural
numbers n such that n /geq k.

Proof.
  [prove off]
  # Define Q[x] = "if x /geq k then P(x)" for any natural number x.
  Define Q = {natural number x | if x /geq k then P(x)}.
  [/prove]

  We have Q(0).

  For all natural numbers x if Q(x) then Q(x + 1).
  proof.
    Let x be a natural number. Assume Q(x).

    If x + 1 /geq k then P(x + 1).
    proof.
      Assume x + 1 /geq k.

      Case x < k.
        Then x + 1 = k. Hence P(x + 1).
      end.

      Case x /geq k.
        Then P(x). Hence P(x + 1).
      end.
    end.

    Thus we have Q(x + 1).
  end.

  Therefore Q holds for every natural number. Hence the thesis.
qed.
