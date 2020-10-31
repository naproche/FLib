# 1 The Peano Axioms

[read FLib/Statements/Library/signature-extensions.ftl]
[read FLib/Statements/Library/statements.ftl]

[prover eprover-2.5]


Signature 0101. A natural number is a notion. Let k,l,m,n denote natural
numbers.

Signature 0102. 0 is a natural number.

Signature 0103. 1 is a natural number.


# 1.1 The axioms

Axiom 0104. n + 1 is a natural number.

Axiom 0105. If n + 1 = m + 1 then n = m.

Axiom 0106. For no n we have n + 1 = 0.

Axiom 0107. Let P be a statement such that P(0) and for all n if P(n) then
P(n + 1). Then we have P(n) for all n.


# 1.2 Immediate consequences

Proposition 0108. n = 0 or n = m + 1 for some natural number m.

Proof.
  [prove off]
  # P(x) iff x = 0 or x = y + 1 for some natural number y.
  Define P = {natural number x | x = 0 or x = y + 1 for some natural number y}.
  [prove on]

  Then P(0) and for all natural numbers x if P(x) then P(x + 1). Hence we
  have P(x) for every natural number x.
qed.

Proposition 0109. n \neq n + 1.

Proof.
  [prove off]
  # P(x) iff x \neq x + 1.
  Define P = {natural number x | x \neq x + 1}.
  [prove on]

  Then P(0).

  For all natural numbers x if P(x) then P(x + 1).
  proof.
    Let x be a natural number. Assume P(x). Then x \neq x + 1. If x + 1 =
    (x + 1) + 1 then x = x + 1. Hence we have P(x + 1).
  end.

  Therefore P holds for every natural number.
qed.


# 1.3 Additional constants

Definition 0110. 2 = 1 + 1.

Definition 0111. 3 = 2 + 1.

Definition 0112. 4 = 3 + 1.

Definition 0113. 5 = 4 + 1.

Definition 0114. 6 = 5 + 1.

Definition 0115. 7 = 6 + 1.

Definition 0116. 8 = 7 + 1.

Definition 0117. 9 = 8 + 1.
