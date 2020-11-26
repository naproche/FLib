# 2 Lambda calculus

[read FLib/Statements/Library/statements.ftl]

[prover eprover-2.5]


# 2.1 Lambda terms

Signature. A lambda term is a notion. Let L,M,N denote lambda terms.

Signature. A variable is a lambda term. Let x,y,z denote variables.

Signature. N(M) is a lambda term.

Signature. \lambda x: L is a lambda term.


Axiom. Let P be a statement. Assume that P(x) for every variable x. Assume
P(N(M)) for all lambda terms N,M. Assume P(\lambda x: L) for all variables x and
all lambda terms L. Then P holds for every lambda term.


Lemma. L is a variable or L = (N(M)) for some lambda terms N,M or
L = \lambda x: M for some variable x and some lambda term M.

Proof.
  [prove off]
  # Define P(R) = " R is a variable or R = N(M) for some lambda terms N,M or
  # R = \lambda x: M for some variable x and some lambda term M" for any lambda
  # term R.
  (1) Define P = {lambda term R | R is a variable or R = (N(M)) for some lambda
  terms N,M or R = \lambda x: M for some variable x and some lambda term M}.
  [/prove]

  (1) P holds for every variable.

  (2) For all lambda terms N,M we have P(N(M)).

  (3) For all variables x and all lambda terms N we have P(\lambda x: N).

  Thus P holds for every lambda term. Hence P holds for L (by 1).
qed.


Lemma. x,y,z are lambda terms.

Lemma. x(x), y(x), x(x(z)) are lambda terms.

Lemma. \lambda x: x(z), \lambda y: \lambda z: x, \lambda x: \lambda x: x
are lambda terms.

Lemma. (\lambda x: x(z))(y), y(\lambda x: x(z)), (\lambda x: x)(\lambda x: x)
are lambda terms.