# 1 Lambda terms

[read FLib/Statements/Library/SetTheory/02_elementary-set-theory.ftl]

[prover eprover-2.5]


Signature. A lambda term is an element. Let L,M,N denote lambda terms.

Signature. A variable is a lambda term. Let x,y,z denote variables.

Signature. N(M) is a lambda term.

Signature. \lambda x: L is a lambda term.


Axiom StructuralInduction. Let P be a statement. Assume that P(x) for every
variable x. Assume for all lambda terms N,M if P(N) and P(M) then P(N(M)).
Assume for all variables x and all lambda terms L If P(x) and P(L) then
P(\lambda x: L). Then P holds for every lambda term.


Lemma. L is a variable or L = (N(M)) for some lambda terms N,M or
L = \lambda x: M for some variable x and some lambda term M.

Proof.
  [prove off]
  # Define P(R) = "R is a variable or R = N(M) for some lambda terms N,M or
  # R = \lambda x: M for some variable x and some lambda term M" for any lambda
  # term R.
  (1) Define P = {lambda term R | R is a variable or R = (N(M)) for some lambda
  terms N,M or R = \lambda x: M for some variable x and some lambda term M}.
  [/prove]

  (1) P holds for every variable.

  (2) For all lambda terms N,M if P(N) and P(M) then P(N(M)).

  (3) For all variables x and all lambda terms N if P(x) and P(N) then
  P(\lambda x: N).

  Thus P holds for every lambda term (by StructuralInduction). Hence P holds for
  L (by 1).
qed.


Lemma. x,y,z are lambda terms.

Lemma. x(x), y(x), x(x(z)) are lambda terms.

Lemma. \lambda x: x(z), \lambda y: \lambda z: x, \lambda x: \lambda x: x
are lambda terms.

Lemma. (\lambda x: x(z))(y), y(\lambda x: x(z)), (\lambda x: x)(\lambda x: x)
are lambda terms.


# Subterms

Signature. Sub(L) is a zet.


Axiom Sub_1. Sub(x) = /Set{x}.

Axiom Sub_2. Sub(N(M)) = (Sub(N) /cup Sub(M)) /cup /Set{N(M)}.

Axiom Sub_3. Sub(\lambda x: L) = Sub(L) /cup /Set{\lambda x: L}.


Definition. A subterm of L is an element of Sub(L).


Proposition. L is a subterm of L.

Proof.
  Case L is a variable.
    Then Sub(L) = /Set{L}. Hence L /in /Set{L}.
  end.

  Case L = (M(N)) for some lambda terms M,N.
    Take lambda terms M,N such that L = (M(N)). Then Sub(L) =
    (Sub(M) /cup Sub(N)) /cup /Set{M(N)} = (Sub(M) /cup Sub(N)) /cup /Set{L}.
    Hence L /in Sub(L).
  end.

  Case L = \lambda x: M for some variable x and some lambda term M.
    Take a variable x and a lambda term M such that L = \lambda x: M. Then
    Sub(L) = Sub(M) /cup /Set{\lambda x: M} = Sub(M) /cup /Set{L}. Hence
    L /in Sub(L).
  end.
qed.


Proposition. If L is a subterm of M and M is a subterm of N then L is a subterm
of N.

Proof.
  [prove off]
  # Define P[T] = "for all lambda terms R,S if R is a subterm of S and S is a
  # subterm of T then R is a subterm of T" for any lambda term T.
  Define P = {lambda term T | for all lambda terms R,S if R is a subterm of S
  and S is a subterm of T then R is a subterm of T}.
  [/prove]

  (1) P holds for every variable.
  proof.
    Let x be a variable.

    For all lambda terms R,S if R is a subterm of S and S is a subterm of x then
    R is a subterm of x.
    proof.
      Let R,S be lambda terms. Assume that R is a subterm of S and S is a
      subterm of x. Then S = x. Hence R = x. Thus R is a subterm of x.
    end.
  end.

  (2) For all lambda terms U,V if P(U) and P(V) then P(U(V)).
  proof.
    Let U,V be lambda terms. Assume P(U) and P(V).

    For all lambda terms R,S if R is a subterm of S and S is a subterm of U(V)
    then R is a subterm of U(V).
    proof.
      Let R,S be lambda terms. Assume that R is a subterm of S and S is a
      subterm of U(V). Then S = (U(V)) or S /in Sub(U) or S /in Sub(V). Indeed
      Sub(U(V)) = (Sub(U) /cup Sub(V)) /cup /Set{U(V)}.

      Case S = (U(V)). Obvious.

      Case S /in Sub(U).
        Then R is a subterm of U. Hence
        R /in (Sub(U) /cup Sub(V)) /cup /Set{U(V)} = Sub(U(V)). Thus R is a
        subterm of U(V).
      end.

      Case S /in Sub(V).
        Then R is a subterm of V. Hence
        R /in (Sub(U) /cup Sub(V)) /cup /Set{U(V)} = Sub(U(V)). Thus R is a
        subterm of U(V).
      end.
    end.
  end.

  (3) For all variables x and all lambda terms T if P(x) and P(T) then
  P(\lambda x: T).
  proof.
    Let x be a variable and T be a lambda term. Assume P(x) and P(T).

    For all lambda terms U,V if U is a subterm of V and V is a subterm of
    \lambda x: T then U is a subterm of \lambda x: T.
    proof.
      Let U,V be lambda terms. Assume that U is a subterm of V and V is a
      subterm of \lambda x: T. We have Sub(\lambda x: T) =
      Sub(T) /cup /Set{\lambda x: T}. Hence V /in Sub(T) or V = \lambda x: T.

      Case V /in Sub(T).
        Then U /in Sub(T). Hence U /in Sub(T) /cup /Set{\lambda x: T} =
        Sub(\lambda x: T). Thus U is a subterm of \lambda x: T.
      end.

      Case V = \lambda x: T. Obvious.
    end.
  end.

  Therefore P holds for every lambda term (by StructuralInduction, 1, 2, 3).
qed.
