# 1 Propositional logic

[read FLib/Statements/Library/statements.ftl]

[prover eprover-2.5]


Signature. A proposition is a notion. Let P,Q,R denote propositions.

Signature. P is true is a relation.

Definition. P is false iff P is not true.

Axiom. If P is true iff Q is true then P = Q.


# 1.1 Atomic propositions and junctors

Signature. /top is a proposition.

Axiom. /top is true.


Signature. /bot is a proposition.

Axiom. /bot is false.


Signature. /neg P is a proposition.

Axiom. /neg P is true iff P is false.


Signature. P /wedge Q is a proposition.

Axiom. P /wedge Q is true iff P is true and Q is true.


Signature. P /vee Q is a proposition.

Axiom. P /vee Q is true iff P is true or Q is true.


Signature. P /implies Q is a proposition.

Axiom. P /implies Q is true iff if P is true then Q is true.


Signature. P /iff Q is a proposition.

Axiom. P /iff Q is true iff P is true iff Q is true.



# 1.2 Logical laws

Proposition 0111. /neg /neg P = P.

Proof.
  Case P is true.
    Then P is not false. Hence /neg P is false. Then /neg /neg P is not false.
    Thus /neg /neg P is true. Therefore /neg /neg P = P.
  end.

  Case P is false.
    Then P is not true. Hence /neg P is true. Then /neg /neg P is not true. Thus
    /neg /neg P is false. Therefore /neg /neg P = P.
  end.
qed.


Proposition 0112. P /wedge Q = Q /wedge P.

Proof.
  Case P and Q are true.
    Then (P is true and Q is true) and (Q is true and P is true). Hence
    P /wedge Q is true and Q /wedge P is true. Therefore P /wedge Q =
    Q /wedge P.
  end.

  Case P is true and Q is false.
    Then not (P is true and Q is true) and not (Q is true and P is true). Hence
    P /wedge Q is not true and Q /wedge P is not true. Thus P /wedge Q is false
    and Q /wedge P is false. Therefore P /wedge Q = Q /wedge P.
  end.

  Case P is false and Q is true.
    Then not (P is true and Q is true) and not (Q is true and P is true). Hence
    P /wedge Q is not true and Q /wedge P is not true. Thus P /wedge Q is false
    and Q /wedge P is false. Therefore P /wedge Q = Q /wedge P.
  end.

  Case P and Q are false.
    Then not (P is true and Q is true) and not (Q is true and P is true). Hence
    P /wedge Q is not true and Q /wedge P is not true. Thus P /wedge Q is false
    and Q /wedge P is false. Therefore P /wedge Q = Q /wedge P.
  end.
qed.


Proposition 0113. P /vee Q = Q /vee P.

Proof.
  Case P and Q are true.
    Then (P is true or Q is true) and (Q is true or P is true). Hence
    P /vee Q is true and Q /vee P is true. Therefore P /vee Q = Q /vee P.
  end.

  Case P is true and Q is false.
    Then (P is true or Q is true) and (Q is true or P is true). Hence
    P /vee Q is true and Q /vee P is true. Thus P /vee Q = Q /vee P.
  end.

  Case P is false and Q is true.
    Then (P is true or Q is true) and (Q is true or P is true). Hence
    P /vee Q is true and Q /vee P is true. Thus P /vee Q = Q /vee P.
  end.

  Case P and Q are false.
    Then not (P is true or Q is true) and not (Q is true or P is true). Hence
    P /vee Q is not true and Q /vee P is not true. Thus P /vee Q is false
    and Q /vee P is false. Therefore P /vee Q = Q /vee P.
  end.
qed.


Proposition 0114. (P /wedge Q) /wedge R = P /wedge (Q /wedge R).

Proof.

qed.


Proposition 0115. (P /vee Q) /vee R = P /vee (Q /vee R).

Proof.

qed.


Proposition 0116. P /wedge (Q /vee R) = (P /wedge Q) /vee (P /wedge R).

Proof.

qed.


Proposition 0117. P /vee (Q /wedge R) = (P /vee Q) /wedge (P /vee R).

Proof.

qed.


Proposition 0118. P /wedge P = P.

Proof.

qed.


Proposition 0119. P /vee P = P.

Proof.

qed.


Proposition 0120. P /wedge /neg P = /bot.

Proof.

qed.


Proposition 0121. P /vee /neg P = /top.

Proof.

qed.


Proposition 0122. P /wedge (P /vee Q) = P.

Proof.

qed.


Proposition 0123. P /vee (P /wedge Q) = P.

Proof.

qed.


Proposition 0124. P /wedge /top = P.

Proof.

qed.


Proposition 0125. P /vee /bot = P.

Proof.

qed.


Proposition 0126. /neg (P /wedge Q) = (/neg P) /vee (/neg Q).

Proof.

qed.


Corollary 0127. P /wedge Q = /neg ((/neg P) /vee (/neg Q)).

Proof.

qed.


Proposition 0128. /neg (P /vee Q) = (/neg P) /wedge (/neg Q).

Proof.

qed.


Corollary 0129. P /vee Q = /neg ((/neg P) /wedge (/neg Q)).

Proof.

qed.


Proposition 0130. P /wedge Q = /neg (P /implies /neg Q).

Proof.

qed.


Proposition 0131. P /vee Q = (/neg P) /implies Q = (/neg Q) /implies P.

Proof.

qed.


Proposition 0132. P /iff Q = (P /implies Q) /wedge (Q /implies P) =
(P /wedge Q) /vee ((/neg P) /wedge /neg Q) =
(P /vee /neg Q) /wedge (Q /vee /neg P).

Proof.

qed.


Corollary 0133. /neg (P /iff Q) = (P /wedge /neg Q) /vee ((/neg P) /wedge Q) =
(P /vee Q) /wedge ((/neg P) /vee /neg Q).

Proof.

qed.


Proposition 0134. P /implies Q = (/neg P) /vee Q = (/neg Q) /implies /neg P.

Proof.

qed.


Corollary 0135. /neg (P /implies Q) = P /wedge /neg Q.

Proof.

qed.


# 1.3 Inference rules

Proposition 0136. If P /implies Q is true and P is true then Q is true.

Proof.

qed.


Proposition 0137. If P /implies Q is true and Q is false then P is false.

Proof.

qed.


Proposition 0138. If P /implies Q is true and Q /implies R is true then
P /implies R is true.

Proof.

qed.


Proposition 0139. If P /vee Q is true and P is false then Q is true.

Proof.

qed.


Proposition 0140. If /neg P is false then P is true.

Proof.

qed.


Proposition 0150. If P /wedge Q is false and P is true then Q is false.

Proof.

qed.
