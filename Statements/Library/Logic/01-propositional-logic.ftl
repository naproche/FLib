# 1 Propositional logic

[read FLib/Statements/Library/statements.ftl]

[prover eprover-2.5]


Let P,Q,R denote propositions.


# Basic junctors

Definition 0101. \neg P = {x | P is false}.

Definition 0102. P \wedge Q = {x | P is true and Q is true}.

Definition 0103. P \vee Q = {x | P is true or Q is true}.

Definition 0104. P \implies Q = {x | if P is true then Q is true}.

Definition 0105. P \iff Q = {x | P is true iff Q is true}.


Lemma 0106. \neg P is a proposition.

Lemma 0107. P \wedge Q is a proposition.

Lemma 0108. P \vee Q is a proposition.

Lemma 0109. P \implies Q is a proposition.

Lemma 0110. P \iff Q is a proposition.


# Logical laws

Proposition 0111. \neg \neg P = P.

Proof.
  Case P is true.
    Then P is not false. Hence \neg P is false. Then \neg \neg P is not false.
    Thus \neg \neg P is true. Therefore \neg \neg P = P.
  end.

  Case P is false.
    Then P is not true. Hence \neg P is true. Then \neg \neg P is not true. Thus
    \neg \neg P is false. Therefore \neg \neg P = P.
  end.
qed.


Proposition 0112. P \wedge Q = Q \wedge P.

Proof.
  Case P and Q are true.
    Then (P is true and Q is true) and (Q is true and P is true). Hence
    P \wedge Q is true and Q \wedge P is true. Therefore P \wedge Q =
    Q \wedge P.
  end.

  Case P is true and Q is false.
    Then not (P is true and Q is true) and not (Q is true and P is true). Hence
    P \wedge Q is not true and Q \wedge P is not true. Thus P \wedge Q is false
    and Q \wedge P is false. Therefore P \wedge Q = Q \wedge P.
  end.

  Case P is false and Q is true.
    Then not (P is true and Q is true) and not (Q is true and P is true). Hence
    P \wedge Q is not true and Q \wedge P is not true. Thus P \wedge Q is false
    and Q \wedge P is false. Therefore P \wedge Q = Q \wedge P.
  end.

  Case P and Q are false.
    Then not (P is true and Q is true) and not (Q is true and P is true). Hence
    P \wedge Q is not true and Q \wedge P is not true. Thus P \wedge Q is false
    and Q \wedge P is false. Therefore P \wedge Q = Q \wedge P.
  end.
qed.


Proposition 0113. P \vee Q = Q \vee P.

Proof.
  Case P and Q are true.
    Then (P is true or Q is true) and (Q is true or P is true). Hence
    P \vee Q is true and Q \vee P is true. Therefore P \vee Q = Q \vee P.
  end.

  Case P is true and Q is false.
    Then (P is true or Q is true) and (Q is true or P is true). Hence
    P \vee Q is true and Q \vee P is true. Thus P \vee Q = Q \vee P.
  end.

  Case P is false and Q is true.
    Then (P is true or Q is true) and (Q is true or P is true). Hence
    P \vee Q is true and Q \vee P is true. Thus P \vee Q = Q \vee P.
  end.

  Case P and Q are false.
    Then not (P is true or Q is true) and not (Q is true or P is true). Hence
    P \vee Q is not true and Q \vee P is not true. Thus P \vee Q is false
    and Q \vee P is false. Therefore P \vee Q = Q \vee P.
  end.
qed.


Proposition 0114. (P \wedge Q) \wedge R = P \wedge (Q \wedge R).

Proof.

qed.


Proposition 0115. (P \vee Q) \vee R = P \vee (Q \vee R).

Proof.

qed.


Proposition 0116. P \wedge (Q \vee R) = (P \wedge Q) \vee (P \wedge R).

Proof.

qed.


Proposition 0117. P \vee (Q \wedge R) = (P \vee Q) \wedge (P \vee R).

Proof.

qed.


Proposition 0118. P \wedge P = P.

Proof.

qed.


Proposition 0119. P \vee P = P.

Proof.

qed.


Proposition 0120. P \wedge \neg P = \bot.

Proof.

qed.


Proposition 0121. P \vee \neg P = \top.

Proof.

qed.


Proposition 0122. P \wedge (P \vee Q) = P.

Proof.

qed.


Proposition 0123. P \vee (P \wedge Q) = P.

Proof.

qed.


Proposition 0124. P \wedge \top = P.

Proof.

qed.


Proposition 0125. P \vee \bot = P.

Proof.

qed.


Proposition 0126. \neg (P \wedge Q) = (\neg P) \vee (\neg Q).

Proof.

qed.


Corollary 0127. P \wedge Q = \neg ((\neg P) \vee (\neg Q)).

Proof.

qed.


Proposition 0128. \neg (P \vee Q) = (\neg P) \wedge (\neg Q).

Proof.

qed.


Corollary 0129. P \vee Q = \neg ((\neg P) \wedge (\neg Q)).

Proof.

qed.


Proposition 0130. P \wedge Q = \neg (P \implies \neg Q).

Proof.

qed.


Proposition 0131. P \vee Q = (\neg P) \implies Q = (\neg Q) \implies P.

Proof.

qed.


Proposition 0132. P \iff Q = (P \implies Q) \wedge (Q \implies P) =
(P \wedge Q) \vee ((\neg P) \wedge \neg Q) =
(P \vee \neg Q) \wedge (Q \vee \neg P).

Proof.

qed.


Corollary 0133. \neg (P \iff Q) = (P \wedge \neg Q) \vee ((\neg P) \wedge Q) =
(P \vee Q) \wedge ((\neg P) \vee \neg Q).

Proof.

qed.


Proposition 0134. P \implies Q = (\neg P) \vee Q = (\neg Q) \implies \neg P.

Proof.

qed.


Corollary 0135. \neg (P \implies Q) = P \wedge \neg Q.

Proof.

qed.


# Inference rules

Proposition 0136. If P \implies Q is true and P is true then Q is true.

Proof.

qed.


Proposition 0137. If P \implies Q is true and Q is false then P is false.

Proof.

qed.


Proposition 0138. If P \implies Q is true and Q \implies R is true then
P \implies R is true.

Proof.

qed.


Proposition 0139. If P \vee Q is true and P is false then Q is true.

Proof.

qed.


Proposition 0140. If \neg P is false then P is true.

Proof.

qed.


Proposition 0150. If P \wedge Q is false and P is true then Q is false.

Proof.

qed.
