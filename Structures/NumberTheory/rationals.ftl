#
# Rational numbers
# (Marcel Schütz, 2020)
#

[read ForTheLib/NumberTheory/integers.ftl]


# 1. Definition

Signature NtRat000. A rational number is a notion.

Definition NtRat005. RAT = {q | q is a rational number}.


Axiom NtRat010. Let n,m be integers. Assume m \neq 0. n/m is a rational number.

Axiom NtRat015. Let q be a rational number. Then q = n/m for some integers n,m such that
m \neq 0.

Axiom NtRat020. Let n be an integer. n = n/1.


# 2. The set of rational numbers

Proposition NtRat025. RAT is an countably infinite set.

Proof. [prove off] qed.


# 3. Arithmetic

# 3.1 Absolute value

Axiom NtRat030. Let n,m be integers. Assume m \neq 0. Then

  |n/m| = |n|/|m|.


# 3.2 Equality

Axiom NtRat035. Let n,m,k,l be integers. Assume m,l \neq 0. Then

  n/m = k/l iff n \cdot l = k \cdot m.


# 3.3 Addition

Axiom NtRat040. Let n,m,k,l be integers. Assume m,l \neq 0. Then

  (n/m) + (k/l) = ((n \cdot l) + (k \cdot m)) / (m \cdot l).


Proposition NtRat045. Let p,q be rational numbers. p + q is a rational number.

Proof. [prove off] qed.


# 3.4 Subtraction

Axiom NtRat050. Let n,m,k,l be integers. Assume m,l \neq 0. Then

  (n/m) - (k/l) = ((n \cdot l) - (k \cdot m)) / (m \cdot l).


Proposition NtRat055. Let p,q be rational numbers. Then p - q is a rational number.

Proof. [prove off] qed.


# 3.5 Multiplication

Axiom NtRat060. Let n,m,k,l be integers. Assume m,l \neq 0. Then

  (n/m) \cdot (k/l) = (n \cdot k)/(m \cdot l).


Proposition NtRat065. Let p,q be rational numbers. Then p \cdot q is a rational number.

Proof. [prove off] qed.


# 3.6 Division

Axiom NtRat070. Let n,m,k,l be integers. Assume m,l \neq 0. Then

  (n/m)/(k/l) = (n \cdot l)/(m \cdot k).


Proposition NtRat075. Let p,q be rational numbers. Assume that q \neq 0. Then p/q is a
rational number.

Proof. [prove off] qed.


# 3.7 Inverse

Axiom NtRat080. Let n,m be integers. Assume m \neq 0. Then

  -(n/m) = (-n)/m.


Proposition NtRat085. Let p be a rational number. Then -p is a rational number.

Proof. [prove off] qed.


# 3.8 Exponentiation

Axiom NtRat090. Let n,m be integers. Assume m \neq 0. Then

  (n/m)^{0} = 1.


Axiom NtRat095. Let n,m be integers. Assume m \neq 0. Let k be a natural number. Then

  (n/m)^{k} = (n^{k}) / (m^{k}).


Axiom NtRat100. Let n,m be integers. Assume n,m \neq 0. Let k be a natural number. Then

  (n/m)^{-k} = (m^{k}) / (n^{k}).


Proposition NtRat105. Let p be a rational number. Assume p \neq 0. Let n be an integer. Then
p^{n} is a rational number.

Proof. [prove off] qed.


# 4. Basic properties

Proposition NtRat110. Let p,q be rational numbers. Then

  p + (-q) = p - q.

Proof. [prove off] qed.


Proposition NtRat115. Let p,q,r be rational numbers. Then

  (p + q) + r = p + (r + q).

Proof. [prove off] qed.


Proposition NtRat120. Let p,q,r be rational numbers. Then

  (p \cdot  q) \cdot r = p \cdot (r \cdot q).

Proof. [prove off] qed.


Proposition NtRat125. Let p,q be rational numbers. Then

  p + q = q + p.

Proof. [prove off] qed.


Proposition NtRat130. Let p,q be rational numbers. Then

  p \cdot q = q \cdot p.

Proof. [prove off] qed.


Proposition NtRat135. Let p be a rational number. Then

  p + 0 = p.

Proof. [prove off] qed.


Proposition NtRat140. Let p be a rational number. Then

  p \cdot 1 = p.

Proof. [prove off] qed.


Proposition NtRat145. Let p be a rational number. Then

  p \cdot 0 = 0.

Proof. [prove off] qed.


Proposition NtRat150. Let p be a rational number. Then

  p - p = 0.

Proof. [prove off] qed.


Proposition NtRat160. Let p be a rational number. Assume that p \neq 0. Then

  p \cdot p^{-(1)} = 1.

Proof. [prove off] qed.


Proposition NtRat165. Let p,q,r be rational numbers. Then

  p \cdot (q + r) = (p \cdot q) + (p \cdot r).

Proof. [prove off] qed.


# 5. Order

Axiom NtRat170. Let n,m,k,l be integers. Assume m,l \neq 0. Then

  n/m < k/l iff n \cdot l < k \cdot m.


Axiom NtRat175. Let p,q be rational numbers. p \leq q iff p < q or p = q.


Proposition NtRat180. Let p be a rational number. Then

  not p < p.

Proof. [prove off] qed.


Proposition NtRat185. Let p,q,r be rational numbers. Then

  p < q < r  =>  p < r.

Proof. [prove off] qed.


Proposition NtRat190. Let p,q be rational numbers. Then

  (p \leq q and q \leq p)  =>  p = q.

Proof. [prove off] qed.


Proposition NtRat195. Let p,q be rational numbers. Then

  p < q or p = q or p > q.

Proof. [prove off] qed.


Proposition NtRat200. Let p,q be rational numbers. Assume p < q. There is a rational number r
such that p < r < q.

Proof. [prove off] qed.


# 6. Misc

Proposition NtRat205. Let p,q be rational numbers. Assume p is positive. Then q - p < q.

Proof. [prove off] qed.
