#
# Natural numbers
# (Marcel Schütz, 2020)
#

[read ForTheLib/Foundations/classes.ftl]


# 1. The Peano axioms

Signature NtNat000. A natural number is a notion.

Definition NtNat005. NAT = {n | n is a natural number}.


Axiom NtNat010. 0 is a natural number.

Axiom NtNat015. 1 is a natural number.

Axiom NtNat020. Let n be a natural number. n + 1 is a natural number.

Axiom NtNat025. Let n,m be natural numbers. If n + 1 = m + 1 then n = m.

Axiom NtNat030. There is no natural number n such that n + 1 = 0.

Axiom NtNat035. For all classes C that are inductive we have NAT \subseteq C.


# 2. Arithmetic

# 2.1 Special numbers

Axiom NtNat040. 2 = 1 + 1.

Axiom NtNat045. 3 = 2 + 1.

Axiom NtNat050. 4 = 3 + 1.

Axiom NtNat055. 5 = 4 + 1.

Axiom NtNat060. 6 = 5 + 1.

Axiom NtNat065. 7 = 6 + 1.

Axiom NtNat070. 8 = 7 + 1.

Axiom NtNat075. 9 = 8 + 1.


Proposition NtNat080. 0,1,2,3,4,5,6,7,8,9 are natural numbers.


# 2.2 Addition

Axiom NtNat085. Let n be a natural number. Then

  n + 0 = n.


Axiom NtNat090. Let n,m be natural numbers. Then

  n + (m + 1) = (n + m) + 1.


Proposition NtNat095. Let n,m be natural numbers. n + m is a natural number.

Proof. [prove off] qed.


Proposition NtNat100. Let n be an natural number. Then

  0 + n = n.

Proof. [prove off] qed.


Proposition NtNat105. Let n,m be natural numbers. Then

  n + m = m + n.

Proof. [prove off] qed.


Proposition NtNat110. Let n,m,k be natural numbers. Then

  (n + m) + k = n + (m + k).

Proof. [prove off] qed.


Proposition NtNat115. Let n,m,k be natural numbers. Then

  n + m = n + k  =>  m = k.

Proof. [prove off] qed.


# 2.3 Multiplication

Axiom NtNat120. Let n be a natural number. Then

  n \cdot 0 = 0.


Axiom NtNat125. Let n,m be natural numbers.Then

  n \cdot (m + 1) = (n \cdot m) + n.


Proposition NtNat130. Let n,m be natural numbers. n \cdot m is a natural number.

Proof. [prove off] qed.


Proposition NtNat135. Let n be an natural number. Then

  0 \cdot n = 0.

Proof. [prove off] qed.


Proposition NtNat140. Let n be an natural number. Then

  n \cdot 1 = n.

Proof. [prove off] qed.


Proposition NtNat145. Let n be an natural number. Then

  1 \cdot n = n.

Proof. [prove off] qed.


Proposition NtNat150. Let n,m be natural numbers. Then

  n \cdot m = m \cdot n.

Proof. [prove off] qed.


Proposition NtNat155. Let n,m,k be natural numbers. Then

  n \cdot (m + k) = (n \cdot m) + (n \cdot k).

Proof. [prove off] qed.


Proposition NtNat160. Let n,m,k be natural numbers.

  n \cdot (m \cdot k) = (n \cdot m) \cdot k.

Proof. [prove off] qed.


Proposition NtNat165. Let n,m,k be natural numbers. Assume that n \neq 0. Then

  n \cdot m = n \cdot k  =>  m = k.

Proof. [prove off] qed.


Proposition NtNat170. Let n,m be natural numbers. Then

  n \cdot m = 0  =>  (n = 0 \/ m = 0).

Proof. [prove off] qed.


# 2.4 Exponentiation

Axiom NtNat175. Let n be a natural number. Then

  n^{0} = 1.


Axiom NtNat180. Let n,m be natural numbers. Then

  n^{m + 1} = n \cdot n^{m}.


Proposition NtNat185. Let n be a natural number. Then

  n^{1} = n.

Proof. [prove off] qed.


Proposition NtNat190. Let n be a natural number. Then

  1^{n} = 1.

Proof. [prove off] qed.


Proposition NtNat195. Let n be a natural number. Assume that n \neq 0. Then

  0^{n} = 0.

Proof. [prove off] qed.


Proposition NtNat200. Let n,m,k be natural numbers. Then

  n^{m + k} = n^{m} \cdot n^{k}.

Proof. [prove off] qed.


Proposition NtNat205. Let n,m,k be natural numbers. Then

  (n^{m})^{k} = n^{m \cdot k}.

Proof. [prove off] qed.


# 2.5 Order

Axiom NtNat210. Let n,m be natural numbers. Then

  n < m iff n + k = m

for some positive natural number k.


Axiom NtNat215. Let n,m be natural numbers. Then

  n \leq m iff n < m or n = m.


Proposition NtNat220. Let n be a natural number. Then

  not n < n.

Proof. [prove off] qed.


Proposition NtNat225. Let n,m be natural numbers. Then

  (n \leq m /\ m \leq n)  =>  n = m.

Proof. [prove off] qed.


Proposition NtNat230. Let n,m,k be natural numbers. Then

  n \leq m \leq k  =>  n \leq k.

Proof. [prove off] qed.


Proposition NtNat235. Let n,m,k be natural numbers. Then

  n < m  =>  k + n < k + m.

Proof. [prove off] qed.


Proposition NtNat240. Let n,m,k be natural numbers. Assume that k \neq 0. Then

  n < m  =>  k \cdot n < k \cdot m.

Proof. [prove off] qed.


Proposition NtNat245. Let n,m be natural numbers. Assume that m \neq 0. There exist natural numbers
k,l such that

  n = (m \cdot k) + l and l < m.

Proof. [prove off] qed.


Proposition NtNat250. There is no natural number that is less than 0.

Proof. [prove off] qed.


Proposition NtNat255. 0 < 1 < 2 < 3 < 4 < 5 < 6 < 7 < 8 < 9.

Proof. [prove off] qed.


Proposition NtNat256. Let n be a positive natural number. Then 1 \leq n.

Proof. [prove off] qed.


# 2.6 Subtraction

Axiom NtNat260. Let n,m be natural numbers. Assume n \geq m. n - m is a natural number such that

  (n - m) + m = n.


Proposition NtNat270. Let n be a natural number. Then

  n - 0 = n.

Proof. [prove off] qed.


Proposition NtNat275. Let n be a natural number. Then

  n - n = 0.

Proof. [prove off] qed.


# 3. Intervals of natural numbers

Definition NtNat280. Let n,m be natural numbers. {n, \ldots, m} = {k in NAT | n \leq k \leq m}.


# 3.1 Domains of n-tuples

Proposition NtNat285. {1, \ldots, 2} = {1,2}.

Proof. [prove off] qed.


Proposition NtNat290. {1, \ldots, 3} = {1,2,3}.

Proof. [prove off] qed.


Proposition NtNat295. {1, \ldots, 4} = {1,2,3,4}.

Proof. [prove off] qed.


Proposition NtNat300. {1, \ldots, 5} = {1,2,3,4,5}.

Proof. [prove off] qed.


Proposition NtNat305. {1, \ldots, 6} = {1,2,3,4,5,6}.

Proof. [prove off] qed.


Proposition NtNat310. {1, \ldots, 7} = {1,2,3,4,5,6,7}.

Proof. [prove off] qed.


Proposition NtNat315. {1, \ldots, 8} = {1,2,3,4,5,6,7,8}.

Proof. [prove off] qed.


Proposition NtNat320. {1, \ldots, 9} = {1,2,3,4,5,6,7,8,9}.

Proof. [prove off] qed.
