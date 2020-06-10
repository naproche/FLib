#
# Integers
# (Marcel Schütz, 2020)
#

[read ForTheLib/Sets/cardinality.ftl]


# 1. Definitions

Signature NtInt000. An integer is a notion.

Definition NtInt005. INT = {n | n is an integer}.


Axiom NtInt010. Let n be an integer. -n is an integer.

Axiom NtInt015. Every natural number is an integer.

Axiom NtInt020. -0 = 0.
Axiom NtInt025. Let n be an integer. -(-n) = n.


Axiom NtInt030. Let n be an integer. n \in NAT or -n \in NAT.


# 2. The set of integers

Proposition NtInt035. INT is countably infinite set.

Proof. [prove off] qed.


# 3. Order

Axiom NtInt040. Let n,m be natural numbers. Then

  -n < -m <=> n > m.


Axiom NtInt045. Let n,m be natural numbers. Assume that n \neq 0. Then

  -n < m.


Axiom NtInt050. Let n,m be integers.

  n \leq m <=> (n < m \/ n = m).


Proposition NtInt055. Let n be an integer. Then

  not n < n.

Proof. [prove off] qed.


Proposition NtInt060. Let n,m be integers. Then

  n < m  =>  not m < n.

Proof. [prove off] qed.


Proposition NtInt065. Let n,m be integers. Then

  (n \leq m /\ m \leq n) => n = m.

Proof. [prove off] qed.


Proposition NtInt070. Let n,m,k be integers. Then

  n < m < k  =>  n < k.

Proof. [prove off] qed.


Proposition NtInt075. Let n,m be integers. Then

  n < m \/ n = m \/ n > m.

Proof. [prove off] qed.


# 4. Arithmetic

# 4.1 Absolute value

Axiom NtInt080. Let n be a natural number. Then

  |n| = n.


Axiom NtInt085. Let n be a natural number. Then

  |-n| = n.


# 4.2 Addition

Axiom NtInt090. Let n,m be integers. n + m is an integer.


Axiom NtInt095. Let n,m be natural numbers. Then

  (-n) + (-m) = -(n + m).


Axiom NtInt100. Let n,m be natural numbers. Assume n \geq m. Then

  n + (-m) = n - m.


Axiom NtInt105. Let n,m be natural numbers. Assume n \geq m. Then

  (-m) + n = n - m.


Axiom NtInt110. Let n,m be natural numbers. Assume n < m. Then

  n + (-m) = -(m - n).


Axiom NtInt115. Let n,m be natural numbers. Assume n < m. Then

  (-m) + n = -(m - n).


Proposition NtInt120. Let n,m,k be integers. Then

  (n + m) + k = n + (m + k).

Proof. [prove off] qed.


Proposition NtInt125. Let n,m be integers. Then

  n + m = m + n.

Proof. [prove off] qed.


Proposition NtInt130. Let n be an integer. Then

  n + 0 = n.

Proof. [prove off] qed.


Proposition NtInt135. Let n be an integer. Then

  n + (-n) = 0.

Proof. [prove off] qed.


Proposition NtInt140. Let n,m,k,l be integers. Then

  (n < m /\ k < l)  =>  n + k < m + l.

Proof. [prove off] qed.


# 4.3 Subtraction

Axiom NtInt145. Let n,m be integers. Then

  n - m = n + (-m).


# 4.4 Multiplication

Axiom NtInt150. Let n,m be integers. n \cdot m is an integer.


Axiom NtInt155. Let n,m be natural numbers. Then

  (-n) \cdot (-m) = n \cdot m.


Axiom NtInt160. Let n,m be natural numbers. Then

  (-n) \cdot m = -(n \cdot m).


Axiom NtInt165. Let n,m be natural numbers. n \cdot (-m) = -(n \cdot m).


# 4.5 Exponentiation

Axiom NtInt170. Let n be an integer. Let k be a natural number. n^{k} is an integer.


Axiom NtInt175. Let n be an integer. Then

  n^{0} = 1.


Axiom NtInt180. Let n be an integer. Let k be a natural number. Then

  n^{k + 1} = n \cdot n^{k}.


# 4.6 Basic properties

Proposition NtInt185. Let n,m,k be integers. Then

  (n \cdot m) \cdot k = n \cdot (m \cdot k).

Proof. [prove off] qed.


Proposition NtInt190. Let n,m be integers. Then

  n \cdot m = m \cdot n.

Proof. [prove off] qed.


Proposition NtInt195. Let n be an integer. Then

  n \cdot 1 = n.

Proof. [prove off] qed.


Proposition NtInt200. Let n be an integer. Then

  n \cdot n = 1  <=> (n = 1 \/ n = -1).

Proof. [prove off] qed.


Proposition NtInt205. Let n,m,k be integers. Then

  n \cdot (m + k) = (n \cdot m) + (n \cdot k).

Proof. [prove off] qed.


Proposition NtInt210. Let n,m,k be integers. Then

  (n + m) \cdot k = (n \cdot k) + (m \cdot k).

Proof. [prove off] qed.


Proposition NtInt215. Let n,m be integers. Then

  n \cdot m = 0  =>  (n = 0 \/ m = 0).

Proof. [prove off] qed.


Proposition NtInt220. Let n,m,k be integers. Assume that k > 0. Then

  n < m  =>  n \cdot k < m \cdot k.

Proof. [prove off] qed.


# 5. Divisibility

Axiom NtInt225. Let n,m be integers. n \mid m iff there exists an integer k such that m = k \cdot n.

Definition NtInt230. Let n,m be integers. m is divisible by n iff n divides m.


Definition NtInt235. Let n be an integer. A factor of n is an integer that divides n.

Definition NtInt240. Let n be an integer. A divisor of n is an integer that divides n.


Proposition NtInt245. Let n be a integers. Then

  n \mid 0.

Proof. [prove off] qed.


Proposition NtInt250. Let n be a integers. Then

  0 \mid n  =>  n = 0.

Proof. [prove off] qed.


Proposition NtInt255. Let n be a integers. Then

  1 \mid n.

Proof. [prove off] qed.


Proposition NtInt260. Let n be a integers. Then

  n \mid n.

Proof. [prove off] qed.


Proposition NtInt265. Let n be a integers. Then

  n \mid 1  =>  (n = 1 \/ n = -1).

Proof. [prove off] qed.


Proposition NtInt270. Let n,m,k be integers. Then

  (n \mid m /\ m \mid k)  =>  n \mid k.

Proof. [prove off] qed.


Proposition NtInt275. Let n,m,k be integers. Then

  n \mid m  =>  k \cdot n \mid k \cdot m.

Proof. [prove off] qed.


Proposition NtInt280. Let n,m,k be integers. Assume k \neq 0. Then

  k \cdot n \mid k \cdot m  =>  n \mid m.

Proof. [prove off] qed.


Proposition NtInt285. Let n,m,k be integers. Then

  (k \mid n /\ k \mid m)  =>  (k \mid (a \cdot n) + (b \cdot m) for all integers a,b).

Proof. [prove off] qed.


Proposition NtInt290. Let n,m be positive integers. Then

  m \mid n  =>  m \leq n.

Proof. [prove off] qed.


Proposition NtInt295. Let n be an integer. n divides n.

Proof. [prove off] qed.


Proposition NtInt300. Let n,m,k be integers. If n divides m and m divides k then n divides k.

Proof. [prove off] qed.


# 6. Odd and even numbers

Definition NtInt305. Let n be an integer. n is even iff n is divisible by 2.

Definition NtInt310. Let n be an integer. n is odd iff n is not divisible by 2.
