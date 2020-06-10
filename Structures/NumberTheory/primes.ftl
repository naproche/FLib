#
# Prime numbers
# (Marcel Schütz, 2020)
#

[read ForTheLib/NumberTheory/integers.ftl]


# 1. Definitions

Definition NtPrm000. A prime number is a natural number p such that p \geq 2 and for all natural numbers
n if n \mid p then n = 1 or n = p.

Definition NtPrm005. Let n be an integer. n is prime iff n is a prime number.

Definition NtPrm010. Let n be an integer. n is composite iff n \geq 2 and n is not prime.


# 2. Basic facts

Proposition NtPrm015. Let n be an natural number. Assume n \geq 2. n is composite iff there
exist factors a,b of n such that 1 < a,b < n and a \neq b.

Proof. [prove off] qed.


Proposition NtPrm020. Let n be an natural number. Assume n > 1. Then n has a prime divisor.

Proof. [prove off] qed.


Proposition NtPrm025. Let n be an natural number. Assume n > 1. Then n has a divisor p such that
p^{2} \leq n.

Proof. [prove off] qed.


# 3. Euclid's theorem

Definition NtPrm030. PRIME = {p | p is a prime number}.


Theorem NtPrm035. PRIME is an countably infinite set.

Proof. [prove off] qed.
