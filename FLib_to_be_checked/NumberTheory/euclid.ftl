[read primes.ftl]
[prove on]

Signature Set.
A set of naturals is a notion.

Let S denote a set of naturals.

Signature Element.
An element of S is a notion.

Let x << S stand for x is an element of S.

Axiom ElementsOfS.
Let S be a set of naturals. Then every element of S is a natural number.

Signature Finite.
S is finite is an atom.

Let S is infinite stand for S is not finite.
Let S denote a finite set of naturals.

Signature Product.
Prod(S) is a natural number such that every element x of S divides Prod(S)
and for every natural number n (if every element of S divides n then Prod(S) divides n).

Axiom ZeroProduct.
Prod(S) = 0 <=> 0 << S.


Axiom NotDivOne.
Let n be a nontrivial natural number. Then n does not divide 1.

Axiom OneAdd.
Let n be a natural number. Assume n != 0. Then n + 1 != 1.



Lemma NotZero.
Let n be a natural number. Then n + 1 != 0.
Proof.
1 != 0.
Therefore n + 1 != 0 (by ZeroAdd).
qed.


Theorem.
Assume for every natural number n (n << S <=> (n is prime)). Then S is infinite.
Proof by contradiction.
Assume S is finite.
Prod(S) + 1 is nontrivial.
Therefore we can take a prime divisor p of Prod(S) + 1 (by PrimDiv).
Then p | Prod(S). Therefore p | 1 (by DivMin).
We have a contradiction.
end.
