[prove off] [check off]
# Set Theory

# Preliminaries

[subset/-s]
Let x,y,z stand for sets.
Let x \in y denote x is an element of y.
Let x \notin y denote x is not an element of y.

Axiom. x \in y => x -<- y.

Theorem. x \notin x.

Proof by induction on x. qed.

Signature. The empty set is the set that has no elements.
Let \emptyset denote the empty set.

Definition. x is nonempty iff x has an element.

Definition. A subset of y is a set x such that every element 
of x is an element of y. 
Let x \subset y stand for x is a subset of y.
Let y \supset x stand for x is a subset of y.

Definition. A proper subset of y is a subset x of y such that there is an element of y that is not an element of x.

Proposition. x \subset x.

Proposition. If x \subset y \subset x then x = y.

Definition. x \cup y = {u | u \in x  or  u \in y}.

Lemma. x \cup y \supset x.

Definition. {x} = {sets y | y = x}.

# Ordinal Numbers

[ordinal/-s]


Definition. x is transitive iff
every element of x is a subset of x.
Let Trans(x) stand for x is transitive.

Definition. An ordinal is a set x such that x is transitive 
and every element of x is transitive.
Let Ord(x) stand for x is an ordinal.
Let alpha, beta, gamma, delta, xi stand for ordinals.


Theorem. \emptyset is an ordinal.

Definition. 0 = \emptyset.

Definition. x + 1 = x \cup {x}.

Theorem. alpha + 1 is an ordinal.

Theorem. If Ord(beta) and alpha \in beta then Ord(alpha). 

# \in is a strict linear ordering of the ordinals

Theorem. alpha \in beta \in gamma => alpha \in gamma.

Theorem. alpha \notin alpha.

Theorem. For all alpha for all beta alpha \in beta or alpha = beta or beta \in alpha.
Proof by induction on alpha. 
  For all beta (alpha \in beta or alpha = beta or beta \in alpha).
  Proof by induction on beta.
  Assume that not alpha \in beta and not beta \in alpha.
    Let us prove that alpha = beta.
      Let us prove that alpha \subset beta.
      Let xi \in alpha. 
        Then xi \in beta or xi = beta or beta \in xi.
        Case beta \in xi. Then beta \in alpha. Contradiction. end.
        Case beta = xi. Then beta \in alpha. Contradiction.end.
        Case xi \in beta. end.
        end.
      end.
      Let us prove that beta \subset alpha.
      Let xi \in beta. 
        Then alpha \in xi or alpha = xi or xi \in alpha.
        Case alpha \in xi. Then alpha \in beta. Contradiction. end.
        Case alpha = xi. Then alpha \in beta. Contradiction. end.
        Case xi \in alpha. end.
        end.
  end.
end.

# The natural ordering of the ordinals:

Definition. alpha < beta iff alpha \in beta.

# alpha + 1 is the immediate successor of alpha

Theorem. alpha < alpha +1.

Theorem. If beta < alpha +1 then beta = alpha or beta < alpha.

Definition. A successor ordinal is an ordinal alpha such that 
there exists beta such that alpha = beta +1.
Let Succ(x) stand for x is a successor ordinal.

Definition. A limit ordinal is an ordinal alpha such that
alpha != 0 and alpha is not a successor ordinal.
Let Lim(x) stand for x is a limit ordinal.



# Natural Numbers

[number/-s]

Definition. A natural number is an ordinal n such that
((n = 0 or Succ(n)) and for all m \in n (m=0 or Succ(m))).
Let m,n stand for natural numbers.

Theorem. 0 is a natural number.
Theorem. m + 1 is a natural numbers.

Definition. \omega is the set of natural numbers.

Definition. x is inductive iff 0 \in x and for all y (y \in x => y+1 \in x). 

# \omega is the \subset-smallest inductive set.



Theorem. \omega is inductive.
Theorem. If x is inductive then \omega \subset x.
Proof. Let x be inductive.
For all natural numbers m we have m \in x.
Proof by induction.
Let m be a natural number.
Case m = 0. Then m \in x. end.
Case Succ(m). Take a natural number n such that m = n + 1.
n < m. n \in x. Then m = n+1 \in x. end.
qed.
qed.

# The principle of complete induction:
Theorem. If x is an inductive subset of \omega then x = \omega.
Theorem. For all subsets x of \omega
  ((0 \in x and for all n \in x n+1 \in x) => x = \omega).

Theorem. \omega is an ordinal.
Theorem. \omega is a limit ordinal.

[/prove] [/check]

# Ordinal Arithmetic
# The operations are defined recursively with case distinctions.
# I need to get the general format of function definitions from Frerix

Definition. Define fac[x] = (Case x != 0 -> x * x) for x << \omega.

