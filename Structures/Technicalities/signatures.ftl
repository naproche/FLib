#
# Signature extensions
# (Marcel Schütz, 2020)
#

[read ForTheLib/Technicalities/synonyms.ftl]
[read ForTheLib/Technicalities/prelude.ftl]


# 1. Operations

Signature. Let x,y be entities. disunion(x,y) is a notion.
Let x \sqcup y stand for disunion(x,y).
Let x \uplus y stand for disunion(x,y).
Let the disjoint union of x and y stand for disunion(x,y).

Signature. Let x,y be entities. times(x,y) is a notion.
Let x \times y stand for times(x,y).
Let the Cartesian product of x and y stand for times(x,y).

Signature. Let x,y be entities. comp(x,y) is a notion.
Let x \circ y stand for comp(x,y).
Let the composition of x and y stand for comp(x,y).


Signature. Let x,y,z be entities. x_{y,z} is a notion.

Signature. Let x,y be entities. x_{y} is a notion.

Signature. Let x,y be entities. x[y] is a notion.
Let the image of y under x stand for x[y].

Signature. Let x,y be entities. sum(x,y) is a notion.
Let x + y stand for sum(x,y).
Let the sum of x and y stand for sum(x,y).

Signature. Let x,y be entities. diff(x,y) is a notion.
Let x - y stand for diff(x,y).
Let the difference of x and y stand for diff(x,y).

Signature. Let x,y be entities. prod(x,y) is a notion.
Let x \cdot y stand for prod(x,y).
Let the product of x and y stand for prod(x,y).

Signature. Let x,y be entities. frac(x,y) is a notion.
Let x / y stand for frac(x,y).
Let \frac{x}{y} stand for frac(x,y).
Let the quotient of x and y stand for frac(x,y).

Signature. Let x,y be entities. exp(x,y) is a notion.
Let x^{y} stand for exp(x,y).
Let the exponentiation of x with y stand for exp(x,y).

Signature. Let x,y be entities. root(x,y) is a notion.
Let \sqrt[x](y) stand for root(x,y).

Signature. Let x,y be entities. B(x,y) is a notion.
Let the ball of radius y around x stand for B(x,y).

Signature. Let x be an entity. Prod(x) is a notion.
Let the product over x stand for Prod(x).

Signature. Let x be an entity. Coprod(x) is a notion.
Let the coproduct over x stand for Coprod(x).

Signature. Let x be an entity. Obj(x) is a notion.

Signature. Let x be an entity. Hom(x) is a notion.

Signature. Let x be an entity. arity(x) is a notion.
Let the arity of x stand for arity(x).

Signature. Let x be an entity. def(x) is a notion.
Let the domain of definition of x stand for def(x).

Signature. Let x be an entity. codom(x) is a notion.
Let the codomain of x stand for codom(x).

Signature. Let x be an entity. im(x) is a notion.
Let the image of x stand for im(x).

Signature. Let x be an entity. succ(x) is a notion.

Signature. Let x be an entity. neg(x) is a notion.
Let -x stand for neg(x).
Let the negative of x stand for neg(x).

Signature. Let x be an entity. abs(x) is a notion.
Let |x| stand for abs(x).
Let the absolute value of x stand for abs(x).

Signature. Let x be an entity. sqrt(x) is a notion.
Let \sqrt{x} stand for sqrt(x).
Let the root of x stand for sqrt(x).

Signature. Let x be an entity. sig(x) is a notion.
Let the sign of x stand for sig(x).

Signature. Let x be an entity. int(x) is a notion.
Let the interior of x stand for int(x).

Signature. Let x be an entity. partial(x) is a notion.
Let \partial x stand for partial(x).
Let the boundary of x stand for partial(x).

Signature. Let x be an entity. cl(x) is a notion.
Let the closure of x stand for cl(x).


Signature. Let x,y be entities. An upper bound of x in y is a notion.

Signature. Let x,y be entities. A lower bound of x in y is a notion.

Signature. Let x,y be entities. A least upper bound of x in y is a notion.

Signature. Let x,y be entities. A greatest lower bound of x in y is a notion.

Signature. Let x be an entity. An initial segment of x is a notion.

Signature. Let x be an entity. A leftinverse of x is a notion.

Signature. Let x be an entity. A rightinverse of x is a notion.

Signature. Let x be an entity. An inverse of x is a notion.

Signature. Let x be an entity. A predecessor of x is a notion.

Signature. Let x be an entity. A direct predecessor of x is a notion.

Signature. Let x be an entity. A successor of x is a notion.

Signature. Let x be an entity. A direct successor of x is a notion.

Signature. Let x be an entity. A maximal element of x is a notion.

Signature. Let x be an entity. A minimal element of x is a notion.

Signature. Let x be an entity. A greatest element of x is a notion.

Signature. Let x be an entity. A least element of x is a notion.

Signature. Let x be an entity. An upper bound of x is a notion.

Signature. Let x be an entity. A lower bound of x is a notion.

Signature. Let x be an entity. A supremum of x is a notion.

Signature. Let x be an entity. An infimum of x is a notion.

Signature. Let x be an entity. A basis of x is a notion.

Signature. Let x be an entity. A subbasis of x is a notion.

Signature. Let x be an entity. A neighbourhood of x is a notion.

Signature. Let x be an entity. An open neighbourhood of x is a notion.

Signature. Let x be an entity. A substructure of x is a notion.
Let a subspace of x stand for a substructure of x.

Signature. Let x be an entity. An interiorpoint of x is a notion.

Signature. Let x be an entity. A boundarypoint of x is a notion.

Signature. Let x be an entity. The topology of x is a notion.



# 2. Constants

Signature. 0 is a notion.
Signature. 1 is a notion.
Signature. 2 is a notion.
Signature. 3 is a notion.
Signature. 4 is a notion.
Signature. 5 is a notion.
Signature. 6 is a notion.
Signature. 7 is a notion.
Signature. 8 is a notion.
Signature. 9 is a notion.

Signature. id is a notion.


# 3. Relations

Signature. Let x,y be entities. sub(x,y) is a statement.
Let x \subseteq  y stand for sub(x,y).
Let x \subset    y stand for sub(x,y).
Let x \nsubset   y stand for not sub(x,y).
Let x \nsubseteq y stand for not sub(x,y).
Let x \subsetneq y stand for sub(x,y) and x \neq y.
Let x \supset    y stand for sub(y,x).
Let x \supseteq  y stand for sub(y,x).
Let x \nsupset   y stand for not sub(y,x).
Let x \nsupseteq y stand for not sub(y,x).
Let x \supsetneq y stand for sub(y,x) and x \neq y.

Signature. Let x,y be entities. less(x,y) is a statement.
Let x < y stand for less(x,y).
Let x is less than y stand for less(x,y).
Let x > y stand for less(y,x).
Let x is greater than y stand for less(y,x).

Signature. Let x,y be entities. leq(x,y) is a statement.
Let x \leq y stand for leq(x,y).
Let x is less than or equal to y stand for leq(x,y).
Let x \geq y stand for leq(y,x).
Let x is greater than or equal to y stand for leq(y,x).

Signature. Let x,y be entities. divides(x,y) is a statement.
Let x \mid y stand for divides(x,y).
Let x \nmid y stand for not divides(x,y).
Let x divides y stand for divides(x,y).

Signature. Let x,y be entities. equiv(x,y) is a statement.
Let x \equiv y stand for equiv(x,y).


Signature. Let x,y be entities. x is continuous at y is a statement.

Signature. Let x,y be entities. x is open in y is a statement.

Signature. Let x,y be entities. x is closed in y is a statement.

Signature. Let x,y be entities. x is clopen in y is a statement.

Signature. Let x,y be entities. x is symmetric on y is a statement.

Signature. Let x,y be entities. x is subadditive on y is a statement.

Signature. Let x,y be entities. x is positive definite on y is a statement.

Signature. Let x,y be entities. x and y are equivalent is a statement.

Signature. Let x,y be entities. x carries y is a statement.

Signature. Let x be an entity. x is discrete is a statement.

Signature. Let x be an entity. x is indiscrete is a statement.

Signature. Let x be an entity. x is monotone is a statement.
Let x is monotonic stand for x is monotone.
Let x is isotone stand for x is monotonic.
Let x is orderpreserving stand for x is monotonic.

Signature. Let x be an entity. x is antimonotone is a statement.
Let x is antitone stand for x is antimonotone.
Let x is orderreversing stand for x is antimonotone.

Signature. Let x be an entity. x is strictly monotonic is a statement.

Signature. Let x be an entity. x is monotonically increasing is a statement.

Signature. Let x be an entity. x is monotonically decreasing is a statement.

Signature. Let x be an entity. x is strictly monotonically increasing is a statement.

Signature. Let x be an entity. x is strictly monotonically decreasing is a statement.

Signature. Let x be an entity. x is continuous is a statement.

Signature. Let x be an entity. x is transitive is a statement.

Signature. Let x be an entity. x is inductive is a statement.

Signature. Let x be an entity. x is open is a statement.

Signature. Let x be an entity. x is closed is a statement.

Signature. Let x be an entity. x is clopen is a statement.

Signature. Let x be an entity. x is invertible is a statement.

Signature. Let x be an entity. x is bounded is a statement.


# 4. Definitions

Definition TecSig000. Let x be an entity. x is positive iff x > 0.

Definition TecSig005. Let x be an entity. x is negative iff x < 0.

Definition TecSig010. Let x be an entity. x is nonpositive iff x \leq 0.

Definition TecSig015. Let x be an entity. x is nonnegative iff x \geq 0.
