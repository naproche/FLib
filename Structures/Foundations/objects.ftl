#
# Objects
# (Marcel Schütz, 2020)
#

#[prove off]
[read ForTheLib/Foundations/synonyms.ftl]
#[prove on]


# 1. Synonyms for build-in notions

Let an object stand for a sadobject.
Let a class stand for a sadclass.
Let a function stand for a sadfunction.
Let an element of x stand for a sadelement of x.
Let dom(f) stand for saddom(f).


Let a \neq b stand for a is not equal to b.

Let a \in x stand for a is an element of x.
Let x \ni a stand for a \in x.
Let a \notin x stand for not a \in x.
Let a lies in x stand for a \in x.
Let a belongs to x stand for a \in x.
Let x contains a stand for a \in x.

Let the domain of f stand for dom(f).
Let the value of f at x stand for f(x).

Let f(x,y) stand for f((x,y)).


# 2. Operations

# 2.0 Ternary operations

Signature. Let f,x,y be objects. f_{x,y} is an object.


# 2.1 Binary operations

# 2.1.1 Set-like objects

Signature. Let x,y be objects. x \cup y is an object.
Let the union of x and y stand for x \cup y.

Signature. Let x,y be objects. x \cap y is an object.
Let the intersection of x and y stand for x \cap y.

Signature. Let x,y be objects. x \setminus y is an object.
Let the complement of y in x stand for x \setminus y.

Signature. Let x,y be objects. x \triangle y is an object.
Let the symmetric difference of x and y stand for x \triangle y.

Signature. Let x,y be objects. x \sqcup y is an object.
Let x \uplus y stand for x \sqcup y.
Let the disjoint union of x and y stand for x \sqcup y.

Signature. Let x,y be objects. x \times y is an object.
Let the Cartesian product of x and y stand for x \times y.

Signature. Let x,y be objects. An upper bound of x in y is an object.

Signature. Let x,y be objects. A lower bound of x in y is an object.

Signature. Let x,y be objects. A least upper bound of x in y is an object.

Signature. Let x,y be objects. A greatest lower bound of x in y is an object.


# 2.1.2 Function-like objects

Signature. Let f,g be objects. f \circ g is an object.
Let the composition of f and g stand for f \circ g.

Signature. Let f be an object and x be an object. f[x] is an object.
Let the image of x under f stand for f[x].

Signature. Let f be an object and x be an object. f \restr x is an object.
Let the restriction of f to x stand for f \restr x.

Signature. Let x,X be objects. x_{X} is an object.


# 2.1.3 Number-like objects

Signature. Let a,b be objects. a + b is an object.
Let the sum of a and b stand for a + b.

Signature. Let a,b be objects. a - b is an object.
Let the difference of a and b stand for a - b.

Signature. Let a,b be objects. a \cdot b is an object.
Let the product of a and b stand for a \cdot b.

Signature. Let a,b be objects. frac(a,b) is an object.
Let the quotient of a and b stand for frac(a,b).
Let a / b stand for frac(a,b).

Signature. Let a,b be objects. a^{b} is an object.
Let the exponentiation of a with b stand for a^{b}.

Signature. Let a,n be objects. \sqrt[n](a) is an object.


# 2.1.4 Structures

Signature. Let x,e be objects. B(x,e) is an object.
Let the ball of radius e around x stand for B(x,e).


# 2.2 Unary operations

# 2.2.1 Set-like objects

Signature. Let x be an object. \bigcup x is an object.
Let the union of x stand for \bigcup x.

Signature. Let x be an object. \bigcap x is an object.
Let the intersection of x stand for \bigcap x.

Signature. Let x be an object. Prod(x) is an object.

Signature. Let x be an object. Coprod(x) is an object.

Signature. Let x be an object. Pow(x) is an object.

Signature. Let x be an object. An initial segment of x is an object.

Signature. Let C be an object. Obj(C) is an object.

Signature. Let C be an object. Hom(C) is an object.

Signature. Let x be an object. arity(x) is an object.
Let the arity of x stand for arity(x).


# 2.2.2 Function-like objects

Signature. Let f be an object. def(f) is an object.
Let the domain of definition of f stand for def(f).

Signature. Let f be an object. range(f) is an object.
Let the range of f stand for range(f).

Signature. Let f be an object. codom(f) is an object.
Let the codomain of f stand for codom(f).

Signature. Let f be an object. im(f) is an object.
Let the image of f stand for im(f).

Signature. Let f be an object. A value of f is an object.


# 2.2.3 Number-like objects

Signature. Let a be an object. succ(a) is an object.

Signature. Let a be an object. -a is an object.
Let the negative of a stand for -a.

Signature. Let a be an object. |a| is an object.
Let the absolute value of a stand for |a|.

Signature. Let a be an object. \sqrt(a) is an object.
Let the root of a stand for \sqrt(a).

Signature. Let a be an object. \sig(a) is an object.
Let the sign of a stand for \sig(a).

Signature. Let a be an object. A predecessor of a is an object.

Signature. Let a be an object. A direct predecessor of a is an object.

Signature. Let a be an object. A successor of a is an object.

Signature. Let a be an object. A direct successor of a is an object.

Signature. Let X be an object. A maximal element of X is an object.

Signature. Let X be an object. A minimal element of X is an object.

Signature. Let X be an object. A greatest element of X is an object.

Signature. Let X be an object. A least element of X is an object.

Signature. Let X be an object. An upper bound of X is an object.

Signature. Let X be an object. A lower bound of X is an object.

Signature. Let X be an object. A supremum of X is an object.

Signature. Let X be an object. An infimum of X is an object.


# 2.2.4 Structures

Signature. Let a be an object. A basis of a is an object.

Signature. Let a be an object. A subbasis of a is an object.

Signature. Let a be an object. A neighbourhood of a is an object.

Signature. Let a be an object. An open neighbourhood of a is an object.

Signature. Let X be an object. A substructure of X is a notion.
Let a subspace of X stand for a substructure of X.

Signature. Let X be an object. An interiorpoint of X is a notion.

Signature. Let X be an object. A boundarypoint of X is a notion.

Signature. Let X be an object. int(X) is an object.
Let the interior of X stand for int(X).

Signature. Let X be an object. \partial X is an object.
Let the boundary of X stand for \partial X.

Signature. Let X be an object. cl(X) is an object.
Let the closure of X stand for cl(X).



# 2.3 Constants

Signature. 0 is an object.
Signature. 1 is an object.
Signature. 2 is an object.
Signature. 3 is an object.
Signature. 4 is an object.
Signature. 5 is an object.
Signature. 6 is an object.
Signature. 7 is an object.
Signature. 8 is an object.
Signature. 9 is an object.

Signature. id is an object.

Signature. forget is an object.


# 3. Relations

# 3.1 Binary relations

Signature. Let x,y be objects. x \subseteq y is an atom.
Let x \subset    y stand for x \subseteq y.
Let x \nsubset   y stand for not x \subset y.
Let x \nsubseteq y stand for not x \subset y.
Let x \subsetneq y stand for x \subset y and x \neq y.
Let x \supset    y stand for y \subset x.
Let x \supseteq  y stand for x \subset y.
Let x \nsupset   y stand for not x \supset y.
Let x \nsupseteq y stand for not x \supset y.
Let x \supsetneq y stand for x \supset y and x \neq y.

Signature. Let f,a be objects. f is continuous at a is an atom.

Signature. Let a,b be objects. a is open in b is an atom.

Signature. Let a,b be objects. a is closed in b is an atom.

Signature. Let a,b be objects. a is clopen in b is an atom.

Signature. Let a,b be objects. a < b is an atom.
Let a is less than b stand for a < b.
Let a > b stand for b < a.
Let a is greater than b stand for a > b.

Signature. Let a,b be objects. a \leq b is an atom.
Let a is less than or equal to b stand for a \leq b.
Let a \geq b stand for b \leq a.
Let a is greater than or equal to b stand for a \geq b.

Signature. Let x,y be objects. x \mid y is an atom.
Let n \nmid m stand for not (n \mid m).
Let n divides m stand for n \mid m.

Signature. Let x,y be objects. x \equiv y is an atom.

Signature. Let f,x be a objects. f is symmetric on x is an atom.

Signature. Let f,x be a objects. f is subadditive on x is an atom.

Signature. Let f,x be a objects. f is positive definite on x is an atom.

Signature. Let x,y be objects. x and y are equivalent is an atom.


# 3.2 Unary relations

Signature. Let f be an object. f is injective is an atom.

Signature. Let f be an object. f is surjective is an atom.

Signature. Let f be an object. f is bijective is an atom.

Signature. Let a be an object. a is monotone is an atom.
Let a is monotonic stand for a is monotone.
Let a is isotone stand for a is monotonic.
Let a is orderpreserving stand for a is monotonic.

Signature. Let a be an object. a is antimonotone is an atom.
Let a is antitone stand for a is antimonotone.
Let a is orderreversing stand for a is antimonotone.

Signature. Let a be an object. a is strictly monotonic is an atom.

Signature. Let a be an object. a is monotonically increasing is an atom.

Signature. Let a be an object. a is monotonically decreasing is an atom.

Signature. Let a be an object. a is strictly monotonically increasing is an atom.

Signature. Let a be an object. a is strictly monotonically decreasing is an atom.

Signature. Let f be an object. f is continuous is an atom.

Signature. Let a be an object. a is transitive is an atom.

Signature. Let a be an object. a is inductive is an atom.

Signature. Let A be an object. A is open is an atom.

Signature. Let A be an object. A is closed is an atom.

Signature. Let A be an object. A is clopen is an atom.

Signature. Let X be an object. X is small is an atom.

Signature. Let X be an object. X is large is an atom.

Signature. Let X be an object. X is locally small is an atom.

Signature. Let f be an object. f is invertible is an atom.

Signature. Let X be an object. X is bounded is an atom.

Signature. Let f be an object. f is constant is an atom.


# 4. Definitions

Definition. Let x be an object. x is positive iff x > 0.

Definition. Let x be an object. x is negative iff x < 0.

Definition. Let x be an object. x is nonpositive iff x \leq 0.

Definition. Let x be an object. x is nonnegative iff x \geq 0.


Definition. Let X be an object. A subcollection of X is an object A such that every element of A is
an element of X.

