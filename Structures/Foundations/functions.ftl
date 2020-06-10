#
# Functions
# (Marcel Schütz, 2020)
#

#[prove off]
[read ForTheLib/Foundations/classes.ftl]
#[prove on]


# 1. Extensionality

Axiom FoundFun000. Let f,g be functions. If the domain of f is equal to the domain of g and the
value of f at x is equal to the value of g at x for all elements x of the domain of f then f is
equal to g.


# 2. Range

Axiom FoundFun005. Let f be a function. range(f) is a class such that range(f) =
{f(x) | x \in dom(f)}.

Axiom FoundFun010. Let f be a function. The image of f is the range of f.

Axiom FoundFun015. Let f be a function. The codomain of f is the range of f.


Axiom FoundFun020. Let f be a function and y be an object. y is a value of f iff y is an element of
the range of f.


Proposition FoundFun025. Let f be a function and y be an object. y is a value of f iff y = f(x) for
some element x of the domain of f.


# 3. Functions from ... to ...

Definition FoundFun035. Let x be an object. A function of x is a function f such that the domain of
f is equal to x.

Definition FoundFun040. Let x,y be objects. A function from x to y is a function f of x such that
the range of f is a subclass of y.

Definition FoundFun045. Let x be an object. A function on x is a function from x to x.


# 4. Preimage

Axiom FoundFun050. Let f be a function. f^{-1} is a function from range(f) to dom(f).


Proposition FoundFun055. Let f be a function. dom(f^{-1}) = range(f).


Proposition FoundFun060. Let f be a function and y \in range(f). f^{-1}(y) \in dom(f).

Proof.
  y \in dom(f^{-1}). range(f^{-1}) \subseteq dom(f).
qed.


Axiom FoundFun065. Let f be a function and y \in range(f). f(f^{-1}(y)) = y.

Let the preimage of y under f stand for f^{-1}[y].


# 5. Injectivity

Axiom FoundFun070. Let f be a function. f is injective iff for all x,y \in dom(f) if f(x) = f(y)
then x = y.


# 6. Bijection

Definition FoundFun075. Let x be an object and y be a class. A bijection between x and y is an
injective function f of x such that the range of f is equal to y.


Proposition FoundFun080. Let x be an object and y be a class and f be a bijection between x and y.
Then dom(f) = x.


Proposition FoundFun085. Let x,y be classes and f be a bijection between x and y. Then f^{-1} is a
bijection between y and x.

Proof. [prove off] qed.


Proposition FoundFun090. Let x,y,z be classes. Let f be a bijection between x and y and g be a
bijection between y and z. Then g \circ f is a bijection between x and z.

Proof. [prove off] qed.


# 7. Composition

Axiom FoundFun095. Let f,g be functions. Assume that range(f) is a subcollection of dom(g). Then
g \circ f is a function of dom(f) such that (g \circ f)(x) = g(f(x)) for all x \in dom(f).


Proposition FoundFun100. Let f,g be functions. Assume that codom(f) \subseteq dom(g). Then
range(g \circ f) \subseteq range(g).

Proof.
  Let us show that y is a value of g for all y \in range(g \circ f).
    Let y \in range(g \circ f). dom(g \circ f) = dom(f). Take x \in dom(f) such that
    y = (g \circ f)(x). y = g(f(x)). Thus y is a value of g.
  end.
qed.


# 8. Restriction

Axiom FoundFun105. Let f be a function and x be an object. Assume that every element of x is an
element of dom(f). f \restr x is a function such that dom(f \restr x) = x and (f \restr x)(u) = f(u)
for all u \in x.


Proposition FoundFun110. Let f be a function and x be an object. Assume that x \subseteq dom(f).
Then range(f \restr x) \subseteq range(f).

Proof. [prove off] qed.


# 9. Image

Axiom FoundFun115. Let f be a function and x be an object. f[x] is a class such that 
f[x] = {f(u) | u \in dom(f) and u \in x}.


Proposition FoundFun120. Let f be a function. The image of the domain of f under f is the range of
f.

Proof.
  f[dom(f)] = {f(x) | x \in dom(f)}. Hence range(f) = {f(x) | x \in dom(f)} (by FoundFun005). Thus
  f[dom(f)] = range(f). Indeed f[dom(f)] and range(f) are classes.
qed.


Proposition FoundFun125. Let x,y,z be classes and f be a bijection between x and y. Assume that
z \subseteq x. Then the restriction of f to z is a bijection between z and f[z].

Proof. [prove off] qed.


Proposition FoundFun130. Let f be a function and Y be a class. Then f^{-1}[Y] =
{x in dom(f) | f(x) \in Y}.

Proof. [prove off] qed.


# 10. Zeroes

Definition FoundFun135. Let f be a function. A zero of f is an element x of the domain of f such
that f(x) = 0.


# 11. Binary functions

Definition FoundFun140. Let X be an object. A binary function on X is a function f such that (x,y)
is an element of the domain of f for all elements x,y of X.
