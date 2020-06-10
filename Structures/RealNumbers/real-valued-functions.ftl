#
# Real functions
# (Marcel Schütz, 2020)
#

[read ForTheLib/RealNumbers/reals.ftl]


# 1. Definition

Definition AnaRvf000. Let f be a function. f is realvalued iff every value of f is a real number.

Lemma AnaRvf001. Let f be a realvalued function. f(x) is a real number for all x \in dom(f).


# 2. Arithmetic

# 2.1 Negating a function

Axiom AnaRvf005. Let f be a realvalued function. -f is a function of dom(f) such that
(-f)(x) = -(f(x)) for all x \in dom(f).


# 2.2 Combining two functions

Axiom AnaRvf010. Let f,g be realvalued functions such that dom(f) = dom(g). f + g is a function of
dom(f) such that (f + g)(x) = f(x) + g(x) for all x \in dom(f).

Axiom AnaRvf015. Let f,g be realvalued functions such that dom(f) = dom(g). f - g is a function of
dom(f) such that (f - g)(x) = f(x) - g(x) for all x \in dom(f).

Axiom AnaRvf020. Let f,g be realvalued functions such that dom(f) = dom(g). f \cdot g is a function
of dom(f) such that (f \cdot g)(x) = f(x) \cdot g(x) for all x \in dom(f).

Axiom AnaRvf025. Let f,g be realvalued functions such that dom(f) = dom(g). Assume that g has no
zeroes. f/g is a function of dom(f) such that (f/g)(x) = f(x)/g(x) for all x \in dom(f).


# 2.3 Combining a function and a scalar

Axiom AnaRvf030. Let f be a realvalued function and c be a real number. f + c is a function of
dom(f) such that (f + c)(x) = f(x) + c for all x \in dom(f).

Axiom AnaRvf035. Let f be a realvalued function and c be a real number. c + f is a function of
dom(f) such that (c + f)(x) = c + f(x) for all x \in dom(f).

Axiom AnaRvf040. Let f be a realvalued function and c be a real number. f - c is a function of
dom(f) such that (f - c)(x) = f(x) - c for all x \in dom(f).

Axiom AnaRvf045. Let f be a realvalued function and c be a real number. c - f is a function of
dom(f) such that (c - f)(x) = c - f(x) for all x \in dom(f).


# 2.4 Combining a scalar and a function

Axiom AnaRvf050. Let f be a realvalued function and c be a real number. c \cdot f is a function of
dom(f) such that (c \cdot f)(x) = c \cdot f(x) for all x \in dom(f).

Axiom AnaRvf055. Let f be a realvalued function and c be a real number. f \cdot c is a function of
dom(f) such that (f \cdot c)(x) = f(x) \cdot c for all x \in dom(f).

Axiom AnaRvf060. Let f be a realvalued function and c be a real number. Assume that c \neq 0. f/c is
a function of dom(f) such that (f/c)(x) = f(x)/c for all x \in dom(f).

Axiom AnaRvf065. Let f be a realvalued function and c be a real number. Assume that f has no zeroes.
f/c is a function of dom(f) such that (f/c)(x) = f(x)/c for all x \in dom(f).


# 2.5 Absolute value

Axiom AnaRvf070. Let f be a realvalued function. |f| is a function of dom(f) such that
|f|(x) = |f(x)| for all x \in dom(f).


# 2.6 Powers

Axiom AnaRvf075. Let f be a realvalued function and n be a natural number. f^{n} is a function of
dom(f) such that (f^{n})(x) = (f(x))^{n} for all x \in dom(f).

# Note that we have f^{-1} defined as the preimage of f. Thus we cannot write f^{-1} instead of 1/f.


# 3. Order

Axiom AnaRvf079. Let f be a realvalued function and c be a real number. f \equiv c iff f(x) = c for
all x \in dom(f).

Axiom AnaRvf080. Let f,g be realvalued functions such that dom(f) = dom(g). f < g iff f(x) < g(x)
for all x \in dom(f).

Axiom AnaRvf085. Let f be a realvalued function and c be a real number. f < c iff f(x) < c for all
x \in dom(f).

Axiom AnaRvf086. Let f,g be realvalued functions such that dom(f) = dom(g). f \leq g iff
f(x) \leq g(x) for all x \in dom(f).

Axiom AnaRvf087. Let f be a realvalued function and c be a real number. f \leq c iff f(x) \leq c for
all x \in dom(f).

Axiom AnaRvf088. Let f be a realvalued function and c be a real number. c \leq f iff c \leq f(x) for
all x \in dom(f).


# 4. Bounded functions

Definition AnaRvf090. Let f be a realvalued function. f is bounded iff |f| < c for some real number
c.


# 5. Misc

Lemma AnaRvf094. Let X be an object and f be a binary function on X. Then (x,y) \in dom(f) for all
x,y \in X.

Proof. [prove off] qed.


Axiom AnaRvf095. Let X be an object and f be a binary function on X that is realvalued. f is
symmetric on X iff f(x,y) = f(y,x) for all x,y \in X.

Axiom AnaRvf100. Let X be an object and f be a binary function on X that is realvalued. f is
subadditive on X iff f(x,z) \leq f(x,y) + f(y,z) for all x,y,z \in X.

Axiom AnaRvf105. Let X be an object and f be a binary function on X such that f is nonnegative and
realvalued. f is positive definite on X iff for all x,y \in X we have f(x,y) = 0 iff x = y.

# Issue: We cannot write "... and f be a binary function on X that is nonnegative and realvalued".
