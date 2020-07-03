#
# Real functions
# (Marcel Schütz, 2020)
#

#[prove off][check off]
[read FLib/Structures/RealNumbers/real-valued-functions.ftl]
#[prove on][check on]


# 1. Definition

Definition AnaRf000. Let f be a function. f is real iff f is realvalued and dom(f) is a subset of
REAL.


Lemma AnaRf005. Let f be a real function. Let x \in dom(f). Then f(x) is a real number.

Proof.
  f is realvalued. f(x) is a value of f.
qed.


# 2. Monotonic functions

Axiom AnaRf010. Let f be a real function. f is monotonically increasing iff for all x,y \in dom(f)
if x < y then f(x) \leq f(y).

Axiom AnaRf015. Let f be a real function. f is monotonically decreasing iff for all x,y \in dom(f)
if x < y then f(x) \geq f(y).

Axiom AnaRf020. Let f be a real function. f is strictly monotonically increasing iff for all
x,y \in dom(f) if x < y then f(x) < f(y).

Axiom AnaRf025. Let f be a real function. f is strictly monotonically decreasing iff for all
x,y \in dom(f) if x < y then f(x) > f(y).

Axiom AnaRf030. Let f be a real function. f is monotonic iff f is monotonically increasing or f is
monotonically decreasing.

Axiom AnaRf035. Let f be a real function. f is strictly monotonic iff f is strictly monotonically
increasing or f is strictly monotonically decreasing.


Proposition AnaRf040. Let f be a real function. If f is strictly monotonic then f is injective.

Proof.
  Assume that f is strictly monotonic. Let x,y \in dom(f). Assume that f(x) = f(y). f(x) and f(y)
  are real numbers.

  Case x = y. Trivial.

  Case x < y.
    Case f is strictly monotonically increasing.
      Then f(x) < f(y) (by AnaRf020). Hence f(x) \neq f(y).
    end.

    Case f is strictly monotonically decreasing.
      Then f(x) > f(y) (by AnaRf025). Hence f(x) \neq f(y).
    end.
  end.

  Case x > y.
    Case f is strictly monotonically increasing.
      Then f(x) > f(y) (by AnaRf020). Hence f(x) \neq f(y).
    end.

    Case f is strictly monotonically decreasing.
      Then f(x) < f(y) (by AnaRf025). Hence f(x) \neq f(y).
    end.
  end.

  x < y or x = y or x > y.
  proof.
    x,y \in dom(f). dom(f) \subseteq REAL. Hence x,y \in REAL. Thus x and y are real numbers.
  end.
qed.


# 3. Continuous functions

Axiom AnaRf045. Let f be a real function and a \in dom(f). f is continuous at a iff for all positive
real numbers epsilon there is a positive real number delta such that for all x \in dom(f) if
|a - x| < delta then |f(a) - f(x)| < epsilon.

Axiom AnaRf050. Let f be a real function. f is continuous iff f is continuous at every element of
dom(f).


Proposition AnaRf055. Let f be a continuous real function. f is strictly monotonic iff f is
injective.

Proof. [prove off] qed.


Proposition AnaRf060. Let f be a real function. f is continuous iff f^{-1}[U] is open in dom(f) for
all sets U that are open in REAL.

Proof. [prove off] qed.


Proposition AnaRf065. Every constant real function is continuous.

Proof. [prove off] qed.


Proposition AnaRf070. Let f be a continuous real function. Then -f is continuous.

Proof. [prove off] qed.


Proposition AnaRf075. Let f be a continuous real function. Then |f| is continuous.

Proof. [prove off] qed.


Proposition AnaRf080. Let f,g be continuous real functions such that dom(f) = dom(g). Then f + g is
continuous.

Proof. [prove off] qed.


Proposition AnaRf085. Let f,g be continuous real functions such that dom(f) = dom(g). Then f - g is
continuous.

Proof. [prove off] qed.


Proposition AnaRf090. Let f,g be continuous real functions such that dom(f) = dom(g). Then f \cdot g
is continuous.

Proof. [prove off] qed.


Proposition AnaRf095. Let f,g be continuous real functions such that dom(f) = dom(g). Assume that g
has no zeroes. Then f / g is continuous.

Proof. [prove off] qed.


Proposition AnaRf100. Let f,g be continuous real functions such that codom(f) \subseteq dom(g). Then
f \circ g is continuous.

Proof. [prove off] qed.
