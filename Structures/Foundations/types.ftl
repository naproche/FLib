#
# Types
# (Marcel Schütz, 2020)
#

#[prove off]
[read ForTheLib/Foundations/functions.ftl]
#[prove on]


# 1. Types

Signature FoundTyp000. A type is a notion.


# 2. Instantiations

Definition FoundTyp005. Let T be a type. An instantiation of T is an injective function of T.

Axiom FoundTyp010. Let f,g be instantiations of some type. f and g are equivalent iff there
exists a bijection h between the range of f and the range of g such that g is the composition of h
and f.


Proposition FoundTyp015. Let f,g be instantiations of some type. f and g are equivalent iff there is
a bijection h between the range of g and the range of f such that f = h \circ g.

Proof.
  If f and g are equivalent then there is a bijection h between the range of g and the range of f
  such that f = h \circ g.
  proof.
    Assume that f and g are equivalent. Take a bijection k between the range of f and the range of
    g such that g = k \circ f (by FoundTy010). k^{-1} is a bijection between the range of g and the
    range of f.

    f = k^{-1} \circ g.
    proof.
      range(g) \subseteq dom(k^{-1}). Hence k^{-1} \circ g is a function (by FoundFun095). Indeed k^{-1}
      is a functions. dom(f) = dom(k^{-1} \circ g). For all x \in dom(f) we have
      f(x) = (k^{-1} \circ g)(x). Hence the thesis (by FoundFun000).
    end.
  end.

  If there is a bijection h between the range of g and the range of f such that f = h \circ g then
  f and g are equivalent.
  proof.
    Assume that there is a bijection h between the range of g and the range of f such that
    f = h \circ g. Take a bijection h between the range of g and the range of f such that
    f = h \circ g. h^{-1} is a bijection between the range of f and the range of g.

    g = h^{-1} \circ f.
    proof. # Analogous to the proof above
      range(f) \subseteq dom(h^{-1}). Hence h^{-1} \circ f is a function (by FoundFun095). Indeed h^{-1}
      is a function. dom(g) = dom(h^{-1} \circ f). For all x \in dom(g) we have
      g(x) = (h^{-1} \circ f)(x). Indeed for all x \in dom(g) we have (h^{-1} \circ f)(x) =
      h^{-1}(f(x)). Hence the thesis (by FoundFun000).
    end.
  end.
qed.


Proposition FoundTyp020. Let f be an instantiation of some type. f and f are equivalent.

Proof.
  Define h(x) = x for x in range(f). h is a bijection between range(f) and range(f). f = h \circ f
  (by FoundFun000). Indeed f and h \circ f are functions such that dom(f) = dom(h \circ f) and for all
  x \in dom(f) we have (h \circ f)(x) = f(x).
qed.


Proposition FoundTyp025. Let f and g be instantiations of some type. If f and g are equivalent then g
and f are equivalent.

Proof.
  Assume that f and g are equivalent. Take a bijection h between the range of f and the range of g
  such that g = h \circ f (by FoundTy010).
qed.


Proposition FoundTyp030. Let f,g,h be instantiations of some type. If f and g are equivalent and g
and h are equivalent then f and h are equivalent.

Proof.
  Assume that f and g are equivalent and g and h are equivalent. Take a bijection k between the
  range of f and the range of g such that g = k \circ f (by FoundTy010). Take a bijection j between
  the range of g and the range of h such that h = j \circ g (by FoundTy010).

  j \circ k is a bijection between the range of f and the range of h.
  proof.
    Take classes x,y,z such that k is a bijection between x and y and j is a bijection between y and
    z. Then j \circ k is a bijection between x and z. x = range(f) and z = range(h).
  end.

  h = (j \circ k) \circ f.
  proof.
    h and (j \circ k) \circ f are functions. dom(h) = dom((j \circ k) \circ f). For all x \in dom(h)
    we have h(x) = ((j \circ k) \circ f)(x). Hence the thesis (by FoundFun000).
  end.
qed.


# 3. Instances

Definition FoundTyp035. Let T be a type. An instance of T is a value of some instantiation of T.

Axiom FoundTyp040. Let T be a type and I be an instantiation of T. Let X be a value of I. Then
X_{I} = I^{-1}(X).

Let the interpretation of X wrt I stand for X_{I}.


# 4. Standard interpretations

