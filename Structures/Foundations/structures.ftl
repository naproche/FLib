#
# Mathematical structures
# (Marcel Schütz, 2020)
#

#[prove off]
[read ForTheLib/Foundations/maps.ftl]
[read ForTheLib/Sets/sets.ftl]
#[prove on]


# 1. Axioms for structures

Signature FoundStr000. A structure is an injective function.

Axiom FoundStr002. Let X be a structure. The domain of X is a class.

Axiom FoundStr005. Let X be a structure and x be an object. x is an element of X iff x lies in the
range of X.


Proposition FoundStr010. Let X be a structure. X is a bijection between the domain of X and the
range of X.


Proposition FoundStr015. Let X be a structure. X^{-1} is a bijection between the range of X and the
domain of X.


Proposition FoundStr020. Let X be a structure and x be an element of the domain of X. Then X(x) is
an element of X.

Proof.
  X(x) lies in the range of X.
qed.


Proposition FoundStr025. Let X be a structure and y be an element of X. Then there is an element x
of the domain of X such that X(x) = y.


Proposition FoundStr030. Let X be a structure and x,y be elements of the domain of X. x = y iff
X(x) = X(y).

Proof.
  X is an injective function.
qed.


Proposition FoundStr031. Let X be a structure and A be a class. X[A] = {X(a) | a \in A and
a \in dom(X)}.

Proof.
  X is a function. Hence we have the thesis (by FoundFun115).
qed.


Proposition FoundStr033. Let X be a structure. range(X) = {x | x \in X}.


# 2. Small and large structures

Axiom FoundStr035. Let X be a structure. X is small iff the domain of X is a set.

Axiom FoundStr036. Let X be a structure. X is large iff the domain of X is a proper class.


Axiom FoundStr040. Every element of any small structure is an element.


Proposition FoundStr045. Let X be a small structure. Then the range of X is a subset of X.

Proof.
  Define iota(x) = X(x) for x in dom(X).

  range(X) = range(iota).
  proof.
    range(iota) = {iota(x) | x lies in the domain of X} (by FoundFun005). For all elements x of the
    domain of X we have iota(x) \in X. Hence range(iota) \subseteq range(X) (by FoundCl000). Indeed
    range(X) is a class such that every element of range(iota) lies in range(X).

    For all y \in X there is an element x of the domain of X such that y = iota(x). Hence every
    element of range(X) lies in the range of iota. Thus range(X) \subseteq range(iota) (by
    FoundCl005). Indeed range(X) is a class such that every element of range(X) lies in range(iota).

    Then we have the thesis (by FoundCl020). Indeed range(iota) and range(X) are classes.
  end.

  range(iota) = iota[dom(iota)] (by FoundFun120). Indeed iota is a function. The
  domain of iota is the domain of X. Take a set A such that A = dom(iota). If every value
  of iota is an element then iota[A] is a set (by SetSet060). Indeed iota is a function
  such that A \subseteq dom(iota).
qed.


# 3. Maps between structures

Axiom FoundStr047. Let X be a structure and f be a map such that dom(f) = X. Let x be an element of
the domain of X. Then f(x) = f(X(x)).


# 4. Operations on classes and structures

Axiom FoundStr050. Let X be a structure and A be an object. X \setminus A is a class such that
X \setminus A = {x in X | x \notin A}.


Proposition FoundStr055. Let X be a structure and A be a subcollection of X. Then
X \setminus (X \setminus A) = A.

Proof. [prove off] qed.


Proposition FoundStr060. Let X be a small structure and A be an object. Then X \setminus A is a
subset of X.

Proof. [prove off] qed.
