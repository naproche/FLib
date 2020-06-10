#
# Mathematical structures
# (Marcel Schütz, 2020)
#

#[prove off]
[read ForTheLib/Foundations/maps.ftl]
#[prove on]


# 1. Axioms for structures

Signature FoundStr000. A structure is a notion.

Signature FoundStr005. Let S be a structure. carr(S) is a class.

Let the carrier of S stand for carr(S).


Axiom FoundStr010. Let X be a structure and x \in carr(X). X(x) is an element of X.

Axiom FoundStr015. Let X be a structure and x,y \in carr(X). If X(x) = X(y) then x = y.

Axiom FoundStr020. Let X be a structure and y \in X. There is an element x of the carrier of X such
that X(x) = y.

Axiom FoundStr025. Let X be a structure and A be a class. X[A] is a class such that X[A] =
{X(a) | a \in A \cap carr(X)}.

Axiom FoundStr030. Let X be a structure. range(X) is a class such that range(X) = {X(x) | x lies in
the carrier of X}.

#Axiom FoundStr032. Let x be an object and X,Y be structures. If x is an element of X and x is an
#element of Y then X = Y.


Proposition FoundStr033. Let X be a structure. range(X) = {x | x \in X}.


# 2. Small and large structures

Axiom FoundStr035. Let X be a structure. X is small iff the carrier of X is a set.

Axiom FoundStr036. Let X be a structure. X is large iff the carrier of X is a proper class.


Axiom FoundStr040. Every element of any small structure is an element.


Proposition FoundStr045. Let X be a small structure. Then the range of X is a subset of X.

Proof.
  Define iota(x) = X(x) for x in carr(X).

  range(X) = range(iota).
  proof.
    range(iota) = {iota(x) | x lies in the carrier of X}. For all elements x of the carrier
    of X we have iota(x) \in X. Hence range(iota) \subseteq range(X) (by FoundCl000). Indeed
    range(X) is a class such that every element of range(iota) lies in range(X).

    For all y \in X there is an element x of the carrier of X such that y = iota(x). Hence every
    element of range(X) lies in the range of iota. Thus range(X) \subseteq range(iota) (by
    FoundCl005). Indeed range(X) is a class such that every element of range(X) lies in range(iota).

    Then we have the thesis (by FoundCl020). Indeed range(iota) and range(X) are classes.
  end.

  range(iota) = iota[dom(iota)] (by FoundFun120). Indeed iota is a function. The
  domain of iota is the carrier of X. Take a set A such that A = dom(iota). If every value
  of iota is an element then iota[A] is a set (by SetSet060). Indeed iota is a function
  such that A \subseteq dom(iota).
qed.


# 3. Maps between structures

Axiom FoundStr047. Let X be a structure and f be a map such that dom(f) = X. Let x be an element of
the carrier of X. Then f(x) = f(X(x)).


# 4. Operations on classes and structures

Axiom FoundStr050. Let X be a structure and A be an object. X \setminus A is a class such that
X \setminus A = {x in X | x \notin A}.


Proposition FoundStr055. Let X be a structure and A be a subcollection of X. Then
X \setminus (X \setminus A) = A.

Proof. [prove off] qed.


Proposition FoundStr060. Let X be a small structure and A be an object. Then X \setminus A is a
subset of X.

Proof. [prove off] qed.
