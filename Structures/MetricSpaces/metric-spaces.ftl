#
# Metric spaces
# (Marcel Schütz, 2020)
#

#[prove off][check off]
[read ForTheLib/Foundations/structures.ftl]
[read ForTheLib/RealNumbers/real-valued-functions.ftl]
#[prove on][check on]


# 1. Metrics

Lemma MetMs000. Let X be a set and d be a function on X \times X. Then for all x,y \in X we have
(x,y) \in dom(d).


Signature MetMs005. Met1 is an axiom.

Axiom MetMs010. Let X be a set and d be a function on X \times X. (X,d) satisfies Met1 iff
d is realvalued and nonnegative.


Signature MetMs015. Met2 is an axiom.

Axiom MetMs020. Let X be a set and d be a function on X \times X. (X,d) satisfies Met2 iff
for all x,y \in X we have d(x,y) = 0 iff x = y.


Signature MetMs025. Met3 is an axiom.

Axiom MetMs030. Let X be a set and d be a function on X \times X. (X,d) satisfies Met3 iff
for all x,y \in X we have d(x,y) = d(y,x).


Signature MetMs035. Met4 is an axiom.

Axiom MetMs040. Let X be a set and d be a function on X \times X. (X,d) satisfies Met4 iff
for all x,y,z \in X we have d(x,z) \leq d(x,y) + d(y,z).


Definition MetMs045. Let X be a set. A metric on X is a function d on X \times X such that

  (X,d) satisfies Met1 and

  (X,d) satisfies Met2 and

  (X,d) satisfies Met3 and

  (X,d) satisfies Met4.


# 2. Metric spaces

Signature MetMs050. MET is a class.

Definition MetMs055. A metric space is an element of MET.


Axiom MetMs060. Every metric spaces is a structure.

Lemma MetMs065. Every metric space is a map.

Lemma MetMs067. Every metric space is a class.


Signature MetMs070. Let x,y be elements of some metric space. dist(x,y) is an entity.


# 3. Constructing metric spaces

Axiom MetMs075. MET_{1} is a class such that MET_{1} = {(X,d) | X is a set and d is a metric on X}.

Signature MetMs080. Met_{1} is a bijection between MET_{1} and MET.

Axiom MetMs085. Let X be a set and d be a metric on X. Then dom(Met_{1}(X,d)) = X.


Lemma MetMs090. Let X be a set and d be a metric on X. Then Met_{1}(X,d) is a metric space.

Proof.
  (X,d) lies in the domain of Met_{1}. The codomain of Met_{1} is MET. Hence Met_{1}(X,d) lies in
  MET. Thus Met_{1}(X,d) lies in MET. Every element of MET is a metric spaces. Therefore we have the
  thesis.
qed.


Lemma MetMs095. Let X be a set and d be a metric on X. Let x be an element of X. Then
Met_{1}(X,d)(x) is an element of Met_{1}(X,d).

Proof.
  Met_{1}(X,d) is a metric space such that X is the domain of Met_{1}(X,d). Hence x lies in the
  domain of Met_{1}(X,d). Then we have the thesis.
qed.


Axiom MetMs100. Let X be a set and d be a metric on X. Then for all x,y \in X we have
dist(Met_{1}(X,d)(x),Met_{1}(X,d)(y)) = d(x,y).


# 4. Basic properties of metric spaces

Proposition MetMs105. Let M be a metric space. Then M = Met_{1}(X,d) for some set X and some metric
d on X.

Proof.
  M lies in the range of Met_{1}. Met_{1} is a surjective map. Hence we can take an element A of the
  domain of Met_{1} such that Met_{1}(A) = M.

  (1) Then A lies in MET_{1}.

  Hence the thesis (by MetMs075, 1).
qed.


Proposition MetMs110. Every metric space is a set.

Proof.
  Let M be a metric space. We can take a set X and a metric d on X such that M = Met_{1}(X,d). Then
  X is the domain of M. 
qed.


Proposition MetMs120. Let M be a metric space and x,y \in M. Let X be a set and d be a metric on X
such that M = Met_{1}(X,d). Then there are a,b \in X such that x = M(a) and y = M(b) and
dist(x,y) = d(a,b).

Proof.
  We can take a,b \in X such that x = M(a) and y = M(b). Indeed M is a bijection between X and the
  range of M. Then we have the thesis (by MetMs100).
qed.


Proposition MetMs125. Let M be a metric space and x,y \in M. dist(x,y) is a real number.

Proof.
  Take a set X and a metric d on X such that M = Met_{1}(X,d). Take a,b \in X such that
  dist(x,y) = d(a,b) (by MetMs120). X is a set and d is a function on X \times X such that (X,d)
  satisfies Met1. Hence d is realvalued (by MetMs010). Thus d(a,b) is a real number. Indeed
  (a,b) \in dom(d) (by MetMs000).
qed.


Proposition MetMs130. Let M be a metric space and x,y \in M. dist(x,y) \geq 0.

Proof.
  Take a set X and a metric d on X such that M = Met_{1}(X,d). Take a,b \in X such that
  dist(x,y) = d(a,b) (by MetMs120). (X,d) satisfies Met1. d is a function on X \times X. Hence d is
  nonnegative and realvalued (by MetMs010). (a,b) \in dom(d) (by MetMs000). Thus d(a,b) \geq 0 (by
  AnaRvf088, TecSig015). Indeed d is a function and 0 is a real number.
qed.


Proposition MetMs135. Let M be a metric space and x,y \in M. dist(x,y) = 0 iff x = y.

Proof.
  Take a set X and a metric d on X such that M = Met_{1}(X,d). Take a,b \in X such that x = M(a) and
  y = M(b) and dist(x,y) = d(a,b) (by MetMs120). (X,d) satisfies Met2. Hence d(a,b) = 0 iff a = b
  (by MetMs020). Indeed d is a function on X \times X. Then dist(x,y) = 0 iff d(a,b) = 0. Hence
  dist(x,y) = 0 iff a = b. a = b iff M(a) = M(b) (by FoundMap092). Indeed M is an injective map and
  a,b lie in the domain of M. Thus we have the thesis.
qed.


Proposition MetMs137. Let M be a metric space and x,y \in M. Assume that x \neq y. Then
dist(x,y) > 0.

Proof.
  dist(x,y) \geq 0 (by MetMs130). dist(x,y) \neq 0 (by MetMs135).
qed.


Proposition MetMs140. Let M be a metric space and x,y \in M. dist(x,y) = dist(y,x).

Proof.
  Take a set X and a metric d on X such that M = Met_{1}(X,d). Take a,b \in X such that x = M(a) and
  y = M(b) and dist(x,y) = d(a,b) (by MetMs120). (X,d) satisfies Met3. Hence d(a,b) = d(b,a) (by
  MetMs030). Indeed d is a function on X \times X. Hence dist(x,y) = dist(M(b),M(a)) = dist(y,x) (by
  MetMs100).
qed.


Proposition MetMs145. Let M be a metric space and x,y,z \in M. dist(x,z) \leq dist(x,y) + dist(y,z).

Proof.
  Take a set X and a metric d on X such that M = Met_{1}(X,d). Take a,b \in X such that x = M(a) and
  y = M(b) and dist(x,y) = d(a,b) (by MetMs120). Take B,c \in X such that y = M(B) and z = M(c)
  and dist(y,z) = d(B,c) (by MetMs120). Then b = B (by FoundMap092). Indeed M is an injective map
  and b,B \in dom(M) and M(b) = M(B). Hence dist(y,z) = d(b,c). dist(x,z) = dist(M(a),M(c)) = d(a,c)
  (by MetMs100).
  (X,d) satisfies Met4. Thus d(a,c) \leq d(a,b) + d(b,c) (by MetMs040). Indeed d is a function on
  X \times X. Then we have the thesis.
qed.
