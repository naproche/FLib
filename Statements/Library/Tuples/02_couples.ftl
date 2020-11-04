# 2 Couples

[read FLib/Statements/Library/Tuples/01_tuples.ftl]


Let a couple        stand for a tuple of length 2.
Let a double        stand for a tuple of length 2.
Let an ordered pair stand for a tuple of length 2.
Let a duad          stand for a tuple of length 2.
Let a twin          stand for a tuple of length 2.
Let a dual          stand for a tuple of length 2.


Axiom TU0201. Let x1,x2 be objects. (x1,x2) is a couple.


Axiom TU0202. Let x1,x2 be objects. x1 is the first entry of (x1,x2).

Axiom TU0203. Let x1,x2 be objects. x2 is the second entry of (x1,x2).


# 2.1 Basic properties

Lemma TU0204. Let t be a couple. Then t = (x1,x2) for some objects x1,x2.

Proof.
  Take x1 = t[1] and x2 = t[2]. t[1] is the first entry of (x1,x2) and t[2] is
  the second entry of (x1,x2). Hence t[x] = (x1,x2)[x] for all elements x of
  \{1, \ldots, 2\}. Thus t = (x1,x2) (by TU0105). Indeed (x1,x2) is a couple and
  2 is a natural number.
qed.


Lemma TU0205. Let x1,x2,y1,y2 be objects. If (x1,x2) = (y1,y2) then x1 = y1 and
x2 = y2.


Lemma TU0206. Let x1,x2 be objects. {x | x is an entry of (x1,x2)} = {x1,x2}.

Proof.
  We have Dom((x1,x2)) = {1,2}. x1 is the first entry of (x1,x2) and x2 is the
  second entry of (x1,x2).

  For all entries x of (x1,x2) we have x = x1 or x = x2.
  proof.
    Let x be an entry of (x1,x2). Then x is the first entry of (x1,x2) or x is
    the second entry of (x1,x2) (by TU0104). Indeed (x1,x2) is a tuple.
  end.
qed.


# 2.2 The 2nd power of sets

Proposition TU0207. Let X be a set. X^{2} = {(x1,x2) | x1,x2 are elements of X}.

Proof.
  We have X^{2} = {t | t is a tuple of length 2 such that every entry of t is an
  element of X} (by TU0110). Indeed 2 is a natural number that is greater than
  1.

  For all elements t of X^{2} there exist elements x1,x2 of X such that
  t = (x1,x2).
  proof.
    Let t be an element of X^{2}. Then t is a tuple of length 2 such that every
    entry of t is an element of X. Take objects x1,x2 such that t = (x1,x2).
    x1 and x2 are entries of t. Hence x1 and x2 are elements of X.
  end.

  (x1,x2) is an element of X^{2} for all elements x1,x2 of X.
  proof.
    Let x1,x2 be elements of X. Take t = (x1,x2). t is a tuple of length 2.
  end.
qed.
