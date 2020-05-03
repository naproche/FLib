[set/-s] [element/-s] [belong/-s] [subset/-s]

Signature SetSort.  A set is a notion.
Signature ElmSort.  An element is a notion.

Let A,B,C,D,P,Q,R,S,T denote sets.
Let x,y,z denote elements.

Signature EOfElem.  An element of S is an element.

Let x belongs to S stand for x is an element of S.
Let x is in S stand for x belongs to S.
Let x << S stand for x is in S.

Signature FinRel.   S is finite is an atom.

Let S is infinite stand for S is not finite.

Definition DefEmp.  {} is a set that has no elements.
Axiom EmpFin.       {} is finite.

Let S is empty stand for S = {}.
Let S is nonempty stand for S != {}.

Signature CntRel.   S is countable is an atom.
Axiom CountNFin.    Every countable set is infinite.
Lemma CountNFin.    Every countable set is nonempty.

Definition DefSub.  A subset of S is a set T such that
                    every element of T belongs to S.

Let A [= B stand for A is a subset of B.

Axiom SubFSet.      Every subset of every finite set is finite.

Lemma SubRefl.      A [= A.
Axiom SubASymm.     A [= B [= A  =>  A = B.
Lemma SubTrans.     A [= B [= C  =>  A [= C.

Definition DefCons.
    S + x = { element y | y << S or y = x }.

Definition DefDiff.
    S - x = { element y | y << S and y != x }.

# we have to write a proof for these simple lemmata,
# in order to be able to apply DefSub.

Lemma ConsDiff. Let x belong to S. (S - x) + x = S.
Indeed S [= (S - x) + x [= S.

Lemma DiffCons. Let x do not belong to S. (S + x) - x = S.
Indeed S [= (S + x) - x [= S.

Axiom CConsSet. For any countable S  (S + x) is countable.
Axiom CDiffSet. For any countable S  (S - x) is countable.
Axiom FConsSet. For any finite S     (S + x) is finite.
Axiom FDiffSet. For any finite S     (S - x) is finite.

