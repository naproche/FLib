[read ramsey/sets.ftl]
[read ramsey/numbers.ftl]

Let A,B,C,D,P,Q,R,S,T denote sets.
Let x,y,z denote elements.
Let i,j,k,l,m,n denote natural numbers.

#
#  Cardinality
#

Signature CardS.    |S| is an element.
Axiom CardNum.      |S| << NAT iff S is finite.
Axiom CardEmpty.    |S| = 0 iff S is empty.

Axiom CardCons.  Let S be finite set.
                 If x does not belong to S then |S + x| = succ |S|.

Lemma CardDiff.  Let S be finite and x belong to S.
                 Then succ |S - x| = |S|.
#Indeed |(S - x) + x| = succ |S - x|.

Axiom CardSub.   Let S be finite and T [= S.
                 Then |T| <= |S|.

Axiom CardSubEx. Let S be finite and k <= |S|.
                 Then there exists T [= S such that |T| = k.

#
#  min and max
#

Definition DefMin.  Let S be a nonempty subset of NAT.
    min S is an element z of S such that for all (x << S) z <= x.

Definition DefMax.  Let S be a nonempty finite subset of NAT.
    max S is an element z of S such that for all (x << S) x <= z.

Lemma MinMin.       Let S,T be nonempty subsets of NAT.
    Assume min S << T and min T << S. Then min S = min T.

Let cdr S stand for S - min S.

#
#  [n] = { 0, 1, ..., n-1 }
#

Definition DefSeg.  [n] = { i << NAT | succ i <= n }.

Axiom SegFin.       [n] is finite.

Lemma SegZero.      [0] = {}.

Lemma SegSucc.      m << [succ n]  <=>  m << [n] \/ m = n.

Lemma SegLess.      m <= n  <=>  [m] [= [n].

Lemma FinSubSeg.    Let S be a finite subset of NAT.
                    For some (k << NAT) S [= [k].
Indeed if S is nonempty then S [= [succ max S].

Axiom CardSeg.      |[k]| = k.

#
#  [ S / k ] = { T | T [= S /\ |T| = k }
#

Definition DefSel.  [S/k] = { T [= S | |T| = k }.

Axiom SelFSet.  For any finite S and any k  [S/k] is finite.
Axiom SelNSet.  For any infinite S and any k  [S/k] is nonempty.
Axiom SelCSet.  For any countable S and any nonzero k  [S/k] is countable.

Lemma SelSub.   Let S,T be sets and k be nonzero.
    Assume [S/k] is a nonempty subset of [T/k].
    Then S is a subset of T.
Proof.
    Let x belong to S.

    Take Q << [S/k].
    Q is a finite set and |Q| = k.
    Choose an element y in Q.
        Indeed Q is nonempty.

    Case x << Q. Obvious.

    Case not x << Q.
        Take P = (Q - y) + x.
        Let us show that P belongs to [S/k].
            x does not belong to Q - y and succ |Q - y| = k.
            Hence P [= S and |P| = k.
        end.
        Hence the thesis.
    end.
qed.

Axiom SelExtra. For every finite subset X of [S/k]
    there exists a finite T [= S such that X [= [T/k].

