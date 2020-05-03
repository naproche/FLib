#
# Preliminary notions from naive set theory
#

[a set/sets] [an element/elements] 
[an element/elements of A]
[x belongs/belong to A @ x is an element of A]
[x is in A @ x belongs to A] [x << A @ x is in A]
[the empty set] [A is empty @ A is the empty set]
[A is nonempty @ A is not empty] [{} @ the empty set]
[A is finite] [A is infinite @ A is not finite]
[A is countable]

Signature SetSort.  Set is a notion.
Signature ElmSort.  Element is a notion.

Let A,B,C,S,T denote sets.
Let x,y,z denote elements.

Signature FinRel.   A is finite is a relation.
Signature CntRel.   A is countable is a relation.
Signature EOfElem.  An element of A is an element.

Definition DefEmp.  {} is a set that has no elements.
Axiom EmpFin.       {} is finite.

Axiom CountNFin.    Every countable set is infinite.
Lemma CountNFin.    Every countable set is nonempty.


[a subset/subsets of A] [A [= B @ A is a subset of B]

Definition DefSub.  A subset of A is a set B such that 
                    all elements of B belong to A.

Axiom SubFSet.      Every subset of every finite set is finite.

Lemma SubRefl.      A [= A.
Axiom SubASymm.     If A [= B and B [= A then A = B.
Lemma SubTrans.     If A [= B and B [= C then A [= C.

#
# adding and removing an element
#

[the cons of S and x] [S + x @ the cons of S and x]
[the diff of S and x] [S - x @ the diff of S and x]

Definition DefCons.
    S + x = { element y | y << S or y = x }.

Definition DefDiff.
    S - x = { element y | y << S and y != x }.

Lemma ConsDiff. Let x belong to S. (S - x) + x = S.
Proof. (S - x) + x [= S and S [= (S - x) + x. end.

Lemma DiffCons. Let x do not belong to S. (S + x) - x = S.
Proof. (S + x) - x [= S and S [= (S + x) - x. end.

Axiom CConsSet. The cons of any countable set and any element is countable.
Axiom CDiffSet. The diff of any countable set and any element is countable.
Axiom FConsSet. The cons of any finite set and any element is finite.
Axiom FDiffSet. The diff of any finite set and any element is finite.

#
# Preliminary notions about functions
#
[a function/functions] [the domain of F] [Dom F @ the domain of F]
[a function from D @ a function F such that Dom F = D]
[F : D @ F is a function from D] 

[the image of x wrt F] [F ( x ) @ the image of x wrt F]
[the prototype of x wrt F] [F [ x ] @ the prototype of x wrt F]
[the set image of x wrt F] [ F { x } @ the set image of x wrt F]
[the restriction of F onto S] [F ! S @ the restriction of F onto S]

[the range of F @ F{Dom F}] [Ran F @ the range of F]
[a function from D to R @ a function F such that Dom F = D and Ran F = R]
[F : D -> R @ F is a function from D to R ]

Signature FunSort.  Function is a notion.

Let F denote functions.

Signature DomSet.   Dom F is a set.
Signature ImgElm.   Let x << Dom F. F(x) is an element.
Definition DefPtt.  F[y] = { x << Dom F | F(x) = y }.

Lemma PttSet.       F[y] [= Dom F.

Definition DefSImg. Let X [= Dom F. F{X} = { F(x) | x << X }.

Lemma ImgRng.       Let x << Dom F. F(x) belongs to Ran F.

Definition DefRst.  Let X [= Dom F.
    F ! X is a function from X such that
        for every (x << X) (F!X)(x) = F(x).

Axiom ImgCount.     Let S be a countable subset of Dom F.
                    Let for all nonequal (i,j << Dom F) F(i) != F(j). 
                    F{S} is countable.

[the dirichlet value of F] [Dir F @ the dirichlet value of F]

Signature Dirichlet.
    Let F have the countable domain and the finite range.
    Dir F is an element with the countable prototype wrt F.

#
# Preliminary notions about natural numbers
#

[the omega] [NAT @ the omega]
[a natural number/numbers @ an element of NAT]
[the zero] [0 @ the zero] [x is nonzero @ x != 0]
[the successor of x] [succ x @ the successor of x]

Signature NATSet.   NAT is a countable set.
Let i,j,k,l,m,n denote natural numbers.

Signature ZeroNum.  0 is a natural number.
Signature SuccNum.  The successor of n is a nonzero natural number.

Axiom SuccEquSucc.  If succ n = succ m then n = m.
Axiom NatExtra.     n = 0 or n = succ m for some m.
Axiom NatNSucc.     n != succ n.


[x is lesseq than y] [x <= y @ x is lesseq than y]

Signature LessRel.  n <= m is a relation.

Axiom ZeroLess.     0 <= n.
Axiom NoScLessZr.   For no n (succ n <= 0).
Axiom SuccLess.     n <= m  <=>  succ n <= succ m.
Axiom LessSucc.     n <= succ n.

Axiom LessRefl.     i <= i.
Axiom LessASymm.    i <= j /\ j <= i  =>  i = j.
Axiom LessTrans.    i <= j /\ j <= k  =>  i <= k.
Axiom LessTotal.    i <= j \/ succ j <= i.

#
# Proof by induction in ForTheL are based on a predefined binary
# predicate symbol (-<-) considered to be a well-founded ordering.
# We give concrete axioms for (-<-) to simulate natural induction.
#

Signature IHSort.   n -<- m is a relation.
Axiom IH.           n -<- succ n.


[the minimal element of S] [min S @ the minimal element of S]
[the maximal element of S] [max S @ the maximal element of S]
[cdr S @ S - min S]

Definition DefMin.  Let S be a nonempty subset of NAT.
    min S is an element of S such that for all (x << S) min S <= x.

Lemma MinMin.       Let S,T be nonempty subsets of NAT.
    Assume min S << T and min T << S. Then min S = min T.

Definition DefMax.  Let S be a nonempty finite subset of NAT.
    max S is an element of S such that for all (x << S) x <= max S.

#Lemma MinNum.
#    The minimal element of every nonempty subset of NAT is a natural number.

#Lemma MaxNum.
#    The maximal element of every nonempty finite subset of NAT is a natural number.


[the cardinality of x] [|x| @ the cardinality of x]

Signature CardS.    |S| is an element.
Axiom CardNum.      |S| << NAT iff S is finite.
Axiom CardEmpty.    |S| = 0 iff S is empty.

Axiom CardCons.  Let S be finite set.
                 If x does not belong to S then |S + x| = succ |S|.

Lemma CardDiff.  Let S be finite and x belong to S.
                 succ |S - x| = |S|.
Proof.
    |(S - x) + x| = succ |S - x|.
qed.

Axiom CardSub.   Let S be finite and T [= S.
                 Then |T| <= |S|.

Axiom CardSubEx. Let S be finite and k <= |S|.
                 Then there exists T [= S such that |T| = k.

#
# [x] = { 0, ..., x - 1 }
#

[the segment up to x] [[x] @ the segment up to x]

Definition DefSeg.  [n] = { i << NAT | succ i <= n }.
Axiom SegFin.       [n] is finite.

#Lemma _SegFin.  For every (t << NAT) [t] is a finite subset of NAT.
#Lemma _SegNum.  For every (t << NAT) all elements of [t] are natural numbers.

Lemma SegZero.  [0] = {}.

Lemma SegSucc.  m << [succ n]  <=>  m << [n] \/ m = n.
#Proof.
#    If m << [succ n] then succ m <= n or m = n.
#    Suppose m << [n]. We have succ m <= n.
#    Hence succ m <= succ n. # (by LessSucc,LessTrans).
#qed.

Lemma SegLess.  m <= n  <=>  [m] [= [n].
#Proof.
#    If [m] [= [n] then n does not belong to [m]. Assume m <= n.
#    Every element of [m] belongs to [n] (by DefSeg,LessTrans).
#    Hence [m] [= [n] (by DefSubB).
#qed.

Lemma FinSubSeg.    Let S be a finite subset of NAT.
                    For some (k << NAT) S [= [k].
Proof.
    If S is nonempty then S [= [succ max S].
end.

Axiom CardSeg.      |[k]| = k.

#
#  [ S / k ] = { T | T [= S /\ |T| = k }
#

[the selection of k from S] [ [S/k] @ the selection of k from S]

Definition DefSel.  [S/k] = { T [= S | |T| = k }.

Axiom SelFSet.  For any finite S and any k  [S/k] is finite.
Axiom SelNSet.  For any infinite S and any k  [S/k] is nonempty.
Axiom SelCSet.  For any countable S and any nonzero k  [S/k] is countable.

Lemma SelSub.   Let S,T be sets and k be nonzero.
    Assume [S/k] is a nonempty subset of [T/k].
    Then S is a subset of T.
Proof.
    Let x belong to S.
    Choose Q << [S/k]. 
    Q is a finite set and |Q| = k.
    Choose an element y in Q.
    Indeed Q is nonempty. end.
    Case x << Q. Obvious.
    Case not x << Q.
        Take P = (Q - y) + x.
        P belongs to [S/k].
        Indeed
            x does not belong to Q - y and succ |Q - y| = k. 
            Hence P is a subset of S and |P| = k.
        end.
        Hence the thesis.
    end.
qed.

Axiom SelExtra. For every finite subset X of [S/k]
    there exists a finite T [= S such that X [= [T/k].


#
# Infinite Ramsey Theorem
#

Theorem RamseyInf. Let T be a finite set.
    For every (K << NAT) and every countable (S [= NAT) and every (c : [S/K] -> T)
        there exists an element u of T and a countable X [= S such that
            for every (Q << [X/K]) c(Q) = u.
Proof by induction.

    Let K be a natural number.
    Let S be a countable subset of NAT.
    Let c : [S/K] -> T.

    Case K = 0. # (by SubRefl).
        The empty set belongs to [S/0].
        For all (Q << [S/0]) c(Q) = c({}).
    end.

    Case K != 0. # (by _).
        Take a natural number k so that K = succ k.
#
#  Here we define the structures we are going to use.
#  So far we cannot verify correctness of complex function
#  definitions, so we turn verification off for this block.
#
[none]
        Choose (C : NAT) and (N : NAT).

        N(0) = S.

        For every (i << NAT)  if N(i) is a countable subset of NAT
        then    
                N(succ i) is a countable subset of cdr N(i)
                    such that for some element u of T
                        for every set Q in [N(succ i)/k]  C(i)(Q) = u.

        For every (i << NAT)  if N(i) is a countable subset of NAT
        then    
                C(i) is a function from [cdr N(i) / k] # -> T
                    such that for every set Q in [cdr N(i) / k]
                        C(i)(Q) = c(Q + min N(i)).
#[full]
#
# Here we prove some obvious properties of the above-defined structures
#
        For every i N(i) is a countable subset of NAT.
        proof by induction.
            Let i be a natural number.
            Case i = 0. Obvious.
            Case i != 0.
                Take m << NAT such that i = succ m.
                N(m) is a countable subset of NAT.
            end.
        end.

#        For every (i << NAT) N(i) is a set. # UGLY!!!!

        For every i,j if j <= i then N(i) [= N(j).
        proof by induction.
            Let i,j be natural numbers so that j <= i.
            Let m be a natural number so that i = succ m.
            Case i <= j. Obvious.
            Case j <= m.
                We have N(m) [= N(j).
                Hence N(i) [= N(j). # (by SubTrans).
            end.
        end.

        For all nonequal (i,j << NAT) min N(i) != min N(j).
        proof.
            Let i,j be nonequal natural numbers.
            We have succ j <= i or succ i <= j.
            Let x,y be natural numbers such that succ y <= x.
            Then N(x) [= N(succ y) and N(x) [= cdr N(y). # (by SubTrans).
            Then min N(x) != min N(y).
        end.
#
# Now, the main sequence N(i) being introduced and investigated,
# we construct a countable subset of S which we need for the step.
#
[none]
        Choose (e : NAT) and (d : NAT).

        For every (i << NAT) e(i) = min N(i).

        For every (i << NAT) and some set Q in [N(succ i)/k]
            d(i) = c(Q + min N(i)).
#[full]
#
# And here the proof of the theorem begins
#
        Let us show that Ran d [= T.
            Let i be a natural number.
[tlim 3]
            Take a set Q such that Q << [N(succ i)/k] and d(i) = c(Q + min N(i)) (by _).
[tlim 1]
            Q is a finite subset of N(succ i) and |Q| = k.
            Take a set P equal to Q + min N(i).
            P is a subset of S (by _).
            Indeed
                Let x belong to P.
                Then x << Q or x = min N(i).
                N(i) [= S and Q [= S.
                Hence x is in S.
            end.
            |P| = K. 
            Indeed
                min N(i) does not belong to N(succ i).
                Hence min N(i) is not in Q.
            end.
            Therefore P << [S/K] and d(i) << T.
        end.

        Therefore Dir d << T and d[Dir d] is countable.
        Indeed
            Dir d is an element and d[Dir d] is nonempty.
            Take x << Dom d such that d(x) = Dir d.
            We have the thesis.
        end.

        e{d[Dir d]} is a countable set (by ImgCount).
        Take a set O equal to e{d[Dir d]}.
        For any element x of O there exists 
            a natural number y such that y << d[Dir d] and e(y) = x.

        Let us prove that O [= S.
            Let x belong to O.
            Take (i << NAT) such that e(i) = x. # (by DefSImg,DefSubF).
            N(i) [= S. Then x << S (by _).
        end.

        Let Q << [O/succ k].
        Show c(Q) = Dir d.

            Q is a nonempty subset of O. Q is a subset of NAT.
            min Q belongs to Q. min Q is a natural number in O.
            cdr Q is a subset of Q. cdr Q is a subset of O.
            |cdr Q| = k.
            Indeed 
                |Q| = succ k and succ |cdr Q| = |Q| and |cdr Q| << NAT. 
            end.
            
            Then cdr Q belongs to [O/k].
            Indeed                              ## UGLY
                Take a set P equal to cdr Q.
                P [= O. |P| = k. P << [O/k].
            end.

            Choose (n << d[Dir d]) such that min Q = e(n). #(by DefSImg).
            n is a natural number. d(n) = Dir d. # (by DefPtt).

            cdr Q [= N(succ n). # (by DefSubB).
            proof.
                Let x belong to cdr Q.
                Then x is a natural number in O. # (by DefSel,SubTrans,DefSubF).
                Choose a natural number m such that x = e(m). # (by DefSImg,DefSubF).
                x = min N(m). Show by case analysis that x << N(succ n).
                Case N(m) [= N(succ n). Obvious. # (by DefMin,DefSubF).
                Case N(n) [= N(m).
                    min Q << N(m). # (by DefMin,DefSubF).
                    x << Q. Then min Q = x (by MinMin).
                    Indeed Q and N(m) are nonempty subsets of NAT. end.
                    Hence min Q << cdr Q and we have a contradiction.
                end. end.
            end.

            Then c(Q) = d(n) (by ConsDiff).
            proof.
                cdr N(n) [= N(n).
                cdr N(n) [= NAT. # (by SubTrans).

[tlim 3]
                N(succ n) [= cdr N(n).
                cdr Q [= cdr N(n). # (by SubTrans).
[tlim 1]
                cdr Q << [cdr N(n) / k].
                Indeed                              ## UGLY
                    Take a set P equal to cdr Q.
                    P [= cdr N(n). |P| = k. 
[none]
                    P << [cdr N(n)/k] (by _).
#[full]
                end.
                Then c(cdr Q + min N(n)) = C(n)(cdr Q) (by _).

                Let P << [(N(succ n))/k].
                P [= cdr N(n). # (by DefSel,SubTrans).
##
                P << [cdr N(n) / k].
                Then c(P + min N(n)) = C(n)(P) (by _).

                cdr Q << [(N(succ n))/k].
                Then C(n)(cdr Q) = C(n)(P) (by _).
            end.
        end.
    end.
qed.

[quit]

[a hypergraph/hypergraphs] [a subgraph/subgraphs of x]
[the vertex set of x] [the hyperedge set of x]
[a vertex/vertice of x @ an element of the vertex set of x]
[an edge/edges of x @ an element of the hyperedge set of x]
[x is monochromatic in h wrt y] [x is chromatic for h]
[Ver H @ the vertex set of H] [Edg H @ the hyperedge set of H]

Axiom _VSSet. The vertex set of every hypergraph is a set.
Axiom _ESSet. The hyperedge set of every hypergraph is a set.
Axiom _ESet.  Every edge of every hypergraph H is a subset of Ver H.

Definition DefMono.
    Let H be a hypergraph and E be an edge of H.
    Let L be a function from Ver H.
    E is monochromatic in H wrt L iff there exists (c << Ran L)
        such that for every (x << E)  L(x) = c.

Definition DefChromC.
    Let H be a hypergraph and L be a function from Ver H with a finite range.
    L is chromatic for H iff H has no edge that is monochromatic in H wrt L.

Definition DefChromT.
    Let H be a hypergraph and T be a finite set.
    T is chromatic for H iff there exists L : Ver H -> T chromatic for H.

Definition DefSubGr.
    Let H be a hypergraph.
    A subgraph of H is a hypergraph J such that
        Ver J [= Ver H and Edg J [= Edg H.

Lemma _SubgrGr.
    Every subgraph of every hypergraph is a hypergraph.

Definition DefFinGr.
    Let H be a hypergraph.
    H is finite iff Ver H is finite.

Definition DefRstGr.
    Let H be a hypergraph and V [= Ver H.
    H ! V is a hypergraph J such that
        Ver J = V and for every edge E of H
            E is an edge of J  iff  E [= V.

Axiom GraphEx.
    Let V be a set and E be a set such that
        every element of E is a subset of V.
    There exists a hypergraph H such that Ver H = V and Edg H = E.

#
# Compactness Principle used to prove Finite Ramsey Theorem
#

Theorem Compactness.
    Assume H is a hypergraph and Ver H = NAT.
    Assume every edge of H is finite.
    Let T be a finite set chromatic for every finite subgraph of H.
    Then T is chromatic for H (by DefChromT).
Proof.
[none]
    Choose (c : NAT), (m : NAT), (C : Ver H -> T), (N : NAT).

[situ]
    For every (i << NAT) c(i) : Ver(H![i]) -> T
        and c(i) is chromatic for H![i].

    For every (i << NAT) m(i) : N(i) -> T
        and for every j << Dom m(i)  m(i)(j) = c(j)(i).

    For every (i << NAT) C(i) = Dir(m(i)).

    N(0) = NAT and for every i << NAT  N(succ i) = m(i)[C(i)] - i.
#[full]

    For every (i << NAT) N(succ i) [= N(i) (by SubTrans).
    Indeed for all (i << NAT) N(succ i) [= m(i)[C(i)] (by DefDiff). end.

    For every (i << NAT) N(i) is a countable subset of NAT.
    proof by induction.
        Let i be a natural number.
        Let k be a natural number such that i = succ k.
        m(k)[C(k)] is a countable subset of N(k) (by IH,Dirichlet).
        N(i) is a countable subset of m(k)[C(k)].
        Hence the thesis (by IH,SubTrans).
    end.

    For every (i << NAT) and every (j << N(i)) i <= j.
    proof by induction.
        Let i be a natural number and j belong to N(i).
        Let k be a natural number such that i = succ k.
        j is a natural number in N(k) (by DefSubF).
        Then k <= j. j != k (by DefDiff).
        Hence i <= j (by LessASymm,LessTotal).
    end.

    For every (i << NAT) and every (j << N(i))
        and every (x << [i])  c(j)(x) = C(x).
    proof by induction.
        Let i be a natural number and j << N(i) and x << [i].
        Let k be a natural number such that i = succ k.
        Case x << [k]. Obvious (by IH,DefSubF).
        Case x = k.
            j belongs to m(k)[C(k)] (by DefDiff,DefSubF).
            c(j)(x) = C(x) (by DefSubF,DefPtt).
        end.
    end.

    Then C is chromatic for H (by DefChromC).
    proof.
        Let E be an edge of H.
        Choose a natural number k such that E [= [k].
        Choose a natural number t that belongs to N(k).
        [k] [= [t]. Then E [= [t] (by SubTrans).

        Let J be H![t] and L = c(t).
        J is a hypergraph and E << Edg J (by DefRstGr).
        L : Ver J -> T and L is chromatic for J.
        Then E is not monochromatic in J wrt L.

        For every x << E  L(x) = C(x) (by DefSubF).
        Then E is not monochromatic in H wrt C (by DefMono).
    end.
end.

[none]
Theorem CompactnessC.
    Assume H is a hypergraph and Ver H is countable.
    Assume every edge of H is finite.
    Let T be a finite set chromatic for every finite subgraph of H.
    Then T is chromatic for H.
#[full]


#
# Finite Ramsey Theorem
#

Theorem RamseyFin. Let T be a finite set. Let k,l be natural numbers.
    Then there exists a natural number n such that for every (c : [[n]/k] -> T)
        there exists an element u of T and an element X of [[n]/l]
            such that for every (Q << [X/k]) c(Q) = u.
Proof.
[none]
    Choose a set Z such that
        (for every (X << [NAT/l]) [X/k] belongs to Z)
        and (for every (E << Z) E = [X/k] for some (X << [NAT/l])).
#[full]

    Every element of Z is a subset of [NAT/k] (by DefSubB,DefSel).
    proof.
        Let E be in Z. E = [X/k] for some (X << [NAT/l]).
        Let Q belong to E. Q is a subset of NAT.
        Hence Q belongs to [NAT/k].
    end.

    Then choose a hypergraph H such that
        Ver H = [NAT/k] and Edg H = Z (by GraphEx).

    NAT [= NAT.

    T is not chromatic for H (by DefChromT).
    proof.
        Let c : [NAT/k] -> T.
        Choose an element u of T and a countable X [= NAT
            such that for every (Q << [X/k]) c(Q) = u (by RamseyInf).
        Choose P << [X/l].
        P is a subset of X. P is a subset of NAT.
        [P/k] is an edge of H (by DefSubF,DefSel).
        [P/k] is monochromatic in H wrt c (by DefMono).
        proof.
            Let Q << [P/k]. Q is a subset of X.
            Then Q << [X/k]. Hence c(Q) = u.
        end.
        Hence c is not chromatic for H (by DefChromC).
    end.

    Case k = 0 (by _).
        [l] belongs to [[l]/l]. {} belongs to [[l]/0].
        Let c : [[l]/0] -> T. Let Q belong to [[l]/0].
        Then c(Q) = c({}) (by DefSel,CardEmpty).
    end.

    Case k != 0 and H has empty edges (by _).
        Choose an empty edge E of H.
        Choose (Y << [NAT/l]) such that E = [Y/k].
        Y is a finite subset of NAT and |Y| = l.
        Let us prove that succ l <= k.
            Assume the contrary. Then k <= l.
            Then take (Q [= Y) such that |Q| = k (by CardSubEx).
            Then Q << [Y/k] (by DefSel).
            We have a contradiction.
        end.
        Then l <= k (by LessSucc,LessTrans).
        |[l]| = l. [l] belongs to [[k]/l].
        Let us show that [[l]/k] is empty.
            Assume the contrary.
            Take Q << [[l]/k].
            Q [= [l] and |Q| = k.
            Then k <= l (by CardSub,DefSel).
            We have a contradiction.
        end.
        [k] belongs to [[k]/k].
        Let c : [[k]/k] -> T.
        For every (Q << [[l]/k]) c(Q) = c([k]).
    end.

    Case k != 0 and no edge of H is empty (by _).
        Ver H is a countable set. Every edge of H is finite.
        Then take a finite subgraph G of H
            such that T is not chromatic for G (by CompactnessC).

        Ver G is a finite subset of [NAT/k].
        Choose a finite S [= NAT such that  Ver G [= [S/k] (by SelExtra).
        Choose a natural number n such that S [= [n].
        Show Ver G [= [[n]/k] (by DefSubB).
            Let Q << Ver G.
            Q << [S/k] (by DefSubF,DefSel).
            Q [= [n] (by DefSel,SubTrans).
            Then Q << [[n]/k].
        end.

        Let c : [[n]/k] -> T.
        (c!Ver G) is not chromatic for G (by DefRst,DefChromT).
        Choose an edge E of G such that
            E is monochromatic in G wrt (c!Ver G) (by DefRst,DefChromC).

        Choose (X << [NAT/l]) such that E = [X/k] (by DefSubF,DefSubGr).
        [X/k] is a subset of [[n]/k]. Then X << [[n]/l] (by DefSel,SelSub).
        For every (Q << E) c(Q) = (c!Ver G)(Q) (by DefRst,DefSubF).
        For some (u << T) and every (Q << E) c(Q) = u (by DefMono,DefRst).
    end.
qed.
