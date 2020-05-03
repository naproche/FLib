[read ramsey/sets.ftl]
[read ramsey/numbers.ftl]
[read ramsey/utils.ftl]
[read ramsey/functions.ftl]

Let A,B,C,D,P,Q,R,S,T denote sets.
Let x,y,z denote elements.
Let i,j,k,l,m,n denote natural numbers.
Let F,G denote functions.

[quit]

#
# Finite Ramsey Theorem
#

Theorem RamseyFin. Let T be a finite set. Let k,l be natural numbers.
    Then there exists a natural number n such that for every (c : [[n]/k] -> T)
        there exists an element u of T and an element X of [[n]/l]
            such that for every (Q << [X/k]) c(Q) = u.
Proof.
[prove off]
    Choose a set Z such that
        (for every (X << [NAT/l]) [X/k] belongs to Z)
        and (for every (E << Z) E = [X/k] for some (X << [NAT/l])).
#[/prove]

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

