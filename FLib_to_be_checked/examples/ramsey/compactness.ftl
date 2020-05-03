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
# Compactness Principle used to prove Finite Ramsey Theorem
#

Theorem Compactness.
    Assume H is a hypergraph and Ver H = NAT.
    Assume every edge of H is finite.
    Let T be a finite set chromatic for every finite subgraph of H.
    Then T is chromatic for H (by DefChromT).
Proof.
[prove off]
    Choose (c : NAT), (m : NAT), (C : Ver H -> T), (N : NAT).

[situ]
    For every (i << NAT) c(i) : Ver(H![i]) -> T
        and c(i) is chromatic for H![i].

    For every (i << NAT) m(i) : N(i) -> T
        and for every j << Dom m(i)  m(i)(j) = c(j)(i).

    For every (i << NAT) C(i) = Dir(m(i)).

    N(0) = NAT and for every i << NAT  N(succ i) = m(i)[C(i)] - i.
#[/prove]

    For every (i << NAT) N(succ i) [= N(i) (by SubTrans).
    proof. for all (i << NAT) N(succ i) [= m(i)[C(i)] (by DefDiff). end.

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

[prove off]
Theorem CompactnessC.
    Assume H is a hypergraph and Ver H is countable.
    Assume every edge of H is finite.
    Let T be a finite set chromatic for every finite subgraph of H.
    Then T is chromatic for H.
#[/prove]

