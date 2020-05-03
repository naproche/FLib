[read ramsey/sets.ftl]
[read ramsey/functions.ftl]

Let A,B,C,D,P,Q,R,S,T denote sets.
Let x,y,z denote elements.
Let F,G denote functions.

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

