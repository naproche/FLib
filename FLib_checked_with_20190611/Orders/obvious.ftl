[synonym element/-s] [synonym relation/-s]

Signature ElmSort.  An element is a notion.
Signature RelSort.  A relation is a notion.

Let x,y,z denote an elements.
Let P,Q,R denote relations.

Signature RelApp.       P[x,y] is an atom.

Definition DefSym.      R is symmetric iff
    for all x,y : R[x,y] => R[y,x].

Definition DefTrans.    R is transitive iff
    for all x,y,z : R[x,y] /\ R[y,z] => R[x,z].

Definition DefTotal.    R is total iff for all x,y R[x,y].

Definition DefCompl.    R and Q are complementary iff
    for all x,y : Q[x,y] \/ R[x,y].

Proposition.
    Let R, Q be transitive complementary relations.
    Assume R is symmetric. Then R is total or Q is total.
