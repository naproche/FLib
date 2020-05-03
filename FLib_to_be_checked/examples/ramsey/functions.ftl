[read ramsey/sets.ftl]

Let A,B,C,D,P,Q,R,S,T denote sets.
Let x,y,z denote elements.

[function/-s]

Signature FunSort.  A function is a notion.

Let F,G denote functions.

Signature DomSet.   Dom F is a set.
Signature ImgElm.   Let x << Dom F. F(x) is an element.
Definition DefPtt.  F[y] = { x << Dom F | F(x) = y }.

Lemma PttSet.       F[y] [= Dom F.

Definition DefSImg. Let X [= Dom F. F{X} = { F(x) | x << X }.

Let Ran F stand for F{Dom F}.

Let a function from D stand for a function F
                    such that Dom F = D.

Let a function from D to R stand for a function F
                    such that Dom F = D and Ran F [= R.

Let F : D stand for F is a function from D.
Let F : D -> R stand for F is a function from D to R.

Lemma ImgRng.       Let x << Dom F. F(x) belongs to Ran F.

Definition DefRst.  Let S [= Dom F. F!S is a function G from S
                    such that for every (x << S) G(x) = F(x).

Axiom ImgCount.     Let S be a countable subset of Dom F.
                    Let for all nonequal (i,j << Dom F) F(i) != F(j).
                    F{S} is countable.

Let the domain of F stand for Dom F.
Let the range of F stand for Ran F.
Let the prototype of x wrt F stand for F[x].

Signature Dirichlet.
    Let F have the countable domain and the finite range.
    Dir F is an element with the countable prototype wrt F.

