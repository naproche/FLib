[synonym set/-s] [synonym element/-s] 
[synonym belong/-s] [synonym subset/-s]

Signature ElmSort.  An element is a notion.

Let A,B,C,D,P,Q,R,S,T denote sets.
Let x,y,z denote elements.

Axiom.  Let x be an element of S. Then x is an element.

Let x belongs to S stand for x is an element of S.

[synonym magma/magmas] [synonym group/groups]

Signature. A magma is a notion. Let M,N stand for magmas.
Signature. dom M is a set. 
Let the domain of M stand for dom M.

Let x << M stand for x is an element of dom M.

Signature. 0(M) is an element of dom M.
Signature. Let x,y << M. x +(M) y is an element of dom M.
Signature. Let x << M. -(M) x is an element of dom M.

Definition. M is associative iff
for every x,y,z << M (x +(M) y) +(M) z = x +(M) (y +(M) z).

Definition. M is unitive iff for every x << M 0(M) +(M) x = x.

Definition. M is invertive iff for every x << M  -(M) x +(M) x = 0(M).

Definition. A group is an associative unitive invertive magma.
Let G,H stand for groups.

Lemma. -(G) -(G) 0(G) = 0(G).

Lemma. Let a,b << G and a +(G) b = a. Then b = 0(G).

Lemma. Let a,b << G and a +(G) b = b. Then a = 0(G).

 







