[read linear_algebra_ftl/A_Props/000A_set.ftl]

[synonym function/-s]

Let M, N, A denote sets.
Let f, g denote functions.

Definition.
Let f be a function.
f is injective iff for all elements x,y of Dom(f) we have (f[x] = f[y] => x = y).

Definition.
Let f be a function. Let M,N be sets.
f is from M to N iff Dom(f) = M and for every x << M : f[x] << N.

Let f:M->N stand for (f is a function from M to N).

Axiom FunExt.
Let f,g be functions. If Dom(f) = Dom(g) and for every element x of Dom(f) f[x] = g[x] then f = g.

Signature. Let A be a set. id{A} is a function from A to A.
Axiom. For all a << A we have id{A}[a] = a.

Signature. f|{M} is a function.
Axiom FunRestr. Let f be a function. Let M be subset of Dom(f).
Then Dom(f|{M}) = M and for all x << M we have f|{M}[x] = f[x].

Signature. comp(f,g) is a notion.
Let f*g stand for comp(f,g).
Axiom FunComp. Let f,g be functions such that for all x << Dom(g) we have g[x] << Dom(f).
 Then f*g is a function and Dom(f*g) = Dom(g)
 and for all x << Dom(g) : (f*g)[x] = f[g[x]].
