[read linear_algebra_ftl/001D_function.ftl]

Let f, g, h denote functions.
Let K, L, M, N denote a set.


Theorem. Let f[x] << M for all x << Dom(f). Then id{M}*f = f.
Proof.
 Let us show that for all x << Dom(f) : (id{M}*f)[x] = f[x].
  Let x << Dom(f).
  Dom(id{M}) = M.
  (id{M}*f)[x] = id{M}[f[x]].
 end.
end.


Theorem. Let Dom(f) = M. Then f*id{M} = f.
Proof.
 Let us show that for all x << M : (f*id{M})[x] = f[x].
  Let x << M.
  Dom(id{M}) = M.
  (f*id{M})[x] = f[id{M}[x]].
 end.
end.


Theorem. Let g:L->M. Let f:M->N. Then f*g : L->N.
Proof.
 Dom(f*g) = L.
end.


Theorem. Let h:K->L. Let g:L->M. Let f:M->N.
Then (f*g)*h : K->N.

Theorem. Let h:K->L. Let g:L->M. Let f:M->N.
Then f*(g*h) : K->N.

Theorem. Let h:K->L. Let g:L->M. Let f:M->N.
Then (f*g)*h = f*(g*h).
Proof.
 Let us show that for all x << K : ((f*g)*h)[x] = (f*(g*h))[x].
  Let x << K.
  ((f*g)*h)[x] = f[g[h[x]]].
  g*h : K->M.
  (g*h)[x] = g[h[x]].
  (f*(g*h))[x] = f[(g*h)[x]].
 end.
end.
