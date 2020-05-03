[synonym element/-s]

Let M,N,A denote sets.
Let x << M stand for x is an element of M.
Let M is subset of N stand for (for all x << M : x << N).

Definition.
Prod(M,N) = { (x,y) | x << M and y << N }.

Axiom SetEq.
Assume for all a << M a << N.
Assume for all a << N a << M.
Then M = N.

Signature. Let a << M. M\{a} is a set.
Axiom. Let a << M. Then M\{a} = {x | x << M and x != a}.
