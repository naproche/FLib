[read Forster/Reals.ftl]
[setCtxt FieldGr AbsDist]
Signature.
A real function is a function f such that every element of Dom(f) is a real number and for every element x of Dom(f) f[x] is a real number.

Signature.
Let f be a real function. f is continuous is an atom.


Definition.
Let f be a real function. Let x,y be element of Dom(f) such that x != y. DiffQuot(f,x,y) = (f[x] - f[y]) * inv(x - y).

Definition.
Let f be a real function. Let x be an element of Dom(f). DiffQuotF(f,x) = \y in {y in Dom(f) | y != x }. DiffQuot(f,x,y).


Definition.
Let f be a real function. f converges to zero iff f is a real number.



Definition.
Let f be a real function. Let x be an element of Dom(f). f is differentiable in x iff there exists a real number f1x such that for every positive real number eps there exists a real number del such that for every element y of Dom(f) such that x!=y and dist(x,y) < del we have dist(DiffQuot(f,x,y), f1x) < eps.

Definition.
Let f be a real function. f is differentiable iff f is differentiable in every element of Dom(f).

Definition.
Let f be a differentiable real function. deriv(f) is a real function such that Dom(f) = Dom(deriv(f)) and for any positive real number eps there exists a real number del such that for every element y of Dom(f) such that x!=y and dist(x,y) < del we have dist(DiffQuot(f,x,y), deriv(f)[x]) < eps where x is an element of Dom(f).

Let f denote a continuous real function.

Signature.
Let f be a continuous real function. Let a,b be elements of Dom(f). Integral(f,a,b) is a real number.

Axiom.
Let a,b,c be elements of Dom(f). Integral(f,a,c) = Integral(f,a,b) + Integral(f,b,c).

Axiom.
Let a,b be elements of Dom(f). Integral(f,a,b) = - Integral(f,b,a).

Signature.
Let f be a continuous real function. Let a be an element of Dom(f). IntegralF(f,a) is a real function such that Dom(f) = Dom(IntegralF(f,a)) and for any element x of Dom(f) IntegralF(f,a)[x] = Integral(f,a,x).

Theorem.
Let f be a continuous real function. Let a be an element of Dom(f). IntegralF(f,a) is differentiable.
Proof.
Let x be an element of Dom(IntegralF(f,a)). 
Let us show that for any positive real number eps there exists a real number. qed. qed.
