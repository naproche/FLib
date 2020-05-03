[synonym set/-s] [synonym element/-s] [synonym belong/-s] 
[synonym subset/-s] [synonym real/-s] [synonym map/-s]

Signature Real.  A real is a notion. Signature Null. 0 is a real. 
Signature Zwei. 2 is a real.
Let x,y,z,u,v, alpha, beta, gamma, delta, epsilon stand for reals.

Signature Sum. x+y is a real. Signature Differenz. x-y is a real.
Signature Quotient. x/y is a real.
Signature Less. x < y is an atom.
Let y > x stand for x < y. Let x is positive stand for x > 0.

Axiom Half. If x is positive then x/2 is positive.
Axiom Half1. (x/2) + (x/2) = x.
Axiom Transitivity. x<y<z => x<z.
Axiom Monotonicity. Let x<u and y<v. Then x+y<u+v.

Axiom Direct. For every positive beta, gamma there is a positive alpha such that
alpha<beta and alpha<gamma.

Signature AbsValue. |x| is a real. 
Axiom Triangle. |(x+y)-(u+v)|<|x-u|+|y-v|.

Signature Function. A map is a notion. Let f,g stand for maps. 
Signature Value. f(x) is a real.

Definition Continuous. f is continuous at x iff for all positive epsilon 
there exists a positive delta such that for all y 
     |x-y|<delta => |f(x)-f(y)|<epsilon.

Definition Continuous1. f is continuous iff f is continuous at x for all x.

Definition Composition. g*f is a map such that (g*f)(x)=g(f(x)) for all x.

Theorem Comp. Let f be continuous and g be continuous. Then g*f is continuous.
Proof. Let x be a real. Let epsilon be a positive real. 
Take a positive delta such that for all z
|f(x)-z|<delta => |g(f(x))-g(z)|<epsilon.
Take a positive gamma such that for all y
|x-y|<gamma => |f(x)-f(y)|<delta.
For all y |x-y|<gamma => |(g*f)(x)-(g*f)(y)|<epsilon.
qed.

Definition MapSum. f ++ g is a map such that (f ++ g)(x)= f(x)+g(x) for all x.

Theorem Sum. Let f be continuous and g be continuous. Then f ++ g is continuous.
Proof. Let x be a real. Let epsilon be a positive real. Let delta=epsilon/2. delta is positive.
Take a positive beta such that for all y
|x-y| < beta => |f(x)-f(y)| < delta.
Take a positive gamma such that for all y
|x-y| < gamma => |g(x)-g(y)| < delta.
Take a positive alpha such that alpha < beta and alpha < gamma.
Let us show that for all reals y |x-y| < alpha => |(f ++ g)(x)-(f ++ g)(y)| < epsilon.
Let y be a real such that  |x-y|<alpha. Then |x-y|<beta and |x-y|<gamma.
Then |f(x)-f(y)|<epsilon/2 and |g(x)-g(y)|<epsilon/2.
|(f ++ g)(x)-(f ++ g)(y)|=|(f(x)+g(x))-(f(y)+g(y))|.
|(f(x)+g(x))-(f(y)+g(y))|<|f(x)-f(y)|+|g(x)-g(y)|.
Then |f(x)-f(y)|+|g(x)-g(y)|<(epsilon/2)+(epsilon/2) (by Monotonicity).
Then |(f ++ g)(x)-(f ++ g)(y)|<epsilon (by Transitivity, Half1).
qed.
qed.

