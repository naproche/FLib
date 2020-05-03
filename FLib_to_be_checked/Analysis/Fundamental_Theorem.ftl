[number/-s][derivative/-s]
[read Forster/Reals.ftl]

Let a,b,c,x,y,z,epsilon,delta,m,M denote real numbers.
Let |x| stand for abs(x).
Let x/y stand for x * inv(y).
Let f,g,F denote functions.

Axiom.
Every real number is an element of Dom(f). ## We only talk about total real functions

Axiom. f[x] is a real number.
Let the value of f at x stand for f[x].

Definition Continuity. f is continuous iff for every x for every positive epsilon there exists a positive delta such that for every y
|y-x| < delta => |f[y]-f[x]| < epsilon.

Definition Derivative. A derivative of F is a function f such that for every x for every positive epsilon there exists a positive delta such that for every y
y !=x /\ |y-x| < delta => |((F[y]-F[x])/(y-x)) - f[x]| < epsilon.

Signature. Integral(f,a,b) is a real number.

Axiom Split_Integral. Integral(f,a,b) = Integral(f,a,c) + Integral(f,c,b).

Axiom Estimation_Lemma. Assume that a =< b. Assume that for every x such that a =< x =< b
m < f[x] < M. Then
m * (b-a) < Integral(f,a,b) < M * (b-a).

Theorem Fundamental_Theorem. Assume that f is continuous. Assume that for every x
F[x]=Integral(f,a,x). Then f is a derivative of F.

Proof.[ontored on]
Let x be a real number.
Let epsilon be positive.
Take a positive delta such that for every z |z-x| < delta => |f[z]-f[x]| < epsilon (by Continuity).
Let us show that y != x /\ |y - x| < delta => |((F[y] - F[x])/(y - x)) - f[x]| < epsilon for every y. Proof.
Let y !=x and |y-x| < delta. Then x - y != 0 and y - x != 0.
Case y > x.
		f[x]-epsilon < f[z] < f[x]+epsilon for every z such that x =< z =< y.
				proof.
				Assume x =< z =< y.[ontored off]
				Then |z - x| = z - x = (z - y) + (y - x) =< y - x =  |x - y| (by AbsGr, FieldGr).[/ontored] Hence | z - x | < delta.
				Therefore |f[z] - f[x]| < epsilon.
				-epsilon < f[z] - f[x] < epsilon (by AbsStrongIneqCharac1).
				-epsilon + f[x] < (f[z] - f[x]) + f[x] < epsilon + f[x] (by TranslationInvariance).
				Therefore the thesis (by AddGr).
				end. [setCtxt Estimation_Lemma leq]
		(f[x]-epsilon)*(y-x) < Integral(f,x,y) < (f[x]+epsilon)*(y-x). [setCtxt]
		(f[x]-epsilon)*(y-x) < Integral(f,a,y) - Integral(f,a,x) < (f[x]+epsilon)*(y-x) (by Split_Integral, AddGr).[ontored off]
		(f[x]-epsilon)*(y-x) < F[y] - F[x] < (f[x]+epsilon)*(y-x). [/ontored] 
		((f[x]-epsilon) *(y-x))/(y -x) < (F[y]-F[x])/(y-x) < ((f[x] + epsilon) * (y-x))/(y-x) (by MultInvariance, ComMult). Indeed inv(y - x) is positive.
		f[x] - epsilon < (F[y]-F[x])/(y-x) < f[x] + epsilon (by AssMult). Indeed (y-x)/(y-x) = 1.
		(f[x] - epsilon) - f[x] < ((F[y]-F[x])/(y-x)) - f[x] < (f[x] + epsilon) - f[x] (by TranslationInvariance).
		-epsilon < ((F[y]-F[x])/(y-x)) - f[x] < epsilon (by AddGr).
		|((F[y]-F[x])/(y-x)) - f[x]| < epsilon (by AbsStrongIneqCharac1).
		end.
Case y < x.
		f[x]-epsilon < f[z] < f[x]+epsilon for every z such that y =< z =< x.
					proof.
					Assume y =< z =< x.  [ontored off]
					Then |x - z| =  x - z = ((x - y) + y) - z =< x - y =  |x - y| (by AbsGr, FieldGr). [/ontored] Hence | z - x | < delta.
					Therefore |f[z] - f[x]| < epsilon.
					-epsilon < f[z] - f[x] < epsilon (by AbsStrongIneqCharac1).
					-epsilon + f[x] < (f[z] - f[x]) + f[x] < epsilon + f[x] (by TranslationInvariance).
					Therefore the thesis (by AddGr).
					end. [setCtxt Estimation_Lemma leq]
		(f[x]-epsilon)*(x-y) < Integral(f,y,x) < (f[x]+epsilon)*(x-y). [setCtxt]
		(f[x]-epsilon)*(x-y) < Integral(f,a,x) - Integral(f,a,y) < (f[x]+epsilon)*(x-y) (by Split_Integral, AddGr).[ontored off]
		(f[x]-epsilon)*(x-y) < F[x] - F[y] < (f[x]+epsilon)*(x-y). [/ontored] 
		((f[x]-epsilon) *(x-y))/(x -y) < (F[x]-F[y])/(x-y) < ((f[x] + epsilon) * (x-y))/(x-y) (by MultInvariance, ComMult). Indeed inv(x - y) is positive.
		f[x] - epsilon < (F[x]-F[y])/(x-y) < f[x] + epsilon (by AssMult). Indeed (x-y)/(x-y) = 1.
		(f[x] - epsilon) - f[x] < ((F[x]-F[y])/(x-y)) - f[x] < (f[x] + epsilon) - f[x] (by TranslationInvariance). 
		-epsilon < ((F[y]-F[x])/(y-x)) - f[x] < epsilon (by AddGr). Indeed (F[x] - F[y])/(x-y) = (F[y] - F[x])/(y - x) (by InvSwap).
		|((F[y]-F[x])/(y-x)) - f[x]| < epsilon (by AbsStrongIneqCharac1).
		end.
end.
[thesis]
qed.
