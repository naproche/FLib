[synonym space/-s] [synonym scalar/-s] [synonym function/-s]


Let M,N denote sets.
Let x << M stand for x is an element of M.

Definition.
Prod(M,N) = { (x,y) | x << M and y << N }.

Definition.
Let f be a function. f is injective iff for all elements x,y of Dom(f) we have (x!=y => f[x] != f[y]).

Definition.
Let f be a function. Let M,N be sets. f is from M to N iff Dom(f) = M and for every element x of M f[x] is an element of N.


Axiom FunExt.
Let f,g be functions. If Dom(f) = Dom(g) and for every element x of Dom(f) f[x] = g[x] then f = g.


Signature.
A scalar is a notion.

Signature.
SK is the set of scalars.

Signature.
Let a,b be scalars. a + b is a scalar.

Signature.
Let a,b be scalars. a * b is a scalar.


Signature.
A vector space is a notion.

Let V,W denote vector spaces.


Signature. Cr(V) is a set.
Signature. add(V) is a function from Prod(Cr(V),Cr(V)) to Cr(V).
Signature. scm(V) is a function from Prod(SK,Cr(V)) to Cr(V).

Definition.
Let f be a function. f is linear from V to W iff 
        ( f is from Cr(V) to Cr(W))
	and (for all elements x,y of Cr(V) f[add(V)[(x,y)]] = add(W)[(f[x], f[y])])
and (for every scalar a for every element x of Cr(V) f[scm(V) [(a,x)]] = scm(W)[(a,f[x])]). 


Definition.
A scalar function on V is a function f such that 
	Dom(f) = Cr(V)
    and (for every element x of Cr(V) f[x] is a scalar)
    and (for every element x,y of Cr(V) f[add(V)[(x,y)]] = f[x] + f[y])
    and (for every element x of Cr(V) and every scalar a f[scm(V)[(a,x)]] = a * f[x]).

Signature.
SF(V) is the set of scalar functions on V.

Definition.
dual(V) is a vector space W such that
	(Cr(W) = SF(V))
   and	(for all scalar functions f,g on V and every element x of Cr(V) (add(W)[(f,g)])[x] = f[x] + g[x])
   and  (for every scalar function f on V, every scalar a and every element x of Cr(V) (scm(W)[(a,f)]) [x] = a * f[x]).


Axiom Exi.
Let x,y be elements of Cr(V). Assume x != y. There exists a scalar function g on V such that g[x] != g[y].




Proposition.
There exists an injective function that is linear from V to dual(dual(V)).
Proof.
Define f = \v in Cr(V). \g in Cr(dual(V)). g[v].
Let us show that f is an injective function that is linear from V to dual(dual(V)).
	Let us show that f is linear from V to dual(dual(V)).
		f is from Cr(V) to Cr(dual(dual(V))).
		proof.
			Dom(f) = Cr(V).
			Let x be an element of Cr(V).
			f[x] is a scalar function on dual(V).
			proof.
				Dom(f[x]) = Cr(dual(V)) and for every element y of Cr(dual(V)) f[x][y] is a scalar.
				For all elements h,g of Cr(dual(V)) f[x][add(dual(V))[(h,g)]] = f[x][h] + f[x][g].
				proof.
					Let h,g be elements of Cr(dual(V)).
					f[x][add(dual(V))[(h,g)]] = add(dual(V))[(h,g)][x] = h[x] + g[x] = f[x][h] + f[x][g]. 
				end.
				For every element g of Cr(dual(V)) and every scalar a f[x][scm(dual(V))[(a,g)]] = a * f[x][g].
				proof.
					Let g be an element of Cr(dual(V)). Let a be a scalar.
					f[x][scm(dual(V))[(a,g)]] = scm(dual(V))[(a,g)][x] = a * g[x] = a * f[x][g].
				end.
			end.
		end.
		For all elements x,y of Cr(V) f[add(V)[(x,y)]] = add(dual(dual(V)))[(f[x], f[y])].
		proof.
			Let x,y be elements of Cr(V). add(dual(dual(V)))[(f[x], f[y])] is an element of Cr(dual(dual(V))).
			Therefore add(dual(dual(V)))[(f[x], f[y])] is a function. f [add(V)[(x,y)]] is a function.
			Dom (f [add(V)[(x,y)]]) = Cr(dual(V)) = Dom(add(dual(dual(V)))[(f[x], f[y])]).
			For every element g of Cr(dual(V)) we have (f [add(V)[(x,y)]])[g] = (add(dual(dual(V)))[(f[x], f[y])])[g].
			Therefore the thesis (by FunExt).
		end.
		For every scalar a and every element x of Cr(V) f[scm(V) [(a,x)]] = scm(dual(dual(V)))[(a,f[x])].
		proof.
			Let a be a scalar and x be an element of Cr(V). f[scm(V) [(a,x)]] and scm(dual(dual(V)))[(a,f[x])] are functions.
			Dom(f[scm(V) [(a,x)]]) = Cr(dual(V)) = Dom(scm(dual(dual(V)))[(a,f[x])]).
			For every element g of Cr(dual(V)) we have f[scm(V) [(a,x)]][g] = scm(dual(dual(V)))[(a,f[x])][g].
			Therefore the thesis (by FunExt).
		end.

	end.
	Let us show that f is injective.
		Let x,y be elements of Dom(f). Assume x != y. Take a scalar function g on V such that g[x] != g[y] (by Exi).
		Then f[x][g] != f[y][g].
	end.
end.
qed.



