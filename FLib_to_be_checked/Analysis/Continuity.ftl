[read Forster/Sequences.ftl]
[function/-s]

[setCtxt AddGr NatGr SumConv SequenceSum SequenceEq Seq]
Definition RealSubSet.
A set of reals is a set M such that every element of M is a real number.

Definition RealFunction.
A real function is a function f such that every element of Dom(f) is a real number and
for every element x of Dom(f) f[x] is a real number.

Definition FunctionSum.
Let g,h be real functions. g +~ h is a real function f such that for every real number x (x is an element of Dom(f) iff x is an element of Dom(g) and x is an element of Dom(h)) and if x is an element of Dom(g) and x is an element of Dom(h) then f[x] = g[x] + h[x].

Signature LiftDef.
Let f be a real function. let a be a sequence such that (a[n] is an element of Dom(f) for every natural number n). lift(f,a) is a sequence b such that for every natural number n b[n] = f[a[n]].  

Definition.
Let f be a real function. Let a be an element of Dom(f). LimitEx(f,a) iff for every sequence b such that (b converges to a and for every natural number n b[n] is an element of Dom(f)) lift(f,b) converges to f[a].

Definition Continuous.
Let f be a real function. f is continuous iff LimitEx(f,a) for every element a of Dom(f).
[ontored on][prove on]
Lemma SumCont.
Let f,g be continuous real functions. f +~ g is continuous.
Proof.
Let us show that LimitEx(f +~ g, a) for every element a of Dom(f +~ g).
  proof.
  Let a be an element of Dom(f +~ g).
  Let b be a sequence such that (b converges to a and for every natural number n b[n] is an element of Dom(f +~ g)).
  Then b[n] is an element of Dom(f) and an element of Dom(g) for every natural number n.
  lift(f,b) +' lift(g,b) = lift(f +~ g, b).
  	proof.
  	lift(f,b) +' lift(g,b) is a sequence. lift(f +~ g,b) is a sequence.
  	(lift(f,b) +' lift(g,b)) [n] = lift(f +~ g, b)[n] for every natural number n.
			proof.
			Let n be a natural number. b[n] is a real number and b[n] is an element of Dom(f) and b[n] is an element of Dom(g).[/ontored]
			(lift(f,b) +' lift(g,b)) [n] .= lift(f,b)[n] + lift(g,b)[n] (by SequenceSum)
																	 .= f[b[n]] + g[b[n]] (by LiftDef)
																	 .= (f +~ g)[b[n]] (by FunctionSum).
			end.
		Therefore the thesis (by SequenceEq).
  	end.
  	lift(f,b) converges to f[a] and lift(g,b) converges to g[a].
  	Therefore lift(f,b) +' lift(g,b) converges to f[a] + g[a].
  end.
 qed.

 Definition.
 Let a,b be real numbers. [a,b] = {real number x | a =< x =< b}.
 
 Definition. A nesting is a function f such that every element of Dom(f) is a natural number 
 				and every natural number is an element of Dom(f) 
 				and for every natural number n ((there exist real numbers a,b such that f[n] = [a,b])
 				and (every element of f[n] is an element of f[n+1]) 
 				and there exists an element of f[n+1] that is not an element of f[n]). 
 				
 
Axiom Completeness. Let f be a nesting. There exists a unique real number x such that x is an element of f[n] for every natural number n.

Let f stand for a real function.
 
Definition. Let f be a real function. Let x be an element of Dom(f). DiffQuot(f,x) = \del in Dom(f). (f[del] - f[x]) * inv(del - x).

Definition. Let x be an element of Dom(f). f is differentiable in x iff LimitEx(DiffQuot(f,x),x).

Proposition. Let x be an element of Dom(f). f is diffenrentiable in x iff there exists a real number c and a real function 


  
