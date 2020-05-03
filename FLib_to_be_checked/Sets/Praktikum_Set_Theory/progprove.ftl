# Type bool

[value/values]
Signature 2_2_1. A truth value is a notion.
Let W denote truth values.

Signature. True is a truth value.
Signature. False is a truth value.

Axiom. W = True or W = False.

# 2.2.2 Type nat

[number/-s]
Signature. A natural number is a notion.
Let m,n denote natural numbers.

Signature. 0 is a natural number.
Signature. Suc n is a natural number.

Axiom. m = 0 or there exists n such that m = Suc n.

Axiom. n -<- Suc n.

Signature. m + n is a natural number.

Axiom. 0 + n = n.
Axiom. (Suc m) + n = Suc (m + n).

Lemma. For all m m + 0 = m.
Proof by induction.
qed.

# 2.2.3 Type list (of objects)

[object/-s]
Signature. An object is a notion.
Let x,y,z denote objects.

[list/-s]
Signature. A list is a notion.
Let xs, ys, zs denote lists.

Signature. Nil is a list.
Signature. Cons(x,xs) is a list. 

Axiom. xs = Nil or there exist x, ys such that xs = Cons(x,ys).

Axiom. ys -<- Cons(x,ys).

Signature. app(xs,ys) is a list.
Axiom. app(Nil,ys) = ys.
Axiom. app(Cons(x,xs),ys) = Cons(x,app(xs,ys)).

Signature. rev xs is a list.
Axiom. rev Nil = Nil.
Axiom. rev Cons(x,xs) = app (rev xs, Cons(x,Nil)).

Lemma p11a. For all xs app(xs,Nil) = xs.
Proof by induction.
qed.

Lemma p11b. For all xs app(app(xs,ys),zs) = app(xs,app(ys,zs)).
Proof by induction.
qed.

Lemma p10b. For all xs rev app(xs,ys) = app(rev ys, rev xs).
Proof by induction.
Let xs be a list.
Case xs = Nil. Obvious.
Case xs != Nil. Obvious.
qed.

Lemma p10a. For all xs rev rev xs = xs.
Proof by induction.
Let xs be a list.
Case xs = Nil. Obvious.
Case xs != Nil.
Take x, ys such that xs = Cons(x,ys).
ys -<- xs.
rev rev xs = rev rev Cons(x,ys)
= rev app(rev ys, Cons(x,Nil))
= app(rev Cons(x,Nil), rev rev ys)
= app(app(rev Nil, Cons(x,Nil)), ys)
= app(app(Nil, Cons(x,Nil)), ys)
= app(Cons(x,Nil),ys)
= Cons(x,app(Nil,ys))
= Cons(x,ys)
= xs. 
end.
qed.

Signature 18. itrev(xs,ys) is a list.
Axiom. itrev(Nil,ys) = ys.
Axiom. itrev(Cons(x,xs),ys) = itrev(xs, Cons(x,ys)).

Lemma. For all xs for all zs itrev(xs,zs) = app(rev xs,zs).
Proof by induction.
Let xs be a list.
Case xs = Nil. Obvious.
Case xs != Nil. 
Take x,ys such that xs = Cons(x,ys).
Let zs be a list.
itrev(xs,zs) =
itrev(Cons(x,ys), zs) =
itrev(ys, Cons(x,zs)) =
app(rev ys, Cons(x,zs)) =
app(app(rev ys,Cons(x,Nil)),zs) =
app(rev Cons(x,ys),zs) =
app(rev xs, zs).
end.
qed.

Lemma. itrev(xs,Nil) = rev xs.

Signature 16. div2 m is a natural number.

Axiom. div2 0 = 0.
Axiom. div2 Suc 0 = 0.
Axiom. div2 Suc Suc n = Suc div2 n.

# 3.3 Proof Automation

Lemma 27a. For all x there exists y such that x = y.

Lemma 27b. forall x exists y x = y.

Signature. T(x,y) is an atom.
Signature. B(x,y) is an atom.

Lemma 28b. Assume that for all x,y 
(T(x,y) \/ T(y,x)) /\
(B(x,y) /\ B(y,x) => x=y) /\
(B(x,y) => T(x,y)).
Then for all x,y B(x,y) => T(x,y).

# 4.1 Isar by Example

Let a,b,A denote classes.
Let f,g denote functions.

Axiom. Every element of a is an object.

Definition. A subclass of a is a class b such that every element
of b is an element of a.

Definition. Pow(a) = {class b | b is a subclass of a}.

Definition. f is from a onto b iff
a = Dom(f) and
(for every element x of a f[x] is an element of b) and
(for every element y of b
there exist an element x of a such that y = f[x]).

Lemma 42. There is no function f from a onto Pow(a).
Proof. Assume that f is a function from a onto Pow(a).
Define A = 
{object x | x is an element of a and x is not an element of f[x]}.
Take an element x of a such that A = f[x].
x is an element of A iff x is not an element of A.
Contradiction.
qed.
