# 8-Transitive Closure

# This section is similiar to the previous one, but that one was too long and for every new proof Isabelle jumped up
# some hundred lines so every small proof took a long time. So I stated the important results from that section as axioms
# and continued here.

# Main results:

# - for every SWR, every zfset x the transitive closure is in /VV
# - definition and existance of the transitive closure wrt eps




[synonym zfset/-s]

Signature. A ZFset is a notion.

Axiom. Let x be a ZFset. Then x is a set.


# General Syntax

Let x /in y stand for x is an element of y.
Let x /notin y stand for x is not an element of y.
Let x /neq y stand for x != y.


# Pretyped Variables

Let w,x,y,z,W,X,Y,Z stand for ZFSets.
Let a,b,c,d,A,B,C,D stand for sets.


# Introduction of Emptyset, Universe

Axiom. Let a, b be sets. (Forall c (c /in a <=> c /in b)) => a = b.
Axiom. Let a be a set. Let b be an object. Let b /in a. Then b is a ZFset.

Definition Emptyset. The empty set is {ZFset x | x /neq x}.
Let /emptyset stand for the empty set.

Definition. Let a be a set. a is empty iff a = /emptyset.
Definition. Let a be a set. a is nonempty iff exists b (b /in a).

Definition Universe. The universe is {ZFset x | x = x}.
Let /VV stand for the universe.

Definition Subset. A subset of A is a set B such that
forall c (c /in B => c /in A).
Let B /subset A stand for B is a subset of A.

Axiom. Let a, b be sets. Let a /subset b /\ b /subset a. Then a = b.


# Arithmetic


Definition Union. The union of A and B is 
{ZFset x | x /in A or x /in B}.
Let A /cup B stand for the union of A and B.

Definition BigUnion. The bigunion of A is
{ZFset b | exists w (w /in A /\ b /in w)}. 
Let /bigcup A denote the bigunion of A.

Definition Intersection. The intersection of A and B is 
{ZFset x | x /in A and x /in B}.
Let A /cap B stand for the intersection of A and B.

Definition BigIntersection. The bigintersection of A is
{ZFset x | forall y (y /in A => x /in y)}.
Let /bigcap A stand for the bigintersection of A.

Definition Difference. The difference of A and B is 
{ZFset x | x /in A and x /notin B}.
Let A /setminus B stand for the difference of A and B.

Definition Singleton. The singleton of X is
{ZFset x | x = X}.
Let <X> stand for the singleton of X.

Definition Pair. Let a,b be ZFsets. The pair of a and b is {ZFset c | c = a \/ c = b}.
Let <a , b> denote the pair of a and b.

Definition Power. The power set of X is
{ZFset x | x /subset X}.
Let /PP X stand for the power set of X.



[synonym class/-es]

Signature. A proper class is a notion.

Axiom. Let L be a proper class. Then L is a set.
Axiom. Let a be a set. a is a proper class iff a /notin /VV.



# Ordered pairs

Axiom OPair1. Let a,b /in /VV. Then (a,b) is a zfset.
Axiom OPair2. (x,y) = (X,Y) => x = X /\ y = Y.

Definition 105a. The cartesian product of A and B is
{set x | exists a,b (x = (a,b) /\ a /in A /\ b /in B)}.
Let A /times B stand for the cartesian product of A and B.



# Relations

[synonym relation/-s]

Definition Relation. A relation is a set R such that 
R /subset /VV /times /VV.
Let a - R - b stand for (a,b) /in R.

Axiom Relation1. Let R be a relation. x /in R => exists a,b /in /VV (x = (a,b)).

Definition Domain. Let R be a relation. The reldomain of R is
{zfset a | exists z (a - R - z)}.
Let reldomain(R) stand for the reldomain of R.

Definition Range. Let R be a relation. The relrange of R is
{zfset a | exists z (z - R - a)}.
Let relrange(R) stand for the relrange of R.

Definition Domain. Let R be a relation. The relfield of R is
relrange(R) /cup reldomain(R).
Let relfield(R) stand for the relfield of R.

Definition. Let R be a relation. Let x /in /VV. The smallerset of R rel x is
{zfset y | y - R - x}.
Let sset(R,x) stand for the smallerset of R rel x.

Definition. Let R be a relation. Let A /subset relfield(R). The relrestriction of R to A is a relation RR such that
forall x,y /in /VV (x - RR - y iff (x - R - y /\ x,y /in A)).
Let R /restrict A stand for the relrestriction of R to A.

Lemma. Let R be a relation. Let A /subset relfield(R). Then relfield(R /restrict A) /subset A.



# Attributes of relations

Definition. Let R be a relation. R is reflexive iff forall x /in relfield(R) (x - R - x).
Let ref(R) stand for R is reflexive.

Definition. Let R be a relation. R is irreflexive iff forall x /in relfield(R) (not (x - R - x)).
Let irref(R) stand for R is irreflexive.

Definition. Let R be a relation. R is symmetric iff forall x,y (x - R - y => y - R - x).
Let sym(R) stand for R is symmetric.

Definition. Let R be a relation. R is antisymmetric iff forall x,y (x - R - y /\ y - R - x => x = y).
Let antisym(R) stand for R is antisymmetric.

Definition. Let R be a relation. R is reltransitive iff forall x,y,z (x - R - y /\ y - R - z => x - R - z).
Let reltrans(R) stand for R is reltransitive.

Definition. Let R be a relation. R is connex iff forall x,y /in relfield(R) (x - R - y \/ y - R - x \/ x = y).
Let con(R) stand for R is connex.

# Kinds of relations

Signature. An equivalence relation is a notion.
Axiom. Let R be an equivalence relation. Then R is a relation.
Axiom. Let R be a relation. R is an equivalence relation iff ref(R) /\ sym(R) /\ reltrans(R).
Let eqrel(R) stand for R is an equivalence relation.

Definition. Let R be an equivalence relation. The equivalence class of x modulo R is {zfset y | y - R - x}.
Let [x]-R stand for the equivalence class of R modulo x.

Signature. A partial order is a notion.
Axiom. Let R be a partial order. Then R is a relation.
Axiom. Let R be a relation. Then R is a partial order iff ref(R) /\ reltrans(R) /\ antisym(R).

Signature. A linear order is a notion.
Axiom. Let R be a linear order. Then R is a relation.
Axiom. Let R be a relation. Then R is a linear order iff con(R) /\ (R is a partial order).

Signature. A partial order on A is a notion.
Axiom. Let A be a set. Let R be a partial order on A. Then R is a partial order.
Axiom. Let R be a relation. Let A be a set. Then R is a partial order on A iff (R is a partial order) /\ relfield(R) = A.

Signature. A strict partial order is a notion.
Axiom. Let R be a strict partial order. Then R is a relation.
Axiom. Let R be a relation. Then R is a strict partial order iff reltrans(R) /\ irref(R).

Lemma. Let R be a strict partial order. Let relfield(R) /neq /emptyset. Then R is not a partial order.

Signature. A strict linear order is a notion.
Axiom. Let R be a strict linear order. Then R is a relation.
Axiom. Let R be a relation. Then R is a strict linear order iff con(R) /\ (R is a strict partial order).



# Functions

Let M stand for a set.
Let func stand for a function.
Let the value of f at x stand for f[x].
Let the domain of f stand for Dom(f).

Axiom. Let f be a function. The domain of f is a set.

[synonym zffunction/-s]
Signature. A zffunction is a notion.
Axiom. Let f be a zffunction. Then f is a function.
Axiom. Let f be a function. f is a zffunction iff forall x /in Dom(f) f[x] /in /VV.

Let f is defined on M stand for M /subset Dom(f).

Let f,g,h,F,G,H stand for zffunction.

Definition Range. Let f be a zffunction. The range of f is
{f[x] | x /in Dom(f)}.
Let ran(f) stand for the range of f.

Definition Image. Let f be a zffunction. Let M be a set. The image of M under f is
{f[x] | x /in Dom(f) /cap M}.
Let f^[M] stand for the image of M under f.

Definition FunctionImage. Let f be a function. Let M be a set. The functionimage of M under f is
{f[x] | x /in Dom(f) /cap M /\ f[x] /in /VV}.
Let f /caret [M] stand for the functionimage of M under f.

Definition Composition. Let f and g be zffunctions. Let ran(f) /subset Dom(g). The composition of g and f is
a function h such that Dom(h) = Dom(f) and forall x /in Dom(f) h[x] = g[f[x]].
Let g /circ f stand for the composition of g and f.
Lemma. Let f and g be zffunctions. Let ran(f) /subset Dom(g). Then g /circ f is a zffunction.

Definition Map. A map from A to B is a zffunction F such that
Dom(F) = A and ran(F) /subset B.
Let F : A /rightarrow B stand for F is a map from A to B.

Definition PMap. A partial map from A to B is a zffunction F such that
Dom(F) /subset A and ran(F) /subset B.
Let F : A /harpoonright B stand for F is a partial map from A to B.

Definition Restriction. Let f be a zffunction. Let M /subset Dom(f). The restriction of f to M is a function g such that
Dom(g) = M and forall x /in M /cap Dom(f) (g[x] = f[x]).
Let f /upharpoonright M stand for the restriction of f to M.
Lemma. Let f be a zffunction. Let M /subset Dom(f). Then f /upharpoonright M is a zffunction.

Signature. Id is a function.
Axiom. Dom(Id) = /VV.
Axiom. Forall x (Id[x] = x).
Lemma. Id is a zffunction.
Axiom. Forall M Id^[M] = M.

Definition Surjective. Let F be a zffunction. Assume F : A /rightarrow B. F is surjective from A to B
iff ran(F) = B.

Definition Injective. Let f be a zffunction. f is injective iff
forall x,y /in Dom(f) (f[x] = f[y] => x = y).

Definition Bijective. Let F be a zffunction. F is bijective from A to B
iff F : A /rightarrow B and Dom(F) = A and ran(F) = B and F is injective.
Let F : A /leftrightarrow B stand for F is bijective from A to B.

Axiom. Forall M (Id /upharpoonright M : M /leftrightarrow M).

Axiom. Let f and g be functions. f = g iff Dom(f) = Dom(g) and forall x /in Dom(f) (f[x] = g[x]).
Axiom. Let f and g be zffunctions. f = g iff Dom(f) = Dom(g) and forall x /in Dom(f) (f[x] = g[x]).


Definition. Let f be an injective zffunction. The inverse of f is a function g such that
Dom(g) = ran(f) and (forall x /in ran(f) forall y /in Dom(f) (g[x] = y iff f[y] = x)).
Let f^{-1} stand for the inverse of f.
Lemma. Let f be an injective zffunction. Then f^{-1} is a zffunction.

Axiom. Let f be a zffunction. Let A,B be sets. Let f : A /leftrightarrow B.
Then f^{-1} : B /leftrightarrow A.

Definition SetofFunctions. ^{A}B = {zffunction f | f : A /rightarrow B}.






# ZF-Axioms



Axiom Empty. /emptyset is a ZFset.

Axiom Pair. Let x, y /in /VV. Then <x, y> /in /VV.

Axiom Union. Let x /in /VV. Then /bigcup x /in /VV.

Axiom Sep. Let x /in /VV. Let a /subset x. Then a /in /VV.

Axiom Power. Let x be a ZFset. Then /PP x is a ZFset.

Axiom Rep. Let f be a zffunction. Let x /in /VV. Then f^[x] /in /VV.

Axiom Found. Let A be a nonempty set. Then there is a ZFset b such that 
(b /in A /\ forall c (c /in b => c /notin A)).

Axiom. Forall x /in /VV x /notin x.
Axiom. Let x /in /VV. Then <x> /in /VV.
Axiom. Let x,y /in /VV. Then x /cup y /in /VV.






# Ordinals


Definition transitive. Let A be a set. A is transitive iff forall x,y (y /in A /\ x /in y => x /in A).
Let Trans(A) stand for A is transitive.

Lemma. Let A be a set. A is transitive iff forall x /in A (x /subset A).

Lemma. Trans(/emptyset).

[synonym ordinal/-s]

Signature. An ordinal is a notion.

Let alpha, beta, gamma, delta stand for ordinals.

Axiom. Let alpha be an ordinal. Then alpha is a ZFset.

Signature. alpha + beta is an ordinal.
Signature. x /plus 1 is a zfset.
Signature. 0 is an ordinal.
Signature. 1 is an ordinal.

Axiom. Let alpha be a ZFset. alpha is an ordinal iff ( Trans(alpha) /\ forall y (y /in alpha => Trans(y) )).

Definition Trans. The class of transitives is
{ZFset x | Trans(x)}.
Let /Trans stand for the class of transitives.

Definition Ord. The class of ordinals is
{set x | x is an ordinal}.
Let /Ord stand for the class of ordinals.

Axiom. 0 = /emptyset.

Axiom. Let alpha be an ordinal. Then alpha + 1 is {ZFset x | x /in alpha \/ x = alpha }.
Axiom. Let x be a zfset. Then x /plus 1 is {ZFset y | y /in x \/ y = x }.
Axiom. Let alpha be an ordinal. Then alpha + 1 = alpha /plus 1.


Axiom. 1 = 0 + 1.

Signature. A successor ordinal is a notion.
Signature. A limit ordinal is a notion.

Axiom successor. Let alpha be an ordinal. alpha is a successor ordinal iff exists beta (alpha = beta + 1).

Definition Succ. The class of successor ordinals is
{ordinal alpha | alpha is a successor ordinal }.
Let /Succ stand for the class of successor ordinals.

Axiom limit. Let gamma be an ordinal. gamma is a limit ordinal iff (gamma /neq /emptyset /\ gamma /notin /Succ).

Definition Lim. The class of limit ordinals is
{ordinal alpha | alpha is a limit ordinal }.
Let /Lim stand for the class of limit ordinals.

Axiom. Let x be an ordinal. Then x = /emptyset \/ x /in /Succ \/ x /in /Lim.

Axiom Infinity. Exists x (/emptyset /in x /\ forall y /in x ((y /plus 1) /in x) ).

Axiom. Let alpha be an ordinal. Then alpha + 1 is an ordinal.
Axiom. Let alpha be an ordinal. Let x be an object. Let x /in alpha. Then x is an ordinal.
Axiom. Forall alpha, beta (alpha /in beta \/ beta /in alpha \/ alpha = beta).
Axiom. Let A /subset /Ord. Let A /neq /emptyset. Then exists alpha (alpha /in A /\ forall beta /in A (alpha = beta \/ alpha /in beta)).
Axiom. Let alpha, beta be ordinals. Let alpha /in beta. Then alpha /subset beta.

Signature. Let alpha /in /Succ. alpha - 1 is an ordinal.

Axiom. Let alpha /in /Succ. Let beta be an ordinal. alpha - 1 = beta iff alpha = beta + 1.

Axiom. Let x /in /Lim. Let y /in x. Then y + 1 /in x.




# Natural Numbers


[synonym number/-s]

Signature. A natural number is a notion.

Let k,l,m,n stand for natural numbers.

Axiom. Let n be a natural number. Then n is an ordinal.
Axiom. Let n be a natural number. Then n + 1 is a natural number.

Definition. The class of inductive sets is
{ZFSet x |  (/emptyset /in x /\ forall y /in x ((y /plus 1) /in x) ) }.
Let /Ind stand for the class of inductive sets.

Definition. The class of natnumbers is /bigcap /Ind.
Let /NN stand for the class of natnumbers.

Axiom. Let alpha be an ordinal. alpha is a natural number iff alpha /in /NN.

Axiom. /NN /in /Lim.

Axiom. 0, 1 are natural numbers.

Axiom. Let n /in /NN. Let n /neq /emptyset. Then n /in /Succ.





# Cardinalities

Axiom AC. Let x be a ZFset. Then exists alpha exists f (f : alpha /leftrightarrow x).

Definition SameCardinality. Let x, y be ZFsets. x and y are equipotent iff
exists f (f : x /leftrightarrow y).

Definition. Let x be a zfset. The cardset of x is 
{ordinal alpha | exists f (f : alpha /leftrightarrow x) }.
Let Cardset(x) stand for the cardset of x.

Definition. Let x be a zfset. The cardinality of x is /bigcap Cardset(x).
Let Card (x) stand for the cardinality of x.

Axiom. Let A be a set. Let A /subset /Ord. Let A /neq /emptyset.
Then /bigcap A is an ordinal.

Axiom. Let x be a zfset. The cardinality of x is an ordinal.

Axiom. Let x be a zfset. Then Card(x) /in Cardset(x).

Axiom. Let x /subset y. Then Card(x) /subset Card(y).



[synonym cardinal/-s]
Signature. A cardinal is a notion.

Axiom. Let kappa be a cardinal. Then kappa is an ordinal.
Axiom. Let kappa be an ordinal. kappa is a cardinal iff exists x (kappa = Card(x)).

Let kappa stand for a cardinal.

Axiom. Let alpha be an ordinal. Then Card(alpha) /subset alpha.

Axiom. Let kappa be a cardinal. Then Card(kappa) = kappa.


Definition. The class of cardinals is
{ordinal alpha | alpha is a cardinal}.
Let /Card stand for the class of cardinals.

Axiom. Forall n /in /NN Card(n) = n.
Axiom. Card(/NN) = /NN.








# Wellfounded Relations


Definition. Let R be a relation.  R is wellfounded iff
(forall A ((A /neq /emptyset /\ A /subset reldomain(R)) => (exists x /in A (forall y /in A (not (y - R - x)))))).

Lemma. Let R be a relation. Let R be wellfounded. Then (forall A ((A /neq /emptyset /\ A /subset reldomain(R)) => (exists x /in A (forall y /in sset(R,x) (y /notin A))))).

Definition. Let R be a relation. R is strongly wellfounded iff
(R is wellfounded) /\ (forall x /in relfield(R) sset(R,x) /in /VV).

Signature. A wellorder is a notion.
Axiom. Let R be a wellorder. Then R is a relation.
Axiom. Let R be a relation. Then R is a wellorder iff (R is wellfounded) and (R is a strict linear order).

Signature. A strong wellorder is a notion.
Axiom. Let R be a strong wellorder. Then R is a relation.
Axiom. Let R be a relation. Then R is a strong wellorder iff (R is strongly wellfounded) and (R is a wellorder).

Definition. Let R be a strongly wellfounded relation. R is extensional iff forall x,y /in reldomain(R) (sset(R,x) = sset(R,y) => x = y).
Let ext(R) stand for R is extensional.

Axiom. Let R be a strong wellorder. Then R is extensional.

Signature. eps is an object.
Axiom. eps is a relation.
Axiom. Forall x,y /in /VV (x - eps - y iff x /in y).
Axiom. reldomain(eps) = /VV.
Axiom. eps is strongly wellfounded.
Axiom. Forall x /in /VV sset(eps,x) = x.
Axiom. eps is extensional.






# Transitive Closure


Definition. Let R be a strongly wellfounded relation. Let x /subset reldomain(R). The class of transclosed sets of x resp R is
{zfset z | z /subset reldomain(R) /\ x /subset z /\ forall u /in z forall v /in sset(R,u) v /in z}.
Let TCsets(R,x) stand for the class of transclosed sets of x resp R.

Definition. Let R be a strongly wellfounded relation. Let x /subset reldomain(R). The transitive closure of x resp R is
/bigcap TCsets(R,x).
Let TC(R,x) stand for the transitive closure of x resp R.

Lemma. Let R be a strongly wellfounded relation. Let x /subset reldomain(R). Let TC(R,x) /in /VV. Then TC(R,x) /subset reldomain(R).
Proof.
Forall y /in TCsets(R,x) y /subset reldomain(R).
Then /bigcap TCsets(R,x) /subset reldomain(R).
qed.

Lemma. Let R be a strongly wellfounded relation. Let x /subset reldomain(R). Let TC(R,x) /in /VV. Then TC(R,x) /in TCsets(R,x).
Proof.
TC(R,x) /subset reldomain(R).
Forall y /in TCsets(R,x) x /subset y.
Then x /subset TC(R,x).
Forall y /in TCsets(R,x) forall u /in y forall v /in sset(R,u) v /in y.
Then forall u /in TC(R,x) forall v /in sset(R,u) v /in TC(R,x).
Proof.
  Let u /in TC(R,x).
  Forall v /in sset(R,u) v /in TC(R,x).
  Proof.
    Let v /in sset(R,u). Forall y /in TCsets(R,x) u /in y. Then forall y /in TCsets(R,x) v /in y.
    Then v /in TC(R,x).
  end.
end.
Then TC(R,x) /in TCsets(R,x).
qed.


Lemma. Let R be a strongly wellfounded relation.
Then forall x /in /VV (x /subset reldomain(R) => TC(R,x) /in /VV).
Proof.
R is wellfounded.
Then (forall A ((A /neq /emptyset /\ A /subset reldomain(R)) => (exists x /in A (forall y /in A (not (y - R - x)))))).
Then (forall A ((A /neq /emptyset /\ A /subset reldomain(R)) => (exists x /in A (forall y /in sset(R,x) (y /notin A))))).
Proof.
  Let A be a set. Let A /neq /emptyset /\ A /subset reldomain(R).
  Take a zfset x such that x /in A /\ forall y /in A (not (y - R - x)).
  Then forall y /in sset(R,x) (y /notin A).
end.


Forall x /in reldomain(R) TC(R,<x>) /in /VV.
Proof.
  Forall x /in reldomain(R)  <x> /subset reldomain(R).
  Define phi[m] =
    Case TC(R,<m>) /in /VV -> 0,
    Case TC(R,<m>) /notin /VV -> 1
  for m in reldomain(R).
  
  Forall x /in reldomain(R) (forall y /in sset(R,x) phi[y] = 0 => phi[x] = 0).
  Proof.
    Let x /in reldomain(R). Let forall y /in sset(R,x) phi[y] = 0.
    Forall y /in sset(R,x) <y> /subset reldomain(R).
    Define A = {TC(R,<y>) | y /in sset(R,x)}.
    Let z = <x> /cup /bigcup A.
    Then z /in TCsets(R,<x>).
    Proof.
      z /subset reldomain(R).
      Proof.
        Let a /in z. Then a = x \/ a /in /bigcup A.
        Then a /in reldomain(R).
        Proof.
          Case a = x. end.
          Case a /in /bigcup A. Take a set b such that b /in sset(R,x) /\ a /in TC(R,<b>).
            TC(R,<b>) /subset reldomain(R). Then a /in reldomain(R).
          end.
        end.
      end.

      <x> /subset z.
      
      Forall u /in z forall v /in sset(R,u) v /in z.
      Proof.
        Let u /in z. Let v /in sset(R,u). Then v /in z.
        Proof.
          Case u = x. Then TC(R,<v>) /in A. Then TC(R,<v>) /subset z.
            <v> /subset TC(R,<v>). Then v /in z.
          end.
          Case u /in /bigcup A. Take a set y such that y /in sset(R,x) /\ u /in TC(R,<y>).
            v /in sset(R,u). TC(R,<y>) /in TCsets(R,<y>). Then v /in TC(R,<y>).
            TC(R,<y>) /subset /bigcup A. Then v /in /bigcup A. Then v /in z.
          end.
        end.
      end.
      
      z /in /VV.
      Proof.
        A /in /VV.
        Proof.
          Define f[m] = TC(R,<m>) for m in sset(R,x).
          Then f is a zffunction.
          A /subset f^[sset(R,x)].
          Proof.
            Let a /in A. Take a set b such that b /in sset(R,x) /\ a = TC(R,<b>).
            Then a = f[b].
          end.
          sset(R,x) /in /VV.
          Then f^[sset(R,x)] /in /VV.
        end.
        
        Then /bigcup A /in /VV.
        x /in /VV.
        <x,x> = <x>.
        <x> /in /VV.
        < <x>, /bigcup A> /in /VV.
        z = /bigcup < <x>, /bigcup A>.
        Then z /in /VV.
      end.
      
    end.
    
    TC(R,<x>) = /bigcap TCsets(R,<x>).
    Then TC(R,<x>) /subset z.
    Then TC(R,<x>) /in /VV.
          
  end.

  Define M = {zfset z | z /in reldomain(R) /\ phi[z] = 0}.
  Then M /subset reldomain(R).
  Let N = reldomain(R) /setminus M.
  Then N /neq /emptyset \/ N = /emptyset.
  Case N = /emptyset. Then reldomain(R) /subset M. M /subset reldomain(R). Then reldomain(R) = M. end.
  Case N /neq /emptyset.
    Then exists x /in N (forall y /in sset(R,x) (y /notin N)).
    Proof.
      Forall B ((B /neq /emptyset /\ B /subset reldomain(R)) => (exists x /in B (forall y /in sset(R,x) (y /notin B)))).
      Let B be a set. Let B = N. Then B /neq /emptyset /\ B /subset reldomain(R).
      # The introduction of B is nonsense, but sometimes it does not work without it.
      # It is only needed that N is a set, but I think Naproche has attached too many attributes to N.
      # If we take a set B such that B = N, then Naproche seems to forget these attributes and can solve easier problems.
      # We sometimes so the same when we have two "complicated" ordinals and want to compare their size.
      # Then we also rename them, so Naproche only thinks of these terms as ordinals and forgets its definitions until it is needed.
    end.
    Take a zfset a such that (a /in N /\ (forall y /in sset(R,a) y /notin N)).
    Then forall y /in sset(R,a) phi[y] = 0.
    Then phi[a] = 0.
    Contradiction.
  end.

end.

Let x /in /VV. Let x /subset reldomain(R).
Forall y /in x <y> /subset reldomain(R).
Define A = {TC(R,<y>) | y /in x}.
Let z = /bigcup A.
Then z /in TCsets(R,x).
Proof.

  z /subset reldomain(R).
  Proof.
    Let a /in z. Take a set b such that b /in x /\ a /in TC(R,<b>).
    TC(R,<b>) /subset reldomain(R).
    Then a /in reldomain(R).
  end.

  x /subset z.
  Proof.
    Let a /in x. <a> /subset TC(R,<a>). Then a /in TC(R,<a>). Then a /in z.
  end.

  Forall u /in z forall v /in sset(R,u) v /in z.
  Proof.
    Let u /in z. Take a set b such that b /in x /\ u /in TC(R,<b>).
    Let v /in sset(R,u).
    Then v /in TC(R,<b>).
    Proof.
      TC(R,<b>) /in TCsets(R,<b>).
      Then forall uu /in TC(R,<b>) forall vv /in sset(R,uu) vv /in TC(R,<b>).
    end.
    Then v /in z.
  end.

  z /in /VV.
  Proof.
    A /in /VV.
    Proof.
      Define f[m] = TC(R,<m>) for m in x.
      Then A /subset f^[x].
      Proof.
        Let b /in A. Take a set c such that c /in x /\ b = TC(R,<c>).
        Then b = f[c].
      end.
      Then f^[x] /in /VV.
      Then A /in /VV.
    end.
  end.

end.

TC(R,x) = /bigcap TCsets(R,x).
Then TC(R,x) /subset z.
Then TC(R,x) /in /VV.


qed.



Definition. Let x /in /VV. The transitive closure of x is
TC(eps,x).
Let TC(x) stand for the transitive closure of x.

Lemma. Let x /in /VV. Then TC(x) /in /VV /\ x /subset TC(x) /\ Trans(TC(x)).
Proof.
TC(x) /in /VV.
x /subset TC(x).
Trans(TC(x)).
Proof.
  TC(x) /in TCsets(eps,x).
  Let a /in TC(x). Then forall b /in sset(eps,a) b /in TC(x).
  Then forall b /in a b /in TC(x).
end.
qed.



Lemma. Contradiction.
