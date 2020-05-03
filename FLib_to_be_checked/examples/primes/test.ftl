## fundamental_notions.ftl, Version 15.3.2012

# I. Foundations

#  1. Sets

## There is some interference between inbuilt set theory and the set theory
## explicitely introduced in a ForTheL text. Some set formations are 
## built in and lead to sets. E.g.
## the pair {x,y} is predefined and is a set by the reasoner.
## On the other hand there is no predefined empty set or singleton set {x}. 
## This leads to an asymmtry in the axiomatic setup: the empty set 
## requires an axiom whereas pairing doesn't.
##
## Some built in set theory seems to be a good thing. Too much would
## make the system too strong and might overburden the proving.
## But it would be good if the built in set theory were a definite
## small axiom system of set theory instead of a pragmatic collection
## of isolated fact.

[set/-s] [element/-s] [belong/-s] [subset/-s]

Signature Set.   A set is a notion.

Let $X,Y,Z$ stand for sets.

Signature Element. An element is a notion.

Let $x,y,z$ stand for elements.

Signature Element_of. An element of $X$ is a notion.
Let $x$ belongs to $X$ stand for $x$ is an element of $X$.
Let $x \in X$ stand for $x$ is an element of $X$.

Definition Subset.  A subset of $Y$ is a set $X$ such that
every element of $X$ belongs to Y.

Let $X \subseteq Y$ stand for $X$ is a subset of $Y$.

Lemma Subset_is_reflexive. $X \subseteq X$.

Lemma Subset_is_transitive. $X \subseteq Y \subseteq Z  =>  X \subseteq Z$.

Definition Emptyset.  $\emptyset$ is a set that has no elements.
Let $X$ is empty stand for $X = \emptyset$.
Let $X$ is nonempty stand for $X \neq \emptyset$.

Axiom Extensionality.     $X \subseteq Y \subseteq X  =>  X = Y$.

Lemma. If $X$ has no elements then $X=\emptyset$.

Lemma Pair. $x,y \in {x,y}$. If $z \in {x,y}$ then $z=x$ or $z=y$.

Lemma PairSet. ${x,y}$ is a set. 

Definition Union. $\bigcup(X) = \{ element z | z belongs to some set y 
such that y is an element of X \}$.
Axiom UnionSet. $\bigcup(X)$ is a set.

Definition Power. $\power(X) = \{ set Y | Y \subseteq X \}$.
Axiom PowerSet. $\power(X)$ is a set.






