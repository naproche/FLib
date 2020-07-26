[read RepresentationTheory/01_map.ftl]

# 1.8 quivers

Definition. A quiver is an object Q such that
     (Q(0) is a set)
 and (Q(1) is a set)
 and (Q(st) is a map from Q(1) to Q(0))
 and (Q(tl) is a map from Q(1) to Q(0)).

Let Q denote a quiver.

Definition. A vertex of Q is a member of Q(0).
Definition. An arrow of Q is a member of Q(1).

Definition. Let a,i be objects. a starts in i in Q iff
 a is an arrow of Q and i is a vertex of Q and Q(st)(a) = i.

Definition. Let a,i be objects. a ends in i in Q iff
 a is an arrow of Q and i is a vertex of Q and Q(tl)(a) = i.

Definition. Let a,i,j be objects. a is from i to j in Q iff a starts in i in Q and ends in j in Q.