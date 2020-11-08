# 1 Tarski's axioms

[read FLib/Statements/Library/statements.ftl]


Signature 0101. A point is a notion. Let u,v,w,x,y,z denote points.

Signature 0102. A line segment is a notion. Let X,Y,Z denote line segments.

Signature 0103. [x,y] is a line segment.


Signature 0104. X and Y are congruent is a relation. Let X \equiv Y stand for X
and Y are congruent.

Signature 0105. x is between y and z is a relation. Let x \in [y,z] stand for x
is between y and z. Let x \notin [y,z] stand for x is not between y and z.


# 1.1 Congruence axioms

# Reflexivity of congruence
Axiom 0106. [x,y] \equiv [y,x].

# Identity of congruence
Axiom 0107. If [x,y] \equiv [z,z] then x = y.

# Transitivity of congruence
Axiom 0108. If X \equiv Y and X \equiv Z then Y \equiv Z.


# 1.2 Betweenness axioms


# Identity of betweenness
Axiom 0109. If y \in [x,x] then x = y.


# Axiom of Pasch
Axiom 0110. If u \in [x,z] and v \in [y,z] then there is a point a such that
a \in [u,y] and a \in [v,x].

# Axiom schema of continuity
Axiom 0111. Let P,Q be statements. Assume that P is nullary or P is unary.
Assume that Q is nullary or Q is unary. If there is a point a such that for all
points x,y if P(x) and P(y) then x \in [a,y] then there is a point b such that
for all points x,y if P(x) and Q(y) then b \in [x,y].

# Lower dimension
Axiom 0112. There exist points a,b,c such that b \notin [a,c] and c \notin [b,a]
and a \notin [c,b].


# 1.3 Congruence and betweenness axioms

# Upper dimension
Axiom 0113. If [x,u] \equiv [x,v] and [y,u] \equiv [y,v] and [z,u] \equiv [z,v]
and u \neq v then y \in [x,z] or z \in [y,x] or x \in [z,y].

# Axiom of Euklid
Axiom 0114. If u \in [x,v] and u \in [y,z] and x \neq u then there exist points
a,b such that y \in [x,a] and z \in [x,b] and v \in [a,b].

# Five segment
Let a,b,c denote points.

Axiom 0115. If x \neq y and y \in [x,z] and b \in [a,c] and [x,y] \equiv [a,b]
and [y,z] \equiv [b,z] and [x,u] \equiv [x,v] and [y,u] \equiv [b,v] then
[z,u] \equiv [c,v].

# Segment construction
Axiom 0116. There exists a point z such that y \in [x,z] and [y,z] \equiv [a,b].
