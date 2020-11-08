# 2 Basic results

[read FLib/Statements/Library/Geometry/01_tarskis-axioms.ftl]


Let a,b,c,d,e,f,x,y,z denote points. Let X,Y,Z denote line segments.


Proposition. [a,b] \equiv [a,b].

Proof.
  Take X = [b,a] and Y = [a,b] and Z = [a,b]. Then X \equiv Y and X \equiv Z.
  Hence Y \equiv Z. Therefore [a,b] \equiv [a,b].
qed.


Proposition. If [a,b] \equiv [c,d] then [c,d] \equiv [a,b].

Proof.
  Assume [a,b] \equiv [c,d]. Take X = [a,b] and Y = [c,d] and Z = [a,b]. Then
  X \equiv Y and X \equiv Z. Hence Y \equiv Z. Thus [c,d] \equiv [a,b].
qed.


Proposition. If [a,b] \equiv [c,d] and [c,d] \equiv [e,f] then
[a,b] \equiv [e,f].

Proof.
  Assume [a,b] \equiv [c,d] and [c,d] \equiv [e,f]. Then we have
  [c,d] \equiv [a,b]. Take X = [c,d] and Y = [a,b] and Z = [e,f]. Then
  X \equiv Y and X \equiv Z. Hence Y \equiv Z. Thus [a,b] \equiv [e,f].
qed.


Proposition. If [a,b] \equiv [c,d] then [b,a] \equiv [c,d].

Proof.
  Assume [a,b] \equiv [c,d]. Take X = [a,b] and Y = [b,a] and Z = [c,d]. Then
  X \equiv Y and X \equiv Z. Hence Y \equiv Z. Thus [b,a] \equiv [c,d].
qed.


Proposition. If [a,b] \equiv [c,d] then [a,b] \equiv [d,c].

Proof.
  Assume [a,b] \equiv [c,d]. Take X = [c,d] and Y = [a,b] and Z = [d,c]. Then
  X \equiv Y and X \equiv Z. Hence Y \equiv Z. Thus [a,b] \equiv [d,c].
qed.


Proposition. [a,a] \equiv [b,b].

Proof.
  Take a point x such that a \in [b,x] and [a,x] \equiv [b,b]. Then a = x. Hence
  [a,a] \equiv [b,b].
qed.
