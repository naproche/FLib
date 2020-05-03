[a set/sets] [the empty set] [{} @ the empty set]
[a subset/subsets of x] [x <= y @ x is a subset of y]
[the union of x and y] [x + y @ the union of x and y]
[the intersection of x and y] [x * y @ the intersection of x and y]
[the complement of x to y] [y - x @ the complement of x to y]
[x is disjoint with y @ x * y = {}] [x !! y @ x is disjoint with y]

Axiom EmSet.   {} is a set.
Axiom SubSet.  Every subset of every set is a set.

Axiom _ReflSub. For every set A     A <= A.
Axiom AsymSub.  For all sets A,B    A <= B /\ B <= A => A = B.
Axiom TranSub.  For all sets A,B,C  A <= B /\ B <= C => A <= C.

Axiom UnSet.   For all sets A,B    A + B is a set.
Axiom InSet.   For all sets A,B    A * B is a set.
Axiom CmSet.   For all sets A,B    A - B is a set.

Axiom _IdemUn.  For every set A     A + A = A.
Axiom _IdemIn.  For every set A     A * A = A.
Axiom _UnEmpty. For every set A     A + {} = A /\ {} + A = A.
Axiom _InEmpty. For every set A     A * {} = {} /\ {} * A = {}.
Axiom _SubsmUn. For all sets A,B    A + (A * B) = A.
Axiom _SubsmIn. For all sets A,B    A * (A + B) = A.

Axiom _SubUn.   For all sets A,B    A <= A + B /\ B <= A + B.
Axiom _SubIn.   For all sets A,B    A * B <= A /\ A * B <= B.
Axiom _SubCm.   For all sets A,B    A - B <= A.

Axiom CommUn.   For all sets A,B    A + B = B + A.
Axiom CommIn.   For all sets A,B    A * B = B * A.
Axiom AssoUn.   For all sets A,B,C  (A + B) + C = A + (B + C).
Axiom AssoIn.   For all sets A,B,C  (A * B) * C = A * (B * C).
Axiom DistLUn.  For all sets A,B,C  A + (B * C) = (A + B) * (A + C).
Axiom DistLIn.  For all sets A,B,C  A * (B + C) = (A * B) + (A * C).
Axiom DistRUn.  For all sets A,B,C  (A * B) + C = (A + C) * (B + C).
Axiom DistRIn.  For all sets A,B,C  (A + B) * C = (A * C) + (B * C).
Axiom UnSub.    For all sets A,B    A <= B <=> A + B = B.
Axiom InSub.    For all sets A,B    A <= B <=> A * B = A.
Axiom CmCm.     For all sets A,B    A - (A - B) = A * B.
Axiom CmDj.     For all sets A,B    A !! B  <=>  (A + B) - A = B.
Axiom DjUn.     For all sets A,B,C  A !! B /\ A !! C  <=>  A !! (B + C).
Axiom DjCm.     For all sets A,B,C  A !! B /\ A <= C => A <= C - B.
Axiom UnCm.     For all sets A,B    (A + B) - A = B - A.
Axiom DuCm.     For all sets A,B    A !! B  =>  A - B = A.


