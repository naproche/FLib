[synonym integer/-s] [synonym program/-s] [synonym code/-s]
[synonym succeed/-s] [synonym decide/-s] [synonym halt/-s]

Signature PrgSort.  A program is a notion.
Signature IntSort.  An integer is a notion.

Let U,V,W stand for programs.
Let x,y,z stand for integers.

Signature CodeInt.  A code of W is an integer.
Axiom ExiCode.      Every program has a code.

Signature HaltRel.  W halts on x is an atom.
Signature SuccRel.  W succeeds on x and y is an atom.

Definition DefDH.   W decides halting iff
    for every z and every code x of every V
        W succeeds on x and z iff V halts on z.

Axiom Cantor.       Let W decide halting.
    Then there exists V such that for every y
    V halts on y iff W does not succeed on y and y.

Proposition.        No program decides halting.
