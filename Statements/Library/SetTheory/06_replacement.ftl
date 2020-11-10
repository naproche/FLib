# 6 Replacement

[read FLib/Statements/Library/SetTheory/02_elementary-set-theory.ftl]


Definition 0601. Let F be a predicate. F is functional iff F has two free
variables and for all objects x,y,z if F(x,y) and F(x,z) then y = z.

Let F denote a functional predicate.


Axiom 0602. Let x be a zet. There is a zet y such that y = {v | F(u,v) for some
u \in x}.


# The following should be forbidden, i.e. it should not be possible to regard a
# predicate as a term!

Definition 0603. dom(F) = {x | F(x,y) for some object y}.
#                ^^^^^^

Definition 0604. Let x \in dom(F). F{x} is the object y such that F(x,y).
#                          ^^^^^^  ^^^^

Definition 0605. Let x,y be zets. A function from x to y is a functional
predicate F such that dom(F) = x and F{u} \in y for all u \in x.
#                     ^^^^^^         ^^^^
