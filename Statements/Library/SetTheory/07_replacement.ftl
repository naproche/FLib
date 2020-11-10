# 7 The replacement schema

[read FLib/Statements/Library/SetTheory/06_functions.ftl]


# The replacement schema

Axiom 0701. Let F be a functional predicate and x be a zet. There is a zet y
such that y = {v | F(u,v) for some u \in x}.


################################################################################

# The following should be forbidden, i.e. it should not be possible to regard a
# predicate as a term!

Let F denote a functional predicate.

Definition. dom(F) = {x | F(x,y) for some object y}.
#           ^^^^^^

Definition. Let x \in dom(F). F{x} is the object y such that F(x,y).
#                     ^^^^^^  ^^^^

Definition. Let x,y be zets. A function from x to y is a functional predicate F
such that dom(F) = x and F{u} \in y for all u \in x.
#         ^^^^^^         ^^^^

################################################################################