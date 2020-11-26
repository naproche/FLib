# 6 The replacement schema

[read FLib/Statements/Library/SetTheory/02_elementary-set-theory.ftl]


Definition 0701. Let F be a statement. F is functional iff F has two free
variables and for all objects x,y,z if (F(x,y) iff F(x,z)) then x = y.

# This definition is dangerous since it treats the meta-variable F as an object-
# variable...

Axiom 0702. Let F be a functional statement and x be a zet. There is a zet y
such that y = {v | F(u,v) for some u /in x}.


################################################################################

# The following should be forbidden, i.e. it should not be possible to regard a
# statement as a term!

Let F denote a functional statement.

Definition. dom(F) = {x | F(x,y) for some object y}.
#           ^^^^^^

Definition. Let x /in dom(F). F{x} is the object y such that F(x,y).
#                     ^^^^^^  ^^^^

Definition. Let x,y be zets. A function from x to y is a functional statement F
such that dom(F) = x and F{u} /in y for all u /in x.
#         ^^^^^^         ^^^^

################################################################################
