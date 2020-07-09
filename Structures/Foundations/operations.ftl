#
# Operations
# (Marcel Schütz, 2020)
#

#[prove off][check off]
[read FLib/Structures/Foundations/maps.ftl]
#[prove on][check on]


# 1. Unary and binary operations

Signature FoundOp000. An operation is a notion.


Signature FoundOp005. Let f be an operation. f is unary is a statement.

Signature FoundOp010. Let f be an operation. f is binary is a statement.


# 2. Examples

Signature FoundOp100. \cdot is a binary operation.

Axiom FoundOp105. Let X be a class and x,y \in X. Then \cdot_{X}(x,y) = x \cdot y.


Signature FoundOp110. ^{-1} is a unary operation.

Axiom FoundOp115. Let X be a class and x \in X. Then ^{-1}_{X}(x) = x^{-1}.
