#
# The category of groups
# (Marcel Schütz, 2020)
#

#[prove off][check off]
[read FLib/Structures/Groups/groups.ftl]
[read FLib/Structures/Categories/functors.ftl]
[read FLib/Structures/Sets/category-of-sets.ftl]
#[prove on][check on]


Definition GrpCat000. Hom_{GRP} is the collection of group homomorphisms.


Proposition GrpCat005. GRP and Hom_{GRP} are classes such that Hom_{GRP} is a homomorphism class
over GRP.

Proof. [prove off] qed.


Definition GrpCat010. Grp = (GRP, Hom_{GRP})_{CAT}.

Let the category of groups stand for Grp.


Proposition GrpCat015. The category of groups is a subcategory of the category of sets.

Proof. [prove off] qed.
