#
# The category of sets
# (Marcel Schütz, 2020)
#

#[prove off][check off]
[read FLib/Structures/Categories/morphisms.ftl]
#[prove on][check on]


Definition SetCat000. Hom_{SET} = {f | f is a map from some set to some set}.


Proposition SetCat005. SET and Hom_{SET} are classes such that Hom_{SET} is a homomorphism class
over SET.

Proof.
  SET and Hom_{SET} are classes.

  Every element of Hom_{SET} is a map from some element of SET to some element of SET.
  proof.
    Let f \in Hom_{SET}. Then f is a map from some set to some set.
  end.

  (1) Hence (SET, Hom_{SET}) satisfies Hom1 (by CatCat220).

  For all X \in SET we have id_{X} \in Hom_{SET} and dom(id_{X}) = X = codom(id_{X}).
  proof.
    Let X \in SET. Then X is a set. id_{X} is a map from X to X. dom(id_{X}) = X = codom(id_{X}).
  end.

  (2) Hence (SET, Hom_{SET}) satisfies Hom2 (by CatCat230).

  For all f,g \in Hom_{SET} such that codom(f) = dom(g) we have g \circ f \in Hom_{SET} and
  dom(g \circ f) = dom(f) and codom(g \circ f) = codom(g).
  proof.
    Let f,g \in Hom_{SET}. Take sets x,y,a,z such that f is a map from x to y and g is a map from a
    to z (by SetCat000). Assume that codom(f) = dom(g). Then a = y. Then range(f) \subseteq dom(g).
    Hence g \circ f is a map from x to z (by FoundMap045, FoundMap035).
  end.

  (3) Hence (SET, Hom_{SET}) satisfies Hom3 (by CatCat240).

  For all f \in Hom_{SET} we have id_{codom(f)} \circ f = f = f \circ id_{dom(f)}.

  (4) Hence (SET, Hom_{SET}) satisfies Hom4 (by CatCat250).


  For all f,g,h \in Hom_{SET} such that codom(f) = dom(g) and codom(g) = dom(h) we have
  (h \circ g) \circ f = h \circ (g \circ f).
  proof.
    Let f,g,h \in Hom_{SET}. Assume that codom(f) = dom(g) and codom(g) = dom(h). Then f,g,h are
    maps. f,g,h are maps. Moreover range(f) \subseteq dom(g) and range(g) \subseteq dom(h).
    Then we have the thesis (by FoundMap060).
  end.

  (5) Hence (SET, Hom_{SET}) satisfies Hom5 (by CatCat260).
  proof.
    [prove off] # Naproche-SAD doesn't want to prove it...
  end.

  We have dom(f),codom(f) \in SET for all f \in Hom_{SET}.

  (6) Hence (SET, Hom_{SET}) satisfies Hom6 (by CatCat285).
qed.


Definition SetCat010. Set = (SET, Hom_{SET})_{CAT}.

Let the category of sets stand for Set.


Proposition SetCat015. The category of sets is a locally small category.

Proof.
  SET and Hom_{SET} are classes such that Hom_{SET} is a homomorphism class over SET. Hence
  (SET, Hom_{SET}) lies in the domain of Cat_{2} (by CatCat295). Indeed dom(Cat_{2}) = CAT_{2}. Thus
  Cat_{2}(SET, Hom_{SET}) is a category. Therefore Set is a category (by CatCat345, SetCat010).

  Hom(X,Y) is a set for all objects X,Y of Set.
  proof.
    Set = (SET, Hom_{SET})_{CAT}. Let X,Y \in Obj(Set). Hom(X,Y) = {F | F is a morphism between X
    and Y}. Take elements x,y of SET such that X = Set(x) and Y = Set(y) (by CatCat365). x and y
    are sets. Define hom = {f | f is a map from x to y}. hom is a set (by SetSet112). Hence Hom(X,Y)
    = Set[hom] (by CatMor027).

    Every element of Hom(X,Y) is an element.
    proof.
      Let f \in Hom(X,Y). Then f is a morphism. Hence f is an element of some category. Every
      category is a structure. Then we have the thesis (by FoundStr007).
    end.

    hom is a subset of the domain of Set. Indeed every element of hom lies in Hom_{SET}. Then we
    have the thesis.
  end.
qed.
