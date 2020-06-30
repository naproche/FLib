# Foundations

This directory provides some basic mathematical notions.


## Classes

The file _classes.ftl_ introduces operations on entities which yiels classes and
provides basic facts about these operations.


## Maps

The fils _maps.ftl_ introduces maps as a generalization of functions and
defines various properties of them. Moreover basic facts of maps are stated.


## Families

The file _families.ftl_ introduces families and tuples. Furthermore products,
exponentiation and disjoint unions of classes are defined.


## Structures

The file _structures.ftl_ introduces mathematical structures X as classes which
are bijective function from dom(X) to X. That seems a bit inconvenient, but it
has some advantages:

* Since structures are classes we can regard them as subclasses of themselves.
* We can interpret the domain of a structure as its underlying class.
* Since there are no axioms which determine if two structure have elements in
  common, we can regard all structures as disjoint. This allows us to use some
  natural formulations in statements about structures.
* We do not need an extra function to switch between the elements of a structure
  and its underlying class (i.e. its domain).
