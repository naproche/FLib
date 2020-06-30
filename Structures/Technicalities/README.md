# Technicalities

This directory contains some files that exist only for technical reasons.


## Prelude

_prelude.ftl_ provides synonyms for build-in notions and inrdocues the notion of
axioms. Such axioms can be used to break down large definitions in a conjunction
of atomic formulas. Consider for example the definition of metrics in
_Structures/MetricSpaces/metric-spaces.ftl_ to see how this works.


## synonyms

_synonyms.ftl_ provides a list of synonyms for every notion that is introduced
in the files of this library, e.g. _"topology"/"topologies"_.


## Signature

_signatures.ftl_ provides signature extensions for relations and operations that
we want to use for several types of mathematical objects. For example we want to
use the predicate "... is open" for both subsets of topological spaces and for
subsets of metric spaces. Hence we state

```
Signature. Let x be an entity. x is open is a statement
```

since we cannot introduce the same predicate for different types like this:

```
Signature. Let x be a subset of some metric space. x is open is a statemnt.
Signature. Let x be a subset of some topological space. x is open is a statemtnt.
```
