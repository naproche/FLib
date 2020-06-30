# Metric spaces

The files in this directory introduce metric spaces


## Metric spaces

The files _metric-spaces.ftl_ defines metrics on a set and introduces metric
spaces as mathematical structures and provides mechanisms for constructing
metric spaces.


## Open sets

The file _open-sets.ftl_ defines the epsilon-ball around a point of a metric
space and introduces open, closed sets and neighbourhoods. Moreover their basic
properties are stated, for example that the open sets form a topology.


## Continuous maps

The file _continuous-maps.ftl_ defines continuous functions between metric
spaces.


## Singleton sets are closed

The file _singletons-are-closed.ftl_ proves the fact that in a metric space
every singleton set is closed. That proof must not occur in any of the other
files about metric spaces since otherwise it would be imported to
_TopologicalSpaces/metrizable-spaces.ftl_ where the same statement is proven in
a different way.
