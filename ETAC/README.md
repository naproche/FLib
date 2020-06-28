# Elementary theory of abstract categories

This is a formalization of the first few bits of the _elementary theory of
abstract categories_ from Lawvere's paper [The Category of Categories as a
Foundation for Mathematics](https://link.springer.com/chapter/10.1007%2F978-3-642-99902-4_1).


## Usage

So that Naproche-SAD can verify this ForTheL-text we have to rename the build-in
notion "object" to "entity". To do this, rename line 200 of
_SAD.Data.Formula.Kit_ from

```
zObj = zTrm objectId "aObj" . pure -- this is a dummy for parsing purposes
```

to

```
zObj = zTrm entityId "aEntity" . pure -- this is a dummy for parsing purposes
```

and line 82 of _SAD.ForTheL.Base_ from

```
([Wd ["object", "objects"], Nm], zObj . head)]
```

to

```
([Wd ["entity", "entities"], Nm], zObj . head)]
```
.
