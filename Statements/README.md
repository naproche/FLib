# Statements

This library has been created to investigate how formulas can be accessed in
then object-level of ForTheL in order to formalize theories which contain axiom
schemes or other meta-theoretical stuff. Be aware that its content is quite
experimental! Since this library contains proofs for many very basic statements
it might also be used as a foundation for more complex formalizations.


## Get access to new ATPs in the Isabelle interface of Naproche-SAD

This library was checked with [E](https://wwwlehre.dhbw-stuttgart.de/~sschulz/E/E.html)
2.5 and [Vampire](https://vprover.github.io/) 4.5.1. To be able to use these
ATPs within the Isabelle interface of Naproche-SAD make sure you can execute E
2.5 with the command `eprover-2.5` and Vampire 4.5.1 with the command
`vampire-4.5.1`.

Then replace the file
`Isabelle_Naproche-20190611/contrib/naproche-20190418/provers.dat` by
`FLib/Statements/provers.dat`.

Now you can enable those new ATPs in the Isabelle interface with the ForTheL
instructions `[prover eprover-2.5]` and `[prover vampire-4.5.1]`, respectively.
