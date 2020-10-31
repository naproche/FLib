# Statements

## About

This library has been created to investigate how formulas can be accessed in
then object-level of ForTheL in order to formalize theories which contain axiom
schemes or which deal with mathematical logic. Be aware that its content is
quite experimental! Since this library contains proofs for many very basic
statements it might also be used as a foundation for more complex
formalizations.


## Get access to E-Prover 2.5 in the Isabelle interface of Naproche-SAD

This library was checked with version 2.5 of E-Prover. To be able to use
E-Prover 2.5 within the Isabelle interface of Naproche-SAD (instead of the
default version 2.0) make sure you can execute E-Prover 2.5 with the command
`eprover-2.5`.

Then replace the file
`Isabelle_Naproche-20190611/contrib/naproche-20190418/provers.dat` by
`FLib/Statements/provers.dat`.

Now you can set E-Prover 2.5 as ATP for Naproche-SAD in the Isabelle interface
with the ForTheL instruction `[prover eprover-2.5]`.
