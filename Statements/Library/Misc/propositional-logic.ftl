# Propositional logic

[read FLib/Statements/Library/statements.ftl]

[prover eprover-2.5]


Let P,Q,R denote statements that have no free variable.


# Atomic propositions

Definition PROP_01. TRUE  = {x | it is wrong that we have a contradiction}.

Definition PROP_02. FALSE = {x | contradiction}.


# Logical laws

## Excluded middle

Proposition PROP_03. "P" or not "P".

Proposition PROP_04. Not not "P" iff "P".


## Commutativity

Proposition PROP_05. "P" and "Q" iff "Q" and "P".

Proposition PROP_06. "P" or "Q" iff "Q" or "P".


## Associativity

Proposition PROP_07. ("P" and "Q") and "R" iff "P" and ("Q" and "R").

Proposition PROP_08. ("P" or "Q") or "R" iff "P" or ("Q" or "R").


## Distributivity

Proposition PROP_09. "P" and ("Q" or "R") iff ("P" and "Q") or ("P" and "R").

Proposition PROP_10. "P" or ("Q" and "R") iff ("P" or "Q") and ("P" or "R").


## Idempocy laws

Proposition PROP_11. "P" and "P" iff "P".

Proposition PROP_12. "P" or "P" iff "P".


## Complement laws

Proposition PROP_13. "P" and not "P" iff "FALSE".

Proposition PROP_14. "P" or not "P" iff "TRUE".


## Absorption laws

Proposition PROP_15. "P" and ("P" or "Q") iff "P".

Corollary PROP_16. "P" and "TRUE" iff "P".


Proposition PROP_17. "P" or ("P" and "Q") iff "P".

Corollary PROP_18. "P" or "FALSE" iff "P".


## De Morgan's laws

Proposition PROP_19. not ("P" and "Q") iff (not "P") or (not "Q").

Corollary PROP_20. "P" and "Q" iff not ((not "P") or (not "Q")).


Proposition PROP_21. not ("P" or "Q") iff (not "P") and (not "Q").

Corollary PROP_22. "P" or "Q" iff not ((not "P") and (not "Q")).


## Rewriting via implication

Proposition PROP_23. "P" and "Q" iff not ("P" => not "Q").

Proposition PROP_24. "P" or "Q" iff (not "P") => "Q".

Proposition PROP_25. "P" or "Q" iff (not "Q") => "P".

Proposition PROP_26. ("P" iff "Q") iff ("P" => "Q") and ("Q" => "P").


## Rewriting via disjunction and conjunction

Proposition PROP_27. ("P" iff "Q") iff ("P" and "Q") or ((not "P") and not "Q").

Corollary PROP_28. Not ("P" iff "Q") iff ((not "P") or not "Q") and ("P" or "Q").


Proposition PROP_29. ("P" iff "Q") iff ("P" or not "Q") and ("Q" or not "P").

Corollary PROP_30. Not ("P" iff "Q") iff ((not "P") and "Q") or ("P" and not "Q").


Proposition PROP_31. "P" => "Q" iff (not "P") or "Q".


## Contraposition

Proposition PROP_32. "P" => "Q" iff (not "Q") => not "P".

Corollary PROP_33. Not ("P" => "Q") iff "P" and not "Q".
