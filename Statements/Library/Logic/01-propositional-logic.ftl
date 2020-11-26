# 1 Propositional logic

[read FLib/Statements/Library/statements.ftl]

[prover eprover-2.5]


Let P,Q,R denote statements that have no free variable.


# 1.1 Atomic propositions

Definition 0101. TRUE  = {x | it is wrong that we have a contradiction}.

Definition 0102. FALSE = {x | contradiction}.


# 1.2 Logical laws

# Excluded middle

Proposition 0103. "P" or not "P".

Proposition 0104. Not not "P" iff "P".


# Commutativity

Proposition 0105. "P" and "Q" iff "Q" and "P".

Proposition 0106. "P" or "Q" iff "Q" or "P".


# Associativity

Proposition 0107. ("P" and "Q") and "R" iff "P" and ("Q" and "R").

Proposition 0108. ("P" or "Q") or "R" iff "P" or ("Q" or "R").


# Distributivity

Proposition 0109. "P" and ("Q" or "R") iff ("P" and "Q") or ("P" and "R").

Proposition 0110. "P" or ("Q" and "R") iff ("P" or "Q") and ("P" or "R").


# Idempocy laws

Proposition 0111. "P" and "P" iff "P".

Proposition 0112. "P" or "P" iff "P".


# Complement laws

Proposition 0113. "P" and not "P" iff "FALSE".

Proposition 0114. "P" or not "P" iff "TRUE".


# Absorption laws

Proposition 0115. "P" and ("P" or "Q") iff "P".

Corollary 0116. "P" and "TRUE" iff "P".


Proposition 0117. "P" or ("P" and "Q") iff "P".

Corollary 0118. "P" or "FALSE" iff "P".


# De Morgan's laws

Proposition 0119. not ("P" and "Q") iff (not "P") or (not "Q").

Corollary 0120. "P" and "Q" iff not ((not "P") or (not "Q")).


Proposition 0121. not ("P" or "Q") iff (not "P") and (not "Q").

Corollary 0122. "P" or "Q" iff not ((not "P") and (not "Q")).


# Rewriting via implication

Proposition 0123. "P" and "Q" iff not ("P" => not "Q").

Proposition 0124. "P" or "Q" iff (not "P") => "Q".

Proposition 0125. "P" or "Q" iff (not "Q") => "P".

Proposition 0126. ("P" iff "Q") iff ("P" => "Q") and ("Q" => "P").


# Rewriting via disjunction and conjunction

Proposition 0127. ("P" iff "Q") iff ("P" and "Q") or ((not "P") and not "Q").

Corollary 0128. Not ("P" iff "Q") iff ((not "P") or not "Q") and ("P" or "Q").


Proposition 0129. ("P" iff "Q") iff ("P" or not "Q") and ("Q" or not "P").

Corollary 0130. Not ("P" iff "Q") iff ((not "P") and "Q") or ("P" and not "Q").


Proposition 0131. "P" => "Q" iff (not "P") or "Q".


# Contraposition

Proposition 0132. "P" => "Q" iff (not "Q") => not "P".

Corollary 0133. Not ("P" => "Q") iff "P" and not "Q".
